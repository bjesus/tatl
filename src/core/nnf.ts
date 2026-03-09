/**
 * NNF (Negation Normal Form) transformation for ATL* formulas.
 *
 * Converts formulas so that:
 * - Negation only appears on atoms (state level) or is eliminated (path level)
 * - ¬⟨⟨A⟩⟩π → [[A]](¬π)  and  ¬[[A]]π → ⟨⟨A⟩⟩(¬π)
 * - Path-level negation is pushed inward using De Morgan, Until/Always duality
 * - Implication, equivalence, Release, Event are eliminated
 *
 * After NNF:
 *   State constructors: Top, Bot, Atom, Neg(Atom), And, Or, Coal, CoCoal
 *   Path constructors:  State(φ), AndP, OrP, Next, Always, Until
 *
 * Reference: TATL transformation_frm.ml
 */

import {
  type StateFormula,
  type PathFormula,
  STop, SBot, Atom, Neg, SAnd, SOr, Coal, CoCoal,
  PState, PAnd, POr, PNext, PAlways, PUntil, PNeg,
} from "./types.ts";

// ============================================================
// State-level NNF
// ============================================================

export function nnfState(f: StateFormula): StateFormula {
  switch (f.kind) {
    case "top":
    case "bot":
    case "atom":
      return f;

    case "neg": {
      const inner = f.sub;
      switch (inner.kind) {
        case "top": return SBot;
        case "bot": return STop;
        case "atom": return Neg(inner); // ¬p stays as-is
        case "neg": return nnfState(inner.sub); // ¬¬φ → φ
        case "and":
          return SOr(nnfState(Neg(inner.left)), nnfState(Neg(inner.right)));
        case "or":
          return SAnd(nnfState(Neg(inner.left)), nnfState(Neg(inner.right)));
        case "coal":
          return CoCoal(inner.coalition, nnfPath(PNeg(inner.path)));
        case "cocoal":
          return Coal(inner.coalition, nnfPath(PNeg(inner.path)));
      }
      break;
    }

    case "and":
      return SAnd(nnfState(f.left), nnfState(f.right));

    case "or":
      return SOr(nnfState(f.left), nnfState(f.right));

    case "coal":
      return Coal(f.coalition, nnfPath(f.path));

    case "cocoal":
      return CoCoal(f.coalition, nnfPath(f.path));
  }
}

// ============================================================
// Path-level NNF
// ============================================================

export function nnfPath(f: PathFormula): PathFormula {
  switch (f.kind) {
    case "state":
      return PState(nnfState(f.sub));

    case "negp": {
      const inner = f.sub;
      switch (inner.kind) {
        case "state":
          return PState(nnfState(Neg(inner.sub)));
        case "negp":
          return nnfPath(inner.sub); // ¬¬π → π
        case "andp":
          return POr(nnfPath(PNeg(inner.left)), nnfPath(PNeg(inner.right)));
        case "orp":
          return PAnd(nnfPath(PNeg(inner.left)), nnfPath(PNeg(inner.right)));
        case "next":
          return PNext(nnfPath(PNeg(inner.sub)));
        case "always":
          // ¬□π → ◇¬π → ⊤ U ¬π
          return PUntil(PState(STop), nnfPath(PNeg(inner.sub)));
        case "until":
          // Special case: ¬(⊤ U π) → □¬π
          if (inner.left.kind === "state" && inner.left.sub.kind === "top") {
            return PAlways(nnfPath(PNeg(inner.right)));
          }
          // General: ¬(π₁ U π₂) → □¬π₂ ∨ (¬π₂ U (¬π₁ ∧ ¬π₂))
          {
            const np1 = nnfPath(PNeg(inner.left));
            const np2 = nnfPath(PNeg(inner.right));
            return POr(PAlways(np2), PUntil(np2, PAnd(np1, np2)));
          }
      }
      break;
    }

    case "andp":
      return PAnd(nnfPath(f.left), nnfPath(f.right));

    case "orp":
      return POr(nnfPath(f.left), nnfPath(f.right));

    case "next":
      return PNext(nnfPath(f.sub));

    case "always":
      return PAlways(nnfPath(f.sub));

    case "until":
      return PUntil(nnfPath(f.left), nnfPath(f.right));
  }
}

// ============================================================
// Simplification (post-NNF)
// ============================================================

export function simplifyState(f: StateFormula): StateFormula {
  const s = simplifyStateOnce(f);
  if (stateStructuralEqual(f, s)) return s;
  return simplifyState(s);
}

function simplifyStateOnce(f: StateFormula): StateFormula {
  switch (f.kind) {
    case "top":
    case "bot":
    case "atom":
      return f;
    case "neg":
      if (f.sub.kind === "neg") return simplifyStateOnce(f.sub.sub);
      if (f.sub.kind === "top") return SBot;
      if (f.sub.kind === "bot") return STop;
      return Neg(simplifyStateOnce(f.sub));
    case "and":
      return SAnd(simplifyStateOnce(f.left), simplifyStateOnce(f.right));
    case "or":
      return SOr(simplifyStateOnce(f.left), simplifyStateOnce(f.right));
    case "coal":
      return Coal(f.coalition, simplifyPath(f.path));
    case "cocoal":
      return CoCoal(f.coalition, simplifyPath(f.path));
  }
}

export function simplifyPath(f: PathFormula): PathFormula {
  const s = simplifyPathOnce(f);
  if (pathStructuralEqual(f, s)) return s;
  return simplifyPath(s);
}

function simplifyPathOnce(f: PathFormula): PathFormula {
  switch (f.kind) {
    case "state":
      return PState(simplifyStateOnce(f.sub));
    case "negp":
      return PNeg(simplifyPathOnce(f.sub));
    case "andp":
      return PAnd(simplifyPathOnce(f.left), simplifyPathOnce(f.right));
    case "orp":
      return POr(simplifyPathOnce(f.left), simplifyPathOnce(f.right));
    case "next":
      return PNext(simplifyPathOnce(f.sub));

    case "always": {
      const inner = simplifyPathOnce(f.sub);
      // □□π → □π
      if (inner.kind === "always") return inner;
      // □○π → ○□π
      if (inner.kind === "next") return PNext(PAlways(simplifyPathOnce(inner.sub)));
      // □(⊤ U □π) → (⊤ U □π)  i.e. □◇□π → ◇□π
      if (inner.kind === "until" && inner.left.kind === "state" && inner.left.sub.kind === "top" && inner.right.kind === "always") {
        return PUntil(PState(STop), simplifyPathOnce(inner.right));
      }
      return PAlways(inner);
    }

    case "until": {
      const left = simplifyPathOnce(f.left);
      const right = simplifyPathOnce(f.right);
      // ◇□◇π → □◇π  i.e. (⊤ U □(⊤ U π)) → □(⊤ U π)
      if (left.kind === "state" && left.sub.kind === "top" && right.kind === "always"
        && right.sub.kind === "until" && right.sub.left.kind === "state" && right.sub.left.sub.kind === "top") {
        return PAlways(PUntil(PState(STop), simplifyPathOnce(right.sub.right)));
      }
      // ◇◇π → ◇π  i.e. (⊤ U (⊤ U π)) → (⊤ U π)
      if (left.kind === "state" && left.sub.kind === "top" && right.kind === "until"
        && right.left.kind === "state" && right.left.sub.kind === "top") {
        return PUntil(PState(STop), simplifyPathOnce(right.right));
      }
      // (⊤ U (π₁ U π₂)) where π₁ ≠ ⊤ → (⊤ U π₂)  i.e. ◇(φUψ) → ◇ψ
      if (left.kind === "state" && left.sub.kind === "top" && right.kind === "until") {
        return PUntil(PState(STop), simplifyPathOnce(right.right));
      }
      // (π₁ U (⊤ U π₂)) → ◇π₂  i.e. φU◇ψ → ◇ψ
      if (right.kind === "until" && right.left.kind === "state" && right.left.sub.kind === "top") {
        return PUntil(PState(STop), simplifyPathOnce(right.right));
      }
      return PUntil(left, right);
    }
  }
}

/** Full NNF + simplification pipeline for a state formula */
export function toNNF(f: StateFormula): StateFormula {
  return simplifyState(nnfState(f));
}

// ============================================================
// Structural equality (for simplification fixpoint detection)
// ============================================================

import { stateKey, pathKey } from "./types.ts";

function stateStructuralEqual(a: StateFormula, b: StateFormula): boolean {
  return stateKey(a) === stateKey(b);
}

function pathStructuralEqual(a: PathFormula, b: PathFormula): boolean {
  return pathKey(a) === pathKey(b);
}
