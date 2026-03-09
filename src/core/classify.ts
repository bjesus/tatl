/**
 * State-level classification for ATL* formulas.
 *
 * In ATL*, the state-level α/β classification is simple because
 * coalition formulas are handled by gamma-decomposition (decomposition.ts),
 * not by α/β rules.
 *
 * State-level classification:
 *   α-formulas (conjunctive):
 *     And(φ, ψ)     → {φ, ψ}
 *     Neg(Neg(φ))    → {φ}  (double negation — shouldn't appear after NNF)
 *
 *   β-formulas (disjunctive):
 *     Or(φ, ψ)      → {φ, ψ}
 *
 *   γ-formulas (coalition — handled by gamma-decomposition):
 *     Coal(A, π) where π ≠ Next(State _)
 *     CoCoal(A, π) where π ≠ Next(State _)
 *
 *   Elementary:
 *     Top, Bot, Atom, Neg(Atom)
 *     Coal(A, Next(State φ))     — enforceable next-time
 *     CoCoal(A, Next(State φ))   — unavoidable next-time
 *
 * Reference: TATL construction.ml — saturation function
 */

import {
  type StateFormula,
} from "./types.ts";

export interface AlphaClassification {
  type: "alpha";
  components: StateFormula[];
}

export interface BetaClassification {
  type: "beta";
  components: StateFormula[];
}

export interface GammaClassification {
  type: "gamma";
}

export interface ElementaryClassification {
  type: "elementary";
}

export type Classification =
  | AlphaClassification
  | BetaClassification
  | GammaClassification
  | ElementaryClassification;

/**
 * Check if a state formula is a next-time formula:
 * Coal(A, Next(State φ)) or CoCoal(A, Next(State φ))
 */
export function isNextTime(f: StateFormula): boolean {
  return (
    (f.kind === "coal" || f.kind === "cocoal") &&
    f.path.kind === "next" &&
    f.path.sub.kind === "state"
  );
}

/**
 * Check if a state formula is an enforceable next-time: Coal(A, Next(State φ))
 */
export function isEnforceableNext(f: StateFormula): boolean {
  return (
    f.kind === "coal" &&
    f.path.kind === "next" &&
    f.path.sub.kind === "state"
  );
}

/**
 * Check if a state formula is an unavoidable next-time: CoCoal(A, Next(State φ))
 */
export function isUnavoidableNext(f: StateFormula): boolean {
  return (
    f.kind === "cocoal" &&
    f.path.kind === "next" &&
    f.path.sub.kind === "state"
  );
}

/**
 * Check if a state formula is a non-next coalition formula
 * (Coal or CoCoal where the path formula is NOT Next(State _)).
 * These are handled by gamma-decomposition.
 */
export function isGamma(f: StateFormula): boolean {
  if (f.kind === "coal" || f.kind === "cocoal") {
    return !(f.path.kind === "next" && f.path.sub.kind === "state");
  }
  return false;
}

/**
 * Classify a state formula as α, β, γ, or elementary.
 */
export function classifyState(f: StateFormula): Classification {
  switch (f.kind) {
    case "top":
    case "bot":
    case "atom":
      return { type: "elementary" };

    case "neg": {
      const inner = f.sub;
      switch (inner.kind) {
        case "atom":
        case "top":
        case "bot":
          return { type: "elementary" };
        case "neg":
          // ¬¬φ → α: {φ} (shouldn't appear after NNF, but handle it)
          return { type: "alpha", components: [inner.sub] };
        case "and":
          // ¬(φ ∧ ψ) → β: {¬φ, ¬ψ} (shouldn't appear after NNF, would be Or)
          return {
            type: "beta",
            components: [
              { kind: "neg", sub: inner.left },
              { kind: "neg", sub: inner.right },
            ],
          };
        case "or":
          // ¬(φ ∨ ψ) → α: {¬φ, ¬ψ} (shouldn't appear after NNF, would be And)
          return {
            type: "alpha",
            components: [
              { kind: "neg", sub: inner.left },
              { kind: "neg", sub: inner.right },
            ],
          };
        case "coal":
        case "cocoal":
          // ¬Coal/¬CoCoal — shouldn't appear after NNF
          // (NNF transforms ¬Coal → CoCoal and vice versa)
          // If it somehow appears, treat as elementary
          return { type: "elementary" };
      }
      break;
    }

    case "and":
      // φ ∧ ψ → α: {φ, ψ}
      return { type: "alpha", components: [f.left, f.right] };

    case "or":
      // φ ∨ ψ → β: {φ, ψ}
      return { type: "beta", components: [f.left, f.right] };

    case "coal":
    case "cocoal":
      if (f.path.kind === "next" && f.path.sub.kind === "state") {
        // Next-time formula — elementary
        return { type: "elementary" };
      }
      // Non-next coalition — handled by gamma-decomposition
      return { type: "gamma" };
  }
}
