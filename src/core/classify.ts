/**
 * α/β classification of ATL formulas (Section 3.1, Table in Proposition 3.3).
 *
 * α-formulas (conjunctive): their truth implies the truth of ALL components.
 *   ¬¬ϕ         → {ϕ}
 *   ϕ ∧ ψ       → {ϕ, ψ}
 *   ⟨⟨A⟩⟩□ϕ    → {ϕ, ⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ}
 *
 * β-formulas (disjunctive): their truth implies the truth of AT LEAST ONE component.
 *   ¬(ϕ ∧ ψ)   → {¬ϕ, ¬ψ}
 *   ⟨⟨A⟩⟩ϕUψ   → {ψ, (ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩ϕUψ)}
 *   ¬⟨⟨A⟩⟩□ϕ   → {¬ϕ, (¬ϕ ∧ ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ)}   — Wait, let me re-check.
 *
 * Actually, from the paper (Proposition 3.3, equivalences for NNF):
 *   ¬⟨⟨A⟩⟩○ϕ           is a next-time formula (elementary in the classification)
 *   ¬⟨⟨A⟩⟩□ϕ   ≡ ⟨⟨Σ\A⟩⟩(⊤ U ¬ϕ)    — this is an "until" which is β
 *   ¬⟨⟨A⟩⟩(ϕ U ψ)  ≡ ⟨⟨Σ\A⟩⟩□(¬ψ) ∨ ⟨⟨Σ\A⟩⟩(¬ψ U (¬ϕ ∧ ¬ψ))
 *
 * But in the tableau procedure, we DON'T transform to NNF.
 * Instead, we classify formulas as they appear:
 *
 * From the paper (Section 4, Definition 4.1/4.2 — decomposition rules):
 *   α-formulas:
 *     ¬¬ϕ                          → {ϕ}
 *     ϕ ∧ ψ                        → {ϕ, ψ}
 *     ⟨⟨A⟩⟩□ϕ                     → {ϕ, ⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ}
 *     ¬⟨⟨A⟩⟩(ϕ U ψ)              → {¬ψ, ¬ϕ ∨ ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ)}  (see below)
 *
 *   β-formulas:
 *     ¬(ϕ ∧ ψ)                     → {¬ϕ, ¬ψ}
 *     ⟨⟨A⟩⟩(ϕ U ψ)               → {ψ, (ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ))}
 *     ¬⟨⟨A⟩⟩□ϕ                    → {¬ϕ, ⟨⟨A⟩⟩○¬⟨⟨A⟩⟩□ϕ}  -- Wait, this isn't right either.
 *
 * Let me follow the paper EXACTLY (Section 4.1, pp. 16-17):
 *
 * The paper uses "downward saturation" (SR rule) which applies:
 *   α-rule: if α ∈ Δ and α_i ∉ Δ, add α_i
 *   β-rule: if β ∈ Δ and no β_i ∈ Δ, branch
 *
 * From Proposition 3.3 (fixpoint characterizations):
 *   ⟨⟨A⟩⟩□ϕ    ≡ ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ              (α: both must hold)
 *   ⟨⟨A⟩⟩(ϕ U ψ) ≡ ψ ∨ (ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ))  (β: one must hold)
 *
 * For negations, using duality ¬⟨⟨A⟩⟩ ≡ [[Σ\A]] but since we don't
 * have [[A]] in our syntax, we keep negations and treat them:
 *   ¬⟨⟨A⟩⟩□ϕ   ≡ ¬ϕ ∨ ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ            (β: at least one must hold)
 *   ¬⟨⟨A⟩⟩(ϕ U ψ) ≡ ¬ψ ∧ (¬ϕ ∨ ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ))
 *             which is: {¬ψ} is always required, and ¬ϕ ∨ ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ)
 *
 * Actually, the cleanest way from the paper (matching TATL implementation):
 *
 *   ¬⟨⟨A⟩⟩□ϕ     → β with components {¬ϕ, ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ}
 *   ¬⟨⟨A⟩⟩(ϕ U ψ) → this has TWO parts:
 *       α-part: ¬ψ must hold (always)
 *       β-part: either ¬ϕ or ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ) must hold
 *     So it's BOTH α and β? The paper handles this by:
 *       - First α-expanding ¬⟨⟨A⟩⟩(ϕ U ψ) → {¬ψ, ¬⟨⟨A⟩⟩(ϕ U ψ)} ... no.
 *
 * Looking at the TATL OCaml code (decomposition.ml), the approach is:
 *   neg_until(A, ϕ, ψ):
 *     alpha-component: {¬ψ}
 *     beta-components: {¬ϕ, ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ)}
 *   This means it's BOTH: first add ¬ψ unconditionally (α), then branch on {¬ϕ, ¬⟨⟨A⟩⟩○...} (β)
 *
 * To match the paper's framework cleanly, we model this as a special "alpha-beta" type,
 * or we can decompose in two steps. For simplicity, let's follow the TATL approach:
 *
 * ¬⟨⟨A⟩⟩(ϕ U ψ) is α with components {¬ψ, X} where X = ¬ϕ ∨ ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ)
 * and X = ¬ϕ ∨ ... is equivalent to ¬(ϕ ∧ ...) which is a β with components {¬ϕ, ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ)}
 *
 * So: ¬⟨⟨A⟩⟩(ϕ U ψ) → α: {¬ψ, ¬(ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ))}
 *     (because ¬⟨⟨A⟩⟩(ϕ U ψ) ≡ ¬ψ ∧ ¬(ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ))
 *      which comes from negating: ψ ∨ (ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ)))
 *     And ¬(ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ)) is then a β-formula → {¬ϕ, ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ)}
 *
 * Similarly: ¬⟨⟨A⟩⟩□ϕ → negating ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ → ¬(ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ)
 *   → β: {¬ϕ, ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ}
 *
 * This all works out cleanly with the existing α/β framework!
 *
 * Summary of ATL classification:
 *   α-formulas:
 *     ¬¬ϕ               → {ϕ}
 *     ϕ ∧ ψ             → {ϕ, ψ}
 *     ⟨⟨A⟩⟩□ϕ          → {ϕ, ⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ}
 *     ¬⟨⟨A⟩⟩(ϕ U ψ)   → {¬ψ, ¬(ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ))}
 *
 *   β-formulas:
 *     ¬(ϕ ∧ ψ)          → {¬ϕ, ¬ψ}
 *     ⟨⟨A⟩⟩(ϕ U ψ)    → {ψ, (ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ))}
 *     ¬⟨⟨A⟩⟩□ϕ         → {¬ϕ, ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ}
 *
 *   Elementary:
 *     p, ¬p
 *     ⟨⟨A⟩⟩○ϕ, ¬⟨⟨A⟩⟩○ϕ    (next-time formulas — handled by the Next rule)
 */

import {
  type Formula,
  Not,
  And,
  Next,
  formulaEqual,
} from "./types.ts";

export interface AlphaFormula {
  type: "alpha";
  components: Formula[];
}

export interface BetaFormula {
  type: "beta";
  components: Formula[];
}

export interface ElementaryFormula {
  type: "elementary";
}

export type Classification = AlphaFormula | BetaFormula | ElementaryFormula;

/**
 * Classify a formula as α, β, or elementary.
 */
export function classifyFormula(f: Formula): Classification {
  switch (f.kind) {
    case "atom":
      // p is elementary
      return { type: "elementary" };

    case "not": {
      const inner = f.sub;
      switch (inner.kind) {
        case "atom":
          // ¬p is elementary
          return { type: "elementary" };

        case "not":
          // ¬¬ϕ is an α-formula with component {ϕ}
          return { type: "alpha", components: [inner.sub] };

        case "and":
          // ¬(ϕ ∧ ψ) is a β-formula with components {¬ϕ, ¬ψ}
          return {
            type: "beta",
            components: [Not(inner.left), Not(inner.right)],
          };

        case "next":
          // ¬⟨⟨A⟩⟩○ϕ is elementary (a negative next-time formula)
          return { type: "elementary" };

        case "always":
          // ¬⟨⟨A⟩⟩□ϕ ≡ ¬(ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ)
          // β-formula with components {¬ϕ, ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ}
          return {
            type: "beta",
            components: [
              Not(inner.sub),
              Not(Next(inner.coalition, inner)),
            ],
          };

        case "until":
          // ¬⟨⟨A⟩⟩(ϕ U ψ) ≡ ¬ψ ∧ ¬(ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ))
          // α-formula with components {¬ψ, ¬(ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ))}
          return {
            type: "alpha",
            components: [
              Not(inner.right),
              Not(And(inner.left, Next(inner.coalition, inner))),
            ],
          };
      }
      break;
    }

    case "and":
      // ϕ ∧ ψ is an α-formula with components {ϕ, ψ}
      return { type: "alpha", components: [f.left, f.right] };

    case "next":
      // ⟨⟨A⟩⟩○ϕ is elementary (a positive next-time formula)
      return { type: "elementary" };

    case "always":
      // ⟨⟨A⟩⟩□ϕ ≡ ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ
      // α-formula with components {ϕ, ⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ}
      return {
        type: "alpha",
        components: [f.sub, Next(f.coalition, f)],
      };

    case "until":
      // ⟨⟨A⟩⟩(ϕ U ψ) ≡ ψ ∨ (ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ))
      // β-formula with components {ψ, (ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ))}
      return {
        type: "beta",
        components: [
          f.right,
          And(f.left, Next(f.coalition, f)),
        ],
      };
  }
}

/**
 * Check if a formula is an α-formula.
 */
export function isAlpha(f: Formula): boolean {
  return classifyFormula(f).type === "alpha";
}

/**
 * Check if a formula is a β-formula.
 */
export function isBeta(f: Formula): boolean {
  return classifyFormula(f).type === "beta";
}

/**
 * Get the α-components of a formula (assumes it is an α-formula).
 */
export function alphaComponents(f: Formula): Formula[] {
  const cls = classifyFormula(f);
  if (cls.type !== "alpha") {
    throw new Error(`Formula is not an α-formula: ${f.kind}`);
  }
  return cls.components;
}

/**
 * Get the β-components of a formula (assumes it is a β-formula).
 */
export function betaComponents(f: Formula): Formula[] {
  const cls = classifyFormula(f);
  if (cls.type !== "beta") {
    throw new Error(`Formula is not a β-formula: ${f.kind}`);
  }
  return cls.components;
}
