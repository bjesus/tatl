/**
 * α/β classification of CMAEL(CD) formulas (Table 1, p.8).
 *
 * α-formulas (conjunctive): their truth implies the truth of ALL components.
 *   ¬¬φ       → {φ}
 *   φ ∧ ψ     → {φ, ψ}
 *   D_A φ     → {D_A φ, φ}     (reflexivity of equivalence relation)
 *   C_A φ     → {φ} ∪ {D_a C_A φ | a ∈ A}   (Proposition 1)
 *
 * β-formulas (disjunctive): their truth implies the truth of AT LEAST ONE component.
 *   ¬(φ ∧ ψ)  → {¬φ, ¬ψ}
 *   ¬C_A φ    → {¬φ} ∪ {¬D_a C_A φ | a ∈ A}
 *
 * Elementary formulas (neither α nor β):
 *   p, ¬p, ¬D_A φ
 */

import {
  type Formula,
  Not,
  D,
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
          // ¬¬φ is an α-formula with component {φ}
          return { type: "alpha", components: [inner.sub] };

        case "and":
          // ¬(φ ∧ ψ) is a β-formula with components {¬φ, ¬ψ}
          return {
            type: "beta",
            components: [Not(inner.left), Not(inner.right)],
          };

        case "D":
          // ¬D_A φ is elementary (a "diamond" — handled by rule DR)
          return { type: "elementary" };

        case "C":
          // ¬C_A φ is a β-formula with components {¬φ} ∪ {¬D_a C_A φ | a ∈ A}
          return {
            type: "beta",
            components: [
              Not(inner.sub),
              ...inner.coalition.map((a) => Not(D([a], inner))),
            ],
          };
      }
      break;
    }

    case "and":
      // φ ∧ ψ is an α-formula with components {φ, ψ}
      return { type: "alpha", components: [f.left, f.right] };

    case "D":
      // D_A φ is an α-formula with components {D_A φ, φ}
      // Note: D_A φ is its own component (reflexivity)
      return { type: "alpha", components: [f, f.sub] };

    case "C":
      // C_A φ is an α-formula with components {φ} ∪ {D_a C_A φ | a ∈ A}
      return {
        type: "alpha",
        components: [
          f.sub,
          ...f.coalition.map((a) => D([a], f)),
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
