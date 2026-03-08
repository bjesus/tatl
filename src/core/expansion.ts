/**
 * Downward saturation (SR rule) for ATL tableau.
 *
 * FullExpansion takes a set of formulas Γ and produces FE(Γ) — a family of
 * fully expanded sets, by applying α-rules and β-rules until fixpoint.
 *
 * In ATL there are no analytic cut rules (unlike CMAEL(CD)).
 * The expansion is simply full expansion.
 *
 * Reference: Goranko & Shkatov 2009, Section 4, Rule (SR), p.18
 */

import {
  type Formula,
  FormulaSet,
  Not,
  formulaKey,
} from "./types.ts";
import { classifyFormula } from "./classify.ts";
import { isPatentlyInconsistent, isEventuality } from "./formula.ts";

/**
 * Check if a set is fully expanded:
 * - Not patently inconsistent
 * - If α-formula ∈ Δ, all α-components are in Δ
 * - If β-formula ∈ Δ, at least one β-component is in Δ
 */
export function isFullyExpanded(fs: FormulaSet): boolean {
  if (isPatentlyInconsistent(fs)) return false;

  for (const f of fs) {
    const cls = classifyFormula(f);
    if (cls.type === "alpha") {
      for (const comp of cls.components) {
        if (!fs.has(comp)) return false;
      }
    } else if (cls.type === "beta") {
      const hasAny = cls.components.some((comp) => fs.has(comp));
      if (!hasAny) return false;
    }
  }
  return true;
}

/**
 * Full expansion: produce all maximally consistent, fully expanded sets
 * from an initial set of formulas.
 *
 * This applies:
 * - α-rules: add all components
 * - β-rules: branch into multiple sets (one per component)
 *
 * No cut rules in ATL.
 */
export function fullExpansion(gamma: FormulaSet): FormulaSet[] {
  if (isPatentlyInconsistent(gamma)) {
    return [];
  }

  let family: FormulaSet[] = [gamma.clone()];

  let changed = true;
  while (changed) {
    changed = false;
    const nextFamily: FormulaSet[] = [];

    for (const phi of family) {
      // Try α-rule
      const alphaResult = tryAlphaRule(phi);
      if (alphaResult !== null) {
        if (!isPatentlyInconsistent(alphaResult)) {
          nextFamily.push(alphaResult);
        }
        changed = true;
        continue;
      }

      // Try β-rule
      const betaResult = tryBetaRule(phi);
      if (betaResult !== null) {
        for (const s of betaResult) {
          if (!isPatentlyInconsistent(s)) {
            nextFamily.push(s);
          }
        }
        changed = true;
        continue;
      }

      // No rule applies — this set is saturated
      nextFamily.push(phi);
    }

    family = deduplicateSets(nextFamily);
  }

  return family;
}

/**
 * Try to apply an α-rule. Returns the modified set, or null.
 */
function tryAlphaRule(phi: FormulaSet): FormulaSet | null {
  for (const f of phi) {
    const cls = classifyFormula(f);
    if (cls.type === "alpha") {
      const missing = cls.components.filter((comp) => !phi.has(comp));
      if (missing.length > 0) {
        const result = phi.clone();
        for (const comp of missing) {
          result.add(comp);
        }
        return result;
      }
    }
  }
  return null;
}

/**
 * Try to apply a β-rule. Returns branches, or null.
 * Only applies when NO β-component is present.
 */
function tryBetaRule(phi: FormulaSet): FormulaSet[] | null {
  for (const f of phi) {
    const cls = classifyFormula(f);
    if (cls.type === "beta") {
      const hasAny = cls.components.some((comp) => phi.has(comp));
      if (!hasAny) {
        return cls.components.map((comp) => {
          const branch = phi.clone();
          branch.add(comp);
          return branch;
        });
      }
    }
  }
  return null;
}

/**
 * Deduplicate a list of formula sets (by their canonical key).
 */
function deduplicateSets(sets: FormulaSet[]): FormulaSet[] {
  const seen = new Set<string>();
  const result: FormulaSet[] = [];
  for (const s of sets) {
    const key = s.key();
    if (!seen.has(key)) {
      seen.add(key);
      result.push(s);
    }
  }
  return result;
}
