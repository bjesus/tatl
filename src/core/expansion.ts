/**
 * FullExpansion (Definition 9, p.9) and Cut-Saturated Expansion (Definition 14, p.17).
 *
 * FullExpansion takes a set of formulas Γ and produces FE(Γ) — a family of
 * fully expanded sets. Cut-Saturated Expansion extends this with analytic cut rules.
 */

import {
  type Formula,
  type Coalition,
  FormulaSet,
  Not,
  D,
  C,
  formulaEqual,
  formulaKey,
  coalitionSubset,
  coalitionIntersects,
} from "./types.ts";
import { classifyFormula } from "./classify.ts";
import { isPatentlyInconsistent, subformulas, isEventuality } from "./formula.ts";

/**
 * Check if a set is fully expanded (Definition 8, p.8):
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
 * Core expansion engine used by both fullExpansion and cutSaturatedExpansion.
 *
 * Strategy:
 * - Maintain a family of sets.
 * - Each pass: try to apply α-rule, β-rule, rule-3, and optionally cut-rules to each set.
 * - α-rules and β-rules REPLACE the set with result(s).
 * - Rule 3 (special ¬C_A ψ rule) ADDS a new set to the family without changing the original.
 * - Cut rules REPLACE the set with two branches.
 * - Iterate until fixpoint.
 */
function expandCore(
  gamma: FormulaSet,
  enableCuts: boolean,
  useRestrictedCuts: boolean
): FormulaSet[] {
  if (isPatentlyInconsistent(gamma)) {
    return [];
  }

  let family: FormulaSet[] = [gamma.clone()];

  // Track which (set-key, formula-key) pairs have had rule 3 applied.
  // This prevents infinite re-triggering.
  const rule3Applied = new Set<string>();

  let changed = true;
  while (changed) {
    changed = false;
    const nextFamily: FormulaSet[] = [];
    const extras: FormulaSet[] = []; // sets added by rule 3

    for (const phi of family) {
      // Try α-rule
      const alphaResult = tryAlphaRule(phi, gamma);
      if (alphaResult !== null) {
        if (!isPatentlyInconsistent(alphaResult)) {
          nextFamily.push(alphaResult);
        }
        changed = true;
        continue;
      }

      // Try β-rule
      const betaResult = tryBetaRule(phi, gamma);
      if (betaResult !== null) {
        for (const s of betaResult) {
          if (!isPatentlyInconsistent(s)) {
            nextFamily.push(s);
          }
        }
        changed = true;
        continue;
      }

      // Try rule 3 (adds extra sets without changing current set)
      const rule3Extras = tryRule3(phi, gamma, rule3Applied);
      if (rule3Extras.length > 0) {
        for (const s of rule3Extras) {
          if (!isPatentlyInconsistent(s)) {
            extras.push(s);
          }
        }
        // Keep the original set too (it's valid — has a β-component)
        nextFamily.push(phi);
        changed = true;
        continue;
      }

      // Try cut rules
      if (enableCuts) {
        const cutResult = tryCutRule(phi, useRestrictedCuts);
        if (cutResult !== null) {
          for (const s of cutResult) {
            if (!isPatentlyInconsistent(s)) {
              nextFamily.push(s);
            }
          }
          changed = true;
          continue;
        }
      }

      // No rule applies — this set is saturated
      nextFamily.push(phi);
    }

    // Add rule-3 extras
    for (const e of extras) {
      nextFamily.push(e);
      changed = true; // new sets added, need another pass
    }

    family = deduplicateSets(nextFamily);
  }

  return family;
}

/**
 * Try to apply an α-rule. Returns the modified set, or null.
 * Prioritizes eventualities from the original input.
 */
function tryAlphaRule(phi: FormulaSet, originalGamma: FormulaSet): FormulaSet | null {
  for (const f of orderedFormulas(phi, originalGamma)) {
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
function tryBetaRule(phi: FormulaSet, originalGamma: FormulaSet): FormulaSet[] | null {
  for (const f of orderedFormulas(phi, originalGamma)) {
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
 * Try to apply rule 3 of Definition 9 (special ¬C_A ψ rule).
 *
 * If ¬C_A ψ ∈ Φ and ¬ψ ∉ Φ, but some OTHER β-component is in Φ,
 * produce Φ ∪ {¬ψ} as an ADDITIONAL set (don't change Φ).
 *
 * Notice from the paper (Definition 9): "the procedure allows adding not more
 * than one β-component of a formula φ = ¬C_A ψ to the initial set, besides ¬ψ."
 *
 * We track which (set, formula) pairs have been processed to prevent re-triggering.
 */
function tryRule3(
  phi: FormulaSet,
  originalGamma: FormulaSet,
  rule3Applied: Set<string>
): FormulaSet[] {
  const extras: FormulaSet[] = [];

  for (const f of phi) {
    if (f.kind !== "not" || f.sub.kind !== "C") continue;

    const cls = classifyFormula(f);
    if (cls.type !== "beta") continue;

    const negPsi = Not(f.sub.sub); // ¬ψ
    if (phi.has(negPsi)) continue; // Already has ¬ψ

    // Check uniqueness key
    const key = phi.key() + "|" + formulaKey(f);
    if (rule3Applied.has(key)) continue;

    // Check if some OTHER β-component is present
    const otherComponents = cls.components.filter(
      (comp) => !formulaEqual(comp, negPsi)
    );
    const hasOther = otherComponents.some((comp) => phi.has(comp));

    if (hasOther) {
      rule3Applied.add(key);
      const additional = phi.clone();
      additional.add(negPsi);
      extras.push(additional);
    }
  }

  return extras;
}

/**
 * Try to apply a cut rule (CS1 or CS2).
 * Returns two branches, or null.
 */
function tryCutRule(
  phi: FormulaSet,
  useRestrictedCuts: boolean
): FormulaSet[] | null {
  for (const psi of phi) {
    const subs = subformulas(psi);
    for (const sub of subs) {
      // CS1: Cut on D_A φ
      if (sub.kind === "D") {
        if (!phi.has(sub) && !phi.has(Not(sub))) {
          if (!useRestrictedCuts || checkC1(psi, sub, phi)) {
            const b1 = phi.clone();
            b1.add(sub);
            const b2 = phi.clone();
            b2.add(Not(sub));
            return [b1, b2];
          }
        }
      }

      // CS2: Cut on C_A φ
      if (sub.kind === "C") {
        if (!phi.has(sub) && !phi.has(Not(sub))) {
          if (!useRestrictedCuts || checkC2(psi, sub, phi)) {
            const b1 = phi.clone();
            b1.add(sub);
            const b2 = phi.clone();
            b2.add(Not(sub));
            return [b1, b2];
          }
        }
      }
    }
  }
  return null;
}

/**
 * Order formulas: eventualities from original input first, then rest.
 */
function orderedFormulas(phi: FormulaSet, originalGamma: FormulaSet): Formula[] {
  const formulas = phi.toArray();
  const eventualities = formulas.filter(
    (f) => isEventuality(f) && originalGamma.has(f)
  );
  const rest = formulas.filter(
    (f) => !(isEventuality(f) && originalGamma.has(f))
  );
  return [...eventualities, ...rest];
}

// ============================================================
// Public API
// ============================================================

export function fullExpansion(gamma: FormulaSet): FormulaSet[] {
  return expandCore(gamma, false, true);
}

export function cutSaturatedExpansion(
  gamma: FormulaSet,
  useRestrictedCuts: boolean = true
): FormulaSet[] {
  return expandCore(gamma, true, useRestrictedCuts);
}

// ============================================================
// Cut condition checkers (C1, C2 from p.24)
// ============================================================

/**
 * C1: Cut on D_A φ ∈ Sub(ψ) where ψ ∈ Δ, if:
 * C11: ψ = D_B δ or ψ = ¬D_B δ, ∃ ¬D_E ε ∈ Δ: A ⊆ E and B ⊆ E
 * C12: ψ = ¬C_B δ, ∃ ¬D_E ε ∈ Δ: A ⊆ E and B ∩ E ≠ ∅
 */
function checkC1(psi: Formula, dAFormula: Formula, delta: FormulaSet): boolean {
  if (dAFormula.kind !== "D") return false;
  const A = dAFormula.coalition;

  let B: Coalition | null = null;
  let psiIsDB = false;
  let psiIsNegDB = false;
  let psiIsNegCB = false;

  if (psi.kind === "D") {
    B = psi.coalition; psiIsDB = true;
  } else if (psi.kind === "not" && psi.sub.kind === "D") {
    B = psi.sub.coalition; psiIsNegDB = true;
  } else if (psi.kind === "not" && psi.sub.kind === "C") {
    B = psi.sub.coalition; psiIsNegCB = true;
  }
  if (B === null) return false;

  for (const f of delta) {
    if (f.kind === "not" && f.sub.kind === "D") {
      const E = f.sub.coalition;
      if ((psiIsDB || psiIsNegDB) && coalitionSubset(A, E) && coalitionSubset(B, E))
        return true;
      if (psiIsNegCB && coalitionSubset(A, E) && coalitionIntersects(B, E))
        return true;
    }
  }
  return false;
}

/**
 * C2: Cut on C_A φ ∈ Sub(ψ) where ψ ∈ Δ, if:
 * C21: ψ = D_B δ or ψ = ¬D_B δ, ∃ ¬D_E ε ∈ Δ: B ⊆ E and A ∩ E ≠ ∅
 * C22: ψ = ¬C_B δ, ∃ ¬D_E ε ∈ Δ: A ∩ E ≠ ∅ and B ∩ E ≠ ∅
 */
function checkC2(psi: Formula, cAFormula: Formula, delta: FormulaSet): boolean {
  if (cAFormula.kind !== "C") return false;
  const A = cAFormula.coalition;

  let B: Coalition | null = null;
  let psiIsDB = false;
  let psiIsNegDB = false;
  let psiIsNegCB = false;

  if (psi.kind === "D") {
    B = psi.coalition; psiIsDB = true;
  } else if (psi.kind === "not" && psi.sub.kind === "D") {
    B = psi.sub.coalition; psiIsNegDB = true;
  } else if (psi.kind === "not" && psi.sub.kind === "C") {
    B = psi.sub.coalition; psiIsNegCB = true;
  }
  if (B === null) return false;

  for (const f of delta) {
    if (f.kind === "not" && f.sub.kind === "D") {
      const E = f.sub.coalition;
      if ((psiIsDB || psiIsNegDB) && coalitionSubset(B, E) && coalitionIntersects(A, E))
        return true;
      if (psiIsNegCB && coalitionIntersects(A, E) && coalitionIntersects(B, E))
        return true;
    }
  }
  return false;
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
