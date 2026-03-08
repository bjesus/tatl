/**
 * Formula utilities: subformulas, closure, extended closure, patent inconsistency.
 *
 * References:
 * - Definition 5 (p.8): Closure of a formula
 * - Definition 6 (p.8): Closure of a set of formulas
 * - Definition 7 (p.8): Patent inconsistency
 * - Definition 15 (p.17): Extended closure
 */

import {
  type Formula,
  type Coalition,
  type Agent,
  FormulaSet,
  Not,
  D,
  formulaKey,
  coalitionSubset,
} from "./types.ts";
import { classifyFormula, type AlphaFormula, type BetaFormula } from "./classify.ts";

/**
 * Get all subformulas of a formula (Sub(ψ) in the paper).
 */
export function subformulas(f: Formula): FormulaSet {
  const result = new FormulaSet();
  function collect(g: Formula): void {
    if (result.has(g)) return;
    result.add(g);
    switch (g.kind) {
      case "atom":
        break;
      case "not":
        collect(g.sub);
        break;
      case "and":
        collect(g.left);
        collect(g.right);
        break;
      case "D":
        collect(g.sub);
        break;
      case "C":
        collect(g.sub);
        break;
    }
  }
  collect(f);
  return result;
}

/**
 * Get all subformulas of all formulas in a set.
 */
export function subformulasOfSet(fs: FormulaSet): FormulaSet {
  const result = new FormulaSet();
  for (const f of fs) {
    for (const sf of subformulas(f)) {
      result.add(sf);
    }
  }
  return result;
}

/**
 * Compute the closure of a formula (Definition 5, p.8).
 *
 * cl(φ) is the smallest set such that:
 * 1. φ ∈ cl(φ)
 * 2. cl(φ) is closed under α- and β-components
 * 3. For any ψ and coalition A, if ¬D_A ψ ∈ cl(φ) then ¬ψ ∈ cl(φ)
 */
export function closure(f: Formula): FormulaSet {
  const result = new FormulaSet();
  const worklist: Formula[] = [f];

  while (worklist.length > 0) {
    const current = worklist.pop()!;
    if (result.has(current)) continue;
    result.add(current);

    // Classify and add components
    const cls = classifyFormula(current);
    if (cls.type === "alpha" || cls.type === "beta") {
      for (const comp of cls.components) {
        if (!result.has(comp)) {
          worklist.push(comp);
        }
      }
    }

    // Rule 3: if ¬D_A ψ ∈ cl(φ) then ¬ψ ∈ cl(φ)
    if (
      current.kind === "not" &&
      current.sub.kind === "D"
    ) {
      const negSub = Not(current.sub.sub);
      if (!result.has(negSub)) {
        worklist.push(negSub);
      }
    }
  }

  return result;
}

/**
 * Compute the closure of a set of formulas (Definition 6, p.8).
 * cl(Δ) = ∪{cl(φ) | φ ∈ Δ}
 */
export function closureOfSet(fs: FormulaSet): FormulaSet {
  const result = new FormulaSet();
  for (const f of fs) {
    for (const g of closure(f)) {
      result.add(g);
    }
  }
  return result;
}

/**
 * Compute the extended closure of a formula (Definition 15, p.17).
 * ecl(θ) = {φ, ¬φ | φ ∈ cl(θ)}
 */
export function extendedClosure(f: Formula): FormulaSet {
  const cl = closure(f);
  const result = new FormulaSet();
  for (const g of cl) {
    result.add(g);
    result.add(Not(g));
  }
  return result;
}

/**
 * Compute the extended closure of a set of formulas.
 */
export function extendedClosureOfSet(fs: FormulaSet): FormulaSet {
  const cl = closureOfSet(fs);
  const result = new FormulaSet();
  for (const g of cl) {
    result.add(g);
    result.add(Not(g));
  }
  return result;
}

/**
 * Check if a set of formulas is patently inconsistent (Definition 7, p.8).
 * A set is patently inconsistent if it contains both φ and ¬φ.
 */
export function isPatentlyInconsistent(fs: FormulaSet): boolean {
  for (const f of fs) {
    if (f.kind === "not") {
      if (fs.has(f.sub)) return true;
    } else {
      if (fs.has(Not(f))) return true;
    }
  }
  return false;
}

/**
 * Collect all agents mentioned in a formula.
 */
export function agentsInFormula(f: Formula): Set<Agent> {
  const result = new Set<Agent>();
  function collect(g: Formula): void {
    switch (g.kind) {
      case "atom":
        break;
      case "not":
        collect(g.sub);
        break;
      case "and":
        collect(g.left);
        collect(g.right);
        break;
      case "D":
        for (const a of g.coalition) result.add(a);
        collect(g.sub);
        break;
      case "C":
        for (const a of g.coalition) result.add(a);
        collect(g.sub);
        break;
    }
  }
  collect(f);
  return result;
}

/**
 * Collect all agents mentioned in a set of formulas.
 */
export function agentsInFormulaSet(fs: FormulaSet): Set<Agent> {
  const result = new Set<Agent>();
  for (const f of fs) {
    for (const a of agentsInFormula(f)) {
      result.add(a);
    }
  }
  return result;
}

/**
 * Check if a formula is an eventuality (¬C_A φ).
 */
export function isEventuality(f: Formula): boolean {
  return f.kind === "not" && f.sub.kind === "C";
}

/**
 * Get all eventualities from a formula set.
 */
export function getEventualities(fs: FormulaSet): Formula[] {
  return fs.toArray().filter(isEventuality);
}

/**
 * Check if a formula has the form ¬D_A φ (a "diamond formula").
 */
export function isDiamond(f: Formula): boolean {
  return f.kind === "not" && f.sub.kind === "D";
}

/**
 * Check if a formula has the form D_A φ (a "box formula").
 */
export function isBox(f: Formula): boolean {
  return f.kind === "D";
}

/**
 * Get all non-empty subsets of a coalition.
 * Used when we need to consider all sub-coalitions.
 */
export function coalitionSubsets(coalition: Coalition): Coalition[] {
  const result: Coalition[] = [];
  const n = coalition.length;
  // Generate all non-empty subsets via bitmask
  for (let mask = 1; mask < (1 << n); mask++) {
    const subset: Agent[] = [];
    for (let i = 0; i < n; i++) {
      if (mask & (1 << i)) {
        subset.push(coalition[i]!);
      }
    }
    result.push(subset.sort());
  }
  return result;
}
