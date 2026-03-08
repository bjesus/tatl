/**
 * Formula utilities: subformulas, closure, extended closure, patent inconsistency.
 *
 * References:
 * - Definition 4.4 (p.17): Closure of a formula
 * - Definition 4.5 (p.17): Extended closure
 * - Definition 4.3 (p.16): Patent inconsistency
 * - Goranko & Shkatov 2009
 */

import {
  type Formula,
  type Coalition,
  type Agent,
  FormulaSet,
  Not,
  Next,
  And,
  formulaKey,
  coalitionSubset,
} from "./types.ts";
import { classifyFormula } from "./classify.ts";

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
      case "next":
        collect(g.sub);
        break;
      case "always":
        collect(g.sub);
        break;
      case "until":
        collect(g.left);
        collect(g.right);
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
 * Compute the closure of a formula (Definition 4.4, p.17).
 *
 * cl(θ) is the smallest set containing θ that is closed under:
 * 1. α-components (if α ∈ cl(θ), then all α_i ∈ cl(θ))
 * 2. β-components (if β ∈ cl(θ), then all β_i ∈ cl(θ))
 *
 * For ATL, this means e.g.:
 * - If ⟨⟨A⟩⟩□ϕ ∈ cl(θ), then ϕ ∈ cl(θ) and ⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ ∈ cl(θ)
 * - If ⟨⟨A⟩⟩(ϕ U ψ) ∈ cl(θ), then ψ ∈ cl(θ) and (ϕ ∧ ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ)) ∈ cl(θ)
 * - etc.
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

    // For ¬⟨⟨A⟩⟩○ϕ, we need ¬ϕ in the closure as well
    // (the Next rule needs access to the inner formula's negation)
    if (current.kind === "not" && current.sub.kind === "next") {
      const negSub = Not(current.sub.sub);
      if (!result.has(negSub)) {
        worklist.push(negSub);
      }
    }
  }

  return result;
}

/**
 * Compute the closure of a set of formulas.
 * cl(Δ) = ∪{cl(ϕ) | ϕ ∈ Δ}
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
 * Compute the extended closure of a formula (Definition 4.5, p.17).
 * ecl(θ) = {ϕ, ¬ϕ | ϕ ∈ cl(θ)}
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
 * Check if a set of formulas is patently inconsistent (Definition 4.3, p.16).
 * A set is patently inconsistent if it contains both ϕ and ¬ϕ.
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
      case "next":
        for (const a of g.coalition) result.add(a);
        collect(g.sub);
        break;
      case "always":
        for (const a of g.coalition) result.add(a);
        collect(g.sub);
        break;
      case "until":
        for (const a of g.coalition) result.add(a);
        collect(g.left);
        collect(g.right);
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
 * Check if a formula is an eventuality.
 *
 * In ATL, the eventualities are:
 * - ⟨⟨A⟩⟩(ϕ U ψ)  — needs ψ to eventually hold
 * - ¬⟨⟨A⟩⟩□ϕ       — needs ¬ϕ to eventually hold
 *
 * These are the formulas that require realization checking (E3 elimination).
 */
export function isEventuality(f: Formula): boolean {
  // ⟨⟨A⟩⟩(ϕ U ψ) is an eventuality
  if (f.kind === "until") return true;

  // ¬⟨⟨A⟩⟩□ϕ is an eventuality
  if (f.kind === "not" && f.sub.kind === "always") return true;

  return false;
}

/**
 * Get all eventualities from a formula set.
 */
export function getEventualities(fs: FormulaSet): Formula[] {
  return fs.toArray().filter(isEventuality);
}

/**
 * Get the "goal" of an eventuality — the formula that must eventually hold.
 * - ⟨⟨A⟩⟩(ϕ U ψ)  → ψ
 * - ¬⟨⟨A⟩⟩□ϕ       → ¬ϕ
 */
export function eventualityGoal(f: Formula): Formula {
  if (f.kind === "until") return f.right;
  if (f.kind === "not" && f.sub.kind === "always") return Not(f.sub.sub);
  throw new Error("Not an eventuality");
}

/**
 * Get the coalition associated with an eventuality.
 * - ⟨⟨A⟩⟩(ϕ U ψ)  → A
 * - ¬⟨⟨A⟩⟩□ϕ       → A
 */
export function eventualityCoalition(f: Formula): Coalition {
  if (f.kind === "until") return f.coalition;
  if (f.kind === "not" && f.sub.kind === "always") return f.sub.coalition;
  throw new Error("Not an eventuality");
}

/**
 * Get the next-time formula that the eventuality unfolds into.
 * This is the formula whose D-set determines which edges the
 * eventuality realization can follow.
 *
 * - ⟨⟨A⟩⟩(ϕ U ψ) unfolds into ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ) (positive)
 * - ¬⟨⟨A⟩⟩□ϕ unfolds into ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ (negative)
 */
export function eventualityNextFormula(f: Formula): Formula {
  if (f.kind === "until") {
    // ⟨⟨A⟩⟩(ϕ U ψ) → ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ)
    return Next(f.coalition, f);
  }
  if (f.kind === "not" && f.sub.kind === "always") {
    // ¬⟨⟨A⟩⟩□ϕ → ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ
    return Not(Next(f.sub.coalition, f.sub));
  }
  throw new Error("Not an eventuality");
}

/**
 * Check if a formula is a positive next-time formula: ⟨⟨A⟩⟩○ϕ
 */
export function isPositiveNext(f: Formula): boolean {
  return f.kind === "next";
}

/**
 * Check if a formula is a negative next-time formula: ¬⟨⟨A⟩⟩○ϕ
 */
export function isNegativeNext(f: Formula): boolean {
  return f.kind === "not" && f.sub.kind === "next";
}

/**
 * Check if a formula is any next-time formula (positive or negative).
 */
export function isNextTime(f: Formula): boolean {
  return isPositiveNext(f) || isNegativeNext(f);
}
