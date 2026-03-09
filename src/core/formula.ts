/**
 * Formula utilities for ATL* two-sorted formulas.
 *
 * Provides:
 * - Agent/coalition collection
 * - Patent inconsistency check
 * - Eventuality detection (recursive, path-level)
 * - Subformula collection
 * - Literal/primitive checks
 *
 * References:
 * - TATL global.ml — is_eventuality, contains_eventuality_operator,
 *   is_inconsistant, search_agent_state/path
 * - Goranko & Shkatov 2009 — ATL tableau definitions
 */

import {
  type StateFormula,
  type PathFormula,
  type Coalition,
  type Agent,
  type FormulaTuple,
  STop, SBot, Neg,
  StateFormulaSet,
  PathFormulaSet,
  stateKey,
  pathKey,
} from "./types.ts";

// ============================================================
// Agent collection
// ============================================================

/**
 * Collect all agents mentioned in a state formula.
 */
export function agentsInState(f: StateFormula): Set<Agent> {
  const result = new Set<Agent>();
  function collectState(g: StateFormula): void {
    switch (g.kind) {
      case "top": case "bot": case "atom": break;
      case "neg": collectState(g.sub); break;
      case "and": collectState(g.left); collectState(g.right); break;
      case "or": collectState(g.left); collectState(g.right); break;
      case "coal": case "cocoal":
        for (const a of g.coalition) result.add(a);
        collectPath(g.path);
        break;
    }
  }
  function collectPath(g: PathFormula): void {
    switch (g.kind) {
      case "state": collectState(g.sub); break;
      case "negp": collectPath(g.sub); break;
      case "andp": collectPath(g.left); collectPath(g.right); break;
      case "orp": collectPath(g.left); collectPath(g.right); break;
      case "next": collectPath(g.sub); break;
      case "always": collectPath(g.sub); break;
      case "until": collectPath(g.left); collectPath(g.right); break;
    }
  }
  collectState(f);
  return result;
}

/**
 * Collect all agents mentioned in a set of state formulas.
 */
export function agentsInStateSet(fs: StateFormulaSet): Set<Agent> {
  const result = new Set<Agent>();
  for (const f of fs) {
    for (const a of agentsInState(f)) result.add(a);
  }
  return result;
}

// ============================================================
// Patent inconsistency
// ============================================================

/**
 * Check if a state formula is a literal: Top, Bot, Prop, Neg(Prop).
 */
export function isLiteral(f: StateFormula): boolean {
  return f.kind === "top" || f.kind === "bot" || f.kind === "atom" ||
    (f.kind === "neg" && f.sub.kind === "atom");
}

/**
 * Check if a set of state formulas is patently inconsistent.
 *
 * A set is patently inconsistent if:
 * - It contains both Top and Bot
 * - It contains both p and ¬p for some proposition p
 *
 * Reference: TATL global.ml is_inconsistant
 */
export function isPatentlyInconsistent(fs: StateFormulaSet): boolean {
  // Collect literals
  const literals = new StateFormulaSet();
  for (const f of fs) {
    if (isLiteral(f)) literals.add(f);
  }

  // Check Top ∧ Bot
  if (literals.has(STop) && literals.has(SBot)) return true;

  // Check p ∧ ¬p
  for (const f of literals) {
    if (literals.has(Neg(f))) return true;
  }

  return false;
}

/**
 * Check if a set of FormulaTuples is patently inconsistent.
 * Extracts the .frm components and checks for contradictions.
 *
 * Reference: TATL global.ml is_inconsistant_tuple
 */
export function isPatentlyInconsistentTuples(tuples: Iterable<FormulaTuple>): boolean {
  const literals = new StateFormulaSet();
  for (const t of tuples) {
    if (isLiteral(t.frm)) literals.add(t.frm);
  }

  if (literals.has(STop) && literals.has(SBot)) return true;

  for (const f of literals) {
    if (literals.has(Neg(f))) return true;
  }

  return false;
}

// ============================================================
// Eventuality detection
// ============================================================

/**
 * Check if a path formula contains an eventuality operator (Until).
 * Recursively checks through path connectives.
 *
 * Reference: TATL global.ml contains_eventuality_operator
 */
export function containsEventualityOperator(path: PathFormula): boolean {
  switch (path.kind) {
    case "state": return false;
    case "until": return true;
    case "andp": return containsEventualityOperator(path.left) || containsEventualityOperator(path.right);
    case "orp": return containsEventualityOperator(path.left) || containsEventualityOperator(path.right);
    case "next": return containsEventualityOperator(path.sub);
    case "always": return containsEventualityOperator(path.sub);
    case "negp": return containsEventualityOperator(path.sub);
  }
}

/**
 * Check if a state formula is an eventuality.
 *
 * In ATL*, a formula is an eventuality if it's a Coal/CoCoal whose
 * path formula contains an Until operator (and it's not a simple
 * next-time formula).
 *
 * Reference: TATL global.ml is_eventuality
 */
export function isEventuality(f: StateFormula): boolean {
  if (f.kind === "coal" || f.kind === "cocoal") {
    // Coal(_, Next(_)) and CoCoal(_, Next(_)) are NOT eventualities
    if (f.path.kind === "next") return false;
    return containsEventualityOperator(f.path);
  }
  return false;
}

/**
 * Get all eventualities from a state formula set.
 */
export function getEventualities(fs: StateFormulaSet): StateFormula[] {
  return fs.toArray().filter(isEventuality);
}

/**
 * Get the coalition of an eventuality.
 */
export function eventualityCoalition(f: StateFormula): Coalition {
  if (f.kind === "coal" || f.kind === "cocoal") {
    return f.coalition;
  }
  throw new Error("Not a coalition formula");
}

// ============================================================
// Next-time formula checks
// ============================================================

/**
 * Check if a state formula is a positive next-time formula: Coal(A, Next(State(φ)))
 */
export function isEnforceableNext(f: StateFormula): boolean {
  return f.kind === "coal" && f.path.kind === "next" && f.path.sub.kind === "state";
}

/**
 * Check if a state formula is an unavoidable next-time formula: CoCoal(A, Next(State(φ)))
 */
export function isUnavoidableNext(f: StateFormula): boolean {
  return f.kind === "cocoal" && f.path.kind === "next" && f.path.sub.kind === "state";
}

/**
 * Check if a state formula is any next-time formula (enforceable or unavoidable).
 */
export function isNextTime(f: StateFormula): boolean {
  return isEnforceableNext(f) || isUnavoidableNext(f);
}

/**
 * Extract the inner state formula from a next-time formula.
 * Coal(A, Next(State(φ))) → φ
 * CoCoal(A, Next(State(φ))) → φ
 */
export function nextTimeInner(f: StateFormula): StateFormula {
  if ((f.kind === "coal" || f.kind === "cocoal") &&
      f.path.kind === "next" && f.path.sub.kind === "state") {
    return f.path.sub.sub;
  }
  throw new Error("Not a next-time formula");
}

// ============================================================
// Subformula collection
// ============================================================

/**
 * Get all state-level subformulas of a state formula.
 */
export function subformulasState(f: StateFormula): StateFormulaSet {
  const result = new StateFormulaSet();
  function collect(g: StateFormula): void {
    if (result.has(g)) return;
    result.add(g);
    switch (g.kind) {
      case "top": case "bot": case "atom": break;
      case "neg": collect(g.sub); break;
      case "and": collect(g.left); collect(g.right); break;
      case "or": collect(g.left); collect(g.right); break;
      case "coal": case "cocoal":
        // Also collect state formulas inside path formulas
        collectFromPath(g.path);
        break;
    }
  }
  function collectFromPath(g: PathFormula): void {
    switch (g.kind) {
      case "state": collect(g.sub); break;
      case "negp": collectFromPath(g.sub); break;
      case "andp": collectFromPath(g.left); collectFromPath(g.right); break;
      case "orp": collectFromPath(g.left); collectFromPath(g.right); break;
      case "next": collectFromPath(g.sub); break;
      case "always": collectFromPath(g.sub); break;
      case "until": collectFromPath(g.left); collectFromPath(g.right); break;
    }
  }
  collect(f);
  return result;
}

/**
 * Get all subformulas of all formulas in a set.
 */
export function subformulasOfSet(fs: StateFormulaSet): StateFormulaSet {
  const result = new StateFormulaSet();
  for (const f of fs) {
    for (const sf of subformulasState(f)) result.add(sf);
  }
  return result;
}
