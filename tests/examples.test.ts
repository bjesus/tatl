/**
 * Integration tests using Examples from the paper:
 *
 * Example 1 (p.19): Construction phase for ¬D_{a,c} C_{a,b} p ∧ C_{a,b}(p ∧ q)
 * Example 3 (p.21): Full procedure → unsatisfiable (same formula)
 * Example 4 (p.25): ¬D_{a,b} p ∧ ¬D_{a,c} ¬D_a p → unsatisfiable (cut rule necessity)
 * Example 5 (p.29): C_{a,b} D_a p → ¬C_{b,c} D_b p (cut restriction efficiency)
 *
 * Additional tests:
 * - Simple satisfiable formulas
 * - Patent inconsistency
 */

import { describe, test, expect } from "bun:test";
import { parseFormula } from "../src/core/parser.ts";
import { printFormula } from "../src/core/printer.ts";
import { printFormulaSet } from "../src/core/printer.ts";
import { runTableau } from "../src/core/tableau.ts";
import {
  Atom,
  Not,
  And,
  D,
  C,
  Or,
  Implies,
  Ka,
  FormulaSet,
  formulaEqual,
} from "../src/core/types.ts";

// ============================================================
// Example 3 (p.21): Full procedure for ¬D_{a,c}C_{a,b}p ∧ C_{a,b}(p ∧ q)
// Expected: unsatisfiable
// ============================================================

describe("Example 3 (p.21): ¬D_{a,c}C_{a,b}p ∧ C_{a,b}(p ∧ q)", () => {
  const theta = parseFormula("(~D{a,c} C{a,b} p & C{a,b} (p & q))");

  test("formula is unsatisfiable", () => {
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(false);
  });

  test("final tableau is empty", () => {
    const result = runTableau(theta);
    expect(result.finalTableau.states.size).toBe(0);
  });

  test("pretableau has states and prestates", () => {
    const result = runTableau(theta);
    expect(result.pretableau.states.size).toBeGreaterThan(0);
    expect(result.pretableau.prestates.size).toBeGreaterThan(0);
  });

  test("initial tableau has states", () => {
    const result = runTableau(theta);
    expect(result.initialTableau.states.size).toBeGreaterThan(0);
  });
});

// ============================================================
// Example 4 (p.25): ¬D_{a,b}p ∧ ¬D_{a,c}¬D_a p
// Expected: unsatisfiable (demonstrates need for cut rules)
// ============================================================

describe("Example 4 (p.25): ¬D_{a,b}p ∧ ¬D_{a,c}¬Ka p", () => {
  const theta = parseFormula("(~D{a,b} p & ~D{a,c} ~Ka p)");

  test("formula is unsatisfiable with cuts", () => {
    const result = runTableau(theta, true);
    expect(result.satisfiable).toBe(false);
  });
});

// ============================================================
// Example 5 (p.29): C_{a,b}D_a p → ¬C_{b,c}D_b p
// This tests cut restriction efficiency.
// The formula is satisfiable (it's an implication that can be falsified or satisfied).
// Actually let's check: the paper uses this to compare state counts.
// ============================================================

describe("Example 5 (p.29): C_{a,b}Ka p → ¬C_{b,c}Kb p", () => {
  const theta = parseFormula("(C{a,b} Ka p -> ~C{b,c} Kb p)");

  test("with restricted cuts produces fewer states than unrestricted", () => {
    const restrictedResult = runTableau(theta, true);
    const unrestrictedResult = runTableau(theta, false);

    // Paper says restricted: 8 states, unrestricted: 35 states (for initial prestate expansion)
    // Our full tableau may differ in total counts since the paper only counts states(θ),
    // but the restricted version should have fewer or equal states.
    const restrictedStates = restrictedResult.pretableau.states.size;
    const unrestrictedStates = unrestrictedResult.pretableau.states.size;

    console.log(`  Restricted: ${restrictedStates} states, Unrestricted: ${unrestrictedStates} states`);
    expect(restrictedStates).toBeLessThanOrEqual(unrestrictedStates);
  });

  test("both restricted and unrestricted give same satisfiability answer", () => {
    const restrictedResult = runTableau(theta, true);
    const unrestrictedResult = runTableau(theta, false);
    expect(restrictedResult.satisfiable).toBe(unrestrictedResult.satisfiable);
  });
});

// ============================================================
// Simple satisfiable formula tests
// ============================================================

describe("Simple satisfiable formulas", () => {
  test("atom p is satisfiable", () => {
    const theta = Atom("p");
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(true);
  });

  test("¬p is satisfiable", () => {
    const theta = Not(Atom("p"));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(true);
  });

  test("Ka p is satisfiable", () => {
    const theta = Ka("a", Atom("p"));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(true);
  });

  test("Ka p ∧ ¬Kb p is satisfiable", () => {
    const theta = And(Ka("a", Atom("p")), Not(Ka("b", Atom("p"))));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(true);
  });

  test("¬Ka p is satisfiable", () => {
    const theta = Not(Ka("a", Atom("p")));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(true);
  });

  test("C{a,b} p is satisfiable", () => {
    const theta = C(["a", "b"], Atom("p"));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(true);
  });
});

// ============================================================
// Simple unsatisfiable formula tests
// ============================================================

describe("Simple unsatisfiable formulas", () => {
  test("p ∧ ¬p is unsatisfiable", () => {
    const theta = And(Atom("p"), Not(Atom("p")));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(false);
  });

  test("Ka p ∧ ¬Ka p is unsatisfiable", () => {
    const theta = And(Ka("a", Atom("p")), Not(Ka("a", Atom("p"))));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(false);
  });

  test("Ka ¬p ∧ Ka p is unsatisfiable", () => {
    // Ka ¬p means D_a ¬p, combined with Ka p = D_a p.
    // Together: agent a knows both p and ¬p, which is impossible.
    const theta = And(Ka("a", Not(Atom("p"))), Ka("a", Atom("p")));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(false);
  });
});

// ============================================================
// Properties of epistemic logic
// ============================================================

describe("Epistemic logic properties", () => {
  test("Ka p → p is valid (negation is unsatisfiable)", () => {
    // Ka p → p is valid, so ¬(Ka p → p) = Ka p ∧ ¬p should be unsat.
    const theta = And(Ka("a", Atom("p")), Not(Atom("p")));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(false);
  });

  test("Ka p → D{a,b} p is valid (negation is unsatisfiable)", () => {
    // Ka p (= D_a p) implies D_{a,b} p since R^D_{a,b} = R^D_a ∩ R^D_b ⊆ R^D_a
    // So if M,s |= D_a p then M,s |= D_{a,b} p (fewer successors to check)
    const theta = And(Ka("a", Atom("p")), Not(D(["a", "b"], Atom("p"))));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(false);
  });

  test("D{a,b} p does NOT imply Ka p (conjunction is satisfiable)", () => {
    // D_{a,b} p does NOT imply Ka p because R^D_{a,b} ⊆ R^D_a,
    // so D_{a,b} p only requires p at the intersection of a and b's knowledge.
    const theta = And(D(["a", "b"], Atom("p")), Not(Ka("a", Atom("p"))));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(true);
  });

  test("C{a,b} p → Ka p is valid (negation is unsatisfiable)", () => {
    // C_{a,b} p implies p, and Ka is reflexive, so C{a,b}p → Ka p
    // Actually C{a,b}p → p (by α-component) and C{a,b}p → D_a C{a,b}p → D_a p = Ka p
    const theta = And(C(["a", "b"], Atom("p")), Not(Ka("a", Atom("p"))));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(false);
  });

  test("C{a,b} p → Kb p is valid (negation is unsatisfiable)", () => {
    const theta = And(C(["a", "b"], Atom("p")), Not(Ka("b", Atom("p"))));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(false);
  });

  test("Ka p ∧ ¬Kb p is satisfiable (agents can have different knowledge)", () => {
    const theta = And(Ka("a", Atom("p")), Not(Ka("b", Atom("p"))));
    const result = runTableau(theta);
    expect(result.satisfiable).toBe(true);
  });
});
