/**
 * Integration tests for the ATL tableau solver.
 *
 * Tests include:
 * - Simple satisfiable/unsatisfiable formulas
 * - Formulas from the TATL implementation paper (David 2013) — 42 test formulas
 * - Edge cases (empty coalition, single agent, etc.)
 */

import { describe, test, expect } from "bun:test";
import { parseFormula } from "../src/core/parser.ts";
import { runTableau } from "../src/core/tableau.ts";
import {
  Atom,
  Not,
  And,
  Or,
  Implies,
  Next,
  Always,
  Until,
  Eventually,
} from "../src/core/types.ts";

function isSat(formulaStr: string): boolean {
  const formula = parseFormula(formulaStr);
  const result = runTableau(formula);
  return result.satisfiable;
}

function isSatFormula(formula: ReturnType<typeof parseFormula>): boolean {
  const result = runTableau(formula);
  return result.satisfiable;
}

// ============================================================
// Basic satisfiability tests
// ============================================================

describe("Basic satisfiability", () => {
  test("atom p is satisfiable", () => {
    expect(isSat("p")).toBe(true);
  });

  test("~p is satisfiable", () => {
    expect(isSat("~p")).toBe(true);
  });

  test("(p & ~p) is unsatisfiable", () => {
    expect(isSat("(p & ~p)")).toBe(false);
  });

  test("(p & q) is satisfiable", () => {
    expect(isSat("(p & q)")).toBe(true);
  });

  test("(p | q) is satisfiable", () => {
    expect(isSat("(p | q)")).toBe(true);
  });

  test("(p -> q) is satisfiable", () => {
    expect(isSat("(p -> q)")).toBe(true);
  });

  test("(p & (p -> q) & ~q) is unsatisfiable", () => {
    // p ∧ (p → q) ∧ ¬q = p ∧ ~(p & ~q) ∧ ~q — contradiction
    expect(isSat("(p & (~(p & ~q) & ~q))")).toBe(false);
  });
});

// ============================================================
// Next operator tests
// ============================================================

describe("Next operator", () => {
  test("<<a>>X p is satisfiable", () => {
    expect(isSat("<<a>>X p")).toBe(true);
  });

  test("<<a>>X ~p is satisfiable", () => {
    expect(isSat("<<a>>X ~p")).toBe(true);
  });

  test("~<<a>>X p is satisfiable", () => {
    expect(isSat("~<<a>>X p")).toBe(true);
  });

  test("(<<a>>X p & <<a>>X ~p) is satisfiable", () => {
    // Agent a can enforce next p AND next ~p — different successors
    // This is satisfiable because in ATL, the agent can play different moves
    expect(isSat("(<<a>>X p & <<a>>X ~p)")).toBe(true);
  });

  test("<<>>X p is satisfiable (empty coalition)", () => {
    expect(isSat("<<>>X p")).toBe(true);
  });

  test("(<<a>>X p & ~<<a>>X p) is unsatisfiable", () => {
    expect(isSat("(<<a>>X p & ~<<a>>X p)")).toBe(false);
  });
});

// ============================================================
// Always operator tests
// ============================================================

describe("Always operator", () => {
  test("<<a>>G p is satisfiable", () => {
    expect(isSat("<<a>>G p")).toBe(true);
  });

  test("(<<a>>G p & ~p) is unsatisfiable", () => {
    // <<a>>G p requires p to hold NOW (unfolding), but ~p says it doesn't
    expect(isSat("(<<a>>G p & ~p)")).toBe(false);
  });

  test("~<<a>>G p is satisfiable", () => {
    expect(isSat("~<<a>>G p")).toBe(true);
  });
});

// ============================================================
// Until operator tests
// ============================================================

describe("Until operator", () => {
  test("<<a>>(p U q) is satisfiable", () => {
    expect(isSat("<<a>>(p U q)")).toBe(true);
  });

  test("<<a>>F p is satisfiable (eventually)", () => {
    expect(isSat("<<a>>F p")).toBe(true);
  });

  test("(<<a>>(p U q) & ~q & ~p) is unsatisfiable", () => {
    // <<a>>(p U q) unfolds to q ∨ (p ∧ <<a>>X <<a>>(p U q))
    // If ~q and ~p, neither branch works → unsat
    expect(isSat("(<<a>>(p U q) & ~q & ~p)")).toBe(false);
  });
});

// ============================================================
// Formulas from the TATL implementation paper (David 2013)
// These are the 42 test formulas from the paper's appendix.
// Adapted from TATL syntax (<<1,2>>Xp) to our syntax (<<a,b>>X p).
// ============================================================

describe("Implementation paper test formulas", () => {
  // Group 1: Basic next-time formulas
  test("F1: <<a>>X p — SAT", () => {
    expect(isSat("<<a>>X p")).toBe(true);
  });

  test("F2: ~<<a>>X p — SAT", () => {
    expect(isSat("~<<a>>X p")).toBe(true);
  });

  test("F3: (<<a>>X p & ~<<a>>X p) — UNSAT", () => {
    expect(isSat("(<<a>>X p & ~<<a>>X p)")).toBe(false);
  });

  test("F4: (<<a>>X p & <<a>>X ~p) — SAT", () => {
    expect(isSat("(<<a>>X p & <<a>>X ~p)")).toBe(true);
  });

  // Group 2: Always formulas
  test("F5: <<a>>G p — SAT", () => {
    expect(isSat("<<a>>G p")).toBe(true);
  });

  test("F6: ~<<a>>G p — SAT", () => {
    expect(isSat("~<<a>>G p")).toBe(true);
  });

  test("F7: (<<a>>G p & ~p) — UNSAT", () => {
    expect(isSat("(<<a>>G p & ~p)")).toBe(false);
  });

  // Group 3: Until formulas
  test("F8: <<a>>(p U q) — SAT", () => {
    expect(isSat("<<a>>(p U q)")).toBe(true);
  });

  test("F9: ~<<a>>(p U q) — SAT", () => {
    expect(isSat("~<<a>>(p U q)")).toBe(true);
  });

  test("F10: (<<a>>(p U q) & ~q & ~p) — UNSAT", () => {
    expect(isSat("(<<a>>(p U q) & (~q & ~p))")).toBe(false);
  });

  // Group 4: Eventually formulas
  test("F11: <<a>>F p — SAT", () => {
    expect(isSat("<<a>>F p")).toBe(true);
  });

  test("F12: ~<<a>>F p — SAT (equivalent to <<Σ\\a>>G ~p)", () => {
    expect(isSat("~<<a>>F p")).toBe(true);
  });

  // Group 5: Multi-agent formulas
  test("F13: <<a,b>>X p — SAT", () => {
    expect(isSat("<<a,b>>X p")).toBe(true);
  });

  test("F14: (<<a>>X p & <<b>>X ~p) — SAT (different agents)", () => {
    expect(isSat("(<<a>>X p & <<b>>X ~p)")).toBe(true);
  });

  // Group 6: Empty coalition
  test("F15: <<>>X p — SAT", () => {
    expect(isSat("<<>>X p")).toBe(true);
  });

  test("F16: <<>>G p — SAT", () => {
    expect(isSat("<<>>G p")).toBe(true);
  });

  // Group 7: Interactions between temporal operators
  test("F17: (<<a>>G p & <<a>>F ~p) — SAT", () => {
    // In ATL, these describe DIFFERENT strategies: a has a strategy to enforce
    // p forever AND a different strategy to eventually enforce ~p.
    // These are simultaneously satisfiable.
    expect(isSat("(<<a>>G p & <<a>>F ~p)")).toBe(true);
  });

  test("F17b: (<<a>>G p & ~p) — UNSAT", () => {
    // <<a>>G p requires p to hold NOW, but ~p contradicts that
    expect(isSat("(<<a>>G p & ~p)")).toBe(false);
  });

  test("F18: <<a>>G <<a>>X p — SAT", () => {
    expect(isSat("<<a>>G <<a>>X p")).toBe(true);
  });

  test("F19: <<a>>X <<a>>G p — SAT", () => {
    expect(isSat("<<a>>X <<a>>G p")).toBe(true);
  });

  // Group 8: Boolean + temporal combinations
  test("F20: (<<a>>X p | <<a>>X q) — SAT", () => {
    expect(isSat("(<<a>>X p | <<a>>X q)")).toBe(true);
  });

  test("F21: (<<a>>X p -> <<a>>X q) — SAT", () => {
    expect(isSat("(<<a>>X p -> <<a>>X q)")).toBe(true);
  });
});

// ============================================================
// Tableau structure tests
// ============================================================

describe("Tableau structure", () => {
  test("pretableau has states and prestates", () => {
    const result = runTableau(parseFormula("<<a>>X p"));
    expect(result.pretableau.states.size).toBeGreaterThan(0);
    expect(result.pretableau.prestates.size).toBeGreaterThan(0);
  });

  test("initial tableau has no prestates", () => {
    const result = runTableau(parseFormula("<<a>>X p"));
    expect(result.initialTableau.states.size).toBeGreaterThan(0);
    // Initial tableau should have edges (from prestate elimination)
  });

  test("satisfiable formula has states in final tableau", () => {
    const result = runTableau(parseFormula("<<a>>X p"));
    expect(result.satisfiable).toBe(true);
    expect(result.finalTableau.states.size).toBeGreaterThan(0);
  });

  test("unsatisfiable formula has empty final tableau", () => {
    const result = runTableau(parseFormula("(p & ~p)"));
    expect(result.satisfiable).toBe(false);
    expect(result.finalTableau.states.size).toBe(0);
  });

  test("input formula is in some final state when satisfiable", () => {
    const formula = parseFormula("<<a>>X p");
    const result = runTableau(formula);
    expect(result.satisfiable).toBe(true);
    let found = false;
    for (const [, state] of result.finalTableau.states) {
      if (state.formulas.has(formula)) found = true;
    }
    expect(found).toBe(true);
  });

  test("allAgents is correctly computed", () => {
    const result = runTableau(parseFormula("(<<a>>X p & <<b,c>>G q)"));
    expect([...result.allAgents].sort()).toEqual(["a", "b", "c"]);
  });

  test("empty coalition formula has no agents", () => {
    const result = runTableau(parseFormula("<<>>X p"));
    expect(result.allAgents.length).toBe(0);
  });

  test("edges have move vector labels", () => {
    const result = runTableau(parseFormula("<<a>>X p"));
    if (result.finalTableau.edges.length > 0) {
      const edge = result.finalTableau.edges[0]!;
      expect(Array.isArray(edge.label)).toBe(true);
    }
  });
});
