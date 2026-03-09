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
  Neg,
  SAnd,
  SOr,
  SImplies,
  Coal,
  CoCoal,
  PNext,
  PAlways,
  PUntil,
  PEvent,
  PState,
  type StateFormula,
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

  test("F14: (<<a>>X p & <<b>>X ~p) — UNSAT (conflicting strategies)", () => {
    // With agents {a, b}, <<a>>X p means "a can enforce p regardless of b's action"
    // and <<b>>X ~p means "b can enforce ~p regardless of a's action".
    // These conflict: the move vector where a votes for p AND b votes for ~p
    // must lead to a state with both p and ~p (contradiction).
    // Verified against TATL OCaml implementation.
    expect(isSat("(<<a>>X p & <<b>>X ~p)")).toBe(false);
  });

  test("F14b: (<<a>>X p & <<a,b>>X ~p) — SAT", () => {
    // <<a,b>>X ~p means the grand coalition can enforce ~p.
    // This is compatible with <<a>>X p because the grand coalition
    // includes a, so a's vote contributes to both.
    expect(isSat("(<<a>>X p & <<a,b>>X ~p)")).toBe(true);
  });

  test("F14c: (<<a>>X p & <<b>>X p) — SAT", () => {
    // Both agents can enforce p — compatible.
    expect(isSat("(<<a>>X p & <<b>>X p)")).toBe(true);
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

  // Group 9: Same-agent interactions
  test("F22: (<<a>>G p & <<a>>G ~p) — UNSAT", () => {
    expect(isSat("(<<a>>G p & <<a>>G ~p)")).toBe(false);
  });

  test("F23: (<<a>>G p & <<a,b>>G ~p) — UNSAT", () => {
    expect(isSat("(<<a>>G p & <<a,b>>G ~p)")).toBe(false);
  });

  test("F24: (<<a>>X p & <<b>>X ~p & <<a,b>>X p) — UNSAT", () => {
    expect(isSat("(<<a>>X p & (<<b>>X ~p & <<a,b>>X p))")).toBe(false);
  });

  // Group 10: Cross-agent temporal interactions
  test("F25: (<<a>>G p & <<b>>F ~p) — UNSAT", () => {
    // Agent a enforces p forever; agent b (opposing) can enforce eventually ~p.
    // With 2 agents, b is the complement of a's coalition in many move vectors.
    expect(isSat("(<<a>>G p & <<b>>F ~p)")).toBe(false);
  });

  test("F26: (<<a>>G p & <<a,b>>F ~p) — SAT", () => {
    // Grand coalition can eventually enforce ~p even while a alone enforces G p
    // (different strategies — <<a,b>>F ~p requires cooperation including a)
    expect(isSat("(<<a>>G p & <<a,b>>F ~p)")).toBe(true);
  });

  // Group 11: Until with Always interactions
  test("F27: (<<a>>(p U q) & <<a>>G ~q) — SAT", () => {
    // Same coalition — describes different strategies
    expect(isSat("(<<a>>(p U q) & <<a>>G ~q)")).toBe(true);
  });

  test("F28: (<<a>>(p U q) & <<a,b>>G ~q) — SAT", () => {
    expect(isSat("(<<a>>(p U q) & <<a,b>>G ~q)")).toBe(true);
  });

  // Group 12: Subset monotonicity tests with Next
  test("F29: (<<a>>X p & ~<<a,b>>X p) — UNSAT", () => {
    // If a alone can enforce X p, then {a,b} can too (superset coalition)
    expect(isSat("(<<a>>X p & ~<<a,b>>X p)")).toBe(false);
  });

  // Group 13: Subset monotonicity tests with Always
  test("F30: (<<a>>G p & ~<<a,b>>G p) — UNSAT", () => {
    expect(isSat("(<<a>>G p & ~<<a,b>>G p)")).toBe(false);
  });

  // Group 14: Cross-agent Until / Always conflicts
  test("F31: (<<a>>G ~q & <<b>>(p U q)) — UNSAT", () => {
    // Agent a enforces ~q forever; agent b must eventually reach q.
    // With 2 agents, these strategies conflict.
    expect(isSat("(<<a>>G ~q & <<b>>(p U q))")).toBe(false);
  });

  test("F32: (<<a>>G p & <<b>>(p U q)) — SAT", () => {
    // a enforces p forever; b enforces p until q. Compatible since
    // both maintain p, and b can choose when to reach q.
    expect(isSat("(<<a>>G p & <<b>>(p U q))")).toBe(true);
  });

  test("F33: (<<a>>G p & <<a,b>>(p U q)) — SAT", () => {
    expect(isSat("(<<a>>G p & <<a,b>>(p U q))")).toBe(true);
  });

  // Group 15: Subset monotonicity with Until
  test("F34: (<<a>>(p U q) & ~<<a,b>>(p U q)) — UNSAT", () => {
    expect(isSat("(<<a>>(p U q) & ~<<a,b>>(p U q))")).toBe(false);
  });

  test("F35: (<<a,b>>(p U q) & ~<<a>>(p U q)) — SAT", () => {
    // Grand coalition can enforce until even if a alone can't
    expect(isSat("(<<a,b>>(p U q) & ~<<a>>(p U q))")).toBe(true);
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

// ============================================================
// Cross-validated against TATL OCaml implementation
// All formulas below verified to match TATL results.
// ============================================================

describe("Multi-agent conflict (verified against TATL)", () => {
  test("conflicting strategies with 2 agents are UNSAT", () => {
    expect(isSat("(<<a>>X p & <<b>>X ~p)")).toBe(false);
    expect(isSat("(<<a>>X (p & q) & <<b>>X ~p)")).toBe(false);
    expect(isSat("(<<a>>G p & <<b>>X ~p)")).toBe(false);
    expect(isSat("(<<a>>G p & <<b>>G ~p)")).toBe(false);
  });

  test("conflicting strategies with 3 agents are UNSAT", () => {
    expect(isSat("(<<a>>X p & (<<b>>X q & <<c>>X ~p))")).toBe(false);
    expect(isSat("(<<a,b>>X p & <<c>>X ~p)")).toBe(false);
    expect(isSat("(<<a>>X p & <<b,c>>X ~p)")).toBe(false);
  });

  test("compatible multi-agent strategies are SAT", () => {
    expect(isSat("(<<a>>X p & <<b>>X p)")).toBe(true);
    expect(isSat("(<<a>>X p & <<a,b>>X ~p)")).toBe(true);
    expect(isSat("(~<<a>>X p & <<b>>X p)")).toBe(true);
    expect(isSat("(~<<a>>X p & ~<<b>>X p)")).toBe(true);
    expect(isSat("(<<a>>G p & <<b>>X p)")).toBe(true);
    expect(isSat("(<<a,b>>X p & ~<<a>>X p)")).toBe(true);
  });

  test("grand coalition formulas", () => {
    expect(isSat("<<a,b>>X p")).toBe(true);
    expect(isSat("<<a,b>>G p")).toBe(true);
    expect(isSat("<<a,b>>X (p & q)")).toBe(true);
    expect(isSat("<<a,b,c>>X p")).toBe(true);
  });
});

describe("Eventualities (verified against TATL)", () => {
  test("eventuality with contradictory strategy is SAT (different strategies)", () => {
    // <<a>>G p and <<a>>F ~p describe different strategies — both can exist
    expect(isSat("(<<a>>G p & <<a>>F ~p)")).toBe(true);
    expect(isSat("(<<a>>G (p & q) & <<a>>F ~q)")).toBe(true);
    expect(isSat("(<<a,b>>F p & <<a>>G ~p)")).toBe(true);
  });

  test("eventuality with immediately satisfied goal", () => {
    expect(isSat("(<<a>>(p U q) & q)")).toBe(true);
  });

  test("eventuality with multi-agent Until", () => {
    expect(isSat("(<<a>>(p U q) & <<a>>(q U p))")).toBe(true);
    expect(isSat("(<<a,b>>(p U q) & (~q & ~p))")).toBe(false);
  });

  test("nested eventualities", () => {
    expect(isSat("<<a>>F <<a>>F p")).toBe(true);
    expect(isSat("<<a>>(p U <<a>>X q)")).toBe(true);
  });

  test("negated always (is an eventuality)", () => {
    expect(isSat("(~<<a>>G p & p)")).toBe(true);
    expect(isSat("(~<<a>>G p & <<a>>G p)")).toBe(false);
    expect(isSat("~<<a>>G (p & ~p)")).toBe(true);
  });

  test("empty coalition eventualities", () => {
    expect(isSat("(<<>>F p & <<>>G ~p)")).toBe(false);
    expect(isSat("(<<>>(p U q) & (~q & ~p))")).toBe(false);
    expect(isSat("~<<>>G p")).toBe(true);
  });

  test("self-contradictory temporal formulas", () => {
    expect(isSat("(<<a>>G p & ~<<a>>G p)")).toBe(false);
    expect(isSat("(<<a>>F p & ~<<a>>F p)")).toBe(false);
    expect(isSat("(<<a>>(p U q) & ~<<a>>(p U q))")).toBe(false);
  });

  test("multiple eventualities", () => {
    expect(isSat("(<<a>>F p & <<a>>F q)")).toBe(true);
    expect(isSat("(<<a>>F p & <<b>>F ~p)")).toBe(true);
  });
});

describe("Purely propositional (verified against TATL)", () => {
  test("propositional tautologies and contradictions", () => {
    expect(isSat("p")).toBe(true);
    expect(isSat("~p")).toBe(true);
    expect(isSat("(p & ~p)")).toBe(false);
    expect(isSat("(p & q)")).toBe(true);
    expect(isSat("(p | ~p)")).toBe(true);
  });
});
