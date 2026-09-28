/**
 * The optimisations: input simplification, tableau-shape optimisations,
 * model extraction and the unsatisfiability proof.
 *
 * Every optimisation is an equivalence-preserving rewrite or a change to the
 * tableau's shape; none may change a verdict. The differential corpus at the
 * end checks that against the plain procedure on random formulas.
 */

import { describe, test, expect } from "bun:test";
import { parseFormula, systemAgents, type System } from "../src/core/parser.ts";
import { runTableau } from "../src/core/tableau.ts";
import { extractModel } from "../src/core/model.ts";
import { printFormula } from "../src/core/printer.ts";
import { DEFAULT_OPTIONS, PLAIN_OPTIONS, withOptions } from "../src/core/options.ts";
import { checkFormula, corpus } from "../src/core/difftest.ts";
import { textProof } from "../src/viz/text.ts";

function solve(input: string, system: System, extra: string[] = []) {
  return runTableau(parseFormula(input, system), [...systemAgents(system), ...extra]);
}

function simplified(input: string, system: System): string {
  return printFormula(solve(input, system).inputFormula, system === "atl" ? "atl" : system === "ltl" ? "ltl" : "ctl");
}

// ============================================================
// The grand-coalition shortcut must not depend on agent names
// ============================================================

describe("Hedging is skipped only for the grand coalition", () => {
  const f = (a: string, b: string) => `(<<${a}>>(F p | F q) & ~<<${a}>>F p & ~<<${a}>>F q & <<${b}>>X p)`;

  test("a coalition with an opponent can enforce a disjunction without either disjunct", () => {
    expect(solve(f("a", "b"), "atl").satisfiable).toBe(true);
    expect(solve(f("b", "c"), "atl").satisfiable).toBe(true);
  });

  test("the verdict is invariant under renaming agents", () => {
    for (const g of ["(<<a>>(F p | F q) & ~<<a>>F p & ~<<a>>F q)", "(<<a>>(G p | G q) & ~<<a>>G p)"]) {
      const renamed = g.replace(/<<a>>/g, "<<b>>");
      expect(solve(g, "atl", ["b"]).satisfiable).toBe(solve(renamed, "atl", ["a"]).satisfiable);
    }
  });

  test("with a as the only agent, the disjunction distributes", () => {
    expect(solve("(<<a>>(F p | F q) & ~<<a>>F p & ~<<a>>F q)", "atl").satisfiable).toBe(false);
  });
});

// ============================================================
// Input simplification
// ============================================================

describe("Input simplification", () => {
  test("propositional tautologies reduce to ⊤", () => {
    expect(simplified("(p -> p)", "ltl")).toBe("_top");
    expect(simplified("(p | ~p)", "ltl")).toBe("_top");
    expect(simplified("(G F p -> G F p)", "ltl")).toBe("_top");
    expect(simplified("(X p | ~X p)", "ltl")).toBe("_top");
    expect(simplified("(G F p | G F ~p)", "ltl")).toBe("_top");
    expect(solve("(G F p -> G F p)", "ltl").finalTableau.states.size).toBe(1);
  });

  test("contradictions reduce to ⊥ and are unsatisfiable", () => {
    expect(simplified("(p & ~p)", "ltl")).toBe("_bot");
    expect(simplified("(G F p & F G ~p)", "ltl")).toBe("_bot");
    expect(solve("(G F p & F G ~p)", "ltl").satisfiable).toBe(false);
  });

  test("absorption and idempotence", () => {
    expect(simplified("((p & q) | p)", "ltl")).toBe("p");
    expect(simplified("(G p & F p)", "ltl")).toBe("G p");
    expect(simplified("(p & p)", "ltl")).toBe("p");
  });

  test("temporal operators distribute over ∧ and ∨", () => {
    expect(simplified("(F G p & F G q)", "ltl")).toBe("F G (p & q)");
    expect(simplified("(X p & X q)", "ltl")).toBe("X (p & q)");
    expect(simplified("(F p | F q)", "ltl")).toBe("F (p | q)");
    expect(simplified("((p U q) | (p U r))", "ltl")).toBe("(p U (q | r))");
    expect(simplified("((p U r) & (q U r))", "ltl")).toBe("((p & q) U r)");
  });

  test("propositional subformulas are canonicalised exactly", () => {
    expect(simplified("((p & q) | (p & ~q))", "ltl")).toBe("p");
    expect(simplified("((p | q) & (p | ~q) & r)", "ltl")).toBe("(p & r)");
    expect(simplified("G((p & q) | (p & ~q) | (~p & q))", "ltl")).toBe("G (q | p)");
  });

  test("a coalition operator over a state formula is dropped", () => {
    expect(simplified("E p", "ctlstar")).toBe("p");
  });

  test("grand-coalition disjunctions are lifted in CTL* too", () => {
    const r = solve("E(G F p | F G q)", "ctlstar");
    expect(r.inputFormula.kind).toBe("or");
    expect(r.satisfiable).toBe(true);
  });

  test("the original formula is kept for display", () => {
    const r = solve("(p -> p)", "ltl");
    expect(printFormula(r.originalFormula, "ltl")).toBe("(~p | p)");
    expect(printFormula(r.inputFormula, "ltl")).toBe("_top");
  });
});

// ============================================================
// Tableau shape
// ============================================================

describe("Tableau size", () => {
  test("□◇p needs two states, not four", () => {
    expect(solve("G F p", "ltl").finalTableau.states.size).toBe(2);
  });

  test("re-associated conjunctions name the same prestate", () => {
    const r = solve("(G (p -> X q) & G ~q & F p)", "ltl");
    expect(r.pretableau.states.size).toBe(3);
    expect(r.satisfiable).toBe(false);
  });

  test("semantic branching makes every state a full valuation", () => {
    const r = solve("(G (p -> F q) & G (q -> F p))", "ltl");
    expect(r.finalTableau.states.size).toBe(12);
    for (const st of r.finalTableau.states.values()) {
      const lits = st.formulas.toArray().filter((f) => f.kind === "atom" || f.kind === "neg");
      expect(lits.length).toBe(2);
    }
  });

  test("the plain procedure is still available", () => {
    const plain = withOptions(PLAIN_OPTIONS, () => solve("G F p", "ltl"));
    expect(plain.finalTableau.states.size).toBe(4);
    expect(plain.satisfiable).toBe(true);
  });
});

// ============================================================
// Models and proofs
// ============================================================

describe("Model extraction", () => {
  test("□◇p has a one-state model with p", () => {
    const m = extractModel(solve("G F p", "ltl"))!;
    expect(m.states.length).toBe(1);
    expect(m.states[0]!.literals.map((l) => printFormula(l))).toEqual(["p"]);
    expect(m.edges).toEqual([{ from: "m0", to: "m0", label: [0] }]);
  });

  test("a tautology has a one-state model with no constraints", () => {
    const m = extractModel(solve("(G F p -> G F p)", "ltl"))!;
    expect(m.states.length).toBe(1);
    expect(m.states[0]!.literals).toEqual([]);
  });

  test("alternation needs a two-state cycle", () => {
    const m = extractModel(solve("(G F p & G F ~p)", "ltl"))!;
    const lits = m.states.map((s) => s.literals.map((l) => printFormula(l)).join(","));
    expect(lits).toContain("p");
    expect(lits).toContain("~p");
  });

  test("every model state has a successor for every move vector", () => {
    for (const [f, sys] of [["(AG EF p & EG ~p)", "ctl"], ["(<<a>>G p & <<a>>F ~p)", "atl"], ["<<a>>(F p | F q) & ~<<a>>F p & ~<<a>>F q & <<b>>X p", "atl"]] as const) {
      const m = extractModel(solve(f, sys))!;
      expect(m).not.toBeNull();
      for (const st of m.states) {
        const out = m.edges.filter((e) => e.from === st.id);
        expect(out.length).toBeGreaterThan(0);
        const labels = new Set(out.map((e) => e.label.join(",")));
        expect(labels.size).toBe(out.length);
      }
    }
  });

  test("unsatisfiable formulas have no model but a proof", () => {
    const r = solve("(G (p -> X q) & G ~q & F p)", "ltl");
    expect(extractModel(r)).toBeNull();
    const proof = textProof(r, "ltl");
    expect(proof).toContain("every initial state");
    expect(proof).toContain("E3");
    expect(proof).toContain("E2");
  });
});

// ============================================================
// Differential corpus
// ============================================================

describe("Optimisations preserve verdicts", () => {
  test("random formulas agree with the plain procedure, flag by flag", () => {
    const mismatches = [];
    for (const { formula, system, extraAgents } of corpus({ seed: 3, count: 120, maxDepth: 4, systems: ["ltl", "ctl", "ctlstar", "atl"] })) {
      mismatches.push(...checkFormula(formula, system, extraAgents));
    }
    expect(mismatches).toEqual([]);
  });

  test("the default options are all optimisations on", () => {
    for (const [k, v] of Object.entries(DEFAULT_OPTIONS)) {
      if (k !== "maxNodes" && k !== "deadline") expect(v).toBe(true);
    }
  });
});
