/**
 * LTL and CTL: the one-agent fragments of ATL*.
 *
 * Both are translated into ATL* over a model with exactly one agent, where a
 * single agent's strategies coincide with paths:
 *
 *   <<a>>π   some path satisfies π   (E)
 *   <<>>π    every path satisfies π  (A)
 *
 * These tests pin down the translation, the satisfiability results against
 * textbook facts, and the syntax each system rejects.
 */

import { describe, test, expect } from "bun:test";
import { parseFormula, parseFormulaRaw, systemAgents } from "../src/core/parser.ts";
import { printFormula } from "../src/core/printer.ts";
import { runTableau } from "../src/core/tableau.ts";
import type { System } from "../src/core/parser.ts";

function translate(input: string, system: System): string {
  return printFormula(parseFormulaRaw(input, system));
}

function isSat(input: string, system: System): boolean {
  const formula = parseFormula(input, system);
  return runTableau(formula, systemAgents(system)).satisfiable;
}

// ============================================================
// Agent set
// ============================================================

describe("System agent sets", () => {
  test("ATL* takes its agents from the formula alone", () => {
    expect(systemAgents("atl")).toEqual([]);
  });

  test("LTL, CTL and CTL* are interpreted over exactly one agent", () => {
    expect(systemAgents("ltl")).toEqual(["a"]);
    expect(systemAgents("ctl")).toEqual(["a"]);
    expect(systemAgents("ctlstar")).toEqual(["a"]);
  });

  test("a CTL formula using only A still gets an agent", () => {
    // AG p translates to <<>>G p, which mentions no agent at all; without the
    // forced agent the model would have none and the embedding would break.
    const result = runTableau(parseFormula("AG p", "ctl"), systemAgents("ctl"));
    expect([...result.allAgents]).toEqual(["a"]);
  });

  test("LTL formulas are solved over one agent", () => {
    const result = runTableau(parseFormula("G F p", "ltl"), systemAgents("ltl"));
    expect([...result.allAgents]).toEqual(["a"]);
  });
});

// ============================================================
// Translation
// ============================================================

describe("LTL translation", () => {
  test("the whole formula is wrapped in a single existential path quantifier", () => {
    expect(translate("X p", "ltl")).toBe("<<a>>X p");
    expect(translate("G p", "ltl")).toBe("<<a>>G p");
    expect(translate("(p U q)", "ltl")).toBe("<<a>>(p U q)");
  });

  test("F is sugar for true U", () => {
    expect(translate("F p", "ltl")).toBe("<<a>>(_top U p)");
  });

  test("a bare atom is a path formula", () => {
    expect(translate("p", "ltl")).toBe("<<a>>p");
  });

  test("infix operators work at the top level without parentheses", () => {
    expect(translate("p U q", "ltl")).toBe("<<a>>(p U q)");
  });

  test("temporal operators nest freely", () => {
    expect(translate("G F p", "ltl")).toBe("<<a>>G (_top U p)");
    expect(translate("F G p", "ltl")).toBe("<<a>>(_top U G p)");
  });

  test("operator letters need no separating space", () => {
    expect(translate("Xp", "ltl")).toBe(translate("X p", "ltl"));
    expect(translate("GFp", "ltl")).toBe(translate("G F p", "ltl"));
  });
});

describe("CTL translation", () => {
  test("A becomes the empty coalition, E the single agent", () => {
    expect(translate("AX p", "ctl")).toBe("<<>>X p");
    expect(translate("EX p", "ctl")).toBe("<<a>>X p");
    expect(translate("AG p", "ctl")).toBe("<<>>G p");
    expect(translate("EG p", "ctl")).toBe("<<a>>G p");
  });

  test("AF and EF desugar through F", () => {
    expect(translate("AF p", "ctl")).toBe("<<>>(_top U p)");
    expect(translate("EF p", "ctl")).toBe("<<a>>(_top U p)");
  });

  test("until accepts square and round brackets alike", () => {
    expect(translate("A[p U q]", "ctl")).toBe("<<>>(p U q)");
    expect(translate("E[p U q]", "ctl")).toBe("<<a>>(p U q)");
    expect(translate("A(p U q)", "ctl")).toBe(translate("A[p U q]", "ctl"));
  });

  test("quantifiers nest", () => {
    expect(translate("AG EF p", "ctl")).toBe("<<>>G <<a>>(_top U p)");
    expect(translate("EG AF p", "ctl")).toBe("<<a>>G <<>>(_top U p)");
  });

  test("a temporal operator binds only its immediate argument", () => {
    // AF p & AG q is (AF p) & (AG q), not AF (p & AG q)
    expect(translate("(AF p & AG q)", "ctl")).toBe("(<<>>(_top U p) & <<>>G q)");
  });

  test("operator letters need no separating space", () => {
    expect(translate("AGp", "ctl")).toBe(translate("AG p", "ctl"));
    expect(translate("EFp", "ctl")).toBe(translate("EF p", "ctl"));
  });
});

// ============================================================
// LTL satisfiability
// ============================================================

describe("LTL satisfiability", () => {
  test("basic operators are satisfiable", () => {
    expect(isSat("p", "ltl")).toBe(true);
    expect(isSat("X p", "ltl")).toBe(true);
    expect(isSat("G p", "ltl")).toBe(true);
    expect(isSat("F p", "ltl")).toBe(true);
    expect(isSat("(p U q)", "ltl")).toBe(true);
    expect(isSat("(p R q)", "ltl")).toBe(true);
  });

  test("safety, liveness and response patterns", () => {
    expect(isSat("G ~p", "ltl")).toBe(true);
    expect(isSat("G F p", "ltl")).toBe(true);
    expect(isSat("G (p -> F q)", "ltl")).toBe(true);
  });

  test("F G p is satisfiable (and is not expressible in CTL)", () => {
    expect(isSat("F G p", "ltl")).toBe(true);
  });

  test("a formula may demand infinitely many alternations", () => {
    expect(isSat("(G F p & G F ~p)", "ltl")).toBe(true);
  });

  test("propositional contradictions are unsatisfiable", () => {
    expect(isSat("(p & ~p)", "ltl")).toBe(false);
  });

  test("temporal contradictions are unsatisfiable", () => {
    expect(isSat("(G p & F ~p)", "ltl")).toBe(false);
    expect(isSat("(X p & X ~p)", "ltl")).toBe(false);
    expect(isSat("(F p & G ~p)", "ltl")).toBe(false);
    expect(isSat("(F G p & G F ~p)", "ltl")).toBe(false);
  });

  test("negating a validity is unsatisfiable", () => {
    expect(isSat("~(G p -> p)", "ltl")).toBe(false);
    expect(isSat("~(G p -> X G p)", "ltl")).toBe(false);
    expect(isSat("~(F G p -> G F p)", "ltl")).toBe(false);
    // expansion laws
    expect(isSat("~(G p -> (p & X G p))", "ltl")).toBe(false);
    expect(isSat("~(F p -> (p | X F p))", "ltl")).toBe(false);
  });
});

// ============================================================
// CTL satisfiability
// ============================================================

describe("CTL satisfiability", () => {
  test("all eight paired operators are satisfiable", () => {
    expect(isSat("AX p", "ctl")).toBe(true);
    expect(isSat("EX p", "ctl")).toBe(true);
    expect(isSat("AG p", "ctl")).toBe(true);
    expect(isSat("EG p", "ctl")).toBe(true);
    expect(isSat("AF p", "ctl")).toBe(true);
    expect(isSat("EF p", "ctl")).toBe(true);
    expect(isSat("A[p U q]", "ctl")).toBe(true);
    expect(isSat("E[p U q]", "ctl")).toBe(true);
  });

  test("branching: a state may have both a p and a not-p successor", () => {
    // This needs the single agent to have at least two available moves, so it
    // would fail if the one-agent model were forced to be linear.
    expect(isSat("(EX p & EX ~p)", "ctl")).toBe(true);
  });

  test("properties expressible in CTL but not in LTL", () => {
    expect(isSat("AG EF p", "ctl")).toBe(true);
    expect(isSat("AG(p -> (EX q & EX ~q))", "ctl")).toBe(true);
  });

  test("nested quantifiers", () => {
    expect(isSat("EF(EG p -> AF r)", "ctl")).toBe(true);
    expect(isSat("AF EG p", "ctl")).toBe(true);
    expect(isSat("EG AF p", "ctl")).toBe(true);
    expect(isSat("AG (p -> AF q)", "ctl")).toBe(true);
  });

  test("contradictions between the quantifiers are unsatisfiable", () => {
    expect(isSat("(AG p & EF ~p)", "ctl")).toBe(false);
    expect(isSat("(AX p & EX ~p)", "ctl")).toBe(false);
    expect(isSat("(AF p & EG ~p)", "ctl")).toBe(false);
    expect(isSat("(p & ~p)", "ctl")).toBe(false);
  });

  test("negating a validity is unsatisfiable", () => {
    expect(isSat("~(AG p -> p)", "ctl")).toBe(false);
  });

  test("negating the A/E dualities is unsatisfiable", () => {
    expect(isSat("~(AX p -> ~EX ~p)", "ctl")).toBe(false);
    expect(isSat("~(~EF ~p -> AG p)", "ctl")).toBe(false);
  });

  test("negating the expansion laws is unsatisfiable", () => {
    expect(isSat("~(AG p -> AX AG p)", "ctl")).toBe(false);
    expect(isSat("~(AF p -> (p | AX AF p))", "ctl")).toBe(false);
    expect(isSat("~(EF p -> (p | EX EF p))", "ctl")).toBe(false);
    expect(isSat("~(EG p -> (p & EX EG p))", "ctl")).toBe(false);
  });
});

// ============================================================
// CTL*: the one-agent fragment of ATL*
// ============================================================

describe("CTL* translation", () => {
  test("A becomes the empty coalition, E the single agent", () => {
    expect(translate("A G p", "ctlstar")).toBe("<<>>G p");
    expect(translate("E G p", "ctlstar")).toBe("<<a>>G p");
  });

  test("a quantifier takes an arbitrary path formula", () => {
    expect(translate("E(G p & F q)", "ctlstar")).toBe("<<a>>(G p & (_top U q))");
    expect(translate("A(F G p)", "ctlstar")).toBe("<<>>(_top U G p)");
    expect(translate("E(p U (q U r))", "ctlstar")).toBe("<<a>>(p U (q U r))");
  });

  test("brackets group like parentheses", () => {
    expect(translate("A[G F p]", "ctlstar")).toBe(translate("A(G F p)", "ctlstar"));
    expect(translate("E[p U q]", "ctlstar")).toBe(translate("E(p U q)", "ctlstar"));
  });

  test("quantifiers nest inside path formulas", () => {
    expect(translate("AG EF p", "ctlstar")).toBe("<<>>G <<a>>(_top U p)");
  });

  test("a state formula is a valid path formula", () => {
    // Legal in CTL* (and equivalent to p), unlike in CTL where A must pair
    // with a temporal operator
    expect(translate("A p", "ctlstar")).toBe("<<>>p");
    expect(() => parseFormula("A p", "ctl")).toThrow();
  });

  test("every CTL formula is also a CTL* formula, with the same translation", () => {
    for (const f of ["AX p", "EX p", "AG p", "EG p", "AF p", "EF p", "AG EF p"]) {
      expect(translate(f, "ctlstar")).toBe(translate(f, "ctl"));
    }
  });
});

describe("CTL* satisfiability", () => {
  test("formulas that are CTL* but not CTL are satisfiable", () => {
    expect(isSat("E(G F p)", "ctlstar")).toBe(true);
    expect(isSat("A(F G p)", "ctlstar")).toBe(true);
    expect(isSat("E(G p & F q)", "ctlstar")).toBe(true);
    expect(isSat("A(G F p -> F G q)", "ctlstar")).toBe(true);
    expect(isSat("E(G F p & G F ~p)", "ctlstar")).toBe(true);
    expect(isSat("E(p U (q U r))", "ctlstar")).toBe(true);
  });

  test("CTL and LTL results carry over", () => {
    expect(isSat("AG EF p", "ctlstar")).toBe(true);
    expect(isSat("(EX p & EX ~p)", "ctlstar")).toBe(true);
    expect(isSat("(AG p & EF ~p)", "ctlstar")).toBe(false);
  });

  test("contradictions along a single path are unsatisfiable", () => {
    expect(isSat("E(G p & F ~p)", "ctlstar")).toBe(false);
    expect(isSat("E(F G p & G F ~p)", "ctlstar")).toBe(false);
  });

  test("a quantified path contradicting another quantifier", () => {
    expect(isSat("(A(G F p) & E(F G ~p))", "ctlstar")).toBe(false);
  });

  test("negating a validity is unsatisfiable", () => {
    expect(isSat("~(A(G p) -> A(X G p))", "ctlstar")).toBe(false);
    expect(isSat("~(E(F G p) -> E(G F p))", "ctlstar")).toBe(false);
    expect(isSat("~(A(G p) -> E(G p))", "ctlstar")).toBe(false);
  });

  test("an LTL formula is satisfiable exactly when E of it is", () => {
    // LTL satisfiability is existential over paths, which is what E expresses
    for (const f of ["G F p", "F G p", "(p U q)", "(G p & F ~p)", "(F G p & G F ~p)"]) {
      expect(isSat("E(" + f + ")", "ctlstar")).toBe(isSat(f, "ltl"));
    }
  });
});

describe("CTL* rejects formulas outside CTL*", () => {
  test("a temporal operator still needs a quantifier", () => {
    expect(() => parseFormula("G p", "ctlstar")).toThrow(/must appear inside a path quantifier/);
    expect(() => parseFormula("F G p", "ctlstar")).toThrow(/must appear inside a path quantifier/);
    expect(() => parseFormula("(p U q)", "ctlstar")).toThrow(/must appear inside a path quantifier/);
  });

  test("coalition operators are not CTL*", () => {
    expect(() => parseFormula("<<a>>X p", "ctlstar")).toThrow(/belong to ATL\*/);
    expect(() => parseFormula("<<>>G p", "ctlstar")).toThrow(/belong to ATL\*/);
    expect(() => parseFormula("[[a]]G p", "ctlstar")).toThrow(/belong to ATL\*/);
  });
});

// ============================================================
// Syntax each system rejects
// ============================================================

describe("CTL rejects formulas outside CTL", () => {
  test("an unpaired temporal operator is not CTL", () => {
    expect(() => parseFormula("G p", "ctl")).toThrow(/must be preceded by a path quantifier/);
    expect(() => parseFormula("F G p", "ctl")).toThrow(/must be preceded by a path quantifier/);
    expect(() => parseFormula("X p", "ctl")).toThrow(/must be preceded by a path quantifier/);
  });

  test("an unpaired until is CTL*, not CTL", () => {
    // Wikipedia gives EF (r U q) as the canonical ill-formed CTL string
    expect(() => parseFormula("EF (r U q)", "ctl")).toThrow(/must be paired with a path quantifier/);
    expect(() => parseFormula("AG (p U q)", "ctl")).toThrow(/must be paired with a path quantifier/);
    expect(() => parseFormula("(p U q)", "ctl")).toThrow();
  });

  test("a quantifier needs a temporal operator", () => {
    expect(() => parseFormula("A p", "ctl")).toThrow(/must be followed by X, G, F/);
    expect(() => parseFormula("E p", "ctl")).toThrow(/must be followed by X, G, F/);
  });

  test("coalition operators are not CTL", () => {
    expect(() => parseFormula("<<a>>X p", "ctl")).toThrow(/belong to ATL\*/);
    expect(() => parseFormula("[[a]]G p", "ctl")).toThrow(/belong to ATL\*/);
  });
});

describe("LTL rejects formulas outside LTL", () => {
  test("path quantifiers are not LTL", () => {
    expect(() => parseFormula("AG p", "ltl")).toThrow(/CTL path quantifier/);
    expect(() => parseFormula("EF p", "ltl")).toThrow(/CTL path quantifier/);
  });

  test("coalition operators are not LTL", () => {
    expect(() => parseFormula("<<a>>X p", "ltl")).toThrow(/belong to ATL\*/);
    expect(() => parseFormula("[[a]]G p", "ltl")).toThrow(/belong to ATL\*/);
  });
});

// ============================================================
// ATL* is untouched by the new systems
// ============================================================

describe("ATL* remains the default", () => {
  test("parseFormula defaults to ATL*", () => {
    expect(printFormula(parseFormulaRaw("<<a>>X p"))).toBe("<<a>>X p");
  });

  test("A and E are ordinary parse errors in ATL*, not quantifiers", () => {
    // Atoms are lowercase, so uppercase A/E are simply not valid ATL* input
    expect(() => parseFormula("AG p", "atl")).toThrow();
  });

  test("ATL* still accepts coalitions and reads its agents from the formula", () => {
    const result = runTableau(parseFormula("(<<a>>X p & <<b,c>>G q)", "atl"), systemAgents("atl"));
    expect([...result.allAgents]).toEqual(["a", "b", "c"]);
  });
});
