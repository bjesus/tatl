/**
 * Unit tests for ATL* formula utilities: parser, printer, classification, expansion.
 * Updated for two-sorted (StateFormula + PathFormula) ATL* types.
 */

import { describe, test, expect } from "bun:test";
import { parseFormula } from "../src/core/parser.ts";
import { printFormula, printFormulaUnicode, printFormulaLatex } from "../src/core/printer.ts";
import { classifyState } from "../src/core/classify.ts";
import {
  isPatentlyInconsistent,
  isEventuality,
  isEnforceableNext,
  isUnavoidableNext,
  agentsInState,
  subformulasState,
} from "../src/core/formula.ts";
import {
  Atom,
  Neg,
  SAnd,
  SOr,
  Coal,
  CoCoal,
  PState,
  PNext,
  PAlways,
  PUntil,
  StateFormulaSet,
  stateKey,
  stateEqual,
} from "../src/core/types.ts";

// ============================================================
// Parser tests
// ============================================================

describe("Parser", () => {
  test("parses atoms", () => {
    const f = parseFormula("p");
    expect(f.kind).toBe("atom");
    if (f.kind === "atom") expect(f.name).toBe("p");
  });

  test("parses negation", () => {
    const f = parseFormula("~p");
    expect(f.kind).toBe("neg");
  });

  test("parses conjunction", () => {
    const f = parseFormula("(p & q)");
    expect(f.kind).toBe("and");
  });

  test("parses disjunction (NNF: becomes or)", () => {
    const f = parseFormula("(p | q)");
    expect(f.kind).toBe("or"); // NNF keeps or as first-class
  });

  test("parses implication (NNF: becomes or)", () => {
    const f = parseFormula("(p -> q)");
    expect(f.kind).toBe("or"); // p -> q = ~p | q in NNF
  });

  test("parses <<a>>X p (next)", () => {
    const f = parseFormula("<<a>>X p");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.coalition).toEqual(["a"]);
      expect(f.path.kind).toBe("next");
    }
  });

  test("parses <<a,b>>G p (always)", () => {
    const f = parseFormula("<<a,b>>G p");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.coalition).toEqual(["a", "b"]);
      expect(f.path.kind).toBe("always");
    }
  });

  test("parses <<>>X p (empty coalition)", () => {
    const f = parseFormula("<<>>X p");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.coalition).toEqual([]);
    }
  });

  test("parses <<a>>F p (eventually, sugar for T U p)", () => {
    const f = parseFormula("<<a>>F p");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.coalition).toEqual(["a"]);
      expect(f.path.kind).toBe("until");
    }
  });

  test("parses <<a>>(p U q) (until)", () => {
    const f = parseFormula("<<a>>(p U q)");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.coalition).toEqual(["a"]);
      expect(f.path.kind).toBe("until");
    }
  });

  test("parses complex formula", () => {
    const f = parseFormula("(<<a>>X p & ~<<b>>G q)");
    expect(f.kind).toBe("and");
  });

  test("parses negated next (NNF: becomes cocoal)", () => {
    const f = parseFormula("~<<a>>X p");
    expect(f.kind).toBe("cocoal");
    if (f.kind === "cocoal") {
      expect(f.path.kind).toBe("next");
    }
  });

  test("parses negated always (NNF: becomes cocoal)", () => {
    const f = parseFormula("~<<a>>G p");
    expect(f.kind).toBe("cocoal");
    if (f.kind === "cocoal") {
      expect(f.path.kind).toBe("until"); // ~<<a>>G p = [[a]](T U ~p) in NNF
    }
  });

  test("parses negated until (NNF: becomes cocoal)", () => {
    const f = parseFormula("~<<a>>(p U q)");
    expect(f.kind).toBe("cocoal");
    if (f.kind === "cocoal") {
      // ~<<a>>(p U q) = [[a]]( (~q & ~p) | (~q & G ~q) ) or similar NNF form
      // The exact path kind depends on NNF expansion
    }
  });

  test("throws on invalid input", () => {
    expect(() => parseFormula("")).toThrow();
  });

  test("parses <<a>> p (bare coalition wrapping state)", () => {
    // In ATL*, <<a>> p is valid: Coal(["a"], PState(p))
    const f = parseFormula("<<a>> p");
    expect(f.kind).toBe("coal");
  });

  test("handles whitespace", () => {
    const f = parseFormula("  <<  a , b  >>  X  p  ");
    expect(f.kind).toBe("coal");
  });

  test("parses nested coalition formulas", () => {
    const f = parseFormula("<<a>>X <<b>>X p");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      // The inner path is PNext(PState(<<b>>X p))
      expect(f.path.kind).toBe("next");
    }
  });
});

// ============================================================
// Printer tests
// ============================================================

describe("Printer", () => {
  test("round-trips simple formulas", () => {
    const cases = ["p", "~p", "(p & q)"];
    for (const input of cases) {
      expect(printFormula(parseFormula(input))).toBe(input);
    }
  });

  test("prints next formula", () => {
    const f = Coal(["a"], PNext(PState(Atom("p"))));
    expect(printFormula(f)).toBe("<<a>>X p");
  });

  test("prints always formula", () => {
    const f = Coal(["a", "b"], PAlways(PState(Atom("p"))));
    expect(printFormula(f)).toBe("<<a,b>>G p");
  });

  test("prints until formula", () => {
    const f = Coal(["a"], PUntil(PState(Atom("p")), PState(Atom("q"))));
    expect(printFormula(f)).toBe("<<a>>(p U q)");
  });

  test("prints empty coalition", () => {
    const f = Coal([], PNext(PState(Atom("p"))));
    expect(printFormula(f)).toBe("<<>>X p");
  });

  test("Unicode output uses special chars", () => {
    const f = Coal(["a"], PNext(PState(Atom("p"))));
    const u = printFormulaUnicode(f);
    expect(u).toContain("\u27E8"); // ⟨
    expect(u).toContain("\u25CB"); // ○
  });

  test("LaTeX output uses LaTeX commands", () => {
    const f = Coal(["a"], PNext(PState(Atom("p"))));
    const tex = printFormulaLatex(f);
    expect(tex).toContain("\\langle");
    expect(tex).toContain("\\bigcirc");
  });
});

// ============================================================
// Classification tests
// ============================================================

describe("Classification", () => {
  test("atom is elementary", () => {
    expect(classifyState(Atom("p")).type).toBe("elementary");
  });

  test("~p is elementary", () => {
    expect(classifyState(Neg(Atom("p"))).type).toBe("elementary");
  });

  test("~~p is alpha -> {p}", () => {
    const cls = classifyState(Neg(Neg(Atom("p"))));
    expect(cls.type).toBe("alpha");
    if (cls.type === "alpha") {
      expect(cls.components.length).toBe(1);
      expect(stateEqual(cls.components[0]!, Atom("p"))).toBe(true);
    }
  });

  test("p & q is alpha -> {p, q}", () => {
    const cls = classifyState(SAnd(Atom("p"), Atom("q")));
    expect(cls.type).toBe("alpha");
    if (cls.type === "alpha") expect(cls.components.length).toBe(2);
  });

  test("~(p & q) is beta -> {~p, ~q}", () => {
    const cls = classifyState(Neg(SAnd(Atom("p"), Atom("q"))));
    expect(cls.type).toBe("beta");
    if (cls.type === "beta") expect(cls.components.length).toBe(2);
  });

  test("<<A>>X p is elementary (next-time)", () => {
    expect(classifyState(Coal(["a"], PNext(PState(Atom("p"))))).type).toBe("elementary");
  });

  test("[[A]]X p is elementary (cocoal next-time)", () => {
    expect(classifyState(CoCoal(["a"], PNext(PState(Atom("p"))))).type).toBe("elementary");
  });

  test("<<A>>G p is gamma (ATL*: coalition always)", () => {
    const f = Coal(["a"], PAlways(PState(Atom("p"))));
    const cls = classifyState(f);
    expect(cls.type).toBe("gamma");
  });

  test("<<A>>(p U q) is gamma (ATL*: coalition until)", () => {
    const f = Coal(["a"], PUntil(PState(Atom("p")), PState(Atom("q"))));
    const cls = classifyState(f);
    expect(cls.type).toBe("gamma");
  });

  test("[[A]]G p is gamma (ATL*: cocoal always)", () => {
    const f = CoCoal(["a"], PAlways(PState(Atom("p"))));
    const cls = classifyState(f);
    expect(cls.type).toBe("gamma");
  });

  test("[[A]](p U q) is gamma (ATL*: cocoal until)", () => {
    const f = CoCoal(["a"], PUntil(PState(Atom("p")), PState(Atom("q"))));
    const cls = classifyState(f);
    expect(cls.type).toBe("gamma");
  });
});

// ============================================================
// Formula utility tests
// ============================================================

describe("Formula utilities", () => {
  test("patent inconsistency detection", () => {
    expect(isPatentlyInconsistent(new StateFormulaSet([Atom("p"), Atom("q")]))).toBe(false);
    expect(isPatentlyInconsistent(new StateFormulaSet([Atom("p"), Neg(Atom("p"))]))).toBe(true);
  });

  test("eventuality detection", () => {
    // Coal until is an eventuality
    expect(isEventuality(Coal(["a"], PUntil(PState(Atom("p")), PState(Atom("q")))))).toBe(true);
    // CoCoal until is an eventuality
    expect(isEventuality(CoCoal(["a"], PUntil(PState(Atom("p")), PState(Atom("q")))))).toBe(true);
    // Coal always is NOT an eventuality
    expect(isEventuality(Coal(["a"], PAlways(PState(Atom("p")))))).toBe(false);
    // CoCoal always is NOT an eventuality
    expect(isEventuality(CoCoal(["a"], PAlways(PState(Atom("p")))))).toBe(false);
    // Coal next is not
    expect(isEventuality(Coal(["a"], PNext(PState(Atom("p")))))).toBe(false);
    // Atom is not
    expect(isEventuality(Atom("p"))).toBe(false);
  });

  test("next-time formula detection (enforceable)", () => {
    expect(isEnforceableNext(Coal(["a"], PNext(PState(Atom("p")))))).toBe(true);
    expect(isEnforceableNext(Atom("p"))).toBe(false);
    expect(isEnforceableNext(CoCoal(["a"], PNext(PState(Atom("p")))))).toBe(false);
  });

  test("next-time formula detection (unavoidable)", () => {
    expect(isUnavoidableNext(CoCoal(["a"], PNext(PState(Atom("p")))))).toBe(true);
    expect(isUnavoidableNext(Atom("p"))).toBe(false);
    expect(isUnavoidableNext(Coal(["a"], PNext(PState(Atom("p")))))).toBe(false);
  });

  test("agents extraction", () => {
    const agents = agentsInState(parseFormula("(<<a>>X p & <<b,c>>G q)"));
    expect(agents.has("a")).toBe(true);
    expect(agents.has("b")).toBe(true);
    expect(agents.has("c")).toBe(true);
    expect(agents.size).toBe(3);
  });

  test("agents in empty coalition", () => {
    const agents = agentsInState(parseFormula("<<>>X p"));
    expect(agents.size).toBe(0);
  });

  test("subformulas contains the formula itself", () => {
    const f = Coal(["a"], PAlways(PState(Atom("p"))));
    const subs = subformulasState(f);
    expect(subs.has(f)).toBe(true);
  });

  test("subformulas of coal always contains atom", () => {
    const f = Coal(["a"], PAlways(PState(Atom("p"))));
    const subs = subformulasState(f);
    expect(subs.has(Atom("p"))).toBe(true);
  });

  test("subformulas of coal until contains both operands", () => {
    const f = Coal(["a"], PUntil(PState(Atom("p")), PState(Atom("q"))));
    const subs = subformulasState(f);
    expect(subs.has(f)).toBe(true);
    expect(subs.has(Atom("p"))).toBe(true);
    expect(subs.has(Atom("q"))).toBe(true);
  });
});
