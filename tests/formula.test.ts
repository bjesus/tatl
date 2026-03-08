/**
 * Unit tests for ATL formula utilities: parser, printer, classification, closure, expansion.
 */

import { describe, test, expect } from "bun:test";
import { parseFormula } from "../src/core/parser.ts";
import { printFormula, printFormulaUnicode, printFormulaLatex } from "../src/core/printer.ts";
import { classifyFormula } from "../src/core/classify.ts";
import { closure, isPatentlyInconsistent, isEventuality, eventualityGoal, isPositiveNext, isNegativeNext, agentsInFormula } from "../src/core/formula.ts";
import { Atom, Not, And, Or, Next, Always, Until, FormulaSet, formulaKey, formulaEqual } from "../src/core/types.ts";

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
    expect(f.kind).toBe("not");
  });

  test("parses conjunction", () => {
    const f = parseFormula("(p & q)");
    expect(f.kind).toBe("and");
  });

  test("parses disjunction (sugar)", () => {
    const f = parseFormula("(p | q)");
    expect(f.kind).toBe("not"); // desugars to ~(~p & ~q)
  });

  test("parses implication (sugar)", () => {
    const f = parseFormula("(p -> q)");
    expect(f.kind).toBe("not"); // desugars to ~(p & ~q)
  });

  test("parses <<a>>X p (next)", () => {
    const f = parseFormula("<<a>>X p");
    expect(f.kind).toBe("next");
    if (f.kind === "next") {
      expect(f.coalition).toEqual(["a"]);
      expect(f.sub.kind).toBe("atom");
    }
  });

  test("parses <<a,b>>G p (always)", () => {
    const f = parseFormula("<<a,b>>G p");
    expect(f.kind).toBe("always");
    if (f.kind === "always") {
      expect(f.coalition).toEqual(["a", "b"]);
      expect(f.sub.kind).toBe("atom");
    }
  });

  test("parses <<>>X p (empty coalition)", () => {
    const f = parseFormula("<<>>X p");
    expect(f.kind).toBe("next");
    if (f.kind === "next") {
      expect(f.coalition).toEqual([]);
    }
  });

  test("parses <<a>>F p (eventually, sugar)", () => {
    const f = parseFormula("<<a>>F p");
    expect(f.kind).toBe("until");
    if (f.kind === "until") {
      expect(f.coalition).toEqual(["a"]);
      expect(f.left.kind).toBe("atom");
      if (f.left.kind === "atom") expect(f.left.name).toBe("_top");
    }
  });

  test("parses <<a>>(p U q) (until)", () => {
    const f = parseFormula("<<a>>(p U q)");
    expect(f.kind).toBe("until");
    if (f.kind === "until") {
      expect(f.coalition).toEqual(["a"]);
      expect(f.left.kind).toBe("atom");
      expect(f.right.kind).toBe("atom");
    }
  });

  test("parses complex formula", () => {
    const f = parseFormula("(<<a>>X p & ~<<b>>G q)");
    expect(f.kind).toBe("and");
  });

  test("parses negated next", () => {
    const f = parseFormula("~<<a>>X p");
    expect(f.kind).toBe("not");
    if (f.kind === "not") expect(f.sub.kind).toBe("next");
  });

  test("parses negated always", () => {
    const f = parseFormula("~<<a>>G p");
    expect(f.kind).toBe("not");
    if (f.kind === "not") expect(f.sub.kind).toBe("always");
  });

  test("parses negated until", () => {
    const f = parseFormula("~<<a>>(p U q)");
    expect(f.kind).toBe("not");
    if (f.kind === "not") expect(f.sub.kind).toBe("until");
  });

  test("throws on invalid input", () => {
    expect(() => parseFormula("")).toThrow();
    expect(() => parseFormula("<<a>> p")).toThrow();
  });

  test("handles whitespace", () => {
    const f = parseFormula("  <<  a , b  >>  X  p  ");
    expect(f.kind).toBe("next");
  });

  test("parses nested coalition formulas", () => {
    const f = parseFormula("<<a>>X <<b>>X p");
    expect(f.kind).toBe("next");
    if (f.kind === "next") {
      expect(f.sub.kind).toBe("next");
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
    const f = Next(["a"], Atom("p"));
    expect(printFormula(f)).toBe("<<a>>X p");
  });

  test("prints always formula", () => {
    const f = Always(["a", "b"], Atom("p"));
    expect(printFormula(f)).toBe("<<a,b>>G p");
  });

  test("prints until formula", () => {
    const f = Until(["a"], Atom("p"), Atom("q"));
    expect(printFormula(f)).toBe("<<a>>(p U q)");
  });

  test("prints empty coalition", () => {
    const f = Next([], Atom("p"));
    expect(printFormula(f)).toBe("<<>>X p");
  });

  test("Unicode output uses special chars", () => {
    const f = Next(["a"], Atom("p"));
    const u = printFormulaUnicode(f);
    expect(u).toContain("\u27E8"); // ⟨
    expect(u).toContain("\u25CB"); // ○
  });

  test("LaTeX output uses LaTeX commands", () => {
    const f = Next(["a"], Atom("p"));
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
    expect(classifyFormula(Atom("p")).type).toBe("elementary");
  });

  test("¬p is elementary", () => {
    expect(classifyFormula(Not(Atom("p"))).type).toBe("elementary");
  });

  test("¬¬ϕ is alpha → {ϕ}", () => {
    const cls = classifyFormula(Not(Not(Atom("p"))));
    expect(cls.type).toBe("alpha");
    if (cls.type === "alpha") {
      expect(cls.components.length).toBe(1);
      expect(formulaEqual(cls.components[0]!, Atom("p"))).toBe(true);
    }
  });

  test("ϕ ∧ ψ is alpha → {ϕ, ψ}", () => {
    const cls = classifyFormula(And(Atom("p"), Atom("q")));
    expect(cls.type).toBe("alpha");
    if (cls.type === "alpha") expect(cls.components.length).toBe(2);
  });

  test("¬(ϕ ∧ ψ) is beta → {¬ϕ, ¬ψ}", () => {
    const cls = classifyFormula(Not(And(Atom("p"), Atom("q"))));
    expect(cls.type).toBe("beta");
    if (cls.type === "beta") expect(cls.components.length).toBe(2);
  });

  test("<<A>>○ϕ is elementary", () => {
    expect(classifyFormula(Next(["a"], Atom("p"))).type).toBe("elementary");
  });

  test("¬<<A>>○ϕ is elementary", () => {
    expect(classifyFormula(Not(Next(["a"], Atom("p")))).type).toBe("elementary");
  });

  test("<<A>>□ϕ is alpha → {ϕ, <<A>>○<<A>>□ϕ}", () => {
    const f = Always(["a"], Atom("p"));
    const cls = classifyFormula(f);
    expect(cls.type).toBe("alpha");
    if (cls.type === "alpha") {
      expect(cls.components.length).toBe(2);
      expect(formulaEqual(cls.components[0]!, Atom("p"))).toBe(true);
      expect(cls.components[1]!.kind).toBe("next");
    }
  });

  test("<<A>>(ϕ U ψ) is beta → {ψ, (ϕ ∧ <<A>>○<<A>>(ϕ U ψ))}", () => {
    const f = Until(["a"], Atom("p"), Atom("q"));
    const cls = classifyFormula(f);
    expect(cls.type).toBe("beta");
    if (cls.type === "beta") {
      expect(cls.components.length).toBe(2);
      expect(formulaEqual(cls.components[0]!, Atom("q"))).toBe(true);
      expect(cls.components[1]!.kind).toBe("and");
    }
  });

  test("¬<<A>>□ϕ is beta → {¬ϕ, ¬<<A>>○<<A>>□ϕ}", () => {
    const f = Not(Always(["a"], Atom("p")));
    const cls = classifyFormula(f);
    expect(cls.type).toBe("beta");
    if (cls.type === "beta") {
      expect(cls.components.length).toBe(2);
      expect(formulaEqual(cls.components[0]!, Not(Atom("p")))).toBe(true);
      expect(cls.components[1]!.kind).toBe("not");
    }
  });

  test("¬<<A>>(ϕ U ψ) is alpha → {¬ψ, ¬(ϕ ∧ <<A>>○<<A>>(ϕ U ψ))}", () => {
    const f = Not(Until(["a"], Atom("p"), Atom("q")));
    const cls = classifyFormula(f);
    expect(cls.type).toBe("alpha");
    if (cls.type === "alpha") {
      expect(cls.components.length).toBe(2);
      expect(formulaEqual(cls.components[0]!, Not(Atom("q")))).toBe(true);
      expect(cls.components[1]!.kind).toBe("not");
    }
  });
});

// ============================================================
// Formula utility tests
// ============================================================

describe("Formula utilities", () => {
  test("patent inconsistency detection", () => {
    expect(isPatentlyInconsistent(new FormulaSet([Atom("p"), Atom("q")]))).toBe(false);
    expect(isPatentlyInconsistent(new FormulaSet([Atom("p"), Not(Atom("p"))]))).toBe(true);
  });

  test("eventuality detection", () => {
    expect(isEventuality(Until(["a"], Atom("p"), Atom("q")))).toBe(true);
    expect(isEventuality(Not(Always(["a"], Atom("p"))))).toBe(true);
    expect(isEventuality(Next(["a"], Atom("p")))).toBe(false);
    expect(isEventuality(Atom("p"))).toBe(false);
    expect(isEventuality(Always(["a"], Atom("p")))).toBe(false);
  });

  test("eventuality goal", () => {
    expect(formulaEqual(
      eventualityGoal(Until(["a"], Atom("p"), Atom("q"))),
      Atom("q")
    )).toBe(true);

    expect(formulaEqual(
      eventualityGoal(Not(Always(["a"], Atom("p")))),
      Not(Atom("p"))
    )).toBe(true);
  });

  test("next-time formula detection", () => {
    expect(isPositiveNext(Next(["a"], Atom("p")))).toBe(true);
    expect(isPositiveNext(Atom("p"))).toBe(false);
    expect(isNegativeNext(Not(Next(["a"], Atom("p"))))).toBe(true);
    expect(isNegativeNext(Not(Atom("p")))).toBe(false);
  });

  test("agents extraction", () => {
    const agents = agentsInFormula(parseFormula("(<<a>>X p & <<b,c>>G q)"));
    expect(agents.has("a")).toBe(true);
    expect(agents.has("b")).toBe(true);
    expect(agents.has("c")).toBe(true);
    expect(agents.size).toBe(3);
  });

  test("agents in empty coalition", () => {
    const agents = agentsInFormula(parseFormula("<<>>X p"));
    expect(agents.size).toBe(0);
  });

  test("closure contains α/β components", () => {
    const f = Always(["a"], Atom("p"));
    const cl = closure(f);
    expect(cl.has(f)).toBe(true);
    expect(cl.has(Atom("p"))).toBe(true);
    expect(cl.has(Next(["a"], f))).toBe(true);
  });

  test("closure of until contains components", () => {
    const f = Until(["a"], Atom("p"), Atom("q"));
    const cl = closure(f);
    expect(cl.has(f)).toBe(true);
    expect(cl.has(Atom("q"))).toBe(true);
    expect(cl.has(And(Atom("p"), Next(["a"], f)))).toBe(true);
  });
});
