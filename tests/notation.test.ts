/**
 * Output notation: printing an encoded formula back in the syntax it was written in.
 *
 * LTL, CTL and CTL* are solved by encoding them as ATL* over a single agent
 * (see systems.test.ts). Showing that encoding back to the user would display a
 * formula they never typed, so the printers take a notation:
 *
 *   ctl   <<a>> -> E   <<>> -> A   [[a]] -> A   [[]] -> E
 *   ltl   <<a>> -> nothing at all
 *
 * The co-coalition readings are forced by [[A]]p == ~<<A>>~p: with one agent
 * [[a]]p == ~E~p == Ap and [[]]p == ~A~p == Ep.
 */

import { describe, test, expect } from "bun:test";
import { parseFormula, parseFormulaRaw, systemAgents, type System } from "../src/core/parser.ts";
import {
  printStateAscii,
  printStateUnicode,
  printStateLatex,
  printStateSetAscii,
  notationFor,
} from "../src/core/printer.ts";
import { runTableau } from "../src/core/tableau.ts";
import { Coal, CoCoal, PNext, PState, Atom } from "../src/core/types.ts";
import { textVerbose } from "../src/viz/text.ts";

/** Parse in `system` and print back in that system's own notation. */
function show(input: string, system: System): string {
  return printStateAscii(parseFormulaRaw(input, system), notationFor(system));
}

/** As `show`, but after negation normal form, which is what introduces [[A]]. */
function showNNF(input: string, system: System): string {
  return printStateAscii(parseFormula(input, system), notationFor(system));
}

/** Every formula appearing anywhere in a solved tableau, as printed for the user. */
function solvedOutput(input: string, system: System): string {
  const formula = parseFormula(input, system);
  const result = runTableau(formula, systemAgents(system));
  return textVerbose(result, notationFor(system));
}

// ============================================================
// Which notation each system gets
// ============================================================

describe("Notation selection", () => {
  test("CTL and CTL* both print with path quantifiers", () => {
    expect(notationFor("ctl")).toBe("ctl");
    expect(notationFor("ctlstar")).toBe("ctl");
  });

  test("LTL prints with no quantifier, ATL* keeps its brackets", () => {
    expect(notationFor("ltl")).toBe("ltl");
    expect(notationFor("atl")).toBe("atl");
  });
});

// ============================================================
// CTL and CTL*
// ============================================================

describe("CTL output notation", () => {
  test("<<a>> prints as E and <<>> as A", () => {
    expect(show("EX p", "ctl")).toBe("EX p");
    expect(show("AX p", "ctl")).toBe("AX p");
    expect(show("EG p", "ctl")).toBe("EG p");
    expect(show("AG p", "ctl")).toBe("AG p");
  });

  test("until keeps the parentheses CTL writes it with", () => {
    expect(show("E(p U q)", "ctl")).toBe("E(p U q)");
    expect(show("A(p U q)", "ctl")).toBe("A(p U q)");
  });

  test("F is printed as the (_top U _) it is encoded as", () => {
    expect(show("EF p", "ctl")).toBe("E(_top U p)");
  });

  test("[[a]] prints as A and [[]] as E, giving back the textbook dualities", () => {
    // Negation normal form turns <<A>> into [[A]]; printed back, each of these
    // is exactly the CTL equivalence it should be.
    expect(showNNF("~EF p", "ctl")).toBe("AG ~p");
    expect(showNNF("~AF p", "ctl")).toBe("EG ~p");
    expect(showNNF("~EG p", "ctl")).toBe("A(_top U ~p)"); // AF ~p
    expect(showNNF("~AG p", "ctl")).toBe("E(_top U ~p)"); // EF ~p
  });

  test("nested quantifiers each get their own letter", () => {
    expect(show("AG EF p", "ctl")).toBe("AG E(_top U p)");
    expect(show("AG (p -> EF q)", "ctl")).toBe("AG (~p | E(_top U q))");
  });

  test("CTL* path formulas print under a single quantifier", () => {
    expect(show("E(G F p)", "ctlstar")).toBe("EG (_top U p)");
    expect(show("A(F p | G q)", "ctlstar")).toBe("A((_top U p) | G q)");
  });

  test("no ATL* bracket survives anywhere in a solved CTL tableau", () => {
    const out = solvedOutput("AG (p -> EF q)", "ctl");
    expect(out).not.toContain("<<");
    expect(out).not.toContain("[[");
    expect(out).toContain("AG (~p | E(_top U q))");
  });

  test("no ATL* bracket survives anywhere in a solved CTL* tableau", () => {
    const out = solvedOutput("E(G F p)", "ctlstar");
    expect(out).not.toContain("<<");
    expect(out).not.toContain("[[");
  });

  test("the quantifiers are set as ∀ and ∃ once symbols are available", () => {
    // A and E are what you type; ∀ and ∃ are the same quantifiers typeset,
    // which is how the app's own syntax reference presents them.
    const f = parseFormulaRaw("AG EF p", "ctl");
    expect(printStateUnicode(f, "ctl")).toBe("∀□∃(⊤ U p)");
    expect(printStateLatex(f, "ctl")).toBe(
      "\\forall\\square \\exists(\\top \\,\\mathsf{U}\\, p)",
    );
  });

  test("a quantifier is spaced off an operand that is not a temporal operator", () => {
    // E<atom> would read as one token; EX/EG/E( do not
    expect(printStateAscii(Coal(["a"], PState(Atom("p"))), "ctl")).toBe("E p");
    expect(printStateAscii(Coal(["a"], PNext(PState(Atom("p")))), "ctl")).toBe("EX p");
  });
});

// ============================================================
// LTL
// ============================================================

describe("LTL output notation", () => {
  test("the encoding's <<a>> wrapper is dropped", () => {
    expect(show("p U q", "ltl")).toBe("(p U q)");
    expect(show("X p", "ltl")).toBe("X p");
    expect(show("G p", "ltl")).toBe("G p");
  });

  test("wrappers introduced inside the encoding are dropped too", () => {
    expect(show("G F p", "ltl")).toBe("G (_top U p)");
    expect(show("F G p", "ltl")).toBe("(_top U G p)");
  });

  test("dropping a wrapper never loses a needed parenthesis", () => {
    // <<a>>X <<a>>(p U q): the inner formula must stay bracketed under X
    expect(show("X (p U q)", "ltl")).toBe("X (p U q)");
    expect(show("G (p | q)", "ltl")).toBe("G (p | q)");
  });

  test("no ATL* bracket survives anywhere in a solved LTL tableau", () => {
    const out = solvedOutput("G F p", "ltl");
    expect(out).not.toContain("<<");
    expect(out).not.toContain("[[");
    expect(out).toContain("X G (_top U p)");
  });

  test("negated LTL stays a bare path formula", () => {
    const out = solvedOutput("~(p U q)", "ltl");
    expect(out).not.toContain("<<");
    expect(out).not.toContain("[[");
  });

  test("Unicode drops the wrapper as well, leaving no quantifier symbol", () => {
    expect(printStateUnicode(parseFormulaRaw("G F p", "ltl"), "ltl")).toBe("□(⊤ U p)");
  });

  test("LaTeX drops the wrapper without leaving a stray macro", () => {
    const tex = printStateLatex(parseFormulaRaw("X G p", "ltl"), "ltl");
    expect(tex).toBe("\\bigcirc \\square p");
  });
});

// ============================================================
// ATL* is unaffected
// ============================================================

describe("ATL* output notation", () => {
  test("brackets are kept, and are still the default", () => {
    const f = parseFormulaRaw("<<a,b>>G p", "atl");
    expect(printStateAscii(f, "atl")).toBe("<<a,b>>G p");
    expect(printStateAscii(f)).toBe("<<a,b>>G p");
  });

  test("multi-agent output is untouched by a solved tableau", () => {
    const out = solvedOutput("<<a>>X p", "atl");
    expect(out).toContain("<<a>>X p");
  });

  test("the empty coalition still prints as <<>>", () => {
    expect(printStateAscii(parseFormulaRaw("<<>>X p", "atl"), "atl")).toBe("<<>>X p");
  });
});

// ============================================================
// Guard rails
// ============================================================

describe("Notation falls back rather than lying", () => {
  test("a coalition the one-agent encoding cannot produce keeps its brackets", () => {
    // Two agents have no E/A reading, so CTL notation must not invent one
    const f = Coal(["a", "b"], PNext(PState(Atom("p"))));
    expect(printStateAscii(f, "ctl")).toBe("<<a,b>>X p");
    expect(printStateAscii(f, "ltl")).toBe("<<a,b>>X p");
  });

  test("LTL keeps a co-coalition visible instead of collapsing it", () => {
    // [[a]] is "on every path", which a bare LTL path formula cannot express;
    // it never arises from an LTL input, but must not be silently dropped.
    const f = CoCoal(["a"], PNext(PState(Atom("p"))));
    expect(printStateAscii(f, "ltl")).toBe("[[a]]X p");
  });

  test("formula sets print in the notation they are given", () => {
    const result = runTableau(parseFormula("AG p", "ctl"), systemAgents("ctl"));
    const state = [...result.finalTableau.states.values()][0]!;
    expect(printStateSetAscii(state.formulas, "ctl")).toBe("{AG p, p, AX AG p}");
    expect(printStateSetAscii(state.formulas, "atl")).toBe("{<<>>G p, p, <<>>X <<>>G p}");
  });
});
