/**
 * Tests for the ATL* foundation: types, NNF, parser, printer.
 */

import { describe, test, expect } from "bun:test";
import { parseFormula, parseFormulaRaw } from "../src/core/parser.ts";
import { toNNF, nnfState, nnfPath } from "../src/core/nnf.ts";
import { printStateAscii, printStateUnicode, printPathAscii } from "../src/core/printer.ts";
import {
  Atom, Neg, SAnd, SOr, Coal, CoCoal, STop, SBot,
  PState, PNeg, PAnd, POr, PNext, PAlways, PUntil, PEvent,
  stateKey, pathKey, stateEqual,
  CoalNext, CoalAlways, CoalUntil, CoalEvent,
} from "../src/core/types.ts";

// ============================================================
// Types and keys
// ============================================================

describe("State formula keys", () => {
  test("atoms", () => {
    expect(stateKey(Atom("p"))).toBe("p");
    expect(stateKey(STop)).toBe("T");
    expect(stateKey(SBot)).toBe("F");
  });

  test("negation", () => {
    expect(stateKey(Neg(Atom("p")))).toBe("~p");
  });

  test("conjunction", () => {
    expect(stateKey(SAnd(Atom("p"), Atom("q")))).toBe("(p&q)");
  });

  test("coal and cocoal", () => {
    expect(stateKey(Coal(["a"], PState(Atom("p"))))).toContain("<<a>>");
    expect(stateKey(CoCoal(["a"], PState(Atom("p"))))).toContain("[[a]]");
  });
});

describe("Path formula keys", () => {
  test("state lift", () => {
    expect(pathKey(PState(Atom("p")))).toBe("S{p}");
  });

  test("next", () => {
    expect(pathKey(PNext(PState(Atom("p"))))).toBe("XS{p}");
  });

  test("always", () => {
    expect(pathKey(PAlways(PState(Atom("p"))))).toBe("GS{p}");
  });

  test("until", () => {
    const u = PUntil(PState(Atom("p")), PState(Atom("q")));
    expect(pathKey(u)).toBe("(S{p}US{q})");
  });

  test("andp / orp", () => {
    const a = PAnd(PAlways(PState(Atom("p"))), PEvent(PState(Atom("q"))));
    expect(pathKey(a)).toContain("&P");
  });
});

// ============================================================
// Parser — basic ATL (backward compatibility)
// ============================================================

describe("Parser: basic ATL formulas", () => {
  test("atom", () => {
    const f = parseFormula("p");
    expect(f.kind).toBe("atom");
  });

  test("negated atom", () => {
    const f = parseFormula("~p");
    expect(f.kind).toBe("neg");
  });

  test("conjunction", () => {
    const f = parseFormula("(p & q)");
    expect(f.kind).toBe("and");
  });

  test("disjunction (NNF'd)", () => {
    // p | q → Or(p, q) → after NNF stays as Or(p, q)
    const f = parseFormula("(p | q)");
    expect(f.kind).toBe("or");
  });

  test("<<a>>X p", () => {
    const f = parseFormula("<<a>>X p");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.coalition).toEqual(["a"]);
      expect(f.path.kind).toBe("next");
    }
  });

  test("<<a>>G p", () => {
    const f = parseFormula("<<a>>G p");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.path.kind).toBe("always");
    }
  });

  test("<<a>>(p U q)", () => {
    const f = parseFormula("<<a>>(p U q)");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.path.kind).toBe("until");
    }
  });

  test("<<a>>F p (desugars to until)", () => {
    const f = parseFormula("<<a>>F p");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.path.kind).toBe("until");
      if (f.path.kind === "until") {
        expect(f.path.left.kind).toBe("state");
        if (f.path.left.kind === "state") {
          expect(f.path.left.sub.kind).toBe("top");
        }
      }
    }
  });

  test("empty coalition <<>>X p", () => {
    const f = parseFormula("<<>>X p");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.coalition).toEqual([]);
    }
  });

  test("multi-agent <<a,b>>G p", () => {
    const f = parseFormula("<<a,b>>G p");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.coalition).toEqual(["a", "b"]);
    }
  });

  test("numeric agents <<0,1>>X p", () => {
    const f = parseFormula("<<0,1>>X p");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.coalition).toEqual(["0", "1"]);
    }
  });
});

// ============================================================
// Parser — ATL* formulas
// ============================================================

describe("Parser: ATL* formulas", () => {
  test("<<a>>(Gp & Fq) — path-level conjunction", () => {
    const f = parseFormula("<<a>>(G p & F q)");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.path.kind).toBe("andp");
      if (f.path.kind === "andp") {
        expect(f.path.left.kind).toBe("always");
        expect(f.path.right.kind).toBe("until"); // F desugars to ⊤ U
      }
    }
  });

  test("<<a>>GFp — nested temporal", () => {
    const f = parseFormula("<<a>>G F p");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.path.kind).toBe("always");
      if (f.path.kind === "always") {
        expect(f.path.sub.kind).toBe("until"); // F desugars to ⊤ U
      }
    }
  });

  test("<<a>>(Gp | Gq) — path-level disjunction", () => {
    const f = parseFormula("<<a>>(G p | G q)");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.path.kind).toBe("orp");
    }
  });

  test("[[a]]G p — co-coalition", () => {
    const f = parseFormula("[[a]]G p");
    expect(f.kind).toBe("cocoal");
    if (f.kind === "cocoal") {
      expect(f.coalition).toEqual(["a"]);
      expect(f.path.kind).toBe("always");
    }
  });

  test("nested coalition in path: <<a>>(G p & <<b>>X q)", () => {
    const f = parseFormula("<<a>>(G p & <<b>>X q)");
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.path.kind).toBe("andp");
    }
  });
});

// ============================================================
// NNF transformation
// ============================================================

describe("NNF transformation", () => {
  test("double negation elimination", () => {
    const f = toNNF(Neg(Neg(Atom("p"))));
    expect(f.kind).toBe("atom");
  });

  test("~Top → Bot", () => {
    const f = toNNF(Neg(STop));
    expect(f.kind).toBe("bot");
  });

  test("~Bot → Top", () => {
    const f = toNNF(Neg(SBot));
    expect(f.kind).toBe("top");
  });

  test("De Morgan: ~(p & q) → (~p | ~q)", () => {
    const f = toNNF(Neg(SAnd(Atom("p"), Atom("q"))));
    expect(f.kind).toBe("or");
    if (f.kind === "or") {
      expect(f.left.kind).toBe("neg");
      expect(f.right.kind).toBe("neg");
    }
  });

  test("~<<a>>π → [[a]]~π", () => {
    const f = toNNF(Neg(Coal(["a"], PAlways(PState(Atom("p"))))));
    expect(f.kind).toBe("cocoal");
    if (f.kind === "cocoal") {
      expect(f.coalition).toEqual(["a"]);
      // ~□p → ⊤ U ~p (i.e. ◇~p)
      expect(f.path.kind).toBe("until");
    }
  });

  test("~[[a]]π → <<a>>~π", () => {
    const f = toNNF(Neg(CoCoal(["a"], PAlways(PState(Atom("p"))))));
    expect(f.kind).toBe("coal");
  });

  test("path: ~(⊤ U p) → □~p", () => {
    const f = toNNF(Neg(Coal(["a"], PUntil(PState(STop), PState(Atom("p"))))));
    // ~<<a>>(⊤ U p) → [[a]]~(⊤ U p) → [[a]]□~p
    expect(f.kind).toBe("cocoal");
    if (f.kind === "cocoal") {
      expect(f.path.kind).toBe("always");
      if (f.path.kind === "always") {
        expect(f.path.sub.kind).toBe("state");
        if (f.path.sub.kind === "state") {
          expect(f.path.sub.sub.kind).toBe("neg");
        }
      }
    }
  });

  test("~<<a>>F p = ~<<a>>(⊤ U p) → [[a]]□~p (via parsing)", () => {
    const f = parseFormula("~<<a>>F p");
    expect(f.kind).toBe("cocoal");
    if (f.kind === "cocoal") {
      expect(f.path.kind).toBe("always");
    }
  });
});

// ============================================================
// Printer
// ============================================================

describe("Printer", () => {
  test("ASCII round-trip for simple formulas", () => {
    expect(printStateAscii(Atom("p"))).toBe("p");
    expect(printStateAscii(Neg(Atom("p")))).toBe("~p");
    expect(printStateAscii(SAnd(Atom("p"), Atom("q")))).toBe("(p & q)");
  });

  test("ASCII for coal/cocoal", () => {
    const coal = Coal(["a"], PAlways(PState(Atom("p"))));
    expect(printStateAscii(coal)).toBe("<<a>>G p");

    const cocoal = CoCoal(["a", "b"], PNext(PState(Atom("q"))));
    expect(printStateAscii(cocoal)).toBe("[[a,b]]X q");
  });

  test("ASCII for ATL* path formulas", () => {
    const f = Coal(["a"], PAnd(PAlways(PState(Atom("p"))), PEvent(PState(Atom("q")))));
    const s = printStateAscii(f);
    expect(s).toContain("G p");
    expect(s).toContain("&");
  });

  test("Unicode printing", () => {
    const f = Coal(["a"], PAlways(PState(Atom("p"))));
    const s = printStateUnicode(f);
    expect(s).toContain("⟨⟨a⟩⟩");
    expect(s).toContain("□");
  });
});

// ============================================================
// ATL convenience constructors
// ============================================================

describe("ATL convenience constructors", () => {
  test("CoalNext creates Coal(A, PNext(PState(φ)))", () => {
    const f = CoalNext(["a"], Atom("p"));
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.path.kind).toBe("next");
      if (f.path.kind === "next") {
        expect(f.path.sub.kind).toBe("state");
      }
    }
  });

  test("CoalAlways creates Coal(A, PAlways(PState(φ)))", () => {
    const f = CoalAlways(["a"], Atom("p"));
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.path.kind).toBe("always");
    }
  });

  test("CoalUntil creates Coal(A, PUntil(PState(φ), PState(ψ)))", () => {
    const f = CoalUntil(["a"], Atom("p"), Atom("q"));
    expect(f.kind).toBe("coal");
    if (f.kind === "coal") {
      expect(f.path.kind).toBe("until");
    }
  });
});

// ============================================================
// Phase 2: Classify
// ============================================================

import { classifyState, isNextTime, isGamma } from "../src/core/classify.ts";

describe("State-level classification", () => {
  test("atoms are elementary", () => {
    expect(classifyState(Atom("p")).type).toBe("elementary");
    expect(classifyState(STop).type).toBe("elementary");
    expect(classifyState(SBot).type).toBe("elementary");
  });

  test("Neg(atom) is elementary", () => {
    expect(classifyState(Neg(Atom("p"))).type).toBe("elementary");
  });

  test("And is alpha", () => {
    const cls = classifyState(SAnd(Atom("p"), Atom("q")));
    expect(cls.type).toBe("alpha");
    if (cls.type === "alpha") {
      expect(cls.components.length).toBe(2);
    }
  });

  test("Or is beta", () => {
    const cls = classifyState(SOr(Atom("p"), Atom("q")));
    expect(cls.type).toBe("beta");
    if (cls.type === "beta") {
      expect(cls.components.length).toBe(2);
    }
  });

  test("Coal(A, Next(State _)) is elementary (next-time)", () => {
    const f = Coal(["a"], PNext(PState(Atom("p"))));
    expect(classifyState(f).type).toBe("elementary");
    expect(isNextTime(f)).toBe(true);
    expect(isGamma(f)).toBe(false);
  });

  test("CoCoal(A, Next(State _)) is elementary (next-time)", () => {
    const f = CoCoal(["a"], PNext(PState(Atom("p"))));
    expect(classifyState(f).type).toBe("elementary");
    expect(isNextTime(f)).toBe(true);
    expect(isGamma(f)).toBe(false);
  });

  test("Coal(A, Always _) is gamma", () => {
    const f = Coal(["a"], PAlways(PState(Atom("p"))));
    expect(classifyState(f).type).toBe("gamma");
    expect(isGamma(f)).toBe(true);
    expect(isNextTime(f)).toBe(false);
  });

  test("Coal(A, Until _) is gamma", () => {
    const f = Coal(["a"], PUntil(PState(Atom("p")), PState(Atom("q"))));
    expect(classifyState(f).type).toBe("gamma");
    expect(isGamma(f)).toBe(true);
  });

  test("CoCoal(A, Always _) is gamma", () => {
    const f = CoCoal(["a"], PAlways(PState(Atom("p"))));
    expect(classifyState(f).type).toBe("gamma");
    expect(isGamma(f)).toBe(true);
  });
});

// ============================================================
// Phase 2: Formula utilities
// ============================================================

import {
  agentsInState,
  isPatentlyInconsistent,
  isEventuality,
  containsEventualityOperator,
  isLiteral,
  isEnforceableNext,
  isUnavoidableNext,
} from "../src/core/formula.ts";
import { StateFormulaSet } from "../src/core/types.ts";

describe("Agent collection", () => {
  test("atoms have no agents", () => {
    expect(agentsInState(Atom("p")).size).toBe(0);
  });

  test("Coal collects coalition agents", () => {
    const f = Coal(["a", "b"], PAlways(PState(Atom("p"))));
    const agents = agentsInState(f);
    expect(agents.has("a")).toBe(true);
    expect(agents.has("b")).toBe(true);
    expect(agents.size).toBe(2);
  });

  test("nested coalitions collect all agents", () => {
    const f = Coal(["a"], PAnd(PState(Coal(["b"], PNext(PState(Atom("p"))))), PState(Atom("q"))));
    const agents = agentsInState(f);
    expect(agents.has("a")).toBe(true);
    expect(agents.has("b")).toBe(true);
  });
});

describe("Patent inconsistency", () => {
  test("p and ~p is inconsistent", () => {
    const fs = new StateFormulaSet([Atom("p"), Neg(Atom("p"))]);
    expect(isPatentlyInconsistent(fs)).toBe(true);
  });

  test("Top and Bot is inconsistent", () => {
    const fs = new StateFormulaSet([STop, SBot]);
    expect(isPatentlyInconsistent(fs)).toBe(true);
  });

  test("p and q is consistent", () => {
    const fs = new StateFormulaSet([Atom("p"), Atom("q")]);
    expect(isPatentlyInconsistent(fs)).toBe(false);
  });
});

describe("Eventuality detection", () => {
  test("Coal(A, Always(State p)) is an eventuality (contains no Until but...)", () => {
    const f = Coal(["a"], PAlways(PState(Atom("p"))));
    // Always alone has no Until → NOT an eventuality
    expect(isEventuality(f)).toBe(false);
  });

  test("Coal(A, Until(p, q)) is an eventuality", () => {
    const f = Coal(["a"], PUntil(PState(Atom("p")), PState(Atom("q"))));
    expect(isEventuality(f)).toBe(true);
  });

  test("Coal(A, Next(State p)) is NOT an eventuality", () => {
    const f = Coal(["a"], PNext(PState(Atom("p"))));
    expect(isEventuality(f)).toBe(false);
  });

  test("CoCoal(A, Always(Until(p, q))) is an eventuality", () => {
    const f = CoCoal(["a"], PAlways(PUntil(PState(Atom("p")), PState(Atom("q")))));
    expect(isEventuality(f)).toBe(true);
  });

  test("plain atom is NOT an eventuality", () => {
    expect(isEventuality(Atom("p"))).toBe(false);
  });

  test("containsEventualityOperator detects Until in nested path", () => {
    expect(containsEventualityOperator(PUntil(PState(Atom("p")), PState(Atom("q"))))).toBe(true);
    expect(containsEventualityOperator(PAlways(PState(Atom("p"))))).toBe(false);
    expect(containsEventualityOperator(PAnd(PAlways(PState(Atom("p"))), PUntil(PState(STop), PState(Atom("q")))))).toBe(true);
  });
});

describe("Next-time formula checks", () => {
  test("Coal(A, Next(State p)) is enforceable", () => {
    expect(isEnforceableNext(Coal(["a"], PNext(PState(Atom("p")))))).toBe(true);
    expect(isUnavoidableNext(Coal(["a"], PNext(PState(Atom("p")))))).toBe(false);
  });

  test("CoCoal(A, Next(State p)) is unavoidable", () => {
    expect(isUnavoidableNext(CoCoal(["a"], PNext(PState(Atom("p")))))).toBe(true);
    expect(isEnforceableNext(CoCoal(["a"], PNext(PState(Atom("p")))))).toBe(false);
  });

  test("Coal(A, Always _) is neither", () => {
    expect(isEnforceableNext(Coal(["a"], PAlways(PState(Atom("p")))))).toBe(false);
    expect(isUnavoidableNext(Coal(["a"], PAlways(PState(Atom("p")))))).toBe(false);
  });
});

// ============================================================
// Phase 2: Gamma-decomposition
// ============================================================

import {
  gammaSets,
  gammaComp,
  otimes,
  oplus,
  clearDecompositionCache,
} from "../src/core/decomposition.ts";

describe("Gamma-decomposition: gammaSets", () => {
  // Clear cache before each test group
  test("State(f) → single tuple with f in f1, singl_top in f3", () => {
    clearDecompositionCache();
    const result = gammaSets(PState(Atom("p")));
    expect(result.size).toBe(1);
    const tuples = result.toArray();
    expect(tuples[0]!.f1.has(Atom("p"))).toBe(true);
    // f3 should be singl_top (contains State(⊤))
    expect(tuples[0]!.f3.size).toBe(1);
  });

  test("Next(f) → single tuple with Top in f1, f in f3", () => {
    clearDecompositionCache();
    const result = gammaSets(PNext(PState(Atom("p"))));
    expect(result.size).toBe(1);
    const tuples = result.toArray();
    expect(tuples[0]!.f1.has(STop)).toBe(true);
    // f3 should contain {State(p)}
    expect(tuples[0]!.f3.size).toBe(1);
  });

  test("Always(State(p)) → single tuple, f1={p}, f3 carries Always", () => {
    clearDecompositionCache();
    const result = gammaSets(PAlways(PState(Atom("p"))));
    expect(result.size).toBe(1);
    const tuples = result.toArray();
    expect(tuples[0]!.f1.has(Atom("p"))).toBe(true);
    // f3 should carry the Always formula
    expect(tuples[0]!.f3.size).toBe(1);
  });

  test("Until(State(p), State(q)) → two alternatives (p-continues, q-resolves)", () => {
    clearDecompositionCache();
    const result = gammaSets(PUntil(PState(Atom("p")), PState(Atom("q"))));
    // Should have 2 tuples: one where q holds (resolved), one where p holds (continues)
    expect(result.size).toBe(2);
  });

  test("AndP(f1, f2) → otimes of gammaSets", () => {
    clearDecompositionCache();
    const result = gammaSets(PAnd(PState(Atom("p")), PState(Atom("q"))));
    expect(result.size).toBeGreaterThanOrEqual(1);
    // Should have both p and q in f1 of some tuple
    const tuples = result.toArray();
    const combined = tuples.some(t => t.f1.has(Atom("p")) && t.f1.has(Atom("q")));
    expect(combined).toBe(true);
  });

  test("OrP(f1, f2) → union + oplus", () => {
    clearDecompositionCache();
    const result = gammaSets({ kind: "orp", left: PState(Atom("p")), right: PState(Atom("q")) });
    // Should have at least 2 tuples: one with p, one with q
    expect(result.size).toBeGreaterThanOrEqual(2);
  });
});

describe("Gamma-decomposition: gammaComp", () => {
  test("Coal(A, Always(State p)) → produces formula tuples", () => {
    clearDecompositionCache();
    const f = Coal(["a"], PAlways(PState(Atom("p"))));
    const result = gammaComp(f);
    expect(result.size).toBeGreaterThanOrEqual(1);
    // Each tuple should have a frm and nextFrm
    for (const t of result) {
      expect(t.frm).toBeDefined();
      expect(t.nextFrm).toBeDefined();
      expect(t.pathFrm).toBeDefined();
    }
  });

  test("Coal(A, Until(State p, State q)) → produces multiple tuples", () => {
    clearDecompositionCache();
    const f = Coal(["a"], PUntil(PState(Atom("p")), PState(Atom("q"))));
    const result = gammaComp(f);
    expect(result.size).toBeGreaterThanOrEqual(1);
  });

  test("CoCoal(A, Always(State p)) → produces formula tuples with cocoal wrapping", () => {
    clearDecompositionCache();
    const f = CoCoal(["a"], PAlways(PState(Atom("p"))));
    const result = gammaComp(f);
    expect(result.size).toBeGreaterThanOrEqual(1);
  });

  test("Coal(A, AndP(Always(State p), Until(State T, State q))) — complex ATL*", () => {
    clearDecompositionCache();
    // <<a>>(Gp & Fq)
    const f = Coal(["a"], PAnd(PAlways(PState(Atom("p"))), PUntil(PState(STop), PState(Atom("q")))));
    const result = gammaComp(f);
    expect(result.size).toBeGreaterThanOrEqual(1);
  });
});

// ============================================================
// Phase 2: Saturation (expansion)
// ============================================================

import { ruleSR, tupleSetToFormulas } from "../src/core/expansion.ts";

describe("Saturation (Rule SR)", () => {
  test("single atom → one state with that atom", () => {
    clearDecompositionCache();
    const fs = new StateFormulaSet([Atom("p")]);
    const result = ruleSR(fs);
    expect(result.size).toBe(1);
  });

  test("And(p, q) → one state with both p and q", () => {
    clearDecompositionCache();
    const fs = new StateFormulaSet([SAnd(Atom("p"), Atom("q"))]);
    const result = ruleSR(fs);
    expect(result.size).toBe(1);
    // The state should contain p and q
    const states = result.toArray();
    const formulas = tupleSetToFormulas(states[0]!);
    expect(formulas.has(Atom("p"))).toBe(true);
    expect(formulas.has(Atom("q"))).toBe(true);
  });

  test("Or(p, q) → two states", () => {
    clearDecompositionCache();
    const fs = new StateFormulaSet([SOr(Atom("p"), Atom("q"))]);
    const result = ruleSR(fs);
    expect(result.size).toBe(2);
  });

  test("p & ~p → inconsistent → one set (inconsistency checked later in tableau)", () => {
    // After removing early inconsistency filtering from product (to match TATL behavior),
    // ruleSR returns the set {p, ~p} which is patently inconsistent.
    // The inconsistency is caught later during state creation (getOrCreateState).
    clearDecompositionCache();
    const fs = new StateFormulaSet([SAnd(Atom("p"), Neg(Atom("p")))]);
    const result = ruleSR(fs);
    expect(result.size).toBe(1);
  });

  test("Coal(A, Next(State p)) — next-time primitive → one state", () => {
    clearDecompositionCache();
    const fs = new StateFormulaSet([Coal(["a"], PNext(PState(Atom("p"))))]);
    const result = ruleSR(fs);
    expect(result.size).toBe(1);
  });

  test("Coal(A, Always(State p)) — gamma → at least one state", () => {
    clearDecompositionCache();
    const fs = new StateFormulaSet([Coal(["a"], PAlways(PState(Atom("p"))))]);
    const result = ruleSR(fs);
    expect(result.size).toBeGreaterThanOrEqual(1);
  });
});
