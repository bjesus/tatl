/**
 * Unit tests for formula utilities: parser, printer, classification, closure, expansion.
 */

import { describe, test, expect } from "bun:test";
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
  formulaKey,
  formulaEqual,
  coalitionSubset,
  coalitionIntersects,
  coalitionEqual,
  type Formula,
} from "../src/core/types.ts";
import { parseFormula } from "../src/core/parser.ts";
import { printFormula } from "../src/core/printer.ts";
import { classifyFormula } from "../src/core/classify.ts";
import {
  subformulas,
  closure,
  extendedClosure,
  isPatentlyInconsistent,
  isEventuality,
  isDiamond,
  isBox,
  agentsInFormula,
} from "../src/core/formula.ts";
import { fullExpansion, isFullyExpanded } from "../src/core/expansion.ts";

// ============================================================
// Parser tests
// ============================================================

describe("Parser", () => {
  test("parse atom", () => {
    const f = parseFormula("p");
    expect(f.kind).toBe("atom");
    if (f.kind === "atom") expect(f.name).toBe("p");
  });

  test("parse negation", () => {
    const f = parseFormula("~p");
    expect(f.kind).toBe("not");
    if (f.kind === "not") {
      expect(f.sub.kind).toBe("atom");
    }
  });

  test("parse conjunction", () => {
    const f = parseFormula("(p & q)");
    expect(f.kind).toBe("and");
    if (f.kind === "and") {
      expect(f.left.kind).toBe("atom");
      expect(f.right.kind).toBe("atom");
    }
  });

  test("parse disjunction (sugar)", () => {
    const f = parseFormula("(p | q)");
    // Desugars to ~(~p & ~q)
    expect(f.kind).toBe("not");
  });

  test("parse implication (sugar)", () => {
    const f = parseFormula("(p -> q)");
    // Desugars to ~(p & ~q)
    expect(f.kind).toBe("not");
  });

  test("parse individual knowledge Ka", () => {
    const f = parseFormula("Ka p");
    expect(f.kind).toBe("D");
    if (f.kind === "D") {
      expect(f.coalition).toEqual(["a"]);
      expect(f.sub.kind).toBe("atom");
    }
  });

  test("parse nested knowledge KaKb without space", () => {
    const f = parseFormula("KaKb p");
    // Should parse as Ka(Kb p), not K(aKb) p
    expect(f.kind).toBe("D");
    if (f.kind === "D") {
      expect(f.coalition).toEqual(["a"]);
      expect(f.sub.kind).toBe("D");
      if (f.sub.kind === "D") {
        expect(f.sub.coalition).toEqual(["b"]);
        expect(f.sub.sub.kind).toBe("atom");
      }
    }
  });

  test("parse ~KaKb p correctly", () => {
    const f = parseFormula("~KaKb p");
    expect(f.kind).toBe("not");
    if (f.kind === "not") {
      expect(f.sub.kind).toBe("D");
      if (f.sub.kind === "D") {
        expect(f.sub.coalition).toEqual(["a"]);
        expect(f.sub.sub.kind).toBe("D");
      }
    }
  });

  test("parse distributed knowledge D{a,b}", () => {
    const f = parseFormula("D{a,b} p");
    expect(f.kind).toBe("D");
    if (f.kind === "D") {
      expect(f.coalition).toEqual(["a", "b"]);
    }
  });

  test("parse common knowledge C{a,b}", () => {
    const f = parseFormula("C{a,b} p");
    expect(f.kind).toBe("C");
    if (f.kind === "C") {
      expect(f.coalition).toEqual(["a", "b"]);
    }
  });

  test("parse K{a} as individual knowledge (same as Ka)", () => {
    const f = parseFormula("K{a} p");
    expect(f.kind).toBe("D");
    if (f.kind === "D") {
      expect(f.coalition).toEqual(["a"]);
      expect(f.sub.kind).toBe("atom");
    }
  });

  test("parse K{a,b} as conjunction of individual knowledge", () => {
    const f = parseFormula("K{a,b} p");
    // K{a,b} p desugars to (Ka p & Kb p)
    expect(f.kind).toBe("and");
    if (f.kind === "and") {
      expect(f.left.kind).toBe("D");
      if (f.left.kind === "D") {
        expect(f.left.coalition).toEqual(["a"]);
      }
      expect(f.right.kind).toBe("D");
      if (f.right.kind === "D") {
        expect(f.right.coalition).toEqual(["b"]);
      }
    }
  });

  test("parse K{a,b,c} as nested conjunction", () => {
    const f = parseFormula("K{a,b,c} p");
    // K{a,b,c} p desugars to (Ka p & (Kb p & Kc p))
    expect(f.kind).toBe("and");
    if (f.kind === "and") {
      expect(f.left.kind).toBe("D");
      if (f.left.kind === "D") expect(f.left.coalition).toEqual(["a"]);
      expect(f.right.kind).toBe("and");
      if (f.right.kind === "and") {
        expect(f.right.left.kind).toBe("D");
        if (f.right.left.kind === "D") expect(f.right.left.coalition).toEqual(["b"]);
        expect(f.right.right.kind).toBe("D");
        if (f.right.right.kind === "D") expect(f.right.right.coalition).toEqual(["c"]);
      }
    }
  });

  test("parse complex formula from Example 1", () => {
    const f = parseFormula("(~D{a,c} C{a,b} p & C{a,b} (p & q))");
    expect(f.kind).toBe("and");
  });

  test("parse Example 4 formula", () => {
    const f = parseFormula("(~D{a,b} p & ~D{a,c} ~Ka p)");
    expect(f.kind).toBe("and");
  });

  test("parse Example 5 formula", () => {
    const f = parseFormula("(C{a,b} Ka p -> ~C{b,c} Kb p)");
    expect(f.kind).toBe("not"); // implication desugars
  });

  test("parse nested negation", () => {
    const f = parseFormula("~~p");
    expect(f.kind).toBe("not");
    if (f.kind === "not") {
      expect(f.sub.kind).toBe("not");
    }
  });

  test("roundtrip: parse then print", () => {
    const inputs = [
      "p",
      "~p",
      "(p & q)",
      "Ka p",
      "D{a,b} p",
      "C{a,b} p",
      "~D{a,b} p",
      "~C{a,b} p",
    ];
    for (const input of inputs) {
      const f = parseFormula(input);
      const printed = printFormula(f);
      const reparsed = parseFormula(printed);
      expect(formulaEqual(f, reparsed)).toBe(true);
    }
  });
});

// ============================================================
// Formula classification tests
// ============================================================

describe("Classification", () => {
  test("atom is elementary", () => {
    const cls = classifyFormula(Atom("p"));
    expect(cls.type).toBe("elementary");
  });

  test("¬p is elementary", () => {
    const cls = classifyFormula(Not(Atom("p")));
    expect(cls.type).toBe("elementary");
  });

  test("¬¬φ is α with component {φ}", () => {
    const p = Atom("p");
    const cls = classifyFormula(Not(Not(p)));
    expect(cls.type).toBe("alpha");
    if (cls.type === "alpha") {
      expect(cls.components.length).toBe(1);
      expect(formulaEqual(cls.components[0]!, p)).toBe(true);
    }
  });

  test("φ ∧ ψ is α with components {φ, ψ}", () => {
    const p = Atom("p");
    const q = Atom("q");
    const cls = classifyFormula(And(p, q));
    expect(cls.type).toBe("alpha");
    if (cls.type === "alpha") {
      expect(cls.components.length).toBe(2);
    }
  });

  test("D_A φ is α with components {D_A φ, φ}", () => {
    const p = Atom("p");
    const d = D(["a", "b"], p);
    const cls = classifyFormula(d);
    expect(cls.type).toBe("alpha");
    if (cls.type === "alpha") {
      expect(cls.components.length).toBe(2);
      expect(formulaEqual(cls.components[0]!, d)).toBe(true);
      expect(formulaEqual(cls.components[1]!, p)).toBe(true);
    }
  });

  test("C_A φ is α with components {φ} ∪ {D_a C_A φ | a ∈ A}", () => {
    const p = Atom("p");
    const c = C(["a", "b"], p);
    const cls = classifyFormula(c);
    expect(cls.type).toBe("alpha");
    if (cls.type === "alpha") {
      // Components: {p, D_a C_{a,b} p, D_b C_{a,b} p}
      expect(cls.components.length).toBe(3);
      expect(formulaEqual(cls.components[0]!, p)).toBe(true);
      // D_a C_{a,b} p
      expect(cls.components[1]!.kind).toBe("D");
      // D_b C_{a,b} p
      expect(cls.components[2]!.kind).toBe("D");
    }
  });

  test("¬(φ ∧ ψ) is β with components {¬φ, ¬ψ}", () => {
    const p = Atom("p");
    const q = Atom("q");
    const cls = classifyFormula(Not(And(p, q)));
    expect(cls.type).toBe("beta");
    if (cls.type === "beta") {
      expect(cls.components.length).toBe(2);
    }
  });

  test("¬C_A φ is β with components {¬φ} ∪ {¬D_a C_A φ | a ∈ A}", () => {
    const p = Atom("p");
    const c = C(["a", "b"], p);
    const cls = classifyFormula(Not(c));
    expect(cls.type).toBe("beta");
    if (cls.type === "beta") {
      // Components: {¬p, ¬D_a C_{a,b} p, ¬D_b C_{a,b} p}
      expect(cls.components.length).toBe(3);
    }
  });

  test("¬D_A φ is elementary", () => {
    const cls = classifyFormula(Not(D(["a"], Atom("p"))));
    expect(cls.type).toBe("elementary");
  });
});

// ============================================================
// Formula utility tests
// ============================================================

describe("Formula utilities", () => {
  test("formulaEqual works", () => {
    expect(formulaEqual(Atom("p"), Atom("p"))).toBe(true);
    expect(formulaEqual(Atom("p"), Atom("q"))).toBe(false);
    expect(formulaEqual(D(["a", "b"], Atom("p")), D(["a", "b"], Atom("p")))).toBe(true);
    expect(formulaEqual(D(["b", "a"], Atom("p")), D(["a", "b"], Atom("p")))).toBe(true); // normalized
  });

  test("coalitionSubset", () => {
    expect(coalitionSubset(["a"], ["a", "b"])).toBe(true);
    expect(coalitionSubset(["a", "b"], ["a", "b"])).toBe(true);
    expect(coalitionSubset(["a", "b"], ["a"])).toBe(false);
    expect(coalitionSubset(["c"], ["a", "b"])).toBe(false);
  });

  test("coalitionIntersects", () => {
    expect(coalitionIntersects(["a"], ["a", "b"])).toBe(true);
    expect(coalitionIntersects(["c"], ["a", "b"])).toBe(false);
    expect(coalitionIntersects(["a", "c"], ["b", "c"])).toBe(true);
  });

  test("isPatentlyInconsistent", () => {
    const fs1 = new FormulaSet([Atom("p"), Not(Atom("p"))]);
    expect(isPatentlyInconsistent(fs1)).toBe(true);

    const fs2 = new FormulaSet([Atom("p"), Atom("q")]);
    expect(isPatentlyInconsistent(fs2)).toBe(false);
  });

  test("isEventuality", () => {
    expect(isEventuality(Not(C(["a", "b"], Atom("p"))))).toBe(true);
    expect(isEventuality(Not(D(["a"], Atom("p"))))).toBe(false);
    expect(isEventuality(Atom("p"))).toBe(false);
  });

  test("isDiamond", () => {
    expect(isDiamond(Not(D(["a"], Atom("p"))))).toBe(true);
    expect(isDiamond(D(["a"], Atom("p")))).toBe(false);
    expect(isDiamond(Not(Atom("p")))).toBe(false);
  });

  test("agentsInFormula", () => {
    const f = parseFormula("(~D{a,c} C{a,b} p & C{a,b} (p & q))");
    const agents = agentsInFormula(f);
    expect(agents.size).toBe(3);
    expect(agents.has("a")).toBe(true);
    expect(agents.has("b")).toBe(true);
    expect(agents.has("c")).toBe(true);
  });
});

// ============================================================
// Closure tests
// ============================================================

describe("Closure", () => {
  test("closure of atom", () => {
    const cl = closure(Atom("p"));
    expect(cl.size).toBe(1);
    expect(cl.has(Atom("p"))).toBe(true);
  });

  test("closure of ¬D_a p includes ¬p", () => {
    const f = Not(D(["a"], Atom("p")));
    const cl = closure(f);
    expect(cl.has(f)).toBe(true);
    expect(cl.has(Not(Atom("p")))).toBe(true);
  });

  test("closure of D_a p includes D_a p and p", () => {
    const f = D(["a"], Atom("p"));
    const cl = closure(f);
    expect(cl.has(f)).toBe(true);
    expect(cl.has(Atom("p"))).toBe(true);
  });

  test("closure of C_{a,b} p includes D_a C_{a,b} p and D_b C_{a,b} p", () => {
    const p = Atom("p");
    const c = C(["a", "b"], p);
    const cl = closure(c);
    expect(cl.has(c)).toBe(true);
    expect(cl.has(p)).toBe(true);
    expect(cl.has(D(["a"], c))).toBe(true);
    expect(cl.has(D(["b"], c))).toBe(true);
  });

  test("extended closure includes negations", () => {
    const p = Atom("p");
    const ecl = extendedClosure(p);
    expect(ecl.has(p)).toBe(true);
    expect(ecl.has(Not(p))).toBe(true);
  });
});

// ============================================================
// FormulaSet tests
// ============================================================

describe("FormulaSet", () => {
  test("add and has", () => {
    const fs = new FormulaSet();
    fs.add(Atom("p"));
    expect(fs.has(Atom("p"))).toBe(true);
    expect(fs.has(Atom("q"))).toBe(false);
  });

  test("equality", () => {
    const fs1 = new FormulaSet([Atom("p"), Atom("q")]);
    const fs2 = new FormulaSet([Atom("q"), Atom("p")]);
    expect(fs1.equals(fs2)).toBe(true);
  });

  test("clone", () => {
    const fs = new FormulaSet([Atom("p")]);
    const copy = fs.clone();
    copy.add(Atom("q"));
    expect(fs.size).toBe(1);
    expect(copy.size).toBe(2);
  });

  test("key is canonical", () => {
    const fs1 = new FormulaSet([Atom("p"), Atom("q")]);
    const fs2 = new FormulaSet([Atom("q"), Atom("p")]);
    expect(fs1.key()).toBe(fs2.key());
  });
});

// ============================================================
// Full expansion tests
// ============================================================

describe("FullExpansion", () => {
  test("expansion of consistent atom set", () => {
    const gamma = new FormulaSet([Atom("p")]);
    const result = fullExpansion(gamma);
    expect(result.length).toBe(1);
    expect(result[0]!.has(Atom("p"))).toBe(true);
  });

  test("expansion of inconsistent set is empty", () => {
    const gamma = new FormulaSet([Atom("p"), Not(Atom("p"))]);
    const result = fullExpansion(gamma);
    expect(result.length).toBe(0);
  });

  test("expansion of conjunction", () => {
    const gamma = new FormulaSet([And(Atom("p"), Atom("q"))]);
    const result = fullExpansion(gamma);
    expect(result.length).toBe(1);
    expect(result[0]!.has(Atom("p"))).toBe(true);
    expect(result[0]!.has(Atom("q"))).toBe(true);
  });

  test("expansion of negated conjunction branches", () => {
    const gamma = new FormulaSet([Not(And(Atom("p"), Atom("q")))]);
    const result = fullExpansion(gamma);
    // Should produce 2 branches: one with ¬p, one with ¬q
    expect(result.length).toBe(2);
  });

  test("expansion of D_a p adds p", () => {
    const gamma = new FormulaSet([D(["a"], Atom("p"))]);
    const result = fullExpansion(gamma);
    expect(result.length).toBe(1);
    expect(result[0]!.has(Atom("p"))).toBe(true);
    expect(result[0]!.has(D(["a"], Atom("p")))).toBe(true);
  });

  test("expansion of ¬C_{a,b} p produces branches", () => {
    const p = Atom("p");
    const negC = Not(C(["a", "b"], p));
    const gamma = new FormulaSet([negC]);
    const result = fullExpansion(gamma);
    // β-components: {¬p, ¬D_a C_{a,b} p, ¬D_b C_{a,b} p}
    // Standard β-branching gives 3 branches, plus the special rule 3
    // may add extra branches with ¬p
    expect(result.length).toBeGreaterThanOrEqual(3);
    // At least one should contain ¬p
    const hasNegP = result.some((s) => s.has(Not(p)));
    expect(hasNegP).toBe(true);
  });

  test("all fully expanded results are indeed fully expanded", () => {
    const gamma = new FormulaSet([
      Not(And(Atom("p"), Atom("q"))),
      D(["a"], Atom("r")),
    ]);
    const result = fullExpansion(gamma);
    for (const s of result) {
      expect(isFullyExpanded(s)).toBe(true);
    }
  });
});
