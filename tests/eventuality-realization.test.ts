/**
 * E3 eventuality-realization completeness tests.
 *
 * E3 may only eliminate a state when an eventuality is genuinely
 * unrealizable. A realization witness is a DAG: the same (state, residual)
 * node may be needed in several AND-branches of the universal check (once
 * per successor prestate), while cycles that merely postpone the eventuality
 * must still fail. The formulas here are satisfiable only through witnesses
 * that share states across branches, so any search that refuses to revisit a
 * state — or otherwise under-approximates the least fixpoint — wrongly
 * reports them unsatisfiable.
 */

import { describe, test, expect } from "bun:test";
import { parseFormula, systemAgents } from "../src/core/parser.ts";
import { runTableau } from "../src/core/tableau.ts";

function isSatCtlStar(formulaStr: string): boolean {
  const formula = parseFormula(formulaStr, "ctlstar");
  return runTableau(formula, systemAgents("ctlstar")).satisfiable;
}

// A CTL* family satisfiable for every n, with deep realization witnesses:
// q encodes an n-bit counter along each path, r marks every n-th level,
// binary branching via p, and AF demands q=1 n times in a row eventually.
// The X-chains funnel distinct branches of the AF witness through shared
// tableau states.
const COUNTER_FORMULAS = [
  "AG(EXp & EX~p) & A(~q) & AF(r & q) & r & AG(r -> X(r)) & A(r -> ((q -> X((~r)U(r & ~q))) & (~q -> X((~r)U(r & q))))) & A(~Xr -> ((~q | Xq) & ((Xq & XXq) | (X~q & XX~q))) | (q & X~q & X~q & XXq))",
  "AG(EXp & EX~p) & A(~q & X(~q)) & AF(r & q & X(q)) & r & AG(r -> X(~r & X(r))) & A(r -> ((q -> X((~r)U(r & ~q))) & (~q -> X((~r)U(r & q))))) & A(~Xr -> ((~q | XXq) & ((Xq & XXXq) | (X~q & XXX~q))) | (q & XX~q & X~q & XXXq))",
  "AG(EXp & EX~p) & A(~q & X(~q & X(~q))) & AF(r & q & X(q & X(q))) & r & AG(r -> X(~r & X(~r & X(r)))) & A(r -> ((q -> X((~r)U(r & ~q))) & (~q -> X((~r)U(r & q))))) & A(~Xr -> ((~q | XXXq) & ((Xq & XXXXq) | (X~q & XXXX~q))) | (q & XXX~q & X~q & XXXXq))",
  "AG(EXp & EX~p) & A(~q & X(~q & X(~q & X(~q)))) & AF(r & q & X(q & X(q & X(q)))) & r & AG(r -> X(~r & X(~r & X(~r & X(r))))) & A(r -> ((q -> X((~r)U(r & ~q))) & (~q -> X((~r)U(r & q))))) & A(~Xr -> ((~q | XXXXq) & ((Xq & XXXXXq) | (X~q & XXXXX~q))) | (q & XXXX~q & X~q & XXXXXq))",
  "AG(EXp & EX~p) & A(~q & X(~q & X(~q & X(~q & X(~q))))) & AF(r & q & X(q & X(q & X(q & X(q))))) & r & AG(r -> X(~r & X(~r & X(~r & X(~r & X(r)))))) & A(r -> ((q -> X((~r)U(r & ~q))) & (~q -> X((~r)U(r & q))))) & A(~Xr -> ((~q | XXXXXq) & ((Xq & XXXXXXq) | (X~q & XXXXXX~q))) | (q & XXXXX~q & X~q & XXXXXXq))",
] as const;

describe("E3 completeness — counter stress family (CTL*)", () => {
  for (let n = 1; n <= COUNTER_FORMULAS.length; n++) {
    test(`counter formula n=${n} is satisfiable`, () => {
      expect(isSatCtlStar(COUNTER_FORMULAS[n - 1]!)).toBe(true);
    }, { timeout: 60000 });
  }
});

describe("E3 completeness — witness state sharing (ATL*)", () => {
  // A model is q, q, ~q, ...: every path satisfies (q U ~q) while {a,b}
  // force q at the next step. The realization witness for <<>>(q U ~q) needs
  // the same successor state under two different prestates.
  test("(<<>>(q U ~q) & (q & <<a,b>>X q)) is satisfiable", () => {
    const formula = parseFormula("(<<>>(q U ~q) & (q & <<a,b>>X q))");
    expect(runTableau(formula).satisfiable).toBe(true);
  });

  // The root carries the eventuality <<>>F e unresolved (~e now, and <<>>X~e
  // kills the resolve-now branch in all successors). <<>>X(a & b) sends the
  // same obligation wrapper <<>>(a & b) — which saturates to {a, b} — into
  // every successor, and <<1>>X a splits the successors into two DISTINCT
  // prestates ({...} and {..., a}) that both expand to the IDENTICAL single
  // state, since a is already produced by the wrapper. Every realization
  // witness therefore uses that one state in both AND-branches.
  // A model: s0(~e) -> s1(a, b, ~e) -> s2(e).
  test("(~e & (<<>>F e & (<<>>X(a & b) & (<<>>X ~e & <<1>>X a)))) is satisfiable", () => {
    const formula = parseFormula("(~e & (<<>>F e & (<<>>X(a & b) & (<<>>X ~e & <<1>>X a))))");
    expect(runTableau(formula).satisfiable).toBe(true);
  });
});
