/**
 * Pretty-printing for ATL* formulas: ASCII, Unicode, and LaTeX.
 *
 * Handles both state formulas and path formulas.
 *
 * Every formula the solver works with is an ATL* formula, but LTL, CTL and
 * CTL* inputs are only *encoded* as ATL* (see parser.ts). Printing them back
 * in raw ATL* brackets would show the user a translation they never wrote, so
 * each printer takes a {@link Notation} saying which surface syntax to use for
 * coalition operators.
 */

import {
  type StateFormula,
  type PathFormula,
  type Coalition,
  StateFormulaSet,
  PathFormulaSet,
} from "./types.ts";
import type { System } from "./parser.ts";

// ============================================================
// Notation
// ============================================================

/**
 * Surface syntax for coalition operators.
 *
 * - `atl` — `<<A>>` / `[[A]]`, the notation the formula is actually in.
 * - `ctl` — path quantifiers, written `A` / `E` in plain text and set as
 *   ∀ / ∃ once typeset. Sound because CTL and CTL* are encoded over the single
 *   agent `a`, leaving only two coalitions: `<<a>>` is "some path" (E) and
 *   `<<>>` is "every path" (A). The co-coalition operators are their duals,
 *   `[[A]]p == ~<<A>>~p`, so `[[a]]` is A and `[[]]` is E.
 * - `ltl` — no quantifier at all. An LTL formula is a bare path formula; the
 *   encoding wraps it in `<<a>>` only to ask "is there a path satisfying it",
 *   so the wrapper is dropped again on the way out.
 */
export type Notation = "atl" | "ctl" | "ltl";

/** The notation a given input system should be printed back in. */
export function notationFor(system: System): Notation {
  switch (system) {
    case "ltl": return "ltl";
    case "ctl": case "ctlstar": return "ctl";
    case "atl": return "atl";
  }
}

/** How a coalition operator is written: as brackets, as a letter, or not at all. */
type Quantifier =
  | { form: "brackets" }
  | { form: "letter"; letter: "A" | "E" }
  | { form: "drop" };

const BRACKETS: Quantifier = { form: "brackets" };

/**
 * Decide how to render the operator of a `coal`/`cocoal` node.
 *
 * The `ctl`/`ltl` readings are only valid for the coalitions the one-agent
 * encoding can produce (empty, or the single agent). Anything else falls back
 * to ATL brackets rather than printing something untrue.
 */
function quantifier(
  kind: "coal" | "cocoal",
  coalition: Coalition,
  n: Notation,
): Quantifier {
  if (n === "atl") return BRACKETS;
  const full = coalition.length === 1;
  const empty = coalition.length === 0;
  if (n === "ltl") return kind === "coal" && full ? { form: "drop" } : BRACKETS;
  if (kind === "coal") {
    if (full) return { form: "letter", letter: "E" };
    if (empty) return { form: "letter", letter: "A" };
  } else {
    if (full) return { form: "letter", letter: "A" };
    if (empty) return { form: "letter", letter: "E" };
  }
  return BRACKETS;
}

/**
 * Whether a space is needed between a path quantifier and its argument.
 *
 * `AG p` and `E(p U q)` read correctly glued together, but `Ep` and `E~p` do
 * not: the letter would look like part of the operand.
 */
function needsQuantifierGap(f: PathFormula): boolean {
  return f.kind === "state" || f.kind === "negp";
}

/**
 * A and E are the letters typed and printed as plain text; ∀ and ∃ are the
 * same two quantifiers once there are real symbols available, which is how the
 * syntax reference presents them.
 */
const QUANTIFIER_UNICODE = { A: "∀", E: "∃" } as const;
const QUANTIFIER_LATEX = { A: "\\forall", E: "\\exists" } as const;

// ============================================================
// ASCII printing (for CLI output and formula keys)
// ============================================================

export function printStateAscii(f: StateFormula, n: Notation = "atl"): string {
  switch (f.kind) {
    case "top": return "_top";
    case "bot": return "_bot";
    case "atom": return f.name;
    case "neg":
      if (f.sub.kind === "and" || f.sub.kind === "or" || f.sub.kind === "neg")
        return `~(${printStateAscii(f.sub, n)})`;
      return `~${printStateAscii(f.sub, n)}`;
    case "and":
      return `(${printStateAscii(f.left, n)} & ${printStateAscii(f.right, n)})`;
    case "or":
      return `(${printStateAscii(f.left, n)} | ${printStateAscii(f.right, n)})`;
    case "coal": case "cocoal": {
      const q = quantifier(f.kind, f.coalition, n);
      const path = printPathAscii(f.path, n);
      switch (q.form) {
        case "drop": return path;
        case "letter": return `${q.letter}${needsQuantifierGap(f.path) ? " " : ""}${path}`;
        case "brackets": return `${bracketsAscii(f.kind, f.coalition)}${path}`;
      }
    }
  }
}

function bracketsAscii(kind: "coal" | "cocoal", c: Coalition): string {
  return kind === "coal" ? `<<${c.join(",")}>>` : `[[${c.join(",")}]]`;
}

export function printPathAscii(f: PathFormula, n: Notation = "atl"): string {
  switch (f.kind) {
    case "state": return printStateAscii(f.sub, n);
    case "negp":
      return `~${printPathAscii(f.sub, n)}`;
    case "andp":
      return `(${printPathAscii(f.left, n)} & ${printPathAscii(f.right, n)})`;
    case "orp":
      return `(${printPathAscii(f.left, n)} | ${printPathAscii(f.right, n)})`;
    case "next":
      return `X ${printPathAsciiAtom(f.sub, n)}`;
    case "always":
      return `G ${printPathAsciiAtom(f.sub, n)}`;
    case "until":
      return `(${printPathAscii(f.left, n)} U ${printPathAscii(f.right, n)})`;
  }
}

/**
 * Operand of a unary operator.
 *
 * Binary path formulas bracket themselves, so nothing needs adding here; the
 * function exists to keep the unary cases readable.
 */
function printPathAsciiAtom(f: PathFormula, n: Notation): string {
  return printPathAscii(f, n);
}

// ============================================================
// Unicode printing (for display)
// ============================================================

export function printStateUnicode(f: StateFormula, n: Notation = "atl"): string {
  switch (f.kind) {
    case "top": return "⊤";
    case "bot": return "⊥";
    case "atom": return f.name;
    case "neg":
      if (f.sub.kind === "and" || f.sub.kind === "or" || f.sub.kind === "neg")
        return `¬(${printStateUnicode(f.sub, n)})`;
      return `¬${printStateUnicode(f.sub, n)}`;
    case "and":
      return `(${printStateUnicode(f.left, n)} ∧ ${printStateUnicode(f.right, n)})`;
    case "or":
      return `(${printStateUnicode(f.left, n)} ∨ ${printStateUnicode(f.right, n)})`;
    case "coal": case "cocoal": {
      const q = quantifier(f.kind, f.coalition, n);
      const path = printPathUnicode(f.path, n);
      switch (q.form) {
        case "drop": return path;
        case "letter": return `${QUANTIFIER_UNICODE[q.letter]}${needsQuantifierGap(f.path) ? " " : ""}${path}`;
        case "brackets": return `${bracketsUnicode(f.kind, f.coalition)}${path}`;
      }
    }
  }
}

function bracketsUnicode(kind: "coal" | "cocoal", c: Coalition): string {
  return kind === "coal" ? `⟨⟨${c.join(",")}⟩⟩` : `⟦${c.join(",")}⟧`;
}

export function printPathUnicode(f: PathFormula, n: Notation = "atl"): string {
  switch (f.kind) {
    case "state": return printStateUnicode(f.sub, n);
    case "negp":
      return `¬${printPathUnicode(f.sub, n)}`;
    case "andp":
      return `(${printPathUnicode(f.left, n)} ∧ ${printPathUnicode(f.right, n)})`;
    case "orp":
      return `(${printPathUnicode(f.left, n)} ∨ ${printPathUnicode(f.right, n)})`;
    case "next":
      return `○${printPathUnicodeAtom(f.sub, n)}`;
    case "always":
      return `□${printPathUnicodeAtom(f.sub, n)}`;
    case "until":
      return `(${printPathUnicode(f.left, n)} U ${printPathUnicode(f.right, n)})`;
  }
}

function printPathUnicodeAtom(f: PathFormula, n: Notation): string {
  return printPathUnicode(f, n);
}

// ============================================================
// LaTeX printing (for KaTeX rendering)
// ============================================================

function bracketsLatex(kind: "coal" | "cocoal", c: Coalition): string {
  const inner = c.length > 0 ? c.join(",") : "\\emptyset";
  return kind === "coal"
    ? `\\langle\\!\\langle ${inner} \\rangle\\!\\rangle`
    : `\\llbracket ${inner} \\rrbracket`;
}

function quantifierLatex(letter: "A" | "E", gap: boolean): string {
  return `${QUANTIFIER_LATEX[letter]}${gap ? "\\," : ""}`;
}

// Nesting depth for adaptive bracket sizing
function stateDepth(f: StateFormula): number {
  switch (f.kind) {
    case "top": case "bot": case "atom": return 0;
    case "neg":
      if (f.sub.kind === "and" || f.sub.kind === "or" || f.sub.kind === "neg")
        return 1 + stateDepth(f.sub);
      return stateDepth(f.sub);
    case "and": return 1 + Math.max(stateDepth(f.left), stateDepth(f.right));
    case "or": return 1 + Math.max(stateDepth(f.left), stateDepth(f.right));
    case "coal": case "cocoal": return pathDepth(f.path);
  }
}

function pathDepth(f: PathFormula): number {
  switch (f.kind) {
    case "state": return stateDepth(f.sub);
    case "negp": return pathDepth(f.sub);
    case "andp": return 1 + Math.max(pathDepth(f.left), pathDepth(f.right));
    case "orp": return 1 + Math.max(pathDepth(f.left), pathDepth(f.right));
    case "next": case "always": return pathDepth(f.sub);
    case "until": return 1 + Math.max(pathDepth(f.left), pathDepth(f.right));
  }
}

const SIZES = ["", "\\big", "\\Big", "\\bigg", "\\Bigg"];

function lp(depth: number): string {
  if (depth <= 0) return "(";
  return `${SIZES[Math.min(depth, SIZES.length - 1)]}(`;
}

function rp(depth: number): string {
  if (depth <= 0) return ")";
  return `${SIZES[Math.min(depth, SIZES.length - 1)]})`;
}

export function printStateLatex(f: StateFormula, n: Notation = "atl"): string {
  const d = stateDepth(f);
  return stateLatexInner(f, d, 0, n);
}

function stateLatexInner(f: StateFormula, maxD: number, curD: number, n: Notation): string {
  switch (f.kind) {
    case "top": return "\\top";
    case "bot": return "\\bot";
    case "atom": return f.name;
    case "neg": {
      if (f.sub.kind === "and" || f.sub.kind === "or" || f.sub.kind === "neg") {
        const dd = maxD - curD - 1;
        return `\\neg${lp(dd)}${stateLatexInner(f.sub, maxD, curD + 1, n)}${rp(dd)}`;
      }
      return `\\neg ${stateLatexInner(f.sub, maxD, curD, n)}`;
    }
    case "and": {
      const dd = maxD - curD - 1;
      return `${lp(dd)}${stateLatexInner(f.left, maxD, curD + 1, n)} \\wedge ${stateLatexInner(f.right, maxD, curD + 1, n)}${rp(dd)}`;
    }
    case "or": {
      const dd = maxD - curD - 1;
      return `${lp(dd)}${stateLatexInner(f.left, maxD, curD + 1, n)} \\vee ${stateLatexInner(f.right, maxD, curD + 1, n)}${rp(dd)}`;
    }
    case "coal": case "cocoal": {
      const q = quantifier(f.kind, f.coalition, n);
      const path = pathLatexAtom(f.path, maxD, curD, n);
      switch (q.form) {
        case "drop": return path;
        case "letter": return `${quantifierLatex(q.letter, needsQuantifierGap(f.path))}${path}`;
        case "brackets": return `${bracketsLatex(f.kind, f.coalition)}${path}`;
      }
    }
  }
}

function pathLatexInner(f: PathFormula, maxD: number, curD: number, n: Notation): string {
  switch (f.kind) {
    case "state": return stateLatexInner(f.sub, maxD, curD, n);
    case "negp":
      return `\\neg ${pathLatexInner(f.sub, maxD, curD, n)}`;
    case "andp": {
      const dd = maxD - curD - 1;
      return `${lp(dd)}${pathLatexInner(f.left, maxD, curD + 1, n)} \\wedge ${pathLatexInner(f.right, maxD, curD + 1, n)}${rp(dd)}`;
    }
    case "orp": {
      const dd = maxD - curD - 1;
      return `${lp(dd)}${pathLatexInner(f.left, maxD, curD + 1, n)} \\vee ${pathLatexInner(f.right, maxD, curD + 1, n)}${rp(dd)}`;
    }
    case "next":
      return `\\bigcirc ${pathLatexAtom(f.sub, maxD, curD, n)}`;
    case "always":
      return `\\square ${pathLatexAtom(f.sub, maxD, curD, n)}`;
    case "until": {
      const dd = maxD - curD - 1;
      return `${lp(dd)}${pathLatexInner(f.left, maxD, curD + 1, n)} \\,\\mathsf{U}\\, ${pathLatexInner(f.right, maxD, curD + 1, n)}${rp(dd)}`;
    }
  }
}

function pathLatexAtom(f: PathFormula, maxD: number, curD: number, n: Notation): string {
  return pathLatexInner(f, maxD, curD, n);
}

// ============================================================
// Set printing
// ============================================================

export function printStateSetAscii(fs: StateFormulaSet, n: Notation = "atl"): string {
  return `{${fs.toArray().map((f) => printStateAscii(f, n)).join(", ")}}`;
}

export function printStateSetLatex(fs: StateFormulaSet, n: Notation = "atl"): string {
  return `\\{${fs.toArray().map((f) => printStateLatex(f, n)).join(",\\; ")}\\}`;
}

// ============================================================
// Move vector printing
// ============================================================

export function printMoveVector(mv: readonly number[], agents?: Coalition): string {
  if (agents && agents.length === mv.length) {
    return `(${agents.map((a, i) => `${a}:${mv[i]}`).join(",")})`;
  }
  return `(${mv.join(",")})`;
}

export function printMoveVectorLatex(mv: readonly number[], agents?: Coalition): string {
  if (agents && agents.length === mv.length) {
    return `(${agents.map((a, i) => `${a}\\!:\\!${mv[i]}`).join(",\\,")})`;
  }
  return `(${mv.join(",")})`;
}

// ============================================================
// Compatibility aliases (used by UI files)
// ============================================================

/** Print a state formula in ASCII (alias for printStateAscii) */
export const printFormula = printStateAscii;

/** Print a state formula in Unicode (alias for printStateUnicode) */
export const printFormulaUnicode = printStateUnicode;

/** Print a state formula in LaTeX (alias for printStateLatex) */
export const printFormulaLatex = printStateLatex;

/** Print a state formula set in ASCII (alias for printStateSetAscii) */
export const printFormulaSet = printStateSetAscii;

/** Print a state formula set in LaTeX (alias for printStateSetLatex) */
export const printFormulaSetLatex = printStateSetLatex;
