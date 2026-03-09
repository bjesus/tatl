/**
 * Pretty-printing for ATL* formulas: ASCII, Unicode, and LaTeX.
 *
 * Handles both state formulas and path formulas.
 */

import {
  type StateFormula,
  type PathFormula,
  type Coalition,
  StateFormulaSet,
  PathFormulaSet,
} from "./types.ts";

// ============================================================
// ASCII printing (for CLI output and formula keys)
// ============================================================

export function printStateAscii(f: StateFormula): string {
  switch (f.kind) {
    case "top": return "_top";
    case "bot": return "_bot";
    case "atom": return f.name;
    case "neg":
      if (f.sub.kind === "and" || f.sub.kind === "or" || f.sub.kind === "neg")
        return `~(${printStateAscii(f.sub)})`;
      return `~${printStateAscii(f.sub)}`;
    case "and":
      return `(${printStateAscii(f.left)} & ${printStateAscii(f.right)})`;
    case "or":
      return `(${printStateAscii(f.left)} | ${printStateAscii(f.right)})`;
    case "coal":
      return `${coalAscii(f.coalition)}${printPathAscii(f.path)}`;
    case "cocoal":
      return `[[${f.coalition.join(",")}]]${printPathAscii(f.path)}`;
  }
}

function coalAscii(c: Coalition): string {
  return `<<${c.join(",")}>>`;
}

export function printPathAscii(f: PathFormula): string {
  switch (f.kind) {
    case "state": return printStateAscii(f.sub);
    case "negp":
      if (needsPathParens(f.sub)) return `~(${printPathAscii(f.sub)})`;
      return `~${printPathAscii(f.sub)}`;
    case "andp":
      return `(${printPathAscii(f.left)} & ${printPathAscii(f.right)})`;
    case "orp":
      return `(${printPathAscii(f.left)} | ${printPathAscii(f.right)})`;
    case "next":
      return `X ${printPathAsciiAtom(f.sub)}`;
    case "always":
      return `G ${printPathAsciiAtom(f.sub)}`;
    case "until":
      return `(${printPathAscii(f.left)} U ${printPathAscii(f.right)})`;
  }
}

function printPathAsciiAtom(f: PathFormula): string {
  if (needsPathParens(f)) return `(${printPathAscii(f)})`;
  return printPathAscii(f);
}

function needsPathParens(f: PathFormula): boolean {
  return f.kind === "andp" || f.kind === "orp" || f.kind === "until" ||
    (f.kind === "negp" && needsPathParens(f.sub));
}

// ============================================================
// Unicode printing (for display)
// ============================================================

export function printStateUnicode(f: StateFormula): string {
  switch (f.kind) {
    case "top": return "⊤";
    case "bot": return "⊥";
    case "atom": return f.name;
    case "neg":
      if (f.sub.kind === "and" || f.sub.kind === "or" || f.sub.kind === "neg")
        return `¬(${printStateUnicode(f.sub)})`;
      return `¬${printStateUnicode(f.sub)}`;
    case "and":
      return `(${printStateUnicode(f.left)} ∧ ${printStateUnicode(f.right)})`;
    case "or":
      return `(${printStateUnicode(f.left)} ∨ ${printStateUnicode(f.right)})`;
    case "coal":
      return `⟨⟨${f.coalition.join(",")}⟩⟩${printPathUnicode(f.path)}`;
    case "cocoal":
      return `⟦${f.coalition.join(",")}⟧${printPathUnicode(f.path)}`;
  }
}

export function printPathUnicode(f: PathFormula): string {
  switch (f.kind) {
    case "state": return printStateUnicode(f.sub);
    case "negp":
      if (needsPathParens(f.sub)) return `¬(${printPathUnicode(f.sub)})`;
      return `¬${printPathUnicode(f.sub)}`;
    case "andp":
      return `(${printPathUnicode(f.left)} ∧ ${printPathUnicode(f.right)})`;
    case "orp":
      return `(${printPathUnicode(f.left)} ∨ ${printPathUnicode(f.right)})`;
    case "next":
      return `○${printPathUnicodeAtom(f.sub)}`;
    case "always":
      return `□${printPathUnicodeAtom(f.sub)}`;
    case "until":
      return `(${printPathUnicode(f.left)} U ${printPathUnicode(f.right)})`;
  }
}

function printPathUnicodeAtom(f: PathFormula): string {
  if (needsPathParens(f)) return `(${printPathUnicode(f)})`;
  return printPathUnicode(f);
}

// ============================================================
// LaTeX printing (for KaTeX rendering)
// ============================================================

function coalLatex(c: Coalition): string {
  return `\\langle\\!\\langle ${c.length > 0 ? c.join(",") : "\\emptyset"} \\rangle\\!\\rangle`;
}

function cocoalLatex(c: Coalition): string {
  return `\\llbracket ${c.length > 0 ? c.join(",") : "\\emptyset"} \\rrbracket`;
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
    case "negp": return needsPathParens(f.sub) ? 1 + pathDepth(f.sub) : pathDepth(f.sub);
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

export function printStateLatex(f: StateFormula): string {
  const d = stateDepth(f);
  return stateLatexInner(f, d, 0);
}

function stateLatexInner(f: StateFormula, maxD: number, curD: number): string {
  switch (f.kind) {
    case "top": return "\\top";
    case "bot": return "\\bot";
    case "atom": return f.name;
    case "neg": {
      if (f.sub.kind === "and" || f.sub.kind === "or" || f.sub.kind === "neg") {
        const dd = maxD - curD - 1;
        return `\\neg${lp(dd)}${stateLatexInner(f.sub, maxD, curD + 1)}${rp(dd)}`;
      }
      return `\\neg ${stateLatexInner(f.sub, maxD, curD)}`;
    }
    case "and": {
      const dd = maxD - curD - 1;
      return `${lp(dd)}${stateLatexInner(f.left, maxD, curD + 1)} \\wedge ${stateLatexInner(f.right, maxD, curD + 1)}${rp(dd)}`;
    }
    case "or": {
      const dd = maxD - curD - 1;
      return `${lp(dd)}${stateLatexInner(f.left, maxD, curD + 1)} \\vee ${stateLatexInner(f.right, maxD, curD + 1)}${rp(dd)}`;
    }
    case "coal":
      return `${coalLatex(f.coalition)}${pathLatexAtom(f.path, maxD, curD)}`;
    case "cocoal":
      return `${cocoalLatex(f.coalition)}${pathLatexAtom(f.path, maxD, curD)}`;
  }
}

function pathLatexInner(f: PathFormula, maxD: number, curD: number): string {
  switch (f.kind) {
    case "state": return stateLatexInner(f.sub, maxD, curD);
    case "negp": {
      if (needsPathParens(f.sub)) {
        const dd = maxD - curD - 1;
        return `\\neg${lp(dd)}${pathLatexInner(f.sub, maxD, curD + 1)}${rp(dd)}`;
      }
      return `\\neg ${pathLatexInner(f.sub, maxD, curD)}`;
    }
    case "andp": {
      const dd = maxD - curD - 1;
      return `${lp(dd)}${pathLatexInner(f.left, maxD, curD + 1)} \\wedge ${pathLatexInner(f.right, maxD, curD + 1)}${rp(dd)}`;
    }
    case "orp": {
      const dd = maxD - curD - 1;
      return `${lp(dd)}${pathLatexInner(f.left, maxD, curD + 1)} \\vee ${pathLatexInner(f.right, maxD, curD + 1)}${rp(dd)}`;
    }
    case "next":
      return `\\bigcirc ${pathLatexAtom(f.sub, maxD, curD)}`;
    case "always":
      return `\\square ${pathLatexAtom(f.sub, maxD, curD)}`;
    case "until": {
      const dd = maxD - curD - 1;
      return `${lp(dd)}${pathLatexInner(f.left, maxD, curD + 1)} \\,\\mathsf{U}\\, ${pathLatexInner(f.right, maxD, curD + 1)}${rp(dd)}`;
    }
  }
}

function pathLatexAtom(f: PathFormula, maxD: number, curD: number): string {
  if (needsPathParens(f)) {
    const dd = maxD - curD - 1;
    return `${lp(dd)}${pathLatexInner(f, maxD, curD + 1)}${rp(dd)}`;
  }
  return pathLatexInner(f, maxD, curD);
}

// ============================================================
// Set printing
// ============================================================

export function printStateSetAscii(fs: StateFormulaSet): string {
  return `{${fs.toArray().map(printStateAscii).join(", ")}}`;
}

export function printStateSetLatex(fs: StateFormulaSet): string {
  return `\\{${fs.toArray().map(printStateLatex).join(",\\; ")}\\}`;
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
