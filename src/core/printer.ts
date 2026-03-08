/**
 * Pretty-printer for ATL formulas.
 * Produces human-readable ASCII, Unicode, and LaTeX output.
 */

import { type Formula, type FormulaSet, type Coalition, type MoveVector } from "./types.ts";

/**
 * Format a coalition for ASCII display.
 */
function coalitionStr(c: Coalition): string {
  return `<<${c.join(",")}>>`;
}

/**
 * Print a formula to a human-readable ASCII string.
 * Uses the same syntax accepted by the parser.
 */
export function printFormula(f: Formula): string {
  switch (f.kind) {
    case "atom":
      return f.name;

    case "not":
      if (f.sub.kind === "and" || f.sub.kind === "not") {
        return `~(${printFormula(f.sub)})`;
      }
      return `~${printFormula(f.sub)}`;

    case "and":
      return `(${printFormula(f.left)} & ${printFormula(f.right)})`;

    case "next":
      return `${coalitionStr(f.coalition)}X ${printFormulaWrapped(f.sub)}`;

    case "always":
      return `${coalitionStr(f.coalition)}G ${printFormulaWrapped(f.sub)}`;

    case "until":
      return `${coalitionStr(f.coalition)}(${printFormula(f.left)} U ${printFormula(f.right)})`;
  }
}

/**
 * Print a formula, wrapping it in parens if it's compound.
 */
function printFormulaWrapped(f: Formula): string {
  if (f.kind === "and" || (f.kind === "not" && f.sub.kind === "and")) {
    return `(${printFormula(f)})`;
  }
  return printFormula(f);
}

/**
 * Format a coalition for Unicode display.
 */
function coalitionUnicode(c: Coalition): string {
  return `\u27E8\u27E8${c.join(",")}\u27E9\u27E9`;
}

/**
 * Print a formula using Unicode mathematical symbols for display.
 */
export function printFormulaUnicode(f: Formula): string {
  switch (f.kind) {
    case "atom":
      if (f.name === "_top") return "\u22A4";
      return f.name;

    case "not":
      if (f.sub.kind === "and" || f.sub.kind === "not") {
        return `\u00AC(${printFormulaUnicode(f.sub)})`;
      }
      return `\u00AC${printFormulaUnicode(f.sub)}`;

    case "and":
      return `(${printFormulaUnicode(f.left)} \u2227 ${printFormulaUnicode(f.right)})`;

    case "next":
      return `${coalitionUnicode(f.coalition)}\u25CB ${printFormulaUnicodeWrapped(f.sub)}`;

    case "always":
      return `${coalitionUnicode(f.coalition)}\u25A1 ${printFormulaUnicodeWrapped(f.sub)}`;

    case "until":
      return `${coalitionUnicode(f.coalition)}(${printFormulaUnicode(f.left)} \u0055 ${printFormulaUnicode(f.right)})`;
  }
}

function printFormulaUnicodeWrapped(f: Formula): string {
  if (f.kind === "and" || (f.kind === "not" && f.sub.kind === "and")) {
    return `(${printFormulaUnicode(f)})`;
  }
  return printFormulaUnicode(f);
}

/**
 * Print a formula set as a comma-separated list in braces.
 */
export function printFormulaSet(fs: FormulaSet): string {
  const items = fs.toArray().map(printFormula);
  return `{${items.join(", ")}}`;
}

/**
 * Print a formula set using compact notation.
 */
export function printFormulaSetCompact(fs: FormulaSet): string {
  const items = fs.toArray().map(printFormula);
  return `{${items.join(", ")}}`;
}

/**
 * Print a move vector as a string like "(0,1,2)".
 */
export function printMoveVector(mv: MoveVector, agents?: Coalition): string {
  if (agents && agents.length === mv.length) {
    const parts = agents.map((a, i) => `${a}:${mv[i]}`);
    return `(${parts.join(",")})`;
  }
  return `(${mv.join(",")})`;
}

// ============================================================
// LaTeX output (for KaTeX rendering in browser)
// ============================================================

/**
 * Map nesting level to LaTeX sizing commands for parentheses.
 */
const PAREN_SIZES = ["", "\\big", "\\Big", "\\bigg", "\\Bigg"];

function sizedOpen(level: number): string {
  if (level <= 0) return "(";
  const cmd = PAREN_SIZES[Math.min(level, PAREN_SIZES.length - 1)];
  return `${cmd}(`;
}

function sizedClose(level: number): string {
  if (level <= 0) return ")";
  const cmd = PAREN_SIZES[Math.min(level, PAREN_SIZES.length - 1)];
  return `${cmd})`;
}

/** Count the maximum parenthesis nesting depth of a formula. */
function maxParenNesting(f: Formula): number {
  switch (f.kind) {
    case "atom":
      return 0;
    case "not":
      if (f.sub.kind === "and" || f.sub.kind === "not") {
        return 1 + maxParenNesting(f.sub);
      }
      return maxParenNesting(f.sub);
    case "and":
      return 1 + Math.max(maxParenNesting(f.left), maxParenNesting(f.right));
    case "next":
    case "always": {
      const sub = f.sub;
      if (sub.kind === "and" || (sub.kind === "not" && sub.sub.kind === "and")) {
        return 1 + maxParenNesting(sub);
      }
      return maxParenNesting(sub);
    }
    case "until":
      return 1 + Math.max(maxParenNesting(f.left), maxParenNesting(f.right));
  }
}

/**
 * LaTeX coalition: \langle\langle a,b \rangle\rangle
 */
function coalitionLatex(c: Coalition): string {
  const agents = c.length > 0 ? c.join(",") : "\\emptyset";
  return `\\langle\\!\\langle ${agents} \\rangle\\!\\rangle`;
}

/**
 * Print a formula as a LaTeX string suitable for KaTeX rendering.
 */
export function printFormulaLatex(f: Formula): string {
  const total = maxParenNesting(f);
  return printLatex(f, total, 0);
}

function printLatex(f: Formula, total: number, depth: number): string {
  switch (f.kind) {
    case "atom":
      if (f.name === "_top") return "\\top";
      return f.name;

    case "not":
      if (f.sub.kind === "and" || f.sub.kind === "not") {
        const level = total - depth - 1;
        return `\\neg${sizedOpen(level)}${printLatex(f.sub, total, depth + 1)}${sizedClose(level)}`;
      }
      return `\\neg ${printLatex(f.sub, total, depth)}`;

    case "and": {
      const level = total - depth - 1;
      return `${sizedOpen(level)}${printLatex(f.left, total, depth + 1)} \\wedge ${printLatex(f.right, total, depth + 1)}${sizedClose(level)}`;
    }

    case "next":
      return `${coalitionLatex(f.coalition)}\\bigcirc ${printLatexWrapped(f.sub, total, depth)}`;

    case "always":
      return `${coalitionLatex(f.coalition)}\\square ${printLatexWrapped(f.sub, total, depth)}`;

    case "until": {
      const level = total - depth - 1;
      return `${coalitionLatex(f.coalition)}${sizedOpen(level)}${printLatex(f.left, total, depth + 1)} \\,\\mathsf{U}\\, ${printLatex(f.right, total, depth + 1)}${sizedClose(level)}`;
    }
  }
}

function printLatexWrapped(f: Formula, total: number, depth: number): string {
  if (f.kind === "and" || (f.kind === "not" && f.sub.kind === "and")) {
    const level = total - depth - 1;
    return `${sizedOpen(level)}${printLatex(f, total, depth + 1)}${sizedClose(level)}`;
  }
  return printLatex(f, total, depth);
}

/**
 * Print a formula set as LaTeX.
 */
export function printFormulaSetLatex(fs: FormulaSet): string {
  const items = fs.toArray().map(printFormulaLatex);
  return `\\{${items.join(",\\; ")}\\}`;
}

/**
 * Print a move vector as LaTeX.
 */
export function printMoveVectorLatex(mv: MoveVector, agents?: Coalition): string {
  if (agents && agents.length === mv.length) {
    const parts = agents.map((a, i) => `${a}\\!:\\!${mv[i]}`);
    return `(${parts.join(",\\,")})`;
  }
  return `(${mv.join(",")})`;
}
