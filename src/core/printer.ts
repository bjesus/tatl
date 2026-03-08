/**
 * Pretty-printer for CMAEL(CD) formulas.
 * Produces human-readable ASCII output.
 */

import { type Formula, type FormulaSet } from "./types.ts";

/**
 * Print a formula to a human-readable string.
 * Uses the same syntax accepted by the parser:
 *   ¬ → ~, ∧ → &, D_A → D{...}, C_A → C{...}
 */
export function printFormula(f: Formula): string {
  switch (f.kind) {
    case "atom":
      return f.name;

    case "not":
      // Check if it's ¬(φ ∧ ψ) — print as ~(φ & ψ)
      if (f.sub.kind === "and" || f.sub.kind === "not") {
        return `~(${printFormula(f.sub)})`;
      }
      return `~${printFormula(f.sub)}`;

    case "and":
      return `(${printFormula(f.left)} & ${printFormula(f.right)})`;

    case "D":
      if (f.coalition.length === 1) {
        // Individual knowledge: D{a} φ → Ka φ
        return `K${f.coalition[0]} ${printFormulaWrapped(f.sub)}`;
      }
      return `D{${f.coalition.join(",")}} ${printFormulaWrapped(f.sub)}`;

    case "C":
      return `C{${f.coalition.join(",")}} ${printFormulaWrapped(f.sub)}`;
  }
}

/**
 * Print a formula, wrapping it in parens if it's compound.
 */
function printFormulaWrapped(f: Formula): string {
  if (f.kind === "and" || (f.kind === "not" && (f.sub.kind === "and"))) {
    return `(${printFormula(f)})`;
  }
  return printFormula(f);
}

/**
 * Print a formula using Unicode mathematical symbols for display.
 */
export function printFormulaUnicode(f: Formula): string {
  switch (f.kind) {
    case "atom":
      return f.name;

    case "not":
      if (f.sub.kind === "and" || f.sub.kind === "not") {
        return `\u00AC(${printFormulaUnicode(f.sub)})`;
      }
      return `\u00AC${printFormulaUnicode(f.sub)}`;

    case "and":
      return `(${printFormulaUnicode(f.left)} \u2227 ${printFormulaUnicode(f.right)})`;

    case "D":
      if (f.coalition.length === 1) {
        return `K${f.coalition[0]} ${printFormulaUnicodeWrapped(f.sub)}`;
      }
      return `D{${f.coalition.join(",")}} ${printFormulaUnicodeWrapped(f.sub)}`;

    case "C":
      return `C{${f.coalition.join(",")}} ${printFormulaUnicodeWrapped(f.sub)}`;
  }
}

function printFormulaUnicodeWrapped(f: Formula): string {
  if (f.kind === "and" || (f.kind === "not" && (f.sub.kind === "and"))) {
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

// ============================================================
// LaTeX output (for KaTeX rendering in browser)
// ============================================================

/**
 * Map nesting level to LaTeX sizing commands for parentheses.
 * Level 0 = innermost (plain parens), increasing = bigger.
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
    case "D":
    case "C": {
      const sub = f.sub;
      if (sub.kind === "and" || (sub.kind === "not" && sub.sub.kind === "and")) {
        return 1 + maxParenNesting(sub);
      }
      return maxParenNesting(sub);
    }
  }
}

/**
 * Print a formula as a LaTeX string suitable for KaTeX rendering.
 * Uses explicit sizing commands (\big, \Big, etc.) so nested
 * parentheses are progressively larger.
 */
export function printFormulaLatex(f: Formula): string {
  const total = maxParenNesting(f);
  return printLatex(f, total, 0);
}

/**
 * Recursive LaTeX printer.
 * @param f     - formula to print
 * @param total - total paren nesting depth of the whole formula
 * @param depth - current paren depth (0 = outermost)
 *
 * Size level for a paren at depth d = total - d - 1
 * (so outermost parens are biggest, innermost are plain).
 */
function printLatex(f: Formula, total: number, depth: number): string {
  switch (f.kind) {
    case "atom":
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

    case "D":
      if (f.coalition.length === 1) {
        return `\\mathbf{K}_{${f.coalition[0]}} ${printLatexWrapped(f.sub, total, depth)}`;
      }
      return `\\mathbf{D}_{\\{${f.coalition.join(",")}\\}} ${printLatexWrapped(f.sub, total, depth)}`;

    case "C":
      return `\\mathbf{C}_{\\{${f.coalition.join(",")}\\}} ${printLatexWrapped(f.sub, total, depth)}`;
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
