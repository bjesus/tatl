/**
 * CMAEL(CD) Tableau Decision Procedure — CLI Entry Point
 *
 * Usage:
 *   bun run src/index.ts <formula>
 *   bun run src/index.ts --interactive
 *   bun run src/index.ts --help
 *
 * Options:
 *   --verbose              Show all phases in detail
 *   --dot [phase]          Output DOT graph (pretableau|initial|final)
 *   --html                 Output standalone HTML visualization
 *   --no-restricted-cuts   Disable C1/C2 cut restrictions
 *   --interactive          Interactive mode (read formulas from stdin)
 */

import { parseFormula } from "./core/parser.ts";
import { printFormula } from "./core/printer.ts";
import { runTableau } from "./core/tableau.ts";
import { textSummary, textVerbose, toDot } from "./viz/text.ts";
import { generateHTML } from "./viz/html.ts";

const args = process.argv.slice(2);

if (args.length === 0 || args.includes("--help") || args.includes("-h")) {
  printHelp();
  process.exit(0);
}

const verbose = args.includes("--verbose") || args.includes("-v");
const noRestrictedCuts = args.includes("--no-restricted-cuts");
const useRestrictedCuts = !noRestrictedCuts;
const interactive = args.includes("--interactive") || args.includes("-i");
const dotIndex = args.indexOf("--dot");
const dotPhase = dotIndex >= 0 ? (args[dotIndex + 1] as "pretableau" | "initial" | "final" || "final") : null;
const htmlOutput = args.includes("--html");

if (interactive) {
  runInteractive();
} else {
  // Get formula from remaining args (skip flags and their values)
  const formulaStr = extractFormulaArg(args);
  if (!formulaStr) {
    console.error("Error: No formula provided. Use --help for usage.");
    process.exit(1);
  }
  solveAndPrint(formulaStr);
}

function extractFormulaArg(args: string[]): string | null {
  const skipNext = new Set(["--dot"]);
  const skipFlags = new Set([
    "--verbose", "-v", "--no-restricted-cuts", "--interactive", "-i",
    "--html", "--help", "-h",
  ]);

  const parts: string[] = [];
  for (let i = 0; i < args.length; i++) {
    if (skipNext.has(args[i]!)) {
      i++; // skip the value
      continue;
    }
    if (skipFlags.has(args[i]!)) continue;
    if (args[i]!.startsWith("--")) continue;
    parts.push(args[i]!);
  }

  return parts.length > 0 ? parts.join(" ") : null;
}

function solveAndPrint(formulaStr: string): void {
  let formula;
  try {
    formula = parseFormula(formulaStr);
  } catch (e: any) {
    console.error(`Parse error: ${e.message}`);
    process.exit(1);
  }

  const result = runTableau(formula, useRestrictedCuts);

  if (htmlOutput) {
    console.log(generateHTML(result));
    return;
  }

  if (dotPhase) {
    console.log(toDot(result, dotPhase));
    return;
  }

  if (verbose) {
    console.log(textVerbose(result));
  } else {
    console.log(textSummary(result));
  }

  process.exit(result.satisfiable ? 0 : 1);
}

async function runInteractive(): Promise<void> {
  const readline = await import("readline");
  const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout,
  });

  console.log("CMAEL(CD) Tableau Decision Procedure — Interactive Mode");
  console.log("Enter a formula to check satisfiability. Type 'help' for syntax, 'quit' to exit.");
  console.log("");

  const prompt = () => {
    rl.question("> ", (line: string) => {
      const trimmed = line.trim();
      if (!trimmed) { prompt(); return; }
      if (trimmed === "quit" || trimmed === "exit") {
        rl.close();
        return;
      }
      if (trimmed === "help") {
        printSyntaxHelp();
        prompt();
        return;
      }

      solveAndPrint(trimmed);
      console.log("");
      prompt();
    });
  };

  prompt();
}

function printHelp(): void {
  console.log(`
CMAEL(CD) Tableau Decision Procedure

Usage:
  cmael <formula>                Check satisfiability of a formula
  cmael --interactive            Interactive mode
  cmael --help                   Show this help

Options:
  --verbose, -v                  Show detailed output for all phases
  --dot [pretableau|initial|final]   Output DOT (Graphviz) graph
  --html                         Output standalone HTML visualization
  --no-restricted-cuts           Disable C1/C2 cut restrictions
  --interactive, -i              Interactive REPL mode

Examples:
  cmael "(Ka p & ~Kb p)"
  cmael "(~D{a,c} C{a,b} p & C{a,b} (p & q))"
  cmael "(Ka p & ~p)" --verbose
  cmael "C{a,b} p" --dot final > graph.dot
`);
  printSyntaxHelp();
}

function printSyntaxHelp(): void {
  console.log(`
Formula Syntax:
  Atoms:        p, q, r, myProp, ...
  Negation:     ~p, ~(p & q)
  Conjunction:  (p & q)
  Disjunction:  (p | q)           desugars to ~(~p & ~q)
  Implication:  (p -> q)          desugars to ~(p & ~q)
  Ind. knowl.:  Ka p              agent a knows p (= D{a} p)
  Dist. knowl.: D{a,b} p          distributed knowledge among {a,b}
  Com. knowl.:  C{a,b} p          common knowledge among {a,b}

Examples:
  Ka p                            agent a knows p
  (Ka p & ~Kb p)                  a knows p, b doesn't
  (~D{a,c} C{a,b} p & C{a,b} (p & q))   Example 3 from paper (UNSAT)
  (C{a,b} Ka p -> ~C{b,c} Kb p)  Example 5 from paper
`);
}
