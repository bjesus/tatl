/**
 * ATL* Tableau Decision Procedure — CLI Entry Point
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
    "--verbose", "-v", "--interactive", "-i",
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

  const result = runTableau(formula);

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

  console.log("ATL* Tableau Decision Procedure — Interactive Mode");
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
ATL* Tableau Decision Procedure

Usage:
  atl <formula>                Check satisfiability of a formula
  atl --interactive            Interactive mode
  atl --help                   Show this help

Options:
  --verbose, -v                  Show detailed output for all phases
  --dot [pretableau|initial|final]   Output DOT (Graphviz) graph
  --html                         Output standalone HTML visualization
  --interactive, -i              Interactive REPL mode

Examples:
  atl "<<a>>X p"
  atl "(<<a>>X p & <<b>>X ~p)"
  atl "<<a>>G p"
  atl "<<a,b>>(p U q)"
  atl "<<>>F p" --verbose
`);
  printSyntaxHelp();
}

function printSyntaxHelp(): void {
  console.log(`
Formula Syntax:
  Atoms:        p, q, r, ...
  Negation:     ~p, ~(p & q)
  Conjunction:  (p & q)
  Disjunction:  (p | q)           desugars to ~(~p & ~q)
  Implication:  (p -> q)          desugars to ~(p & ~q)
  Next:         <<a>>X p          coalition {a} enforces p at next step
  Always:       <<a,b>>G p        coalition {a,b} enforces p forever
  Eventually:   <<a>>F p          coalition {a} enforces eventually p
  Until:        <<a>>(p U q)      coalition {a} enforces p until q
  Empty coal.:  <<>>X p           empty coalition enforces next p
  ATL* path:    <<a>>(G p & F q)  same strategy: always p and eventually q
  ATL* nested:  <<a>>(G F p)      infinitely often p

Examples:
  <<a>>X p                        agent a enforces next p
  <<a>>(G p & F q)                ATL*: always p and eventually q
  <<a>>(G p & F ~p)               ATL*: unsatisfiable (contradictory path)
  (<<a>>G p & <<a>>F ~p)          different strategies (satisfiable)
  <<a,b>>(p U q)                  {a,b} enforce p until q
  <<>>F p                         eventually p (empty coalition)
`);
}
