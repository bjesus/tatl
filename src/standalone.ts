/**
 * ATL* Tableau Solver — Standalone binary entry point.
 *
 * This is the entry point for `bun build --compile`. It embeds the
 * pre-built web UI (dist/index.html) and supports two modes:
 *
 *   Default (no args):    Launch web server and open browser
 *   Formula argument:     Solve formula on command line
 *
 * Usage:
 *   ./atl                           Launch web UI (default)
 *   ./atl "<<a>>G p"               Solve a formula
 *   ./atl --interactive             Interactive REPL
 *   ./atl --web                     Explicitly launch web UI
 *   ./atl --web --port 8080         Custom port
 *   ./atl --no-open                 Launch web UI without opening browser
 *   ./atl --help                    Show help
 */

// Embed the pre-built web UI into the binary
import htmlPath from "../dist/index.html" with { type: "file" };

import { parseFormula } from "./core/parser.ts";
import { runTableau } from "./core/tableau.ts";
import { textSummary, textVerbose, toDot } from "./viz/text.ts";
import { generateHTML } from "./viz/html.ts";
import { spawn } from "child_process";

// ============================================================
// Argument parsing
// ============================================================

const args = process.argv.slice(2);

const knownFlags = new Set([
  "--verbose", "-v", "--interactive", "-i",
  "--html", "--help", "-h", "--web", "--no-open",
]);
const flagsWithValue = new Set(["--dot", "--port"]);

function hasFormulaArg(): boolean {
  for (let i = 0; i < args.length; i++) {
    const a = args[i]!;
    if (flagsWithValue.has(a)) { i++; continue; }
    if (knownFlags.has(a)) continue;
    if (a.startsWith("--")) continue;
    return true;
  }
  return false;
}

function extractFormulaArg(): string | null {
  const parts: string[] = [];
  for (let i = 0; i < args.length; i++) {
    const a = args[i]!;
    if (flagsWithValue.has(a)) { i++; continue; }
    if (knownFlags.has(a)) continue;
    if (a.startsWith("--")) continue;
    parts.push(a);
  }
  return parts.length > 0 ? parts.join(" ") : null;
}

function getPort(): number {
  const idx = args.indexOf("--port");
  if (idx >= 0 && idx + 1 < args.length) {
    const val = parseInt(args[idx + 1]!);
    if (!isNaN(val) && val > 0) return val;
  }
  return 3000;
}

// ============================================================
// Mode selection
// ============================================================

if (args.includes("--help") || args.includes("-h")) {
  printHelp();
  process.exit(0);
}

if (args.includes("--interactive") || args.includes("-i")) {
  runInteractive();
} else if (hasFormulaArg() && !args.includes("--web")) {
  runCLI();
} else {
  // Default: launch web server
  runWeb();
}

// ============================================================
// Web server mode
// ============================================================

function runWeb(): void {
  const port = getPort();
  const noOpen = args.includes("--no-open");

  Bun.serve({
    port,
    hostname: "0.0.0.0",
    fetch() {
      return new Response(Bun.file(htmlPath as unknown as string), {
        headers: { "Content-Type": "text/html" },
      });
    },
  });

  const url = `http://localhost:${port}`;
  console.log(`ATL* Tableau Solver`);
  console.log(`Running at ${url}`);
  console.log(`Press Ctrl+C to stop`);

  if (!noOpen) {
    openBrowser(url);
  }
}

function openBrowser(url: string): void {
  try {
    const platform = process.platform;
    if (platform === "darwin") {
      spawn("open", [url], { stdio: "ignore", detached: true }).unref();
    } else if (platform === "win32") {
      spawn("cmd", ["/c", "start", url], { stdio: "ignore", detached: true }).unref();
    } else {
      // Linux / other
      spawn("xdg-open", [url], { stdio: "ignore", detached: true }).unref();
    }
  } catch {
    // Silently ignore — URL is printed to console
  }
}

// ============================================================
// CLI mode
// ============================================================

function runCLI(): void {
  const formulaStr = extractFormulaArg();
  if (!formulaStr) {
    console.error("Error: No formula provided. Use --help for usage.");
    process.exit(1);
  }

  const verbose = args.includes("--verbose") || args.includes("-v");
  const dotIndex = args.indexOf("--dot");
  const dotPhase = dotIndex >= 0 ? (args[dotIndex + 1] as "pretableau" | "initial" | "final" || "final") : null;
  const htmlOutput = args.includes("--html");

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

// ============================================================
// Interactive mode
// ============================================================

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

      // Inline solve for interactive mode
      try {
        const f = parseFormula(trimmed);
        const r = runTableau(f);
        console.log(textSummary(r));
      } catch (e: any) {
        console.error(`Error: ${e.message}`);
      }
      console.log("");
      prompt();
    });
  };

  prompt();
}

// ============================================================
// Help
// ============================================================

function printHelp(): void {
  console.log(`
ATL* Tableau Decision Procedure

Usage:
  atl                              Launch web interface (default)
  atl <formula>                    Check satisfiability of a formula
  atl --interactive                Interactive REPL mode
  atl --help                       Show this help

Web server options:
  --web                            Explicitly launch web interface
  --port <number>                  Port for web server (default: 3000)
  --no-open                        Don't open browser automatically

CLI options:
  --verbose, -v                    Show detailed output for all phases
  --dot [pretableau|initial|final] Output DOT (Graphviz) graph
  --html                           Output standalone HTML visualization
  --interactive, -i                Interactive REPL mode

Examples:
  atl                              Open web UI in browser
  atl "<<a>>X p"                   Check satisfiability
  atl "<<a>>(G p & F q)" -v        Verbose output (ATL* formula)
  atl --web --port 8080            Web UI on custom port
`);
  printSyntaxHelp();
}

function printSyntaxHelp(): void {
  console.log(`
Formula Syntax:
  Atoms:        p, q, r, ...
  Negation:     ~p, ~(p & q)
  Conjunction:  (p & q)
  Disjunction:  (p | q)
  Implication:  (p -> q)
  Next:         <<a>>X p          coalition {a} enforces p at next step
  Always:       <<a,b>>G p        coalition {a,b} enforces p forever
  Eventually:   <<a>>F p          coalition {a} enforces eventually p
  Until:        <<a>>(p U q)      coalition {a} enforces p until q
  Empty coal.:  <<>>X p           empty coalition enforces next p
  ATL* path:    <<a>>(G p & F q)  same strategy: always p and eventually q
  ATL* nested:  <<a>>(G F p)      infinitely often p
`);
}
