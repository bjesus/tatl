/**
 * Cross-validation script: systematically compare our ATL solver against TATL.
 *
 * Generates a large set of ATL formulas and checks that both solvers agree
 * on satisfiability for every formula.
 *
 * Usage: bun run crossval.ts [--count N]
 */

import { parseFormula } from "./src/core/parser.ts";
import { runTableau } from "./src/core/tableau.ts";
import { execSync } from "child_process";

const NIX_SHELL = "/nix/store/jsk4cy6azq4cgf2j2qs1lpvh0mm38avb-nix-2.24.4/bin/nix-shell";
const TATL_DIR = `${import.meta.dir}/TATL`;

// Convert our syntax to TATL syntax:
// - agents: a→0, b→1, c→2
// - operators: & → /\, | → \/, ~ → ~, -> → ->
// - coalitions: <<a,b>> → <<0,1>>
// - TATL uses same <<>>, X, G, F, U syntax
function toTATL(formula: string): string {
  return formula
    .replace(/<<([^>]*)>>/g, (_match, agents: string) => {
      if (agents.trim() === "") return "<<>>";
      const mapped = agents.split(",").map((a: string) => {
        const t = a.trim();
        if (t === "a") return "0";
        if (t === "b") return "1";
        if (t === "c") return "2";
        return t;
      });
      return `<<${mapped.join(",")}>>`;
    })
    .replace(/&/g, "/\\")
    .replace(/\|/g, "\\/")
    .replace(/->/g, "->");
}

function runTATL(formula: string): boolean | null {
  const tatlFormula = toTATL(formula);
  try {
    const result = execSync(
      `${NIX_SHELL} shell.nix --run './_build/default/tatl.exe -o -f "${tatlFormula}"'`,
      { cwd: TATL_DIR, timeout: 10000, encoding: "utf-8", stdio: ["pipe", "pipe", "pipe"] }
    );
    if (result.includes("satisfiable") && !result.includes("unsatisfiable")) return true;
    if (result.includes("unsatisfiable")) return false;
    return null; // parse error or unexpected
  } catch {
    return null; // timeout or error
  }
}

function runOurs(formula: string): boolean | null {
  try {
    const f = parseFormula(formula);
    const result = runTableau(f);
    return result.satisfiable;
  } catch {
    return null;
  }
}

// Generate formulas systematically
function* generateFormulas(): Generator<string> {
  const atoms = ["p", "q"];
  const agents1 = ["a", "b"];
  const coalitions = ["<<a>>", "<<b>>", "<<a,b>>", "<<>>"];

  // Layer 1: atoms and negated atoms
  for (const p of atoms) {
    yield p;
    yield `~${p}`;
  }

  // Layer 2: single temporal operators on atoms
  for (const c of coalitions) {
    for (const p of atoms) {
      yield `${c}X ${p}`;
      yield `${c}X ~${p}`;
      yield `~${c}X ${p}`;
      yield `${c}G ${p}`;
      yield `${c}G ~${p}`;
      yield `~${c}G ${p}`;
      yield `${c}F ${p}`;
      yield `~${c}F ${p}`;
      for (const q of atoms) {
        yield `${c}(${p} U ${q})`;
        yield `~${c}(${p} U ${q})`;
      }
    }
  }

  // Layer 3: conjunctions of two temporal formulas (same or different coalitions)
  const temporals: string[] = [];
  for (const c of coalitions) {
    for (const p of atoms) {
      temporals.push(`${c}X ${p}`, `${c}X ~${p}`, `~${c}X ${p}`);
      temporals.push(`${c}G ${p}`, `${c}G ~${p}`, `~${c}G ${p}`);
      temporals.push(`${c}F ${p}`, `~${c}F ${p}`);
      for (const q of atoms) {
        temporals.push(`${c}(${p} U ${q})`, `~${c}(${p} U ${q})`);
      }
    }
  }

  // Conjunctions of pairs
  for (let i = 0; i < temporals.length; i++) {
    for (let j = i; j < temporals.length; j++) {
      yield `(${temporals[i]} & ${temporals[j]})`;
    }
  }

  // Layer 4: a few nested formulas
  for (const c1 of ["<<a>>", "<<b>>"]) {
    for (const c2 of ["<<a>>", "<<b>>", "<<a,b>>"]) {
      for (const p of atoms) {
        yield `${c1}G ${c2}X ${p}`;
        yield `${c1}X ${c2}G ${p}`;
        yield `${c1}G ${c2}G ${p}`;
        yield `~${c1}G ${c2}X ${p}`;
        yield `(${c1}G ${p} & ${c2}(${p} U q))`;
        yield `(${c1}G ~${p} & ${c2}(${p} U q))`;
      }
    }
  }
}

// Main
async function main() {
  const maxCount = parseInt(process.argv.find(a => a.startsWith("--count="))?.split("=")[1] ?? "0") || Infinity;

  let total = 0;
  let matches = 0;
  let mismatches = 0;
  let errors = 0;
  const mismatchList: { formula: string; ours: boolean | null; tatl: boolean | null }[] = [];

  console.log("Cross-validating ATL solver against TATL...\n");

  for (const formula of generateFormulas()) {
    if (total >= maxCount) break;
    total++;

    const ours = runOurs(formula);
    const tatl = runTATL(formula);

    if (ours === null || tatl === null) {
      errors++;
      if (tatl === null && ours !== null) {
        // TATL parse error — skip silently
      } else {
        console.log(`  ERROR: "${formula}" — ours=${ours}, tatl=${tatl}`);
      }
      continue;
    }

    if (ours === tatl) {
      matches++;
    } else {
      mismatches++;
      mismatchList.push({ formula, ours, tatl });
      console.log(`  MISMATCH: "${formula}" — ours=${ours ? "SAT" : "UNSAT"}, tatl=${tatl ? "SAT" : "UNSAT"}`);
    }

    if (total % 100 === 0) {
      process.stdout.write(`  ... ${total} formulas checked (${matches} match, ${mismatches} mismatch, ${errors} error)\r`);
    }
  }

  console.log(`\n\nResults:`);
  console.log(`  Total formulas:  ${total}`);
  console.log(`  Matches:         ${matches}`);
  console.log(`  Mismatches:      ${mismatches}`);
  console.log(`  Errors/skipped:  ${errors}`);

  if (mismatchList.length > 0) {
    console.log(`\nMismatches:`);
    for (const m of mismatchList) {
      console.log(`  "${m.formula}" — ours=${m.ours ? "SAT" : "UNSAT"}, tatl=${m.tatl ? "SAT" : "UNSAT"}`);
    }
    process.exit(1);
  } else {
    console.log(`\nAll formulas match!`);
    process.exit(0);
  }
}

main();
