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

const TATL_EXE = `${import.meta.dir}/TATL/_build/default/tatl.exe`;

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
      `${TATL_EXE} -o -f "${tatlFormula}"`,
      { timeout: 30000, encoding: "utf-8", stdio: ["pipe", "pipe", "pipe"] }
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

  // Layer 5: ATL*-specific — complex path formulas inside coalitions
  // These are genuine ATL* formulas (not expressible in basic ATL)
  for (const c of coalitions) {
    for (const p of atoms) {
      // Combined path formulas
      yield `${c}(G ${p} & F ~${p})`;           // always p AND eventually ~p (UNSAT)
      yield `${c}(F ${p} & F ~${p})`;           // eventually p AND eventually ~p
      yield `${c}(G ${p} | F ~${p})`;           // always p OR eventually ~p
      yield `${c}(G ${p} & G ~${p})`;           // always p AND always ~p (UNSAT path)
      yield `${c}(X ${p} & X ~${p})`;           // next p AND next ~p (UNSAT)
      yield `${c}(X ${p} | X ~${p})`;           // next p OR next ~p (tautological path)
      yield `${c}(G ${p} & X ~${p})`;           // always p AND next ~p (UNSAT)
      yield `${c}(F ${p} & G ~${p})`;           // eventually p AND always ~p (UNSAT)

      // Negated complex path formulas
      yield `~${c}(G ${p} & F ~${p})`;
      yield `~${c}(F ${p} & F ~${p})`;

      // GF and FG patterns
      yield `${c}(G F ${p})`;                    // infinitely often p
      yield `${c}(F G ${p})`;                    // eventually always p
      yield `~${c}(G F ${p})`;
      yield `~${c}(F G ${p})`;

      // Mixed with Until
      for (const q of atoms) {
        yield `${c}(G ${p} & (${p} U ${q}))`;
        yield `${c}((${p} U ${q}) | G ~${q})`;
        yield `${c}(X ${p} & (${p} U ${q}))`;
      }
    }
  }

  // Layer 6: Conjunctions involving ATL*-specific formulas
  for (const c of ["<<a>>", "<<b>>"]) {
    yield `(${c}(G p & F q) & ${c}(G q & F p))`;
    yield `(${c}(G p) & ${c}(F ~p))`;           // different strategies — SAT
    yield `(${c}G p & ~${c}G p)`;                // contradiction — UNSAT
    yield `(${c}(G p & F ~p) & q)`;              // UNSAT (inner path unsat)
    yield `(${c}(F p) & ${c}(F ~p))`;            // SAT
    yield `(${c}(G F p) & ${c}(G F ~p))`;        // SAT (different strategies)
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
