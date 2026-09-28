/**
 * Differential testing: the optimised procedure against the plain one.
 *
 * Usage:
 *   bun run difftest.ts [--count N] [--seed N] [--max-depth N] [--systems ltl,ctl,ctlstar,atl]
 *
 * Every optimisation flag is checked on its own and all together, and every
 * verdict is checked to be invariant under renaming. Exit code 1 on any
 * mismatch.
 */

import { checkFormula, corpus, type Mismatch } from "./src/core/difftest.ts";
import type { System } from "./src/core/parser.ts";

function arg(name: string, def: string): string {
  const eq = process.argv.find((a) => a.startsWith(`--${name}=`));
  if (eq) return eq.slice(name.length + 3);
  const i = process.argv.indexOf(`--${name}`);
  return i >= 0 && i + 1 < process.argv.length ? process.argv[i + 1]! : def;
}

const count = parseInt(arg("count", "500"));
const seed = parseInt(arg("seed", String(Math.floor(Math.random() * 1_000_000))));
const maxDepth = parseInt(arg("max-depth", "4"));
const systems = arg("systems", "ltl,ctl,ctlstar,atl").split(",") as System[];
const verbose = process.argv.includes("--verbose");

console.log(`difftest: ${count} formulas, seed ${seed}, depth ${maxDepth}, systems ${systems.join(",")}`);

const mismatches: Mismatch[] = [];
let n = 0;
const started = Date.now();
for (const { formula, system, extraAgents } of corpus({ seed, count, maxDepth, systems })) {
  n++;
  if (verbose) console.log(`[${n}] ${system}: ${formula}`);
  const found = checkFormula(formula, system, extraAgents);
  for (const m of found) {
    mismatches.push(m);
    console.log(`MISMATCH [${m.system}] ${m.check}: ${m.formula}  expected ${m.expected}, got ${m.got}`);
  }
  if (n % 100 === 0) console.log(`  ${n}/${count} (${((Date.now() - started) / 1000).toFixed(1)}s)`);
}

console.log(`${n} formulas, ${mismatches.length} mismatches, ${((Date.now() - started) / 1000).toFixed(1)}s`);
process.exit(mismatches.length === 0 ? 0 : 1);
