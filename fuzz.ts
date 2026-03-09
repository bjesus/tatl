/**
 * Fuzz testing: generate random ATL* formulas and cross-validate
 * our solver against the TATL OCaml implementation.
 *
 * Usage:
 *   bun run fuzz.ts [--count N] [--seed N] [--timeout N] [--max-depth N] [--agents N]
 *
 * Options:
 *   --count N      Number of formulas to test (default: 1000)
 *   --seed N       Random seed for reproducibility (default: random)
 *   --timeout N    Timeout per formula in ms (default: 10000)
 *   --max-depth N  Maximum formula depth (default: 5)
 *   --agents N     Number of agents: 1, 2, or 3 (default: 2)
 *   --verbose      Print each formula as it's tested
 */

import { parseFormula } from "./src/core/parser.ts";
import { runTableau } from "./src/core/tableau.ts";
import { execSync } from "child_process";

const TATL_EXE = `${import.meta.dir}/TATL/_build/default/tatl.exe`;

// ============================================================
// Seeded PRNG (xoshiro128**)
// ============================================================

class Rng {
  private s: Uint32Array;

  constructor(seed: number) {
    // SplitMix32 to initialize state from a single seed
    this.s = new Uint32Array(4);
    for (let i = 0; i < 4; i++) {
      seed += 0x9e3779b9;
      let z = seed;
      z = (z ^ (z >>> 16)) * 0x85ebca6b;
      z = (z ^ (z >>> 13)) * 0xc2b2ae35;
      z = z ^ (z >>> 16);
      this.s[i] = z >>> 0;
    }
  }

  /** Returns a random integer in [0, 2^32) */
  private next(): number {
    const s = this.s;
    const result = Math.imul(s[1]! * 5, 7) >>> 0;
    const t = (s[1]! << 9) >>> 0;
    s[2]! ^= s[0]!;
    s[3]! ^= s[1]!;
    s[1]! ^= s[2]!;
    s[0]! ^= s[3]!;
    s[2]! ^= t;
    s[3] = ((s[3]! << 11) | (s[3]! >>> 21)) >>> 0;
    return result;
  }

  /** Returns a random float in [0, 1) */
  random(): number {
    return this.next() / 0x100000000;
  }

  /** Returns a random integer in [0, max) */
  int(max: number): number {
    return Math.floor(this.random() * max);
  }

  /** Pick a random element from an array */
  pick<T>(arr: readonly T[]): T {
    return arr[this.int(arr.length)]!;
  }

  /** Returns true with given probability */
  chance(p: number): boolean {
    return this.random() < p;
  }
}

// ============================================================
// Random formula generation
// ============================================================

interface GenOptions {
  maxDepth: number;
  agents: string[];
  atoms: string[];
}

/**
 * Generate a random state formula string in our syntax.
 * Keeps formulas at controllable depth to avoid exponential blowup.
 */
function genStateFormula(rng: Rng, opts: GenOptions, depth: number): string {
  // At max depth, only generate atoms
  if (depth >= opts.maxDepth) {
    return rng.chance(0.3) ? `~${rng.pick(opts.atoms)}` : rng.pick(opts.atoms);
  }

  const roll = rng.random();

  // Atom (30%)
  if (roll < 0.15) {
    return rng.pick(opts.atoms);
  }

  // Negated atom (15%)
  if (roll < 0.30) {
    return `~${rng.pick(opts.atoms)}`;
  }

  // Conjunction (15%)
  if (roll < 0.45) {
    const left = genStateFormula(rng, opts, depth + 1);
    const right = genStateFormula(rng, opts, depth + 1);
    return `(${left} & ${right})`;
  }

  // Disjunction (10%)
  if (roll < 0.55) {
    const left = genStateFormula(rng, opts, depth + 1);
    const right = genStateFormula(rng, opts, depth + 1);
    return `(${left} | ${right})`;
  }

  // Negation of compound (5%)
  if (roll < 0.60) {
    const sub = genStateFormula(rng, opts, depth + 1);
    return `~${sub}`;
  }

  // Coalition formula (40%) — the interesting part
  const coal = genCoalition(rng, opts);
  const path = genPathFormula(rng, opts, depth + 1);
  return `${coal}${path}`;
}

/**
 * Generate a random path formula string.
 * Path formulas appear after <<A>> and include temporal operators.
 */
function genPathFormula(rng: Rng, opts: GenOptions, depth: number): string {
  // At max depth, only generate X/G/F of atoms
  if (depth >= opts.maxDepth) {
    const atom = rng.pick(opts.atoms);
    const op = rng.pick(["X", "G", "F"]);
    return `${op} ${atom}`;
  }

  const roll = rng.random();

  // Simple temporal operator on atom (30%)
  if (roll < 0.30) {
    const atom = rng.chance(0.3) ? `~${rng.pick(opts.atoms)}` : rng.pick(opts.atoms);
    const op = rng.pick(["X", "G", "F"]);
    return `${op} ${atom}`;
  }

  // Until on atoms (15%)
  if (roll < 0.45) {
    const left = rng.chance(0.3) ? `~${rng.pick(opts.atoms)}` : rng.pick(opts.atoms);
    const right = rng.chance(0.3) ? `~${rng.pick(opts.atoms)}` : rng.pick(opts.atoms);
    return `(${left} U ${right})`;
  }

  // Nested temporal: X/G/F of path (10%)
  if (roll < 0.55) {
    const op = rng.pick(["X", "G", "F"]);
    const sub = genPathFormula(rng, opts, depth + 1);
    return `${op} ${sub}`;
  }

  // Temporal op on nested coalition (auto-lifted state formula) (10%)
  if (roll < 0.65) {
    const op = rng.pick(["X", "G", "F"]);
    const innerCoal = genCoalition(rng, opts);
    const innerPath = genPathFormula(rng, opts, depth + 1);
    return `${op} ${innerCoal}${innerPath}`;
  }

  // Complex path: conjunction/disjunction inside parens (20%)
  if (roll < 0.85) {
    const left = genPathPrimary(rng, opts, depth + 1);
    const right = genPathPrimary(rng, opts, depth + 1);
    const op = rng.pick(["&", "|"]);
    return `(${left} ${op} ${right})`;
  }

  // Until with path sub-formulas (15%)
  {
    const left = genPathPrimary(rng, opts, depth + 1);
    const right = genPathPrimary(rng, opts, depth + 1);
    return `(${left} U ${right})`;
  }
}

/**
 * Generate a path primary (simple path formula, not infix).
 */
function genPathPrimary(rng: Rng, opts: GenOptions, depth: number): string {
  if (depth >= opts.maxDepth) {
    return rng.chance(0.3) ? `~${rng.pick(opts.atoms)}` : rng.pick(opts.atoms);
  }

  const roll = rng.random();

  // Atom (possibly negated)
  if (roll < 0.3) {
    return rng.chance(0.3) ? `~${rng.pick(opts.atoms)}` : rng.pick(opts.atoms);
  }

  // Temporal op on atom
  if (roll < 0.7) {
    const atom = rng.chance(0.3) ? `~${rng.pick(opts.atoms)}` : rng.pick(opts.atoms);
    const op = rng.pick(["X", "G", "F"]);
    return `${op} ${atom}`;
  }

  // Nested temporal
  {
    const op = rng.pick(["X", "G", "F"]);
    const sub = genPathPrimary(rng, opts, depth + 1);
    return `${op} ${sub}`;
  }
}

/**
 * Generate a random coalition string.
 */
function genCoalition(rng: Rng, opts: GenOptions): string {
  // Include empty coalition as a possibility
  if (rng.chance(0.1)) return "<<>>";

  // Random subset of agents
  const subset: string[] = [];
  for (const a of opts.agents) {
    if (rng.chance(0.5)) subset.push(a);
  }
  if (subset.length === 0) {
    // At least pick one agent (or empty coalition)
    if (rng.chance(0.3)) return "<<>>";
    subset.push(rng.pick(opts.agents));
  }
  return `<<${subset.join(",")}>>`;
}

// ============================================================
// Syntax conversion: our syntax → TATL syntax
// ============================================================

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

// ============================================================
// Solvers
// ============================================================

function runTATL(formula: string, timeout: number): boolean | "timeout" | "error" {
  const tatlFormula = toTATL(formula);
  try {
    const result = execSync(
      `${TATL_EXE} -o -f "${tatlFormula}"`,
      { timeout, encoding: "utf-8", stdio: ["pipe", "pipe", "pipe"] }
    );
    if (result.includes("unsatisfiable")) return false;
    if (result.includes("satisfiable")) return true;
    return "error";
  } catch (e: any) {
    if (e.killed || (e.message && e.message.includes("TIMEOUT"))) return "timeout";
    return "error";
  }
}

function runOurs(formula: string, timeout: number): boolean | "timeout" | "error" {
  try {
    const f = parseFormula(formula);
    // Simple timeout: use AbortSignal-like approach with a flag
    const start = Date.now();
    const result = runTableau(f);
    if (Date.now() - start > timeout) return "timeout";
    return result.satisfiable;
  } catch {
    return "error";
  }
}

// ============================================================
// Main
// ============================================================

function parseArg(name: string, defaultVal: number): number {
  const arg = process.argv.find(a => a.startsWith(`--${name}=`));
  if (arg) return parseInt(arg.split("=")[1]!) || defaultVal;

  const idx = process.argv.indexOf(`--${name}`);
  if (idx >= 0 && idx + 1 < process.argv.length) {
    const val = parseInt(process.argv[idx + 1]!);
    if (!isNaN(val)) return val;
  }
  return defaultVal;
}

function main() {
  const count = parseArg("count", 1000);
  const seedArg = parseArg("seed", -1);
  const seed = seedArg >= 0 ? seedArg : Math.floor(Math.random() * 1_000_000);
  const timeout = parseArg("timeout", 10000);
  const maxDepth = parseArg("max-depth", 5);
  const agentCount = parseArg("agents", 2);
  const verbose = process.argv.includes("--verbose");

  const agents = ["a", "b", "c"].slice(0, agentCount);
  const atoms = ["p", "q"];

  const rng = new Rng(seed);
  const opts: GenOptions = { maxDepth, agents, atoms };

  console.log(`Fuzz testing ATL* solver against TATL`);
  console.log(`  Seed: ${seed}`);
  console.log(`  Count: ${count}`);
  console.log(`  Max depth: ${maxDepth}`);
  console.log(`  Agents: {${agents.join(", ")}}`);
  console.log(`  Timeout: ${timeout}ms`);
  console.log();

  let tested = 0;
  let matches = 0;
  let mismatches = 0;
  let bothTimeout = 0;
  let oneTimeout = 0;
  let errors = 0;
  const mismatchList: { formula: string; ours: any; tatl: any }[] = [];

  for (let i = 0; i < count; i++) {
    const formula = genStateFormula(rng, opts, 0);

    if (verbose) {
      process.stdout.write(`  [${i + 1}/${count}] ${formula} ... `);
    }

    const oursResult = runOurs(formula, timeout);
    const tatlResult = runTATL(formula, timeout);

    tested++;

    // Handle timeout/error cases
    if (oursResult === "timeout" && tatlResult === "timeout") {
      bothTimeout++;
      if (verbose) console.log("both timeout");
      continue;
    }
    if (oursResult === "timeout" || tatlResult === "timeout") {
      oneTimeout++;
      if (verbose) console.log(`timeout (ours=${oursResult}, tatl=${tatlResult})`);
      continue;
    }
    if (oursResult === "error" || tatlResult === "error") {
      errors++;
      if (verbose) console.log(`error (ours=${oursResult}, tatl=${tatlResult})`);
      continue;
    }

    // Compare results
    if (oursResult === tatlResult) {
      matches++;
      if (verbose) console.log(oursResult ? "SAT" : "UNSAT");
    } else {
      mismatches++;
      mismatchList.push({ formula, ours: oursResult, tatl: tatlResult });
      if (verbose) {
        console.log(`MISMATCH: ours=${oursResult ? "SAT" : "UNSAT"}, tatl=${tatlResult ? "SAT" : "UNSAT"}`);
      } else {
        console.log(`  MISMATCH [${i + 1}]: "${formula}" — ours=${oursResult ? "SAT" : "UNSAT"}, tatl=${tatlResult ? "SAT" : "UNSAT"}`);
      }
    }

    if (!verbose && (i + 1) % 50 === 0) {
      process.stdout.write(`  ... ${i + 1}/${count} (${matches} match, ${mismatches} mismatch)\r`);
    }
  }

  console.log(`\n`);
  console.log(`Results (seed=${seed}):`);
  console.log(`  Tested:         ${tested}`);
  console.log(`  Matches:        ${matches}`);
  console.log(`  Mismatches:     ${mismatches}`);
  console.log(`  Both timeout:   ${bothTimeout}`);
  console.log(`  One timeout:    ${oneTimeout}`);
  console.log(`  Errors:         ${errors}`);

  if (mismatchList.length > 0) {
    console.log(`\nMismatches:`);
    for (const m of mismatchList) {
      console.log(`  "${m.formula}"`);
      console.log(`    ours=${m.ours ? "SAT" : "UNSAT"}, tatl=${m.tatl ? "SAT" : "UNSAT"}`);
    }
    console.log(`\nTo reproduce: bun run fuzz.ts --seed=${seed} --count=${count} --max-depth=${maxDepth} --agents=${agentCount}`);
    process.exit(1);
  } else {
    console.log(`\nAll formulas match!`);
    process.exit(0);
  }
}

main();
