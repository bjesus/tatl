/**
 * Differential testing of the optimised procedure against the plain one.
 *
 * Every optimisation behind a {@link SolverOptions} flag must leave the
 * verdict unchanged. This module generates random formulas and checks, for
 * each one, that
 *
 *   1. the plain procedure and the optimised procedure agree,
 *   2. every single optimisation on its own agrees with the plain procedure,
 *   3. the verdict is invariant under renaming agents and atoms.
 *
 * It needs no external oracle: the plain procedure has been cross-validated
 * against the original TATL implementation on thousands of formulas.
 */

import { parseFormula, systemAgents, type System } from "./parser.ts";
import { runTableau, BudgetExceeded } from "./tableau.ts";
import { DEFAULT_OPTIONS, PLAIN_OPTIONS, withOptions, type SolverOptions } from "./options.ts";

// ============================================================
// Seeded PRNG (xoshiro128**)
// ============================================================

export class Rng {
  private s: Uint32Array;

  constructor(seed: number) {
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

  random(): number { return this.next() / 4294967296; }
  int(n: number): number { return Math.floor(this.random() * n); }
  pick<T>(xs: readonly T[]): T { return xs[this.int(xs.length)]!; }
  chance(p: number): boolean { return this.random() < p; }
}

// ============================================================
// Random formulas
// ============================================================

export interface GenOptions {
  system: System;
  maxDepth: number;
  agents: string[];
  atoms: string[];
}

function coalition(rng: Rng, o: GenOptions): string {
  if (o.system === "ltl") return "";
  if (o.system !== "atl") return rng.chance(0.5) ? "A" : "E";
  const n = rng.int(o.agents.length + 1);
  const chosen = [...o.agents].sort(() => rng.random() - 0.5).slice(0, n);
  return `<<${chosen.join(",")}>>`;
}

function literal(rng: Rng, o: GenOptions): string {
  const a = rng.pick(o.atoms);
  return rng.chance(0.35) ? `~${a}` : a;
}

/** A path formula (used under a coalition, or as the whole LTL formula). */
export function genPath(rng: Rng, o: GenOptions, depth: number): string {
  if (depth >= o.maxDepth) return literal(rng, o);
  const r = rng.random();
  if (r < 0.15) return literal(rng, o);
  if (r < 0.30) return `X ${genPath(rng, o, depth + 1)}`;
  if (r < 0.45) return `G ${genPath(rng, o, depth + 1)}`;
  if (r < 0.60) return `F ${genPath(rng, o, depth + 1)}`;
  if (r < 0.70) return `(${genPath(rng, o, depth + 1)} U ${genPath(rng, o, depth + 1)})`;
  if (r < 0.80) return `(${genPath(rng, o, depth + 1)} & ${genPath(rng, o, depth + 1)})`;
  if (r < 0.90) return `(${genPath(rng, o, depth + 1)} | ${genPath(rng, o, depth + 1)})`;
  if (r < 0.95 && o.system !== "ltl") return genState(rng, o, depth + 1);
  return `(${genPath(rng, o, depth + 1)} -> ${genPath(rng, o, depth + 1)})`;
}

/** A state formula. */
export function genState(rng: Rng, o: GenOptions, depth: number): string {
  if (o.system === "ltl") return genPath(rng, o, depth);
  if (depth >= o.maxDepth) return literal(rng, o);
  const r = rng.random();
  if (r < 0.15) return literal(rng, o);
  if (r < 0.30) return `(${genState(rng, o, depth + 1)} & ${genState(rng, o, depth + 1)})`;
  if (r < 0.42) return `(${genState(rng, o, depth + 1)} | ${genState(rng, o, depth + 1)})`;
  if (r < 0.50) return `~${genState(rng, o, depth + 1)}`;
  const q = coalition(rng, o);
  const inner = genPath(rng, o, depth + 1);
  if (o.system === "ctl") {
    // CTL pairs each quantifier with exactly one temporal operator
    const op = rng.pick(["X", "G", "F"]);
    const arg = genState(rng, o, depth + 1);
    return rng.chance(0.2)
      ? `${q}[${genState(rng, o, depth + 1)} U ${arg}]`
      : `${q}${op} ${arg}`;
  }
  return `${q}(${inner})`;
}

export function genFormula(rng: Rng, o: GenOptions): string {
  const r = rng.random();
  // Conjoin with the negation of a second formula so a fair share of the
  // corpus is unsatisfiable or nearly so.
  if (r < 0.35) return `(${genState(rng, o, 1)} & ~${genState(rng, o, 1)})`;
  if (r < 0.50) return `(${genState(rng, o, 1)} & ${genState(rng, o, 1)})`;
  return genState(rng, o, 0);
}

// ============================================================
// Verdicts
// ============================================================

export type Verdict = boolean | "error" | "budget";

/** Node and time budget per run; the plain procedure blows up on some deep formulas. */
export let NODE_BUDGET = 1500;
export let TIME_BUDGET_MS = 2000;
export function setNodeBudget(n: number): void { NODE_BUDGET = n; }
export function setTimeBudget(ms: number): void { TIME_BUDGET_MS = ms; }

export function verdict(formula: string, system: System, extraAgents: string[], opts: SolverOptions): Verdict {
  try {
    return withOptions({ ...opts, maxNodes: NODE_BUDGET, deadline: Date.now() + TIME_BUDGET_MS }, () => {
      const f = parseFormula(formula, system);
      return runTableau(f, [...systemAgents(system), ...extraAgents]).satisfiable;
    });
  } catch (e) {
    return e instanceof BudgetExceeded ? "budget" : "error";
  }
}

/** Rename agents a,b,c → x,y,z and atoms p,q → u,v in a formula string. */
export function rename(formula: string): string {
  return formula
    .replace(/\b([abc])\b(?=[^a-z0-9_]|$)/g, (m) => ({ a: "x", b: "y", c: "z" }[m] ?? m))
    .replace(/\bp\b/g, "u")
    .replace(/\bq\b/g, "v");
}

export interface Mismatch {
  formula: string;
  system: System;
  check: string;
  expected: Verdict;
  got: Verdict;
}

/**
 * Run all checks on one formula. Returns the mismatches found (none if the
 * optimisations are sound on it).
 */
export function checkFormula(formula: string, system: System, extraAgents: string[] = []): Mismatch[] {
  const out: Mismatch[] = [];
  const plain = verdict(formula, system, extraAgents, PLAIN_OPTIONS);
  if (plain === "error" || plain === "budget") return out; // unparsable, or too big for the plain procedure

  const all = verdict(formula, system, extraAgents, DEFAULT_OPTIONS);
  if (all !== plain && all !== "budget") out.push({ formula, system, check: "all optimisations", expected: plain, got: all });

  const flags = (Object.keys(DEFAULT_OPTIONS) as Array<keyof SolverOptions>).filter((k) => k !== "maxNodes" && k !== "deadline");
  for (const key of flags) {
    const single = { ...PLAIN_OPTIONS, [key]: true };
    const v = verdict(formula, system, extraAgents, single);
    if (v !== plain && v !== "budget") out.push({ formula, system, check: key, expected: plain, got: v });
  }

  const renamed = rename(formula);
  const renamedAgents = extraAgents.map((a) => rename(a));
  const r = verdict(renamed, system, renamedAgents, DEFAULT_OPTIONS);
  if (r !== plain && r !== "budget") out.push({ formula: renamed, system, check: "renaming", expected: plain, got: r });

  return out;
}

/** Whether a formula is usable as a reference (parsed and fit the budget). */
export function isReference(v: Verdict): boolean {
  return v === true || v === false;
}

export interface Corpus {
  seed: number;
  count: number;
  maxDepth: number;
  systems: System[];
}

export function* corpus(c: Corpus): Generator<{ formula: string; system: System; extraAgents: string[] }> {
  const rng = new Rng(c.seed);
  for (let i = 0; i < c.count; i++) {
    const system = rng.pick(c.systems);
    const agents = system === "atl" ? ["a", "b"].slice(0, 1 + rng.int(2)) : [];
    const o: GenOptions = { system, maxDepth: c.maxDepth, agents, atoms: ["p", "q"] };
    const extraAgents = system === "atl" && rng.chance(0.3) ? ["c"] : [];
    yield { formula: genFormula(rng, o), system, extraAgents };
  }
}
