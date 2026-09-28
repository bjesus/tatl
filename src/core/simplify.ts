/**
 * Input preprocessing: equivalence-preserving rewrites applied to the input
 * formula once, before the tableau is built.
 *
 * Everything here is a genuine ATL* equivalence, so the tableau built for the
 * rewritten formula decides the original one. The rewrites are applied to the
 * input only, never to labels the construction produces: a label such as
 * ⟨⟨a⟩⟩(□◇p ∧ ◇p) carries ◇p as an *obligation marker* that the E3 check
 * relies on, and absorbing it into □◇p would silence that check.
 *
 * Steps, in order:
 *   1. co-coalition normalisation:  [[∅]]π → ⟨⟨Σ⟩⟩π,  [[Σ]]π → ⟨⟨∅⟩⟩π
 *   2. propositional simplification to a fixpoint (constants, idempotence,
 *      complementary pairs, absorption with a small syntactic entailment
 *      relation, ⟨⟨A⟩⟩φ → φ for state formulas φ)
 *   3. disjunction lifting:  ⟨⟨Σ⟩⟩(π₁ ∨ π₂) → ⟨⟨Σ⟩⟩π₁ ∨ ⟨⟨Σ⟩⟩π₂
 *   4. □-closure of coalition path conjunctions:  □◇π ∧ ρ → □◇π ∧ ◇π ∧ ρ
 */

import {
  type StateFormula,
  type PathFormula,
  type Coalition,
  STop, SBot, Atom, Neg, SAnd, SOr, Coal, CoCoal,
  PState, PNeg, PAnd, POr, PNext, PAlways, PUntil,
  stateKey, pathKey, stateOperands, pathOperands, coalitionEqual,
} from "./types.ts";
import { nnfState, nnfPath, simplifyPath as simplifyTemporal } from "./nnf.ts";
import { getOptions } from "./options.ts";

// ============================================================
// Entry point
// ============================================================

export function preprocess(theta: StateFormula, allAgents: Coalition): StateFormula {
  const o = getOptions();
  let f = theta;
  if (o.simplify) {
    f = normalizeCoalitions(f, allAgents);
    f = unliftDisjunctions(f, allAgents);
    f = simplifyState(f);
  }
  if (o.liftDisjunctions) f = liftDisjunctions(f, allAgents);
  if (o.alwaysClosure) f = closeAlwaysState(f);
  return f;
}

// ============================================================
// 1. Co-coalition normalisation
// ============================================================

function normalizeCoalitions(f: StateFormula, all: Coalition): StateFormula {
  const st = (g: StateFormula): StateFormula => {
    switch (g.kind) {
      case "top": case "bot": case "atom": return g;
      case "neg": return Neg(st(g.sub));
      case "and": return SAnd(st(g.left), st(g.right));
      case "or": return SOr(st(g.left), st(g.right));
      case "coal": return Coal(g.coalition, pt(g.path));
      case "cocoal": {
        const path = pt(g.path);
        if (g.coalition.length === 0) return Coal(all, path);
        if (coalitionEqual(g.coalition, all)) return Coal([], path);
        return CoCoal(g.coalition, path);
      }
    }
  };
  const pt = (g: PathFormula): PathFormula => {
    switch (g.kind) {
      case "state": return PState(st(g.sub));
      case "negp": return PNeg(pt(g.sub));
      case "andp": return PAnd(pt(g.left), pt(g.right));
      case "orp": return POr(pt(g.left), pt(g.right));
      case "next": return PNext(pt(g.sub));
      case "always": return PAlways(pt(g.sub));
      case "until": return PUntil(pt(g.left), pt(g.right));
    }
  };
  return st(f);
}

// ============================================================
// 2. Propositional simplification
// ============================================================

const isTop = (f: StateFormula) => f.kind === "top";
const isBot = (f: StateFormula) => f.kind === "bot";
const isPTop = (f: PathFormula) => f.kind === "state" && f.sub.kind === "top";
const isPBot = (f: PathFormula) => f.kind === "state" && f.sub.kind === "bot";

function stateComplementKey(f: StateFormula): string {
  return stateKey(nnfState(Neg(f)));
}

function pathComplementKey(f: PathFormula): string {
  return pathKey(nnfPath(PNeg(f)));
}

/**
 * Syntactic entailment φ ⊨ ψ on state formulas. Sound but incomplete.
 */
export function stateEntails(a: StateFormula, b: StateFormula): boolean {
  if (stateKey(a) === stateKey(b)) return true;
  if (isTop(b) || isBot(a)) return true;
  // a = a₁ ∧ a₂ entails b if some conjunct does
  if (a.kind === "and" && stateOperands(a, "and").some(x => stateEntails(x, b))) return true;
  // a entails b₁ ∨ b₂ if it entails some disjunct
  if (b.kind === "or" && stateOperands(b, "or").some(y => stateEntails(a, y))) return true;
  // a entails b₁ ∧ b₂ if it entails every conjunct
  if (b.kind === "and" && stateOperands(b, "and").every(y => stateEntails(a, y))) return true;
  // a₁ ∨ a₂ entails b if every disjunct does
  if (a.kind === "or" && stateOperands(a, "or").every(x => stateEntails(x, b))) return true;
  // same coalition operator, entailment on the path formula
  if (a.kind === b.kind && (a.kind === "coal" || a.kind === "cocoal") &&
      coalitionEqual(a.coalition, (b as typeof a).coalition)) {
    return pathEntails(a.path, (b as typeof a).path);
  }
  return false;
}

/**
 * Syntactic entailment π ⊨ ρ on path formulas (read on one path).
 */
export function pathEntails(a: PathFormula, b: PathFormula): boolean {
  if (pathKey(a) === pathKey(b)) return true;
  if (isPTop(b) || isPBot(a)) return true;
  if (a.kind === "state" && b.kind === "state") return stateEntails(a.sub, b.sub);
  if (a.kind === "andp" && pathOperands(a, "andp").some(x => pathEntails(x, b))) return true;
  if (b.kind === "orp" && pathOperands(b, "orp").some(y => pathEntails(a, y))) return true;
  if (b.kind === "andp" && pathOperands(b, "andp").every(y => pathEntails(a, y))) return true;
  if (a.kind === "orp" && pathOperands(a, "orp").every(x => pathEntails(x, b))) return true;
  // □π ⊨ π, □π ⊨ ○π, □π ⊨ □ρ if π ⊨ ρ
  if (a.kind === "always") {
    if (pathEntails(a.sub, b)) return true;
    if (b.kind === "next" && pathEntails(a.sub, b.sub)) return true;
    if (b.kind === "always" && pathEntails(a.sub, b.sub)) return true;
  }
  // π ⊨ ρ U σ if π ⊨ σ (σ holds now); (a₁ U a₂) ⊨ (b₁ U b₂) if a₁ ⊨ b₁ and a₂ ⊨ b₂
  if (b.kind === "until") {
    if (pathEntails(a, b.right)) return true;
    if (a.kind === "until" && pathEntails(a.left, b.left) && pathEntails(a.right, b.right)) return true;
  }
  if (a.kind === "next" && b.kind === "next") return pathEntails(a.sub, b.sub);
  return false;
}

function rebuildState(ops: StateFormula[], kind: "and" | "or", empty: StateFormula): StateFormula {
  if (ops.length === 0) return empty;
  let r = ops[ops.length - 1]!;
  for (let i = ops.length - 2; i >= 0; i--) r = kind === "and" ? SAnd(ops[i]!, r) : SOr(ops[i]!, r);
  return r;
}

function rebuildPath(ops: PathFormula[], kind: "andp" | "orp", empty: PathFormula): PathFormula {
  if (ops.length === 0) return empty;
  let r = ops[ops.length - 1]!;
  for (let i = ops.length - 2; i >= 0; i--) r = kind === "andp" ? PAnd(ops[i]!, r) : POr(ops[i]!, r);
  return r;
}

/** Remove duplicates (by key) preserving first occurrence. */
function dedupe<T>(xs: T[], key: (x: T) => string): T[] {
  const seen = new Set<string>();
  const out: T[] = [];
  for (const x of xs) {
    const k = key(x);
    if (!seen.has(k)) { seen.add(k); out.push(x); }
  }
  return out;
}

export function simplifyState(f: StateFormula): StateFormula {
  let cur = f;
  for (let i = 0; i < 50; i++) {
    const next = simplifyStateOnce(cur);
    if (stateKey(next) === stateKey(cur)) return next;
    cur = next;
  }
  return cur;
}

function simplifyStateOnce(f: StateFormula): StateFormula {
  switch (f.kind) {
    case "top": case "bot": case "atom": return f;
    case "neg": {
      const s = simplifyStateOnce(f.sub);
      if (s.kind === "top") return SBot;
      if (s.kind === "bot") return STop;
      if (s.kind === "neg") return s.sub;
      return Neg(s);
    }
    case "and": {
      let ops = dedupe(stateOperands(f, "and").map(simplifyStateOnce), stateKey);
      if (ops.some(isBot)) return SBot;
      ops = ops.filter(x => !isTop(x));
      const keys = new Set(ops.map(stateKey));
      for (const x of ops) if (keys.has(stateComplementKey(x))) return SBot;
      // absorption: drop ψ when another conjunct entails it
      ops = ops.filter((x, i) => !ops.some((y, j) => j !== i && stateEntails(y, x) && !(stateEntails(x, y) && j > i)));
      return canonicalPropositional(rebuildState(ops, "and", STop));
    }
    case "or": {
      let ops = dedupe(stateOperands(f, "or").map(simplifyStateOnce), stateKey);
      if (ops.some(isTop)) return STop;
      ops = ops.filter(x => !isBot(x));
      const keys = new Set(ops.map(stateKey));
      for (const x of ops) if (keys.has(stateComplementKey(x))) return STop;
      // absorption: drop ψ when it entails another disjunct
      ops = ops.filter((x, i) => !ops.some((y, j) => j !== i && stateEntails(x, y) && !(stateEntails(y, x) && j > i)));
      return canonicalPropositional(rebuildState(ops, "or", SBot));
    }
    case "coal": case "cocoal": {
      const path = simplifyPathOnce(f.path);
      // ⟨⟨A⟩⟩φ ≡ φ for a state formula φ
      if (path.kind === "state") return path.sub;
      return f.kind === "coal" ? Coal(f.coalition, path) : CoCoal(f.coalition, path);
    }
  }
}

export function simplifyPathFull(f: PathFormula): PathFormula {
  let cur = f;
  for (let i = 0; i < 50; i++) {
    const next = simplifyPathOnce(cur);
    if (pathKey(next) === pathKey(cur)) return next;
    cur = next;
  }
  return cur;
}

function simplifyPathOnce(f: PathFormula): PathFormula {
  switch (f.kind) {
    case "state": return PState(simplifyStateOnce(f.sub));
    case "negp": return PNeg(simplifyPathOnce(f.sub));
    case "andp": {
      let ops = dedupe(pathOperands(f, "andp").map(simplifyPathOnce), pathKey);
      if (ops.some(isPBot)) return PState(SBot);
      ops = ops.filter(x => !isPTop(x));
      const keys = new Set(ops.map(pathKey));
      for (const x of ops) if (keys.has(pathComplementKey(x))) return PState(SBot);
      ops = ops.filter((x, i) => !ops.some((y, j) => j !== i && pathEntails(y, x) && !(pathEntails(x, y) && j > i)));
      ops = distributeAnd(ops);
      // state formulas under one ∧ merge into one state formula
      return mergeStateOperands(rebuildPath(ops, "andp", PState(STop)), "andp");
    }
    case "orp": {
      let ops = dedupe(pathOperands(f, "orp").map(simplifyPathOnce), pathKey);
      if (ops.some(isPTop)) return PState(STop);
      ops = ops.filter(x => !isPBot(x));
      const keys = new Set(ops.map(pathKey));
      for (const x of ops) if (keys.has(pathComplementKey(x))) return PState(STop);
      ops = ops.filter((x, i) => !ops.some((y, j) => j !== i && pathEntails(x, y) && !(pathEntails(y, x) && j > i)));
      ops = distributeOr(ops);
      return mergeStateOperands(rebuildPath(ops, "orp", PState(SBot)), "orp");
    }
    case "next": {
      const s = simplifyPathOnce(f.sub);
      if (isPTop(s) || isPBot(s)) return s;
      return PNext(s);
    }
    case "always": {
      const s = simplifyPathOnce(f.sub);
      if (isPTop(s) || isPBot(s)) return s;
      return simplifyTemporal(PAlways(s));
    }
    case "until": {
      const l = simplifyPathOnce(f.left);
      const r = simplifyPathOnce(f.right);
      if (isPTop(r) || isPBot(r)) return r;          // π U ⊤ ≡ ⊤,  π U ⊥ ≡ ⊥
      if (isPBot(l)) return r;                        // ⊥ U π ≡ π
      return simplifyTemporal(PUntil(l, r));
    }
  }
}

// ============================================================
// Exact propositional canonicalisation
// ============================================================

const MAX_CANON_ATOMS = 8;

function atomsOf(f: StateFormula, out: Set<string>): void {
  switch (f.kind) {
    case "atom": out.add(f.name); break;
    case "neg": atomsOf(f.sub, out); break;
    case "and": case "or": atomsOf(f.left, out); atomsOf(f.right, out); break;
    default: break;
  }
}

function isPropositionalState(f: StateFormula): boolean {
  switch (f.kind) {
    case "top": case "bot": case "atom": return true;
    case "neg": return isPropositionalState(f.sub);
    case "and": case "or": return isPropositionalState(f.left) && isPropositionalState(f.right);
    default: return false;
  }
}

function evalProp(f: StateFormula, val: Map<string, boolean>): boolean {
  switch (f.kind) {
    case "top": return true;
    case "bot": return false;
    case "atom": return val.get(f.name)!;
    case "neg": return !evalProp(f.sub, val);
    case "and": return evalProp(f.left, val) && evalProp(f.right, val);
    case "or": return evalProp(f.left, val) || evalProp(f.right, val);
    default: throw new Error("not propositional");
  }
}

function stateSize(f: StateFormula): number {
  switch (f.kind) {
    case "top": case "bot": case "atom": return 1;
    case "neg": return 1 + stateSize(f.sub);
    case "and": case "or": return 1 + stateSize(f.left) + stateSize(f.right);
    default: return 1;
  }
}

/**
 * A propositional formula over a few atoms is replaced by a minimal DNF of
 * its prime implicants when that is smaller (by a truth table, so
 * (p ∧ q) ∨ (p ∧ ¬q) becomes p). Only propositional subformulas are touched.
 */
function canonicalPropositional(f: StateFormula): StateFormula {
  if (!isPropositionalState(f) || (f.kind !== "and" && f.kind !== "or")) return f;
  const atomSet = new Set<string>();
  atomsOf(f, atomSet);
  const atoms = [...atomSet].sort();
  const n = atoms.length;
  if (n === 0 || n > MAX_CANON_ATOMS) return f;

  // Truth table: bit i of a minterm index gives atom i
  const rows = 1 << n;
  const truth: boolean[] = new Array(rows);
  const val = new Map<string, boolean>();
  let trueCount = 0;
  for (let m = 0; m < rows; m++) {
    for (let i = 0; i < n; i++) val.set(atoms[i]!, ((m >> i) & 1) === 1);
    truth[m] = evalProp(f, val);
    if (truth[m]) trueCount++;
  }
  if (trueCount === rows) return STop;
  if (trueCount === 0) return SBot;

  // Implicants: for each atom 0 (negative), 1 (positive), 2 (absent).
  // Enumerate all 3^n; keep those whose covered minterms are all true; keep
  // the prime ones (no atom can be dropped).
  const total = Math.pow(3, n);
  const digitsOf = (code: number): number[] => {
    const d: number[] = [];
    for (let i = 0; i < n; i++) { d.push(code % 3); code = Math.floor(code / 3); }
    return d;
  };
  const covers = (d: number[]): number[] => {
    let ms = [0];
    for (let i = 0; i < n; i++) {
      if (d[i] === 2) ms = ms.flatMap(m => [m, m | (1 << i)]);
      else if (d[i] === 1) ms = ms.map(m => m | (1 << i));
    }
    return ms;
  };
  const valid = new Set<number>();
  const implicants: Array<{ d: number[]; ms: number[] }> = [];
  for (let code = 0; code < total; code++) {
    const d = digitsOf(code);
    const ms = covers(d);
    if (ms.every(m => truth[m])) { valid.add(code); implicants.push({ d, ms }); }
  }
  const codeOf = (d: number[]) => d.reduce((acc, x, i) => acc + x * Math.pow(3, i), 0);
  const primes = implicants.filter(({ d }) =>
    !d.some((x, i) => x !== 2 && valid.has(codeOf(d.map((y, j) => (j === i ? 2 : y))))));

  // Greedy cover of the true minterms by prime implicants, largest first
  primes.sort((a, b) => b.ms.length - a.ms.length);
  const uncovered = new Set<number>();
  for (let m = 0; m < rows; m++) if (truth[m]) uncovered.add(m);
  const chosen: number[][] = [];
  // essential primes first
  for (const p of primes) {
    if (p.ms.some(m => uncovered.has(m) && primes.filter(q => q.ms.includes(m)).length === 1)) {
      chosen.push(p.d);
      for (const m of p.ms) uncovered.delete(m);
    }
  }
  while (uncovered.size > 0) {
    let best: { d: number[]; ms: number[] } | null = null;
    let bestGain = 0;
    for (const p of primes) {
      const gain = p.ms.filter(m => uncovered.has(m)).length;
      if (gain > bestGain) { bestGain = gain; best = p; }
    }
    if (!best) break;
    chosen.push(best.d);
    for (const m of best.ms) uncovered.delete(m);
  }

  const terms = chosen.map(d => {
    const lits: StateFormula[] = [];
    d.forEach((x, i) => { if (x === 1) lits.push(Atom(atoms[i]!)); else if (x === 0) lits.push(Neg(Atom(atoms[i]!))); });
    return rebuildState(lits, "and", STop);
  });
  const dnf = rebuildState(terms, "or", SBot);
  return stateSize(dnf) < stateSize(f) ? dnf : f;
}

// ============================================================
// Temporal distribution
// ============================================================

const isEventually = (f: PathFormula): f is { kind: "until"; left: PathFormula; right: PathFormula } =>
  f.kind === "until" && f.left.kind === "state" && f.left.sub.kind === "top";
const isGF = (f: PathFormula) => f.kind === "always" && isEventually(f.sub);
const isFG = (f: PathFormula) => isEventually(f) && f.right.kind === "always";

/** Group operands satisfying `pred`, and replace them by `build(group)` when there are at least two. */
function group(ops: PathFormula[], pred: (f: PathFormula) => boolean, build: (g: PathFormula[]) => PathFormula): PathFormula[] {
  const hits = ops.filter(pred);
  if (hits.length < 2) return ops;
  const rest = ops.filter(x => !pred(x));
  return [build(hits), ...rest];
}

/**
 * Equivalences that merge temporal operators across a conjunction:
 *   ○φ ∧ ○ψ → ○(φ ∧ ψ),   □φ ∧ □ψ → □(φ ∧ ψ),   ◇□φ ∧ ◇□ψ → ◇□(φ ∧ ψ)
 *   (φ U χ) ∧ (ψ U χ) → (φ ∧ ψ) U χ
 * Each merged operand is re-simplified, since the merge can expose more.
 */
function distributeAnd(ops: PathFormula[]): PathFormula[] {
  let out = ops;
  out = group(out, f => f.kind === "next", g => PNext(simplifyPathOnce(rebuildPath(g.map(x => (x as { sub: PathFormula }).sub), "andp", PState(STop)))));
  out = group(out, f => isFG(f), g => PUntil(PState(STop), PAlways(simplifyPathOnce(rebuildPath(g.map(x => ((x as { right: PathFormula }).right as { sub: PathFormula }).sub), "andp", PState(STop))))));
  out = group(out, f => f.kind === "always", g => PAlways(simplifyPathOnce(rebuildPath(g.map(x => (x as { sub: PathFormula }).sub), "andp", PState(STop)))));
  // same right-hand side: group untils by the key of their goal
  const byGoal = new Map<string, PathFormula[]>();
  for (const f of out) if (f.kind === "until" && !isEventually(f)) {
    const k = pathKey(f.right);
    byGoal.set(k, [...(byGoal.get(k) ?? []), f]);
  }
  for (const g of byGoal.values()) {
    if (g.length < 2) continue;
    const merged = PUntil(simplifyPathOnce(rebuildPath(g.map(x => (x as { left: PathFormula }).left), "andp", PState(STop))), (g[0] as { right: PathFormula }).right);
    out = [merged, ...out.filter(x => !g.includes(x))];
  }
  return out;
}

/**
 * Equivalences that merge temporal operators across a disjunction:
 *   ○φ ∨ ○ψ → ○(φ ∨ ψ),   ◇φ ∨ ◇ψ → ◇(φ ∨ ψ),   □◇φ ∨ □◇ψ → □◇(φ ∨ ψ)
 *   (φ U ψ) ∨ (φ U χ) → φ U (ψ ∨ χ)
 */
function distributeOr(ops: PathFormula[]): PathFormula[] {
  let out = ops;
  out = group(out, f => f.kind === "next", g => PNext(simplifyPathOnce(rebuildPath(g.map(x => (x as { sub: PathFormula }).sub), "orp", PState(SBot)))));
  out = group(out, f => isGF(f), g => PAlways(PUntil(PState(STop), simplifyPathOnce(rebuildPath(g.map(x => ((x as { sub: PathFormula }).sub as { right: PathFormula }).right), "orp", PState(SBot))))));
  // untils with the same left-hand side (◇ included: its left-hand side is ⊤)
  const byGuard = new Map<string, PathFormula[]>();
  for (const f of out) if (f.kind === "until") {
    const k = pathKey(f.left);
    byGuard.set(k, [...(byGuard.get(k) ?? []), f]);
  }
  for (const g of byGuard.values()) {
    if (g.length < 2) continue;
    const merged = PUntil((g[0] as { left: PathFormula }).left, simplifyPathOnce(rebuildPath(g.map(x => (x as { right: PathFormula }).right), "orp", PState(SBot))));
    out = [merged, ...out.filter(x => !g.includes(x))];
  }
  return out;
}

/**
 * Inside a path ∧/∨, collect the operands that are plain state formulas into
 * a single state formula, so ⟨⟨a⟩⟩(p ∧ q ∧ ◇r) is read as ⟨⟨a⟩⟩((p ∧ q) ∧ ◇r).
 */
function mergeStateOperands(f: PathFormula, kind: "andp" | "orp"): PathFormula {
  if (f.kind !== kind) return f;
  const ops = pathOperands(f, kind);
  const stateOps = ops.filter(x => x.kind === "state").map(x => (x as { sub: StateFormula }).sub);
  if (stateOps.length <= 1) return f;
  const rest = ops.filter(x => x.kind !== "state");
  const merged = PState(rebuildState(stateOps, kind === "andp" ? "and" : "or", kind === "andp" ? STop : SBot));
  return rebuildPath([merged, ...rest], kind, merged);
}

// ============================================================
// 3. Disjunction lifting
// ============================================================

/**
 * The inverse of lifting: ⟨⟨Σ⟩⟩π₁ ∨ ⟨⟨Σ⟩⟩π₂ → ⟨⟨Σ⟩⟩(π₁ ∨ π₂), so that the
 * simplifier sees complementary path formulas side by side (the parser has
 * already lifted an LTL formula's top-level disjunction before NNF).
 */
function unliftDisjunctions(f: StateFormula, all: Coalition): StateFormula {
  const st = (g: StateFormula): StateFormula => {
    switch (g.kind) {
      case "top": case "bot": case "atom": case "neg": return g;
      case "and": return SAnd(st(g.left), st(g.right));
      case "or": {
        const ops = stateOperands(g, "or").map(st);
        const grand = ops.filter(x => x.kind === "coal" && coalitionEqual(x.coalition, all));
        if (grand.length < 2) return rebuildState(ops, "or", SBot);
        const rest = ops.filter(x => !grand.includes(x));
        const merged = Coal(all, rebuildPath(grand.map(x => (x as { path: PathFormula }).path), "orp", PState(SBot)));
        return rebuildState([merged, ...rest], "or", SBot);
      }
      case "coal": return Coal(g.coalition, pt(g.path));
      case "cocoal": return CoCoal(g.coalition, pt(g.path));
    }
  };
  const pt = (g: PathFormula): PathFormula => {
    switch (g.kind) {
      case "state": return PState(st(g.sub));
      case "negp": return PNeg(pt(g.sub));
      case "andp": return PAnd(pt(g.left), pt(g.right));
      case "orp": return POr(pt(g.left), pt(g.right));
      case "next": return PNext(pt(g.sub));
      case "always": return PAlways(pt(g.sub));
      case "until": return PUntil(pt(g.left), pt(g.right));
    }
  };
  return st(f);
}

function liftDisjunctions(f: StateFormula, all: Coalition): StateFormula {
  const st = (g: StateFormula): StateFormula => {
    switch (g.kind) {
      case "top": case "bot": case "atom": case "neg": return g;
      case "and": return SAnd(st(g.left), st(g.right));
      case "or": return SOr(st(g.left), st(g.right));
      case "coal": {
        if (coalitionEqual(g.coalition, all) && g.path.kind === "orp") {
          return SOr(st(Coal(g.coalition, g.path.left)), st(Coal(g.coalition, g.path.right)));
        }
        return Coal(g.coalition, pt(g.path));
      }
      case "cocoal": return CoCoal(g.coalition, pt(g.path));
    }
  };
  // Nested coalition formulas inside path formulas are lifted in place
  const pt = (g: PathFormula): PathFormula => {
    switch (g.kind) {
      case "state": return PState(st(g.sub));
      case "negp": return PNeg(pt(g.sub));
      case "andp": return PAnd(pt(g.left), pt(g.right));
      case "orp": return POr(pt(g.left), pt(g.right));
      case "next": return PNext(pt(g.sub));
      case "always": return PAlways(pt(g.sub));
      case "until": return PUntil(pt(g.left), pt(g.right));
    }
  };
  return st(f);
}

// ============================================================
// 4. □-closure
// ============================================================

/**
 * For every coalition formula ⟨⟨A⟩⟩(… ∧ □π ∧ …) make π's conjuncts explicit
 * conjuncts as well. See alwaysClosure in decomposition.ts for why.
 */
function closeAlwaysState(f: StateFormula): StateFormula {
  const st = (g: StateFormula): StateFormula => {
    switch (g.kind) {
      case "top": case "bot": case "atom": case "neg": return g;
      case "and": return SAnd(st(g.left), st(g.right));
      case "or": return SOr(st(g.left), st(g.right));
      case "coal": return Coal(g.coalition, closeTop(pt(g.path)));
      case "cocoal": return CoCoal(g.coalition, closeTop(pt(g.path)));
    }
  };
  const pt = (g: PathFormula): PathFormula => {
    switch (g.kind) {
      case "state": return PState(st(g.sub));
      case "negp": return PNeg(pt(g.sub));
      case "andp": return PAnd(pt(g.left), pt(g.right));
      case "orp": return POr(pt(g.left), pt(g.right));
      case "next": return PNext(pt(g.sub));
      case "always": return PAlways(pt(g.sub));
      case "until": return PUntil(pt(g.left), pt(g.right));
    }
  };
  return st(f);
}

export function closeTop(path: PathFormula): PathFormula {
  const ops = pathOperands(path, "andp");
  const keys = new Set(ops.map(pathKey));
  const out = [...ops];
  let changed = true;
  while (changed) {
    changed = false;
    for (const x of [...out]) {
      if (x.kind !== "always") continue;
      for (const c of pathOperands(x.sub, "andp")) {
        // Only eventualities double a label; a plain state conjunct never does
        if (c.kind !== "until") continue;
        const k = pathKey(c);
        if (!keys.has(k)) { keys.add(k); out.push(c); changed = true; }
      }
    }
  }
  if (out.length === ops.length) return path;
  return rebuildPath(out, "andp", PState(STop));
}
