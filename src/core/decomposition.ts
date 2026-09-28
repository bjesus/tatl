/**
 * Gamma-decomposition for ATL* formulas.
 *
 * This is the heart of the ATL* extension — it decomposes path formulas
 * inside coalition operators into gamma tuples that separate present-state
 * requirements, path formula tracking, and next-state obligations.
 *
 * Key types:
 *   GammaTuple = { f1: StateFormulaSet, f2: PathFormulaSet, f3: SetOfPathFormulaSets }
 *     f1: state formulas required at the current state
 *     f2: path formulas being tracked (for eventuality checking)
 *     f3: path formulas required at the next state (conjunction of disjunctions)
 *
 *   FormulaTuple = { frm: StateFormula, pathFrm: PathFormulaSet, nextFrm: StateFormula }
 *     The output of gammaComp — used by saturation/tableau.
 *
 * Key operations:
 *   gammaSets(π)      — decompose a path formula into gamma tuples
 *   otimes(G1, G2)    — conjunctive combination (⊗) for AndP
 *   oplus(G1, G2)     — disjunctive combination (⊕) for OrP
 *   gammaComp(φ)      — entry point: decompose Coal(A,π) or CoCoal(A,π)
 *
 * Reference: TATL decomposition.ml
 */

import {
  type StateFormula,
  type PathFormula,
  type FormulaTuple,
  STop,
  SAnd,
  Coal,
  CoCoal,
  PState,
  PNext,
  PAlways,
  PUntil,
  PAnd,
  StateFormulaSet,
  PathFormulaSet,
  stateKey,
  pathKey,
  formulaTupleKey,
} from "./types.ts";
import { getOptions } from "./options.ts";

/** Thrown when construction exceeds the configured node or time budget. */
export class BudgetExceeded extends Error {
  constructor() { super("tableau construction exceeded its budget"); this.name = "BudgetExceeded"; }
}
import { nnfState, nnfPath } from "./nnf.ts";
import { isPropositional, containsEventualityOperator } from "./formula.ts";
import { type Coalition, coalitionEqual, Neg, PNeg, PAnd as PAndCtor } from "./types.ts";

// ============================================================
// Internal types for gamma-decomposition
// ============================================================

/**
 * A set of PathFormulaSets — represents a conjunction of disjunctions
 * (CNF-like structure over path formulas).
 *
 * { S₁, S₂, ..., Sₖ } means (∨S₁) ∧ (∨S₂) ∧ ... ∧ (∨Sₖ)
 *
 * We use a Map keyed by the canonical key of each PathFormulaSet.
 */
export class SetOfPathFormulaSets {
  private _map: Map<string, PathFormulaSet> = new Map();

  constructor(sets?: Iterable<PathFormulaSet>) {
    if (sets) {
      for (const s of sets) this.add(s);
    }
  }

  add(s: PathFormulaSet): void {
    const key = s.key();
    if (!this._map.has(key)) this._map.set(key, s);
  }

  has(s: PathFormulaSet): boolean {
    return this._map.has(s.key());
  }

  remove(s: PathFormulaSet): void {
    this._map.delete(s.key());
  }

  get size(): number { return this._map.size; }

  isEmpty(): boolean { return this._map.size === 0; }

  *[Symbol.iterator](): Iterator<PathFormulaSet> {
    yield* this._map.values();
  }

  toArray(): PathFormulaSet[] { return [...this._map.values()]; }

  equals(other: SetOfPathFormulaSets): boolean {
    if (this.size !== other.size) return false;
    for (const key of this._map.keys()) {
      if (!other._map.has(key)) return false;
    }
    return true;
  }

  clone(): SetOfPathFormulaSets {
    const copy = new SetOfPathFormulaSets();
    for (const [key, val] of this._map) copy._map.set(key, val);
    return copy;
  }

  union(other: SetOfPathFormulaSets): SetOfPathFormulaSets {
    const result = this.clone();
    for (const s of other) result.add(s);
    return result;
  }

  key(): string {
    const keys = [...this._map.keys()].sort();
    return "{{" + keys.join("},{") + "}}";
  }
}

/**
 * A gamma tuple — the intermediate representation during decomposition.
 */
export interface GammaTuple {
  readonly f1: StateFormulaSet;      // state formulas for the current state
  readonly f2: PathFormulaSet;       // path formulas being tracked
  readonly f3: SetOfPathFormulaSets; // next-state obligations (conj of disj)
}

function gammaTupleKey(t: GammaTuple): string {
  return `<${t.f1.key()},${t.f2.key()},${t.f3.key()}>`;
}

/**
 * A set of gamma tuples.
 */
export class GammaSetCollection {
  private _map: Map<string, GammaTuple> = new Map();

  constructor(tuples?: Iterable<GammaTuple>) {
    if (tuples) {
      for (const t of tuples) this.add(t);
    }
  }

  add(t: GammaTuple): void {
    const key = gammaTupleKey(t);
    if (!this._map.has(key)) this._map.set(key, t);
  }

  get size(): number { return this._map.size; }

  isEmpty(): boolean { return this._map.size === 0; }

  *[Symbol.iterator](): Iterator<GammaTuple> {
    yield* this._map.values();
  }

  toArray(): GammaTuple[] { return [...this._map.values()]; }

  union(other: GammaSetCollection): GammaSetCollection {
    const result = new GammaSetCollection();
    for (const t of this) result.add(t);
    for (const t of other) result.add(t);
    return result;
  }
}

// ============================================================
// Singleton constants
// ============================================================

/** The trivial next-state obligation: { { State(⊤) } } */
const SINGL_TOP = new SetOfPathFormulaSets([
  new PathFormulaSet([PState(STop)])
]);

/** Wrap a single path formula into {{ f }} */
function singlPath(f: PathFormula): SetOfPathFormulaSets {
  return new SetOfPathFormulaSets([new PathFormulaSet([f])]);
}

// ============================================================
// Helper: check if a formula contains Next
// ============================================================

let _containsNext = false;

function containsNextState(f: StateFormula): boolean {
  switch (f.kind) {
    case "top": case "bot": case "atom": return false;
    case "neg": return containsNextState(f.sub);
    case "and": return containsNextState(f.left) || containsNextState(f.right);
    case "or": return containsNextState(f.left) || containsNextState(f.right);
    case "coal": case "cocoal": return containsNextPath(f.path);
  }
}

function containsNextPath(f: PathFormula): boolean {
  switch (f.kind) {
    case "state": return containsNextState(f.sub);
    case "negp": return containsNextPath(f.sub);
    case "andp": return containsNextPath(f.left) || containsNextPath(f.right);
    case "orp": return containsNextPath(f.left) || containsNextPath(f.right);
    case "next": return true;
    case "always": return containsNextPath(f.sub);
    case "until": return containsNextPath(f.left) || containsNextPath(f.right);
  }
}

// ============================================================
// Helper: convert sets to formulas
// ============================================================

/**
 * Convert a set of state formulas to a single conjunction.
 * Removes Top if there are multiple elements.
 */
function stateSetToAnd(s: StateFormulaSet): StateFormula {
  let arr = s.toArray();
  if (arr.length === 0) return STop;
  if (arr.length > 1) {
    arr = arr.filter(f => f.kind !== "top");
    if (arr.length === 0) return STop;
  }
  let result = arr[arr.length - 1]!;
  for (let i = arr.length - 2; i >= 0; i--) {
    result = SAnd(arr[i]!, result);
  }
  return result;
}

/**
 * Convert a set of path formulas to a single disjunction.
 * If State(⊤) is present, the whole thing is State(⊤).
 */
function pathSetToOr(s: PathFormulaSet): PathFormula {
  const arr = s.toArray();
  if (arr.length === 0) return PState(STop); // shouldn't happen
  // If State(Top) ∈ s, the disjunction is trivially true
  if (arr.length >= 1 && arr.some(f => f.kind === "state" && f.sub.kind === "top")) {
    return PState(STop);
  }
  let result = arr[arr.length - 1]!;
  for (let i = arr.length - 2; i >= 0; i--) {
    result = { kind: "orp", left: arr[i]!, right: result };
  }
  return result;
}

/**
 * Convert a set of path formulas to a single conjunction.
 * Removes State(⊤) if there are multiple elements.
 */
function pathSetToAnd(s: PathFormulaSet): PathFormula {
  let arr = s.toArray();
  if (arr.length === 0) return PState(STop);
  if (arr.length > 1) {
    arr = arr.filter(f => !(f.kind === "state" && f.sub.kind === "top"));
    if (arr.length === 0) return PState(STop);
  }
  let result = arr[arr.length - 1]!;
  for (let i = arr.length - 2; i >= 0; i--) {
    result = PAnd(arr[i]!, result);
  }
  return result;
}

/**
 * Convert an f3 (SetOfPathFormulaSets) into a single path formula.
 * f3 = { S₁, S₂, ..., Sₖ } → (∨S₁) ∧ (∨S₂) ∧ ... ∧ (∨Sₖ)
 * Removes trivial {State(⊤)} elements if there are multiple conjuncts.
 */
function f3ToPathFormula(f3: SetOfPathFormulaSets): PathFormula {
  let arr = f3.toArray();
  if (arr.length === 0) return PState(STop);
  const singlTopKey = new PathFormulaSet([PState(STop)]).key();
  if (arr.length > 1) {
    arr = arr.filter(s => s.key() !== singlTopKey);
    if (arr.length === 0) return PState(STop);
  }
  // Each inner set becomes a disjunction
  const disjunctions = arr.map(pathSetToOr);
  let result = disjunctions[disjunctions.length - 1]!;
  for (let i = disjunctions.length - 2; i >= 0; i--) {
    result = PAnd(disjunctions[i]!, result);
  }
  return result;
}

// ============================================================
// Simplifications
// ============================================================

/**
 * Simplification 1: For Until(_f1, State(f2)) in f3, if f2 ∈ f1
 * (present-state formulas), the Until is already satisfied and can be removed.
 * Only applied when the formula does NOT contain Next.
 */
function simplification1(t: GammaTuple): SetOfPathFormulaSets {
  const result = new SetOfPathFormulaSets();
  for (const innerSet of t.f3) {
    const filtered = new PathFormulaSet();
    for (const frm of innerSet) {
      if (frm.kind === "until" && frm.right.kind === "state") {
        if (t.f1.has(frm.right.sub)) {
          // Until is satisfied at current state — skip it
          continue;
        }
      }
      filtered.add(frm);
    }
    if (filtered.size > 0) {
      result.add(filtered);
    }
  }
  return result;
}

/**
 * Simplification 2: Subsumption. If a singleton set {φ} exists in f3,
 * any multi-element set containing φ is subsumed and can be removed.
 */
function simplification2(setEns: SetOfPathFormulaSets): SetOfPathFormulaSets {
  const clauses = setEns.toArray();
  if (clauses.length <= 1) return setEns;
  const general = getOptions().clauseSubsumption;

  const keysOf = (c: PathFormulaSet) => new Set(c.toArray().map(pathKey));
  const keyed = clauses.map(c => ({ c, keys: keysOf(c), key: c.key() }));

  const toRemove = new Set<string>();
  for (const d of keyed) {
    for (const c of keyed) {
      if (c === d || toRemove.has(c.key)) continue;
      // The plain procedure only removes a clause containing a singleton's formula
      if (!general && c.keys.size !== 1) continue;
      if (c.keys.size >= d.keys.size) continue;
      let subset = true;
      for (const k of c.keys) if (!d.keys.has(k)) { subset = false; break; }
      if (subset) { toRemove.add(d.key); break; }
    }
  }

  if (toRemove.size === 0) return setEns;

  const result = new SetOfPathFormulaSets();
  for (const s of setEns) {
    if (!toRemove.has(s.key())) result.add(s);
  }
  return result;
}

/**
 * Closure under □π ⇒ π, for every Until conjunct of π: for every singleton
 * clause {□(… ∧ (ρ U σ) ∧ …)} add the clause {ρ U σ}.
 *
 * The label "□π" and the label "□π ∧ π" name the same obligation (the
 * second only makes the first step of the □ explicit), but the procedure
 * produces both: the former when π was fulfilled in the current state and
 * the latter when parts of π are still pending. Closing every label under
 * this rule makes the two coincide, so a □ formula no longer doubles the
 * tableau. Adding an implied conjunct never loses an eventuality marker;
 * only removing one could.
 */
function alwaysClosure(setEns: SetOfPathFormulaSets): SetOfPathFormulaSets {
  let result = setEns;
  let added = true;
  while (added) {
    added = false;
    for (const clause of result.toArray()) {
      if (clause.size !== 1) continue;
      const f = clause.toArray()[0]!;
      if (f.kind !== "always") continue;
      for (const conj of pathOperandsOf(f.sub)) {
        if (conj.kind !== "until") continue;
        const single = new PathFormulaSet([conj]);
        if (!result.has(single)) {
          if (result === setEns) result = setEns.clone();
          result.add(single);
          added = true;
        }
      }
    }
  }
  return result;
}

/**
 * Drop a singleton clause {ψ} when another singleton clause {φ} entails ψ by a
 * □-free entailment (see trackedEntails). The E3 check follows the residual of
 * a label's path formula, and under a □-free entailment "φ realized" implies
 * "ψ realized" clause by clause, so nothing E3 tracks is lost. Entailments
 * through □ are excluded: E3 treats □ as structurally realized and relies on
 * the explicit ◇ marker next to it.
 */
function labelAbsorption(setEns: SetOfPathFormulaSets): SetOfPathFormulaSets {
  const singles = setEns.toArray().filter(c => c.size === 1).map(c => c.toArray()[0]!);
  if (singles.length < 2) return setEns;
  const drop = new Set<string>();
  for (const psi of singles) {
    const k = pathKey(psi);
    if (drop.has(k)) continue;
    for (const phi of singles) {
      if (phi === psi || drop.has(pathKey(phi))) continue;
      if (trackedEntails(phi, psi) && !(trackedEntails(psi, phi))) { drop.add(k); break; }
    }
  }
  if (drop.size === 0) return setEns;
  const result = new SetOfPathFormulaSets();
  for (const c of setEns) {
    if (c.size === 1 && drop.has(pathKey(c.toArray()[0]!))) continue;
    result.add(c);
  }
  return result.isEmpty() ? singlPath(PState(STop)) : result;
}

/**
 * φ ⊨ ψ, restricted so that the E3 residual of ψ is realized whenever that
 * of φ is: identical formulas, ⊤, membership in a disjunction, a conjunct,
 * Untils with the same goal and entailed guard, and ○ with entailed body.
 * No rule looks through □.
 */
function trackedEntails(a: PathFormula, b: PathFormula): boolean {
  if (pathKey(a) === pathKey(b)) return true;
  if (b.kind === "state" && b.sub.kind === "top") return true;
  if (a.kind === "state" && b.kind === "state") return statePropEntails(a.sub, b.sub);
  if (a.kind === "andp" && pathOperandsOf(a).some(x => trackedEntails(x, b))) return true;
  if (b.kind === "orp" && [b.left, b.right].some(y => trackedEntails(a, y))) return true;
  if (b.kind === "andp" && [b.left, b.right].every(y => trackedEntails(a, y))) return true;
  if (a.kind === "orp" && [a.left, a.right].every(x => trackedEntails(x, b))) return true;
  if (a.kind === "until" && b.kind === "until" && pathKey(a.right) === pathKey(b.right)) {
    return trackedEntails(a.left, b.left);
  }
  if (a.kind === "next" && b.kind === "next") return trackedEntails(a.sub, b.sub);
  return false;
}

/** Propositional entailment on state formulas by structure only. */
function statePropEntails(a: StateFormula, b: StateFormula): boolean {
  if (stateKey(a) === stateKey(b)) return true;
  if (b.kind === "top" || a.kind === "bot") return true;
  if (a.kind === "and" && [a.left, a.right].some(x => statePropEntails(x, b))) return true;
  if (b.kind === "or" && [b.left, b.right].some(y => statePropEntails(a, y))) return true;
  if (b.kind === "and" && [b.left, b.right].every(y => statePropEntails(a, y))) return true;
  if (a.kind === "or" && [a.left, a.right].every(x => statePropEntails(x, b))) return true;
  return false;
}

function pathOperandsOf(f: PathFormula): PathFormula[] {
  if (f.kind !== "andp") return [f];
  return [...pathOperandsOf(f.left), ...pathOperandsOf(f.right)];
}

/**
 * Apply both simplifications to a gamma tuple.
 */
function simplifyTuple(t: GammaTuple): GammaTuple {
  let newF3: SetOfPathFormulaSets;
  if (!_containsNext) {
    newF3 = simplification1(t);
  } else {
    newF3 = t.f3;
  }

  if (newF3.isEmpty()) newF3 = singlPath(PState(STop));

  if (getOptions().alwaysClosure) newF3 = alwaysClosure(newF3);

  newF3 = simplification2(newF3);

  if (getOptions().labelAbsorption) newF3 = labelAbsorption(newF3);

  if (newF3.isEmpty()) newF3 = singlPath(PState(STop));

  return { f1: t.f1, f2: t.f2, f3: newF3 };
}

// ============================================================
// Memoization
// ============================================================

const decompositionCache = new Map<string, GammaSetCollection>();

/** Clear memoization cache (call between independent solver runs if needed) */
export function clearDecompositionCache(): void {
  decompositionCache.clear();
}

// ============================================================
// otimes (⊗) — conjunctive combination
// ============================================================

/**
 * Conjunctive combination of two gamma-decomposition results.
 * For each pair (t₁, t₂), produce:
 *   f1: t₁.f1 ∪ t₂.f1
 *   f2: t₁.f2 ∪ t₂.f2
 *   f3: t₁.f3 ∪ t₂.f3 (with identity optimization for singl_top)
 */
export function otimes(set1: GammaSetCollection, set2: GammaSetCollection): GammaSetCollection {
  const result = new GammaSetCollection();
  for (const t1 of set1) {
    for (const t2 of set2) {
      let f3: SetOfPathFormulaSets;
      if (t1.f3.equals(SINGL_TOP)) {
        f3 = t2.f3;
      } else if (t2.f3.equals(SINGL_TOP)) {
        f3 = t1.f3;
      } else {
        f3 = t1.f3.union(t2.f3);
      }
      result.add(simplifyTuple({
        f1: t1.f1.union(t2.f1),
        f2: t1.f2.union(t2.f2),
        f3,
      }));
    }
  }
  return result;
}

// ============================================================
// oplus (⊕) — disjunctive combination
// ============================================================

/**
 * Cartesian product of two SetOfPathFormulaSets.
 * Each pair (A, B) produces A ∪ B in the result.
 * This distributes disjunction into the CNF structure.
 */
function produitCartEns(set1: SetOfPathFormulaSets, set2: SetOfPathFormulaSets): SetOfPathFormulaSets {
  const result = new SetOfPathFormulaSets();
  for (const s1 of set1) {
    for (const s2 of set2) {
      result.add(s1.union(s2));
    }
  }
  return result;
}

/**
 * Disjunctive combination of two gamma-decomposition results.
 * Like otimes but uses produitCartEns for f3.
 * Skips pairs where either f3 is singl_top.
 */
export function oplus(set1: GammaSetCollection, set2: GammaSetCollection): GammaSetCollection {
  const result = new GammaSetCollection();
  for (const t1 of set1) {
    for (const t2 of set2) {
      if (!t1.f3.equals(SINGL_TOP) && !t2.f3.equals(SINGL_TOP)) {
        result.add(simplifyTuple({
          f1: t1.f1.union(t2.f1),
          f2: t1.f2.union(t2.f2),
          f3: produitCartEns(t1.f3, t2.f3),
        }));
      }
    }
  }
  return result;
}

// ============================================================
// gammaSets — core decomposition of path formulas
// ============================================================

/**
 * Decompose a path formula into a set of gamma tuples.
 *
 * This is the heart of ATL* decomposition — it recursively breaks down
 * path formulas into present-state requirements (f1), tracked path
 * formulas (f2), and next-state obligations (f3).
 *
 * Reference: TATL decomposition.ml gamma_sets
 */
/**
 * Decompose a path formula into a set of gamma tuples.
 *
 * This is the heart of ATL* decomposition — it recursively breaks down
 * path formulas into present-state requirements (f1), tracked path
 * formulas (f2), and next-state obligations (f3).
 *
 * When noOpponents is true (e.g., single-agent LTL / CTL* or grand coalition),
 * adversarial hedging via oplus (⊕) on OrP is unnecessary because the coalition
 * has no opponents whose actions it must hedge against. Skipping oplus avoids
 * combinatorial state explosion on disjunctions.
 *
 * Reference: TATL decomposition.ml gamma_sets
 */
export function gammaSets(path: PathFormula, noOpponents: boolean = false): GammaSetCollection {
  if (Date.now() > getOptions().deadline) throw new BudgetExceeded();
  // Check memoization cache
  const o = getOptions();
  const cacheKey = (noOpponents ? "no_opp:" : "opp:") +
    (o.semanticBranching ? "sb:" : "") + (o.semanticBranchingTemporal ? "sbt:" : "") + (o.clauseSubsumption ? "cs:" : "") + (o.alwaysClosure ? "ac:" : "") +
    (o.labelAbsorption ? "la:" : "") + pathKey(path);
  const cached = decompositionCache.get(cacheKey);
  if (cached) return cached;

  let result: GammaSetCollection;

  switch (path.kind) {
    case "state": {
      // State(f) → single tuple: f1={f}, f2={State(f)}, f3=singl_top
      result = new GammaSetCollection([{
        f1: new StateFormulaSet([path.sub]),
        f2: new PathFormulaSet([path]),
        f3: SINGL_TOP,
      }]);
      break;
    }

    case "next": {
      // Next(f) → single tuple: f1={⊤}, f2={State(⊤)}, f3={{f}}
      result = new GammaSetCollection([{
        f1: new StateFormulaSet([STop]),
        f2: new PathFormulaSet([PState(STop)]),
        f3: singlPath(path.sub),
      }]);
      break;
    }

    case "always": {
      const inner = path.sub;
      if (inner.kind === "state") {
        // Always(State(fs)) → {fs}, {State(fs)}, {{Always(State(fs))}}
        result = new GammaSetCollection([{
          f1: new StateFormulaSet([inner.sub]),
          f2: new PathFormulaSet([inner]),
          f3: singlPath(PAlways(inner)),
        }]);
      } else {
        // Always(fp) → otimes of:
        //   {⊤}, {fp}, {{Always(path)}}
        //   with gammaSets(fp, noOpponents)
        const carry = new GammaSetCollection([{
          f1: new StateFormulaSet([STop]),
          f2: new PathFormulaSet([inner]),
          f3: singlPath(path), // Always(fp) carried forward
        }]);
        result = otimes(carry, gammaSets(inner, noOpponents));
      }
      break;
    }

    case "until": {
      const p1 = path.left;
      const p2 = path.right;

      // tuple1: p1 holds now, Until continues
      let tuple1: GammaSetCollection;
      if (p1.kind === "state") {
        // p1 = State(fs) → simple: fs now, Until forward
        tuple1 = new GammaSetCollection([{
          f1: new StateFormulaSet([p1.sub]),
          f2: new PathFormulaSet([p1]),
          f3: singlPath(path), // Until(p1,p2) carried forward
        }]);
      } else if (p1.kind === "always") {
        // Special case: Always as left-hand of Until
        // The Always is self-sustaining, simplify continuation
        const carryAlways = new GammaSetCollection([{
          f1: new StateFormulaSet([STop]),
          f2: new PathFormulaSet([p1]),
          f3: new SetOfPathFormulaSets([
            new PathFormulaSet([p1]),               // carry Always
            new PathFormulaSet([PUntil(PState(STop), p2)]) // simplify Until LHS to ⊤
          ]),
        }]);
        tuple1 = otimes(carryAlways, gammaSets(p1, noOpponents));
      } else if (p1.kind === "next" && p1.sub.kind === "always") {
        // Special case: Next(Always(fp)) as left-hand of Until
        const fp = p1.sub;
        tuple1 = new GammaSetCollection([{
          f1: new StateFormulaSet([STop]),
          f2: new PathFormulaSet([PState(STop)]),
          f3: new SetOfPathFormulaSets([
            new PathFormulaSet([fp]),                // carry Always to next
            new PathFormulaSet([PUntil(PState(STop), p2)]) // simplify Until LHS
          ]),
        }]);
      } else {
        // General fp: otimes of carry with gammaSets(p1, noOpponents)
        const carry = new GammaSetCollection([{
          f1: new StateFormulaSet([STop]),
          f2: new PathFormulaSet([p1]),
          f3: singlPath(path), // Until(p1,p2) carried forward
        }]);
        tuple1 = otimes(carry, gammaSets(p1, noOpponents));
      }

      // tuple2: p2 holds now, Until resolved
      let tuple2: GammaSetCollection;
      if (p2.kind === "state") {
        // p2 = State(fs) → simple: fs now, no continuation
        tuple2 = new GammaSetCollection([{
          f1: new StateFormulaSet([p2.sub]),
          f2: new PathFormulaSet([p2]),
          f3: SINGL_TOP,
        }]);
      } else {
        // General p2: otimes of base with gammaSets(p2, noOpponents)
        const base = new GammaSetCollection([{
          f1: new StateFormulaSet([STop]),
          f2: new PathFormulaSet([p2]),
          f3: SINGL_TOP, // Until resolved — no continuation
        }]);
        tuple2 = otimes(base, gammaSets(p2, noOpponents));
      }

      // Until = tuple1 ∪ tuple2 (p2 now OR p1 now + continue)
      result = tuple1.union(tuple2);
      break;
    }

    case "andp": {
      // AndP(p1, p2) → otimes(γ(p1), γ(p2))
      result = otimes(gammaSets(path.left, noOpponents), gammaSets(path.right, noOpponents));
      break;
    }

    case "orp": {
      // OrP(p1, p2) → γ(p1) ∪ γ(p2) (∪ oplus(γ(p1), γ(p2)) if opponents exist)
      //
      // Semantic branching: π₁ ∨ π₂ ≡ π₁ ∨ (¬π₁ ∧ π₂). When π₁ is a
      // propositional state formula, ¬π₁ is cheap and the two branches then
      // describe disjoint sets of worlds. (Symmetrically for π₂.)
      let left = path.left;
      let right = path.right;
      const o = getOptions();
      if (o.semanticBranching) {
        // ¬π must add no eventuality: π propositional, or (when enabled)
        // e.g. π = ◇ℓ whose negation □¬ℓ is eventuality-free.
        const nl = nnfPath(PNeg(left));
        const nr = nnfPath(PNeg(right));
        const ok = (orig: PathFormula, neg: PathFormula) =>
          (orig.kind === "state" && isPropositional(orig.sub)) ||
          (o.semanticBranchingTemporal && !containsEventualityOperator(neg) && !containsNextPath(neg));
        if (ok(left, nl)) {
          right = PAndCtor(nl, right);
        } else if (ok(right, nr)) {
          left = PAndCtor(nr, left);
        }
      }
      const g1 = gammaSets(left, noOpponents);
      const g2 = gammaSets(right, noOpponents);
      const union = g1.union(g2);
      result = noOpponents ? union : union.union(oplus(g1, g2));
      break;
    }

    case "negp": {
      // NegP should not appear after NNF
      throw new Error(`gammaSets: unexpected NegP (should be eliminated by NNF)`);
    }

    default:
      throw new Error(`gammaSets: unexpected path formula kind`);
  }

  decompositionCache.set(cacheKey, result);
  return result;
}

// ============================================================
// gammaComp — top-level decomposition with coalition wrapping
// ============================================================

/**
 * A set of FormulaTuples (output of gammaComp).
 */
export class FormulaTupleSet {
  private _map: Map<string, FormulaTuple> = new Map();

  constructor(tuples?: Iterable<FormulaTuple>) {
    if (tuples) {
      for (const t of tuples) this.add(t);
    }
  }

  add(t: FormulaTuple): void {
    const key = formulaTupleKey(t);
    if (!this._map.has(key)) this._map.set(key, t);
  }

  get size(): number { return this._map.size; }

  *[Symbol.iterator](): Iterator<FormulaTuple> {
    yield* this._map.values();
  }

  toArray(): FormulaTuple[] { return [...this._map.values()]; }
}

/**
 * Decompose a coalition state formula into formula tuples.
 *
 * Takes Coal(A, π) or CoCoal(A, π) and returns a set of FormulaTuples.
 * Each tuple represents one disjunctive alternative in the decomposition.
 *
 * For each gamma tuple {f1, f2, f3} from gammaSets(π):
 *   - Convert f1 to a conjunction of state formulas
 *   - Convert f3 to a path formula (CNF → single formula)
 *   - If f3 = State(⊤): frm = conjunction(f1)
 *   - Otherwise: frm = conjunction(f1) ∧ Coal/CoCoal(A, X(State(Coal/CoCoal(A, f3))))
 *   - nextFrm = Coal/CoCoal(A, f3)
 *
 * Reference: TATL decomposition.ml gamma_comp
 */
export function gammaComp(formula: StateFormula, allAgents: Coalition): FormulaTupleSet {
  if (formula.kind !== "coal" && formula.kind !== "cocoal") {
    throw new Error("gammaComp: expected Coal or CoCoal formula");
  }

  // Set the containsNext flag (used by simplification1)
  _containsNext = containsNextState(formula);

  const la = formula.coalition;
  const pathFrm = formula.path;
  const isCoal = formula.kind === "coal";

  // When the coalition is the grand coalition (every agent in the model) it
  // completely controls the play: there is nobody to hedge against, so the
  // OrP decomposition can skip oplus. ⟨⟨Σ⟩⟩(π₁ ∨ π₂) ≡ ⟨⟨Σ⟩⟩π₁ ∨ ⟨⟨Σ⟩⟩π₂,
  // and every ⊕-tuple is subsumed by a plain tuple on a single path.
  const noOpponents = isCoal && coalitionEqual(la, allAgents);

  const setTuples = gammaSets(pathFrm, noOpponents);
  const result = new FormulaTupleSet();

  for (const t of setTuples) {
    const f1 = stateSetToAnd(t.f1);
    const f3path = f3ToPathFormula(t.f3);

    let frm: StateFormula;
    let nextFrm: StateFormula;

    if (f3path.kind === "state" && f3path.sub.kind === "top") {
      // No next-state obligation
      frm = f1;
      nextFrm = isCoal ? Coal(la, PState(STop)) : CoCoal(la, PState(STop));
    } else {
      // Wrap next-state obligation: Coal(A, X(State(Coal(A, f3))))
      const innerCoal = isCoal ? Coal(la, f3path) : CoCoal(la, f3path);
      const nextTimeFrm = isCoal
        ? Coal(la, PNext(PState(innerCoal)))
        : CoCoal(la, PNext(PState(innerCoal)));
      frm = SAnd(f1, nextTimeFrm);
      nextFrm = innerCoal;
    }

    result.add({
      frm,
      pathFrm: t.f2,
      nextFrm,
    });
  }

  return result;
}
