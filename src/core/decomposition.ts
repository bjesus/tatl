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
import { printPathAscii, printStateAscii } from "./printer.ts";

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
  // Partition into singletons and multi-element sets
  const singletons: PathFormulaSet[] = [];
  const multis: PathFormulaSet[] = [];
  for (const s of setEns) {
    if (s.size <= 1) singletons.push(s);
    else multis.push(s);
  }

  // Check each multi-element set: if any of its elements appears as a singleton, remove it
  const toRemove = new Set<string>();
  for (const multi of multis) {
    for (const frm of multi) {
      const singleton = new PathFormulaSet([frm]);
      if (singletons.some(s => s.key() === singleton.key())) {
        toRemove.add(multi.key());
        break;
      }
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

  newF3 = simplification2(newF3);

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
export function gammaSets(path: PathFormula): GammaSetCollection {
  // Check memoization cache
  const cacheKey = pathKey(path);
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
        //   with gammaSets(fp)
        const carry = new GammaSetCollection([{
          f1: new StateFormulaSet([STop]),
          f2: new PathFormulaSet([inner]),
          f3: singlPath(path), // Always(fp) carried forward
        }]);
        result = otimes(carry, gammaSets(inner));
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
        tuple1 = otimes(carryAlways, gammaSets(p1));
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
        // General fp: otimes of carry with gammaSets(p1)
        const carry = new GammaSetCollection([{
          f1: new StateFormulaSet([STop]),
          f2: new PathFormulaSet([p1]),
          f3: singlPath(path), // Until(p1,p2) carried forward
        }]);
        tuple1 = otimes(carry, gammaSets(p1));
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
        // General p2: otimes of base with gammaSets(p2)
        const base = new GammaSetCollection([{
          f1: new StateFormulaSet([STop]),
          f2: new PathFormulaSet([p2]),
          f3: SINGL_TOP, // Until resolved — no continuation
        }]);
        tuple2 = otimes(base, gammaSets(p2));
      }

      // Until = tuple1 ∪ tuple2 (p2 now OR p1 now + continue)
      result = tuple1.union(tuple2);
      break;
    }

    case "andp": {
      // AndP(p1, p2) → otimes(γ(p1), γ(p2))
      result = otimes(gammaSets(path.left), gammaSets(path.right));
      break;
    }

    case "orp": {
      // OrP(p1, p2) → γ(p1) ∪ γ(p2) ∪ oplus(γ(p1), γ(p2))
      const g1 = gammaSets(path.left);
      const g2 = gammaSets(path.right);
      result = g1.union(g2).union(oplus(g1, g2));
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
export function gammaComp(formula: StateFormula): FormulaTupleSet {
  if (formula.kind !== "coal" && formula.kind !== "cocoal") {
    throw new Error("gammaComp: expected Coal or CoCoal formula");
  }

  // Set the containsNext flag (used by simplification1)
  _containsNext = containsNextState(formula);

  const la = formula.coalition;
  const pathFrm = formula.path;
  const isCoal = formula.kind === "coal";

  const setTuples = gammaSets(pathFrm);
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
