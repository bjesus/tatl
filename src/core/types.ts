/**
 * Core types for the ATL* tableau decision procedure.
 *
 * ATL* (full Alternating-time Temporal Logic) has two sorts of formulas:
 *
 * State formulas:
 *   φ := ⊤ | ⊥ | p | ¬φ | (φ₁ ∧ φ₂) | ⟨⟨A⟩⟩π | [[A]]π
 *
 * Path formulas:
 *   π := φ | ¬π | (π₁ ∧ π₂) | (π₁ ∨ π₂) | ○π | □π | (π₁ U π₂)
 *
 * After NNF transformation (applied at parse time), the only constructors are:
 *   State: Top | Bot | Prop | Neg(Prop) | And | Or | Coal | CoCoal
 *   Path:  State(φ) | AndP | OrP | Next | Always | Until
 *
 * References:
 * - Goranko & Shkatov (2009): ATL tableau procedure
 * - Cerrito, David & Goranko (2014): ATL+ extension
 * - David (2015): Full ATL* extension
 * - TATL OCaml implementation: github.com/theoremprover-museum/TATL
 */

// An agent is just a name (string). Both letters and numbers are allowed.
export type Agent = string;

// A coalition is a set of agents, represented as a sorted array for canonical form.
// Empty coalitions are allowed in ATL*.
export type Coalition = readonly Agent[];

// ============================================================
// Two-sorted Formula AST
// ============================================================

/**
 * State formulas — evaluated at a state in a concurrent game structure.
 *
 * After NNF, negation only appears directly on atoms (Neg(Prop _)).
 * Before NNF, Neg can wrap any state formula.
 */
export type StateFormula =
  | { readonly kind: "top" }
  | { readonly kind: "bot" }
  | { readonly kind: "atom"; readonly name: string }
  | { readonly kind: "neg"; readonly sub: StateFormula }
  | { readonly kind: "and"; readonly left: StateFormula; readonly right: StateFormula }
  | { readonly kind: "or"; readonly left: StateFormula; readonly right: StateFormula }
  | { readonly kind: "coal"; readonly coalition: Coalition; readonly path: PathFormula }
  | { readonly kind: "cocoal"; readonly coalition: Coalition; readonly path: PathFormula };

/**
 * Path formulas — evaluated along a path (infinite sequence of states).
 *
 * After NNF, no NegP/ImplyP/EquivP/Release/Event remain.
 * State(φ) lifts a state formula into the path sort.
 */
export type PathFormula =
  | { readonly kind: "state"; readonly sub: StateFormula }
  | { readonly kind: "negp"; readonly sub: PathFormula }
  | { readonly kind: "andp"; readonly left: PathFormula; readonly right: PathFormula }
  | { readonly kind: "orp"; readonly left: PathFormula; readonly right: PathFormula }
  | { readonly kind: "next"; readonly sub: PathFormula }
  | { readonly kind: "always"; readonly sub: PathFormula }
  | { readonly kind: "until"; readonly left: PathFormula; readonly right: PathFormula };

// ============================================================
// Constructors — State formulas
// ============================================================

export const STop: StateFormula = { kind: "top" };
export const SBot: StateFormula = { kind: "bot" };

export function Atom(name: string): StateFormula {
  return { kind: "atom", name };
}

export function Neg(sub: StateFormula): StateFormula {
  return { kind: "neg", sub };
}

export function SAnd(left: StateFormula, right: StateFormula): StateFormula {
  return { kind: "and", left, right };
}

export function SOr(left: StateFormula, right: StateFormula): StateFormula {
  return { kind: "or", left, right };
}

export function Coal(coalition: Coalition, path: PathFormula): StateFormula {
  return { kind: "coal", coalition: normalizeCoalition(coalition), path };
}

export function CoCoal(coalition: Coalition, path: PathFormula): StateFormula {
  return { kind: "cocoal", coalition: normalizeCoalition(coalition), path };
}

// Sugar constructors (state level) — eliminated by NNF
export function SImplies(left: StateFormula, right: StateFormula): StateFormula {
  return SOr(Neg(left), right);
}

// ============================================================
// Constructors — Path formulas
// ============================================================

export function PState(sub: StateFormula): PathFormula {
  return { kind: "state", sub };
}

export function PNeg(sub: PathFormula): PathFormula {
  return { kind: "negp", sub };
}

export function PAnd(left: PathFormula, right: PathFormula): PathFormula {
  return { kind: "andp", left, right };
}

export function POr(left: PathFormula, right: PathFormula): PathFormula {
  return { kind: "orp", left, right };
}

export function PNext(sub: PathFormula): PathFormula {
  return { kind: "next", sub };
}

export function PAlways(sub: PathFormula): PathFormula {
  return { kind: "always", sub };
}

export function PUntil(left: PathFormula, right: PathFormula): PathFormula {
  return { kind: "until", left, right };
}

/** ◇π = ⊤ U π */
export function PEvent(sub: PathFormula): PathFormula {
  return PUntil(PState(STop), sub);
}

// ============================================================
// Convenience: ATL-style constructors (coalition fused with temporal)
// These create Coal(A, PNext/PAlways/PUntil(PState(...), ...))
// ============================================================

/** ⟨⟨A⟩⟩○φ */
export function CoalNext(coalition: Coalition, sub: StateFormula): StateFormula {
  return Coal(coalition, PNext(PState(sub)));
}

/** ⟨⟨A⟩⟩□φ */
export function CoalAlways(coalition: Coalition, sub: StateFormula): StateFormula {
  return Coal(coalition, PAlways(PState(sub)));
}

/** ⟨⟨A⟩⟩(φ U ψ) */
export function CoalUntil(coalition: Coalition, left: StateFormula, right: StateFormula): StateFormula {
  return Coal(coalition, PUntil(PState(left), PState(right)));
}

/** ⟨⟨A⟩⟩◇φ */
export function CoalEvent(coalition: Coalition, sub: StateFormula): StateFormula {
  return Coal(coalition, PEvent(PState(sub)));
}

// ============================================================
// Coalition utilities
// ============================================================

export function normalizeCoalition(agents: readonly Agent[]): Coalition {
  return [...new Set(agents)].sort();
}

export function coalitionSubset(a: Coalition, b: Coalition): boolean {
  const bSet = new Set(b);
  return a.every((agent) => bSet.has(agent));
}

export function coalitionIntersects(a: Coalition, b: Coalition): boolean {
  const bSet = new Set(b);
  return a.some((agent) => bSet.has(agent));
}

export function coalitionEqual(a: Coalition, b: Coalition): boolean {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) {
    if (a[i] !== b[i]) return false;
  }
  return true;
}

export function coalitionComplement(a: Coalition, allAgents: Coalition): Coalition {
  const aSet = new Set(a);
  return allAgents.filter((agent) => !aSet.has(agent));
}

// ============================================================
// Canonical keys (for hashing and equality)
// ============================================================

export function stateKey(f: StateFormula): string {
  switch (f.kind) {
    case "top": return "T";
    case "bot": return "F";
    case "atom": return f.name;
    case "neg": return `~${stateKey(f.sub)}`;
    case "and": return `(${stateKey(f.left)}&${stateKey(f.right)})`;
    case "or": return `(${stateKey(f.left)}|${stateKey(f.right)})`;
    case "coal": return `<<${f.coalition.join(",")}>>@${pathKey(f.path)}`;
    case "cocoal": return `[[${f.coalition.join(",")}]]@${pathKey(f.path)}`;
  }
}

export function pathKey(f: PathFormula): string {
  switch (f.kind) {
    case "state": return `S{${stateKey(f.sub)}}`;
    case "negp": return `~P${pathKey(f.sub)}`;
    case "andp": return `(${pathKey(f.left)}&P${pathKey(f.right)})`;
    case "orp": return `(${pathKey(f.left)}|P${pathKey(f.right)})`;
    case "next": return `X${pathKey(f.sub)}`;
    case "always": return `G${pathKey(f.sub)}`;
    case "until": return `(${pathKey(f.left)}U${pathKey(f.right)})`;
  }
}

export function stateEqual(a: StateFormula, b: StateFormula): boolean {
  return stateKey(a) === stateKey(b);
}

export function pathEqual(a: PathFormula, b: PathFormula): boolean {
  return pathKey(a) === pathKey(b);
}

// ============================================================
// Formula sets (keyed by canonical string)
// ============================================================

/** A set of state formulas */
export class StateFormulaSet {
  private _map: Map<string, StateFormula> = new Map();

  constructor(formulas?: Iterable<StateFormula>) {
    if (formulas) {
      for (const f of formulas) this.add(f);
    }
  }

  add(f: StateFormula): void {
    const key = stateKey(f);
    if (!this._map.has(key)) this._map.set(key, f);
  }

  has(f: StateFormula): boolean {
    return this._map.has(stateKey(f));
  }

  delete(f: StateFormula): boolean {
    return this._map.delete(stateKey(f));
  }

  get size(): number { return this._map.size; }

  *[Symbol.iterator](): Iterator<StateFormula> {
    yield* this._map.values();
  }

  toArray(): StateFormula[] { return [...this._map.values()]; }

  clone(): StateFormulaSet {
    const copy = new StateFormulaSet();
    for (const [key, formula] of this._map) copy._map.set(key, formula);
    return copy;
  }

  key(): string {
    const keys = [...this._map.keys()].sort();
    return "{" + keys.join(",") + "}";
  }

  equals(other: StateFormulaSet): boolean {
    if (this.size !== other.size) return false;
    for (const key of this._map.keys()) {
      if (!other._map.has(key)) return false;
    }
    return true;
  }

  isSubsetOf(other: StateFormulaSet): boolean {
    for (const key of this._map.keys()) {
      if (!other._map.has(key)) return false;
    }
    return true;
  }

  union(other: StateFormulaSet): StateFormulaSet {
    const result = this.clone();
    for (const f of other) result.add(f);
    return result;
  }
}

/** A set of path formulas */
export class PathFormulaSet {
  private _map: Map<string, PathFormula> = new Map();

  constructor(formulas?: Iterable<PathFormula>) {
    if (formulas) {
      for (const f of formulas) this.add(f);
    }
  }

  add(f: PathFormula): void {
    const key = pathKey(f);
    if (!this._map.has(key)) this._map.set(key, f);
  }

  has(f: PathFormula): boolean {
    return this._map.has(pathKey(f));
  }

  delete(f: PathFormula): boolean {
    return this._map.delete(pathKey(f));
  }

  get size(): number { return this._map.size; }

  *[Symbol.iterator](): Iterator<PathFormula> {
    yield* this._map.values();
  }

  toArray(): PathFormula[] { return [...this._map.values()]; }

  clone(): PathFormulaSet {
    const copy = new PathFormulaSet();
    for (const [key, formula] of this._map) copy._map.set(key, formula);
    return copy;
  }

  key(): string {
    const keys = [...this._map.keys()].sort();
    return "{" + keys.join(",") + "}";
  }

  equals(other: PathFormulaSet): boolean {
    if (this.size !== other.size) return false;
    for (const key of this._map.keys()) {
      if (!other._map.has(key)) return false;
    }
    return true;
  }

  isEmpty(): boolean { return this._map.size === 0; }

  union(other: PathFormulaSet): PathFormulaSet {
    const result = this.clone();
    for (const f of other) result.add(f);
    return result;
  }
}

// ============================================================
// Formula tuple — tracks a formula with its eventuality context
// ============================================================

/**
 * A formula tuple tracks a state formula along with the path formula context
 * needed for eventuality checking in ATL*.
 *
 * - frm: the state formula in the current state
 * - pathFrm: set of path formulas being tracked (for immediate realizability)
 * - nextFrm: the formula that continues at successors (wrapped in a coalition)
 *
 * In plain ATL, pathFrm is trivial. In ATL*, it tracks the complex path
 * formula structure for residual-based eventuality checking.
 */
export interface FormulaTuple {
  readonly frm: StateFormula;
  readonly pathFrm: PathFormulaSet;
  readonly nextFrm: StateFormula;
}

export function formulaTupleKey(t: FormulaTuple): string {
  return `<${stateKey(t.frm)},${t.pathFrm.key()},${stateKey(t.nextFrm)}>`;
}

// ============================================================
// Move vector types
// ============================================================

/**
 * A MoveVector is a tuple of integers, one per agent (in the order of allAgents).
 * Each integer represents which action that agent plays.
 * Range of each component is 0..k-1 where k depends on the
 * number of next-time formulas (positive + negative).
 */
export type MoveVector = readonly number[];

// ============================================================
// Tableau graph types
// ============================================================

export type NodeId = string;

export interface PreState {
  readonly id: NodeId;
  readonly formulas: StateFormulaSet;
  readonly tuples: FormulaTuple[];
  readonly kind: "prestate";
}

export interface State {
  readonly id: NodeId;
  readonly formulas: StateFormulaSet;
  readonly tuples: FormulaTuple[];
  readonly kind: "state";
}

export interface DashedEdge {
  readonly from: NodeId; // prestate
  readonly to: NodeId;   // state
}

export interface SolidEdge {
  readonly from: NodeId;
  readonly to: NodeId;
  readonly label: MoveVector;
  readonly viaPrestate?: NodeId;
}

export interface Pretableau {
  prestates: Map<NodeId, PreState>;
  states: Map<NodeId, State>;
  dashedEdges: DashedEdge[];
  solidEdges: SolidEdge[];
  allAgents: Coalition;
}

export interface Tableau {
  states: Map<NodeId, State>;
  edges: SolidEdge[];
  allAgents: Coalition;
}

export type EliminationRule = "E1" | "E2" | "E3";

export interface EliminationRecord {
  stateId: NodeId;
  rule: EliminationRule;
  formula: StateFormula;
  stateFormulas: StateFormulaSet;
}

export interface TableauResult {
  satisfiable: boolean;
  pretableau: Pretableau;
  initialTableau: Tableau;
  finalTableau: Tableau;
  inputFormula: StateFormula;
  allAgents: Coalition;
  eliminations: EliminationRecord[];
}
