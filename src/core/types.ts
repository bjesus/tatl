/**
 * Core types for the CMAEL(CD) tableau decision procedure.
 *
 * The logic CMAEL(CD) has:
 * - Atomic propositions p, q, r, ...
 * - Boolean connectives: negation (¬) and conjunction (∧)
 * - Distributed knowledge operator D_A for coalition A
 * - Common knowledge operator C_A for coalition A
 *
 * BNF: φ := p | ¬φ | (φ₁ ∧ φ₂) | D_A φ | C_A φ
 */

// An agent is just a name (string)
export type Agent = string;

// A coalition is a non-empty set of agents, represented as a sorted array for canonical form
// We use sorted arrays instead of Set for deterministic ordering and easy comparison.
export type Coalition = readonly Agent[];

// Formula AST — directly from the BNF on page 5 of the paper
export type Formula =
  | { readonly kind: "atom"; readonly name: string }
  | { readonly kind: "not"; readonly sub: Formula }
  | { readonly kind: "and"; readonly left: Formula; readonly right: Formula }
  | { readonly kind: "D"; readonly coalition: Coalition; readonly sub: Formula }
  | { readonly kind: "C"; readonly coalition: Coalition; readonly sub: Formula };

// Constructors for convenience
export function Atom(name: string): Formula {
  return { kind: "atom", name };
}

export function Not(sub: Formula): Formula {
  return { kind: "not", sub };
}

export function And(left: Formula, right: Formula): Formula {
  return { kind: "and", left, right };
}

export function D(coalition: Coalition, sub: Formula): Formula {
  return { kind: "D", coalition: normalizeCoalition(coalition), sub };
}

export function C(coalition: Coalition, sub: Formula): Formula {
  return { kind: "C", coalition: normalizeCoalition(coalition), sub };
}

// Sugar constructors
export function Or(left: Formula, right: Formula): Formula {
  return Not(And(Not(left), Not(right)));
}

export function Implies(left: Formula, right: Formula): Formula {
  return Not(And(left, Not(right)));
}

export function Ka(agent: Agent, sub: Formula): Formula {
  return D([agent], sub);
}

// Normalize a coalition to sorted, deduplicated form
export function normalizeCoalition(agents: readonly Agent[]): Coalition {
  const sorted = [...new Set(agents)].sort();
  if (sorted.length === 0) {
    throw new Error("Coalition must be non-empty");
  }
  return sorted;
}

// Check if coalition A is a subset of coalition B
export function coalitionSubset(a: Coalition, b: Coalition): boolean {
  const bSet = new Set(b);
  return a.every((agent) => bSet.has(agent));
}

// Check if coalitions A and B have non-empty intersection
export function coalitionIntersects(a: Coalition, b: Coalition): boolean {
  const bSet = new Set(b);
  return a.some((agent) => bSet.has(agent));
}

// Check if two coalitions are equal
export function coalitionEqual(a: Coalition, b: Coalition): boolean {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) {
    if (a[i] !== b[i]) return false;
  }
  return true;
}

// A FormulaSet is a set of formulas, keyed by their canonical string representation
export class FormulaSet {
  private _map: Map<string, Formula> = new Map();

  constructor(formulas?: Iterable<Formula>) {
    if (formulas) {
      for (const f of formulas) {
        this.add(f);
      }
    }
  }

  add(f: Formula): void {
    const key = formulaKey(f);
    if (!this._map.has(key)) {
      this._map.set(key, f);
    }
  }

  has(f: Formula): boolean {
    return this._map.has(formulaKey(f));
  }

  delete(f: Formula): boolean {
    return this._map.delete(formulaKey(f));
  }

  get size(): number {
    return this._map.size;
  }

  *[Symbol.iterator](): Iterator<Formula> {
    yield* this._map.values();
  }

  toArray(): Formula[] {
    return [...this._map.values()];
  }

  clone(): FormulaSet {
    const copy = new FormulaSet();
    for (const [key, formula] of this._map) {
      copy._map.set(key, formula);
    }
    return copy;
  }

  // Canonical key for this set (for comparing sets of formulas)
  key(): string {
    const keys = [...this._map.keys()].sort();
    return "{" + keys.join(",") + "}";
  }

  equals(other: FormulaSet): boolean {
    if (this.size !== other.size) return false;
    for (const key of this._map.keys()) {
      if (!other._map.has(key)) return false;
    }
    return true;
  }

  // Check if this set is a subset of another
  isSubsetOf(other: FormulaSet): boolean {
    for (const key of this._map.keys()) {
      if (!other._map.has(key)) return false;
    }
    return true;
  }

  // Union (returns new set)
  union(other: FormulaSet): FormulaSet {
    const result = this.clone();
    for (const f of other) {
      result.add(f);
    }
    return result;
  }
}

// Canonical string key for a formula (used for hashing and equality)
export function formulaKey(f: Formula): string {
  switch (f.kind) {
    case "atom":
      return f.name;
    case "not":
      return `~${formulaKey(f.sub)}`;
    case "and":
      return `(${formulaKey(f.left)}&${formulaKey(f.right)})`;
    case "D":
      return `D{${f.coalition.join(",")}}${formulaKey(f.sub)}`;
    case "C":
      return `C{${f.coalition.join(",")}}${formulaKey(f.sub)}`;
  }
}

// Check structural equality of two formulas
export function formulaEqual(a: Formula, b: Formula): boolean {
  return formulaKey(a) === formulaKey(b);
}

// --- Tableau graph types ---

export type NodeId = string;

export interface PreState {
  readonly id: NodeId;
  readonly formulas: FormulaSet;
  readonly kind: "prestate";
}

export interface State {
  readonly id: NodeId;
  readonly formulas: FormulaSet;
  readonly kind: "state";
}

// A dashed edge (search dimension): prestate → state
export interface DashedEdge {
  readonly from: NodeId; // prestate
  readonly to: NodeId; // state
}

// A solid edge (transition relation): state → prestate (pretableau) or state → state (tableau)
export interface SolidEdge {
  readonly from: NodeId;
  readonly to: NodeId;
  readonly label: Formula; // the ¬D_A φ formula that triggered this edge
}

export interface Pretableau {
  prestates: Map<NodeId, PreState>;
  states: Map<NodeId, State>;
  dashedEdges: DashedEdge[];
  solidEdges: SolidEdge[];
}

export interface Tableau {
  states: Map<NodeId, State>;
  edges: SolidEdge[];
}

// Elimination tracking — records why each state was removed in Phase 3
export type EliminationRule = "E1" | "E2";

export interface EliminationRecord {
  /** The state that was eliminated */
  stateId: NodeId;
  /** Which rule eliminated it: E1 (missing diamond successor) or E2 (unrealized eventuality) */
  rule: EliminationRule;
  /** The formula that caused elimination (diamond for E1, eventuality for E2) */
  formula: Formula;
  /** The formulas the state contained when it was eliminated */
  stateFormulas: FormulaSet;
}

export interface TableauResult {
  satisfiable: boolean;
  pretableau: Pretableau;
  initialTableau: Tableau;
  finalTableau: Tableau;
  inputFormula: Formula;
  /** Ordered list of state eliminations from Phase 3 */
  eliminations: EliminationRecord[];
}
