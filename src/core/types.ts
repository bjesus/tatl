/**
 * Core types for the ATL tableau decision procedure.
 *
 * ATL (Alternating-time Temporal Logic) has:
 * - Atomic propositions p, q, r, ...
 * - Boolean connectives: negation (¬) and conjunction (∧)
 * - Coalition next:   ⟨⟨A⟩⟩○ϕ  (coalition A can enforce ϕ at the next step)
 * - Coalition always: ⟨⟨A⟩⟩□ϕ  (coalition A can enforce ϕ forever)
 * - Coalition until:  ⟨⟨A⟩⟩ϕUψ (coalition A can enforce ϕ until ψ)
 *
 * BNF: ϕ := p | ¬ϕ | (ϕ₁ ∧ ϕ₂) | ⟨⟨A⟩⟩○ϕ | ⟨⟨A⟩⟩□ϕ | ⟨⟨A⟩⟩ϕ₁Uϕ₂
 *
 * Reference: Goranko & Shkatov 2009, Section 2
 */

// An agent is just a name (string, lowercase)
export type Agent = string;

// A coalition is a set of agents, represented as a sorted array for canonical form.
// Unlike CMAEL(CD), coalitions CAN be empty (the empty coalition ⟨⟨∅⟩⟩).
export type Coalition = readonly Agent[];

// Formula AST — directly from the BNF
export type Formula =
  | { readonly kind: "atom"; readonly name: string }
  | { readonly kind: "not"; readonly sub: Formula }
  | { readonly kind: "and"; readonly left: Formula; readonly right: Formula }
  | { readonly kind: "next"; readonly coalition: Coalition; readonly sub: Formula }
  | { readonly kind: "always"; readonly coalition: Coalition; readonly sub: Formula }
  | { readonly kind: "until"; readonly coalition: Coalition; readonly left: Formula; readonly right: Formula };

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

export function Next(coalition: Coalition, sub: Formula): Formula {
  return { kind: "next", coalition: normalizeCoalition(coalition), sub };
}

export function Always(coalition: Coalition, sub: Formula): Formula {
  return { kind: "always", coalition: normalizeCoalition(coalition), sub };
}

export function Until(coalition: Coalition, left: Formula, right: Formula): Formula {
  return { kind: "until", coalition: normalizeCoalition(coalition), left, right };
}

// Sugar constructors

export function Or(left: Formula, right: Formula): Formula {
  return Not(And(Not(left), Not(right)));
}

export function Implies(left: Formula, right: Formula): Formula {
  return Not(And(left, Not(right)));
}

/** ⟨⟨A⟩⟩◇ϕ = ⟨⟨A⟩⟩⊤Uϕ — coalition A can enforce eventually ϕ */
export function Eventually(coalition: Coalition, sub: Formula): Formula {
  return Until(coalition, Atom("_top"), sub);
}

// Top and Bottom (useful internally)
export const Top: Formula = Atom("_top");
export const Bottom: Formula = Not(Top);

// Normalize a coalition to sorted, deduplicated form.
// Empty coalitions are allowed in ATL.
export function normalizeCoalition(agents: readonly Agent[]): Coalition {
  return [...new Set(agents)].sort();
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

// Compute the complement of coalition A with respect to the full agent set Σ
export function coalitionComplement(a: Coalition, allAgents: Coalition): Coalition {
  const aSet = new Set(a);
  return allAgents.filter((agent) => !aSet.has(agent));
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
    case "next":
      return `<<${f.coalition.join(",")}>>X${formulaKey(f.sub)}`;
    case "always":
      return `<<${f.coalition.join(",")}>>G${formulaKey(f.sub)}`;
    case "until":
      return `<<${f.coalition.join(",")}>>U(${formulaKey(f.left)},${formulaKey(f.right)})`;
  }
}

// Check structural equality of two formulas
export function formulaEqual(a: Formula, b: Formula): boolean {
  return formulaKey(a) === formulaKey(b);
}

// --- Move vector types ---

/**
 * A MoveVector is a tuple of integers, one per agent (in the order of allAgents).
 * Each integer represents which action that agent plays.
 * For ATL, the range of each component is 0..k-1 where k depends on the
 * number of next-time formulas (positive + negative).
 */
export type MoveVector = readonly number[];

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
// In ATL, labels are move vectors (tuples of agent actions) instead of formulas.
export interface SolidEdge {
  readonly from: NodeId;
  readonly to: NodeId;
  readonly label: MoveVector; // the move vector that triggered this edge
}

export interface Pretableau {
  prestates: Map<NodeId, PreState>;
  states: Map<NodeId, State>;
  dashedEdges: DashedEdge[];
  solidEdges: SolidEdge[];
  /** The ordered list of all agents (determines move vector indexing) */
  allAgents: Coalition;
}

export interface Tableau {
  states: Map<NodeId, State>;
  edges: SolidEdge[];
  /** The ordered list of all agents (determines move vector indexing) */
  allAgents: Coalition;
}

// Elimination tracking — records why each state was removed in Phase 3
export type EliminationRule = "E1" | "E2" | "E3";

export interface EliminationRecord {
  /** The state that was eliminated */
  stateId: NodeId;
  /** Which rule eliminated it:
   *  E1 (patently inconsistent / no matching state)
   *  E2 (missing next-time successor)
   *  E3 (unrealized eventuality) */
  rule: EliminationRule;
  /** The formula that caused elimination */
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
  /** The ordered list of all agents */
  allAgents: Coalition;
  /** Ordered list of state eliminations from Phase 3 */
  eliminations: EliminationRecord[];
}
