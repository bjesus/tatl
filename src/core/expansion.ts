/**
 * Saturation (Rule SR) for ATL* formulas.
 *
 * The saturation procedure takes a set of state formulas (the label of a
 * prestate) and produces all possible sets of formula tuples — each of
 * which will become a candidate state in the pretableau.
 *
 * Three kinds of state formulas:
 *   - Primitive: Top, Bot, Prop, Neg(Prop), Coal(A, Next(State _)), CoCoal(A, Next(State _))
 *     → kept as-is in a singleton tuple
 *   - Alpha (And): product of both sub-saturations
 *   - Beta (Or): union of both sub-saturations
 *   - Gamma (Coal/CoCoal non-next): decomposed via gammaComp, then recursively saturated
 *
 * Reference: TATL construction.ml — saturation, product, rule_sr
 */

import {
  type StateFormula,
  type FormulaTuple,
  type Coalition,
  STop,
  Neg,
  SAnd,
  PathFormulaSet,
  StateFormulaSet,
  formulaTupleKey,
} from "./types.ts";
import { gammaComp } from "./decomposition.ts";
import { isPropositional, stateHasUntil } from "./formula.ts";

function isGrandCoalition(f: StateFormula, allAgents: Coalition): boolean {
  return f.kind === "coal" && f.coalition.length === allAgents.length &&
    f.coalition.every((a, i) => a === allAgents[i]);
}
import { nnfState } from "./nnf.ts";
import { getOptions } from "./options.ts";

// ============================================================
// TupleSet — a set of FormulaTuples (one candidate state)
// ============================================================

export class TupleSet {
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

  key(): string {
    const keys = [...this._map.keys()].sort();
    return "{" + keys.join(",") + "}";
  }

  union(other: TupleSet): TupleSet {
    const result = new TupleSet();
    for (const t of this) result.add(t);
    for (const t of other) result.add(t);
    return result;
  }
}

// ============================================================
// SetOfTupleSets — all candidate states from a prestate
// ============================================================

export class SetOfTupleSets {
  private _map: Map<string, TupleSet> = new Map();

  constructor(sets?: Iterable<TupleSet>) {
    if (sets) {
      for (const s of sets) this.add(s);
    }
  }

  add(s: TupleSet): void {
    const key = s.key();
    if (!this._map.has(key)) this._map.set(key, s);
  }

  get size(): number { return this._map.size; }

  isEmpty(): boolean { return this._map.size === 0; }

  *[Symbol.iterator](): Iterator<TupleSet> {
    yield* this._map.values();
  }

  toArray(): TupleSet[] { return [...this._map.values()]; }

  union(other: SetOfTupleSets): SetOfTupleSets {
    const result = new SetOfTupleSets();
    for (const s of this) result.add(s);
    for (const s of other) result.add(s);
    return result;
  }
}

// ============================================================
// product — Cartesian product of two SetOfTupleSets
// ============================================================

/**
 * Compute the Cartesian product of two sets of tuple-sets.
 * Each pair (S₁, S₂) produces S₁ ∪ S₂.
 * Empty sets are treated as identity (matching TATL behavior).
 *
 * Reference: TATL construction.ml product
 */
function product(set1: SetOfTupleSets, set2: SetOfTupleSets): SetOfTupleSets {
  // Empty acts as identity (matching TATL behavior — empty means "no formulas yet",
  // not "unsatisfiable"). Inconsistency is checked later in get_or_create_state.
  if (set1.isEmpty()) return set2;
  if (set2.isEmpty()) return set1;

  const result = new SetOfTupleSets();
  for (const s1 of set1) {
    for (const s2 of set2) {
      result.add(s1.union(s2));
    }
  }
  return result;
}

// ============================================================
// saturation — core recursive expansion of a single formula
// ============================================================

/**
 * Saturate a single state formula into a SetOfTupleSets.
 *
 * This is the recursive expansion that handles:
 * - Primitives: return singleton
 * - And: product of sub-saturations
 * - Or: union of sub-saturations
 * - Coal/CoCoal (non-next): gammaComp + recursive saturation of residuals
 *
 * Reference: TATL construction.ml saturation
 */
function saturation(formula: StateFormula, allAgents: Coalition): SetOfTupleSets {
  switch (formula.kind) {
    // Primitives — return singleton tuple in singleton set
    case "top":
    case "bot":
    case "atom":
      return new SetOfTupleSets([
        new TupleSet([{ frm: formula, pathFrm: new PathFormulaSet(), nextFrm: STop }])
      ]);

    case "neg":
      // After NNF, neg only wraps atoms → primitive
      return new SetOfTupleSets([
        new TupleSet([{ frm: formula, pathFrm: new PathFormulaSet(), nextFrm: STop }])
      ]);

    case "and":
      // Alpha: product of both sides
      return product(saturation(formula.left, allAgents), saturation(formula.right, allAgents));

    case "or": {
      // Beta: union of both sides.
      //
      // Semantic branching: φ ∨ ψ ≡ φ ∨ (¬φ ∧ ψ). When ¬φ adds no
      // eventuality (φ propositional, or a grand-coalition ◇-formula whose
      // negation is a □-formula) the second branch gets ¬φ, so the two
      // branches describe disjoint worlds instead of overlapping ones.
      let left = formula.left;
      let right = formula.right;
      const o = getOptions();
      if (o.semanticBranching) {
        const nl = nnfState(Neg(left));
        const nr = nnfState(Neg(right));
        const t = o.semanticBranchingTemporal;
        if (isPropositional(left) || (t && isGrandCoalition(left, allAgents) && !stateHasUntil(nl))) {
          right = SAnd(nl, right);
        } else if (isPropositional(right) || (t && isGrandCoalition(right, allAgents) && !stateHasUntil(nr))) {
          left = SAnd(nr, left);
        }
      }
      return saturation(left, allAgents).union(saturation(right, allAgents));
    }

    case "coal":
    case "cocoal": {
      // Check if this is a next-time formula (primitive)
      if (formula.path.kind === "next" && formula.path.sub.kind === "state") {
        return new SetOfTupleSets([
          new TupleSet([{ frm: formula, pathFrm: new PathFormulaSet(), nextFrm: STop }])
        ]);
      }

      // Gamma: decompose via gammaComp, then recursively saturate residuals
      const gammaComponents = gammaComp(formula, allAgents);
      let result = new SetOfTupleSets();

      for (const t of gammaComponents) {
        // Create a tuple with the ORIGINAL formula annotated with path/next from decomposition
        const originalTuple = new TupleSet([{
          frm: formula,
          pathFrm: t.pathFrm,
          nextFrm: t.nextFrm,
        }]);

        // Recursively saturate the state-level residual from decomposition
        const residualSaturation = saturation(t.frm, allAgents);

        // Product: the original annotated tuple × the saturated residual
        const combined = product(
          new SetOfTupleSets([originalTuple]),
          residualSaturation
        );

        result = result.union(combined);
      }

      return result;
    }
  }
}

// ============================================================
// rule_sr — the full saturation rule
// ============================================================

/**
 * Apply Rule SR: saturate a set of state formulas (prestate label)
 * into a set of tuple-sets (candidate states).
 *
 * Folds over each formula in the prestate, saturating each one
 * and combining via product (conjunction semantics).
 *
 * Reference: TATL construction.ml rule_sr
 */
export function ruleSR(formulas: StateFormulaSet, allAgents: Coalition): SetOfTupleSets {
  let result = new SetOfTupleSets();
  for (const f of formulas) {
    result = product(saturation(f, allAgents), result);
  }
  return result;
}

/**
 * Extract the state formula set from a TupleSet.
 * Collects all .frm fields into a StateFormulaSet.
 */
export function tupleSetToFormulas(ts: TupleSet): StateFormulaSet {
  const result = new StateFormulaSet();
  for (const t of ts) {
    result.add(t.frm);
  }
  return result;
}

/**
 * Extract the FormulaTuple list from a TupleSet.
 */
export function tupleSetToTuples(ts: TupleSet): FormulaTuple[] {
  return ts.toArray();
}
