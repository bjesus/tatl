/**
 * Solver options.
 *
 * Every optimisation that changes the shape of the tableau (but never the
 * verdict) sits behind a flag here, so the differential harness can run the
 * plain procedure against the optimised one on the same formulas.
 */

export interface SolverOptions {
  /**
   * Propositional and temporal simplification of the input formula before
   * construction: constants, idempotence, complementary pairs, absorption,
   * ⟨⟨A⟩⟩φ → φ for state formulas φ, and co-coalition normalisation.
   */
  simplify: boolean;
  /**
   * Lift ⟨⟨Σ⟩⟩(π₁ ∨ π₂) to ⟨⟨Σ⟩⟩π₁ ∨ ⟨⟨Σ⟩⟩π₂ when Σ is the grand coalition
   * (E distributes over ∨). Applied to LTL, CTL* and ATL* alike.
   */
  liftDisjunctions: boolean;
  /**
   * Treat ∧ and ∨ as associative and commutative when comparing formulas, so
   * (A ∧ B) ∧ C and A ∧ (B ∧ C) name the same prestate.
   */
  acKeys: boolean;
  /**
   * When branching on φ ∨ ψ with φ propositional, add ¬φ to the ψ branch so
   * the two branches describe disjoint sets of worlds.
   */
  semanticBranching: boolean;
  /**
   * Extend semantic branching to non-propositional disjuncts whose negation
   * introduces no eventuality, such as ◇ℓ (negation □¬ℓ).
   */
  semanticBranchingTemporal: boolean;
  /** Drop any next-obligation clause that is a superset of another clause. */
  clauseSubsumption: boolean;
  /**
   * Close labels under □π ⇒ π so the "eventuality just fulfilled" and
   * "eventuality pending" states of a □ formula share a label.
   */
  alwaysClosure: boolean;
  /**
   * Drop a state at creation when its universal next-time obligations
   * (⟨⟨∅⟩⟩○φ) are already patently inconsistent together, instead of building
   * its successors first and eliminating it by E2 afterwards.
   */
  earlyInconsistency: boolean;
  /**
   * In a next obligation, drop a conjunct entailed by another conjunct via a
   * □-free entailment, so the E3 check loses nothing it tracks.
   */
  labelAbsorption: boolean;
  /**
   * Abort construction (with an error) once this many pretableau nodes
   * exist. Infinity by default; the differential harness uses it to skip
   * formulas on which the plain procedure blows up.
   */
  maxNodes: number;
  /** Abort (with an error) once this timestamp (ms) has passed. Infinity by default. */
  deadline: number;
}

export const DEFAULT_OPTIONS: SolverOptions = {
  simplify: true,
  liftDisjunctions: true,
  acKeys: true,
  semanticBranching: true,
  semanticBranchingTemporal: true,
  clauseSubsumption: true,
  alwaysClosure: true,
  earlyInconsistency: true,
  labelAbsorption: true,
  maxNodes: Infinity,
  deadline: Infinity,
};

/** The plain procedure, as described in the papers, with no optimisation. */
export const PLAIN_OPTIONS: SolverOptions = {
  simplify: false,
  liftDisjunctions: false,
  acKeys: false,
  semanticBranching: false,
  semanticBranchingTemporal: false,
  clauseSubsumption: false,
  alwaysClosure: false,
  earlyInconsistency: false,
  labelAbsorption: false,
  maxNodes: Infinity,
  deadline: Infinity,
};

let current: SolverOptions = { ...DEFAULT_OPTIONS };

export function getOptions(): SolverOptions {
  return current;
}

export function setOptions(opts: Partial<SolverOptions>): void {
  current = { ...current, ...opts };
}

/** Run `fn` with the given options in force, restoring the previous ones after. */
export function withOptions<T>(opts: Partial<SolverOptions>, fn: () => T): T {
  const saved = current;
  current = { ...current, ...opts };
  try {
    return fn();
  } finally {
    current = saved;
  }
}
