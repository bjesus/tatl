/**
 * Main tableau procedure for ATL* satisfiability checking.
 *
 * Three phases:
 * 1. Construction phase: Build pretableau using rules (SR) and (Next)
 * 2. Prestate elimination phase: Remove prestates to get initial tableau
 * 3. State elimination phase: Remove bad states (E2: missing successors,
 *    E3: unrealized eventualities via whatfalse residuals)
 *
 * References:
 * - Goranko & Shkatov 2009: ATL tableau (Section 4)
 * - Cerrito, David & Goranko 2014: ATL+ extension
 * - David 2015: Full ATL* extension
 * - TATL OCaml: vertex_state.ml, construction.ml, elimination_star.ml
 */

import {
  type StateFormula,
  type PathFormula,
  type Coalition,
  type Agent,
  type FormulaTuple,
  type MoveVector,
  type NodeId,
  type PreState,
  type State,
  type DashedEdge,
  type SolidEdge,
  type Pretableau,
  type Tableau,
  type TableauResult,
  type EliminationRecord,
  STop,
  Coal,
  CoCoal,
  PNext,
  PState,
  StateFormulaSet,
  PathFormulaSet,
  stateKey,
  pathKey,
  coalitionEqual,
  normalizeCoalition,
  coalitionComplement,
} from "./types.ts";
import { ruleSR, tupleSetToFormulas, tupleSetToTuples, type TupleSet } from "./expansion.ts";
import {
  isPatentlyInconsistent,
  isPatentlyInconsistentTuples,
  isEventuality,
  isEnforceableNext,
  isUnavoidableNext,
  isNextTime,
  nextTimeInner,
  agentsInStateSet,
} from "./formula.ts";
import { clearDecompositionCache } from "./decomposition.ts";

// ============================================================
// Node ID generation
// ============================================================

let nodeCounter = 0;

function freshNodeId(prefix: string): NodeId {
  return `${prefix}${nodeCounter++}`;
}

function resetNodeCounter(): void {
  nodeCounter = 0;
}

// ============================================================
// Main entry point
// ============================================================

/**
 * Run the tableau procedure on a state formula.
 *
 * @param theta - The input formula to test for satisfiability
 * @returns TableauResult with all phases recorded
 */
export function runTableau(
  theta: StateFormula,
  onProgress?: (stage: string) => void
): TableauResult {
  resetNodeCounter();
  clearDecompositionCache();

  // Compute all agents from the formula (tight satisfiability)
  const allAgents = normalizeCoalition([...agentsInStateSet(new StateFormulaSet([theta]))]);

  // Phase 1: Construction
  if (onProgress) onProgress("Phase 1: Construction");
  const pretableau = constructionPhase(theta, allAgents);

  // Phase 2: Prestate elimination
  if (onProgress) onProgress("Phase 2: Prestate Elimination");
  const initialTableau = prestateEliminationPhase(pretableau, allAgents);

  // Phase 3: State elimination
  if (onProgress) onProgress("Phase 3: State Elimination");
  const { tableau: finalTableau, eliminations } = stateEliminationPhase(initialTableau, allAgents);

  // Check if open: does any surviving state contain theta?
  if (onProgress) onProgress("Checking Satisfiability");
  let satisfiable = false;

  // Find the initial prestate's successor states
  const initialPrestateId = "p0"; // We create the initial prestate as p0
  // Get initial states (those reachable from the initial prestate via dashed edges)
  const initialStateIds = new Set<NodeId>();
  for (const edge of pretableau.dashedEdges) {
    if (edge.from === initialPrestateId) {
      initialStateIds.add(edge.to);
    }
  }

  // Check if any initial state survives
  for (const stateId of initialStateIds) {
    if (finalTableau.states.has(stateId)) {
      satisfiable = true;
      break;
    }
  }

  return {
    satisfiable,
    pretableau,
    initialTableau,
    finalTableau,
    inputFormula: theta,
    allAgents,
    eliminations,
  };
}

// ============================================================
// Phase 1: Construction Phase
// ============================================================

/**
 * Construction phase: builds the pretableau.
 *
 * Starts with a single prestate {theta}, then alternates (SR) and (Next)
 * until no new prestates or states are created.
 *
 * Reference: TATL vertex_state.ml — construct_state / construct_pre
 */
function constructionPhase(
  theta: StateFormula,
  allAgents: Coalition
): Pretableau {
  const pretableau: Pretableau = {
    prestates: new Map(),
    states: new Map(),
    dashedEdges: [],
    solidEdges: [],
    allAgents,
  };

  // Maps from formula set key -> node ID for reuse
  const prestateIndex = new Map<string, NodeId>();
  const stateIndex = new Map<string, NodeId>();

  // Create initial prestate {theta}
  const initialSet = new StateFormulaSet([theta]);
  const initialId = getOrCreatePrestate(pretableau, prestateIndex, initialSet);

  // BFS construction loop (matching TATL's construct_state / construct_pre)
  let prestatesToExpand: NodeId[] = [initialId];

  while (prestatesToExpand.length > 0) {
    // cons_from_pre: Apply (SR) to pending prestates -> get new states
    const newStates = consFromPre(pretableau, stateIndex, prestatesToExpand, allAgents);
    prestatesToExpand = [];

    if (newStates.length === 0) break;

    // cons_from_states: Apply (Next) to new states -> get new prestates
    const newPrestates = consFromStates(pretableau, prestateIndex, newStates, allAgents);

    if (newPrestates.length === 0) break;

    prestatesToExpand = newPrestates;
  }

  return pretableau;
}

/**
 * Apply Rule SR to a list of prestates, creating states.
 * Returns IDs of newly created states.
 *
 * Reference: TATL vertex_state.ml — cons_from_pre
 */
function consFromPre(
  pretableau: Pretableau,
  stateIndex: Map<string, NodeId>,
  prestateIds: NodeId[],
  allAgents: Coalition
): NodeId[] {
  const newStateIds: NodeId[] = [];

  for (const psId of prestateIds) {
    const ps = pretableau.prestates.get(psId)!;

    // Apply Rule SR to get sets of formula tuples
    const tupleSets = ruleSR(ps.formulas);

    for (const tupleSet of tupleSets) {
      // Extract detail: formulas and eventualities from tuples
      const { formulas: ensFrm, eventualities: lstEvent } = getDetail(tupleSet);

      // Remove Top if formula set has >1 element (matching TATL treat_top)
      const treated = treatTop(ensFrm);

      // Get or create state
      const { id: stateId, isNew } = getOrCreateState(
        pretableau, stateIndex, treated, lstEvent, allAgents
      );

      if (stateId === null) {
        // State was inconsistent — skip
        continue;
      }

      // Add dashed edge: prestate -> state
      pretableau.dashedEdges.push({ from: psId, to: stateId });

      if (isNew) {
        newStateIds.push(stateId);
      }
    }
  }

  return newStateIds;
}

/**
 * Apply Rule Next to a list of states, creating successor prestates.
 * Returns IDs of newly created prestates.
 *
 * Reference: TATL vertex_state.ml — cons_from_states
 */
function consFromStates(
  pretableau: Pretableau,
  prestateIndex: Map<string, NodeId>,
  stateIds: NodeId[],
  allAgents: Coalition
): NodeId[] {
  const newPrestateIds: NodeId[] = [];

  for (const stId of stateIds) {
    const state = pretableau.states.get(stId)!;

    // get_formulae_next_rule: compute successor formula sets + move vectors
    const successors = getFormulaeNextRule(state, allAgents);

    for (const { formulas: ensFrm, moveVecs } of successors) {
      const { id: psId, isNew } = getOrCreatePrestateChecked(
        pretableau, prestateIndex, ensFrm
      );

      // Add one solid edge per move vector: state ->[mv] prestate
      // (TATL stores a Movecs.t on each edge; we store individual edges)
      for (const mv of moveVecs) {
        pretableau.solidEdges.push({
          from: stId,
          to: psId,
          label: mv,
        });
      }

      if (isNew) {
        newPrestateIds.push(psId);
      }
    }
  }

  return newPrestateIds;
}

/**
 * Extract formulas and eventualities from a TupleSet.
 * 
 * Reference: TATL vertex_state.ml — get_detail
 */
function getDetail(tupleSet: TupleSet): {
  formulas: StateFormulaSet;
  eventualities: FormulaTuple[];
} {
  const formulas = new StateFormulaSet();
  const eventualities: FormulaTuple[] = [];

  for (const tuple of tupleSet) {
    formulas.add(tuple.frm);
    if (isEventuality(tuple.frm)) {
      eventualities.push(tuple);
    }
  }

  return { formulas, eventualities };
}

/**
 * Remove Top from a formula set if it has more than one element.
 *
 * Reference: TATL vertex_state.ml — treat_top
 */
function treatTop(fs: StateFormulaSet): StateFormulaSet {
  if (fs.size > 1 && fs.has(STop)) {
    const result = fs.clone();
    result.delete(STop);
    return result;
  }
  return fs;
}

/**
 * Get or create a state vertex.
 * If the formula set is inconsistent, returns null.
 * If the state already exists, returns it without creating a new one.
 * States with no next-time formulas get a synthetic Coal(allAgents, Next(State(Top))) added.
 *
 * Reference: TATL vertex_state.ml — get_or_create_state
 */
function getOrCreateState(
  pretableau: Pretableau,
  stateIndex: Map<string, NodeId>,
  formulas: StateFormulaSet,
  eventualities: FormulaTuple[],
  allAgents: Coalition
): { id: NodeId | null; isNew: boolean } {
  const key = formulas.key();

  // Already exists?
  if (stateIndex.has(key)) {
    return { id: stateIndex.get(key)!, isNew: false };
  }

  // Inconsistency check
  if (isPatentlyInconsistent(formulas)) {
    return { id: null, isNew: false };
  }

  // Classify next-time formulas (three categories)
  const { enforceable, properUnavoidable, agentsUnavoidable } =
    classifyNextTime(formulas, allAgents);

  const nbrPos = enforceable.length;
  const nbrNeg = properUnavoidable.length;
  const nbrAgents = agentsUnavoidable.length;

  let stateFormulas: StateFormulaSet;
  let stateEnforceable: Array<[number, StateFormula]>;
  let stateProperUnavoidable: Array<[number, StateFormula]>;
  let stateAgentsUnavoidable: StateFormula[];
  let moveVecCount: number;
  let nbPos: number;
  let nbNeg: number;

  if (nbrPos + nbrNeg + nbrAgents === 0) {
    // No next-time formulas: inject synthetic Coal(allAgents, Next(State(Top)))
    // Matching TATL: Coal(!ag_all, Next(State(Top)))
    const syntheticNext = Coal(allAgents, PNext(PState(STop)));
    stateFormulas = formulas.clone();
    stateFormulas.add(syntheticNext);
    stateEnforceable = [[0, syntheticNext]];
    stateProperUnavoidable = [];
    stateAgentsUnavoidable = [];
    moveVecCount = 1;
    nbPos = 1;
    nbNeg = 0;
  } else {
    stateFormulas = formulas;
    stateEnforceable = enforceable.map((f, i) => [i, f]);
    stateProperUnavoidable = properUnavoidable.map((f, i) => [i, f]);
    stateAgentsUnavoidable = agentsUnavoidable;
    moveVecCount = Math.max(nbrPos + nbrNeg, 1);
    nbPos = nbrPos;
    nbNeg = nbrNeg;
  }

  const stateId = freshNodeId("s");
  const state: State = {
    id: stateId,
    formulas: stateFormulas,
    tuples: eventualities,
    kind: "state",
    // Store next-time classification for the Next rule
    _nextPos: stateEnforceable,
    _nextNeg: stateProperUnavoidable,
    _nextAgents: stateAgentsUnavoidable,
    _nbPos: nbPos,
    _nbNeg: nbNeg,
    _moveVecCount: moveVecCount,
  } as State & StateNextInfo;

  pretableau.states.set(stateId, state);
  stateIndex.set(key, stateId);

  return { id: stateId, isNew: true };
}

/**
 * Get or create a prestate vertex.
 *
 * Reference: TATL vertex_state.ml — get_or_create_prestate
 */
function getOrCreatePrestate(
  pretableau: Pretableau,
  prestateIndex: Map<string, NodeId>,
  formulas: StateFormulaSet
): NodeId {
  const key = formulas.key();
  if (prestateIndex.has(key)) {
    return prestateIndex.get(key)!;
  }
  const id = freshNodeId("p");
  const ps: PreState = { id, formulas, tuples: [], kind: "prestate" };
  pretableau.prestates.set(id, ps);
  prestateIndex.set(key, id);
  return id;
}

function getOrCreatePrestateChecked(
  pretableau: Pretableau,
  prestateIndex: Map<string, NodeId>,
  formulas: StateFormulaSet
): { id: NodeId; isNew: boolean } {
  const key = formulas.key();
  if (prestateIndex.has(key)) {
    return { id: prestateIndex.get(key)!, isNew: false };
  }
  const id = freshNodeId("p");
  const ps: PreState = { id, formulas, tuples: [], kind: "prestate" };
  pretableau.prestates.set(id, ps);
  prestateIndex.set(key, id);
  return { id, isNew: true };
}

// ============================================================
// Next-time formula classification
// ============================================================

/** Internal state info stored alongside the State node */
interface StateNextInfo {
  _nextPos: Array<[number, StateFormula]>;      // numbered enforceable
  _nextNeg: Array<[number, StateFormula]>;      // numbered proper unavoidable
  _nextAgents: StateFormula[];                   // agents unavoidable
  _nbPos: number;
  _nbNeg: number;
  _moveVecCount: number;
}

/**
 * Classify next-time formulas in a state into three categories:
 *
 * 1. Enforceable: Coal(A, Next(State(f)))
 * 2. Proper unavoidable: CoCoal(A, Next(State(f))) where A != allAgents
 * 3. Agents unavoidable: CoCoal(allAgents, Next(State(f)))
 *
 * Reference: TATL construction.ml — create_lst_nexttime
 */
function classifyNextTime(
  formulas: StateFormulaSet,
  allAgents: Coalition
): {
  enforceable: StateFormula[];
  properUnavoidable: StateFormula[];
  agentsUnavoidable: StateFormula[];
} {
  const enforceable: StateFormula[] = [];
  const properUnavoidable: StateFormula[] = [];
  const agentsUnavoidable: StateFormula[] = [];

  for (const f of formulas) {
    if (isEnforceableNext(f)) {
      enforceable.push(f);
    } else if (isUnavoidableNext(f)) {
      if (f.kind === "cocoal" && coalitionEqual(f.coalition, allAgents)) {
        agentsUnavoidable.push(f);
      } else {
        properUnavoidable.push(f);
      }
    }
  }

  return { enforceable, properUnavoidable, agentsUnavoidable };
}

// ============================================================
// Next Rule — compute successor formula sets + move vectors
// ============================================================

/**
 * Compute N(sigma): set of agents playing negative moves (sigma_i >= nbPos).
 *
 * Reference: TATL construction.ml — function_n_sigma
 */
function functionNSigma(
  movec: Array<[Agent, number]>,
  nbPos: number
): Set<Agent> {
  const result = new Set<Agent>();
  for (const [agent, move] of movec) {
    if (move >= nbPos) {
      result.add(agent);
    }
  }
  return result;
}

/**
 * Compute Co(sigma): the negative move index.
 *
 * Reference: TATL construction.ml — function_co_sigma
 */
function functionCoSigma(
  movec: Array<[Agent, number]>,
  nbPos: number,
  nbNeg: number
): number {
  const nAgents = functionNSigma(movec, nbPos);
  let sum = 0;
  for (const [agent, move] of movec) {
    if (nAgents.has(agent)) {
      sum += move - nbPos;
    }
  }
  return sum % nbNeg;
}

/**
 * Compute Gamma(sigma): the successor formula set for a given move vector.
 *
 * Reference: TATL construction.ml — function_gamma_sigma
 */
function functionGammaSigma(
  movec: Array<[Agent, number]>,
  lstNextEnforc: Array<[number, StateFormula]>,
  lstNextUnavoid: Array<[number, StateFormula]>,
  lstNextAgents: StateFormula[],
  nbPos: number,
  nbNeg: number,
  allAgents: Coalition
): StateFormulaSet {
  const result = new StateFormulaSet();

  // Enforceable: Coal(A, Next(State(f))) at index n
  // Fires if ALL agents in A play n
  for (const [n, formula] of lstNextEnforc) {
    if (formula.kind === "coal" && formula.path.kind === "next" && formula.path.sub.kind === "state") {
      const la = formula.coalition;
      const f = formula.path.sub.sub;
      if (la.every(a => {
        const entry = movec.find(([ag]) => ag === a);
        return entry !== undefined && entry[1] === n;
      })) {
        result.add(f);
      }
    }
  }

  // Proper unavoidable: CoCoal(A, Next(State(f))) at index n
  // Fires if Co(sigma) == n AND allAgents\A ⊆ N(sigma)
  if (nbNeg > 0) {
    for (const [n, formula] of lstNextUnavoid) {
      if (formula.kind === "cocoal" && formula.path.kind === "next" && formula.path.sub.kind === "state") {
        const la = formula.coalition;
        const f = formula.path.sub.sub;
        const coSigma = functionCoSigma(movec, nbPos, nbNeg);
        const nSigma = functionNSigma(movec, nbPos);
        const complement = coalitionComplement(la, allAgents);
        if (coSigma === n && complement.every(a => nSigma.has(a))) {
          result.add(f);
        }
      }
    }
  }

  // Agents unavoidable: CoCoal(allAgents, Next(State(f))) — always fires
  for (const formula of lstNextAgents) {
    if (formula.kind === "cocoal" && formula.path.kind === "next" && formula.path.sub.kind === "state") {
      result.add(formula.path.sub.sub);
    }
  }

  // If empty, add Top (matching TATL)
  if (result.size === 0) {
    result.add(STop);
  }

  return result;
}

/**
 * Generate all move vectors and compute successor formula sets.
 * Groups identical formula sets together with their move vectors.
 *
 * Reference: TATL construction.ml — get_formulae_next_rule, create_lst_movecs
 */
function getFormulaeNextRule(
  state: State & Partial<StateNextInfo>,
  allAgents: Coalition
): Array<{ formulas: StateFormulaSet; moveVecs: MoveVector[] }> {
  const info = state as State & StateNextInfo;
  const lstNextEnforc = info._nextPos ?? [];
  const lstNextUnavoid = info._nextNeg ?? [];
  const lstNextAgents = info._nextAgents ?? [];
  const nbPos = info._nbPos ?? 0;
  const nbNeg = info._nbNeg ?? 0;
  const moveVecCount = info._moveVecCount ?? 1;

  const n = allAgents.length;
  const totalMoveVecs = Math.pow(moveVecCount, n);

  // For grouping: formula set key -> { formulas, moveVecs[] }
  const groups = new Map<string, { formulas: StateFormulaSet; moveVecs: MoveVector[] }>();

  // Generate all move vectors (base moveVecCount, n digits)
  for (let i = 0; i < totalMoveVecs; i++) {
    // Convert index to move vector: list of (agent, move) pairs
    const movec: Array<[Agent, number]> = [];
    let remaining = i;
    for (let j = n - 1; j >= 0; j--) {
      const move = remaining % moveVecCount;
      remaining = Math.floor(remaining / moveVecCount);
      movec.unshift([allAgents[j]!, move]);
    }

    // Compute Gamma(sigma)
    const ensFrm = functionGammaSigma(
      movec, lstNextEnforc, lstNextUnavoid, lstNextAgents,
      nbPos, nbNeg, allAgents
    );

    // Extract just the move numbers as a MoveVector
    const mv: MoveVector = movec.map(([, m]) => m);

    // Group by formula set
    const key = ensFrm.key();
    if (groups.has(key)) {
      groups.get(key)!.moveVecs.push(mv);
    } else {
      groups.set(key, { formulas: ensFrm, moveVecs: [mv] });
    }
  }

  // Return one entry per group. Each entry contains the formula set and ALL move vectors
  // that lead to this successor. In consFromStates we create one edge per move vector.
  return [...groups.values()];
}

// ============================================================
// Phase 2: Prestate Elimination Phase
// ============================================================

/**
 * Prestate elimination phase.
 *
 * For every prestate P:
 * 1. Remove P
 * 2. If state S ->[mv] P and P -->> S', then add edge S ->[mv] S' (viaPrestate=P)
 *
 * Reference: TATL elimination uses the graph directly (prestates stay in graph).
 * We flatten to state->state edges with viaPrestate annotation.
 */
function prestateEliminationPhase(pretableau: Pretableau, allAgents: Coalition): Tableau {
  const tableau: Tableau = {
    states: new Map(pretableau.states),
    edges: [],
    allAgents,
  };

  // Build map: prestate ID -> set of state IDs it expands to
  const prestateToStates = new Map<NodeId, Set<NodeId>>();
  for (const edge of pretableau.dashedEdges) {
    if (!prestateToStates.has(edge.from)) {
      prestateToStates.set(edge.from, new Set());
    }
    prestateToStates.get(edge.from)!.add(edge.to);
  }

  // For each solid edge S ->[mv] P, replace with S ->[mv] S' for each S' in states(P)
  for (const edge of pretableau.solidEdges) {
    const targetStates = prestateToStates.get(edge.to);
    if (targetStates) {
      for (const stateId of targetStates) {
        tableau.edges.push({
          from: edge.from,
          to: stateId,
          label: edge.label,
          viaPrestate: edge.to,
        });
      }
    }
  }

  return tableau;
}

// ============================================================
// Phase 3: State Elimination Phase
// ============================================================

/**
 * State elimination phase.
 *
 * Uses a dovetailed fixpoint loop:
 * - E2: Every move vector from a state must have a surviving successor
 * - E3: Every eventuality must be realizable via whatfalse residuals
 *
 * Reference: TATL elimination_star.ml — cycle_state_elimination, state_elimination
 */
function stateEliminationPhase(
  initialTableau: Tableau,
  allAgents: Coalition
): { tableau: Tableau; eliminations: EliminationRecord[] } {
  const states = new Map(initialTableau.states);
  let edges = [...initialTableau.edges];
  const eliminations: EliminationRecord[] = [];
  const suppressed = new Set<NodeId>(); // h_suppr equivalent

  // Dovetailed elimination loop
  let changed = true;
  while (changed) {
    const prevSuppressed = suppressed.size;

    stateElimination(states, edges, allAgents, suppressed, eliminations);

    const newSuppressed = suppressed.size;
    changed = newSuppressed !== prevSuppressed;

    // Check if still open
    if (changed) {
      // Clean edges of suppressed nodes
      edges = edges.filter(e => !suppressed.has(e.from) && !suppressed.has(e.to));
    }
  }

  // Remove suppressed states
  for (const id of suppressed) {
    states.delete(id);
  }

  // Final edge cleanup
  edges = edges.filter(e => states.has(e.from) && states.has(e.to));

  return { tableau: { states, edges, allAgents }, eliminations };
}

/**
 * One round of state elimination (E2 + E3).
 *
 * Reference: TATL elimination_star.ml — state_elimination
 */
function stateElimination(
  states: Map<NodeId, State>,
  edges: SolidEdge[],
  allAgents: Coalition,
  suppressed: Set<NodeId>,
  eliminations: EliminationRecord[]
): void {
  for (const [id, state] of states) {
    if (suppressed.has(id)) continue;

    // E2: Check complete successors
    if (!isCompletSucc(id, state, edges, suppressed, allAgents)) {
      removeState(id, state, suppressed, eliminations, "E2");
      continue;
    }

    // E3: Check eventuality realization
    const nonImmReal = getEvNonImmReal(state, suppressed);
    if (nonImmReal.length > 0) {
      if (!verifEvNonImmReal(nonImmReal, id, state, states, edges, allAgents, suppressed)) {
        removeState(id, state, suppressed, eliminations, "E3");
      }
    }
  }
}

/**
 * Remove a state (mark as suppressed).
 */
function removeState(
  id: NodeId,
  state: State,
  suppressed: Set<NodeId>,
  eliminations: EliminationRecord[],
  rule: "E2" | "E3"
): void {
  if (suppressed.has(id)) return;
  suppressed.add(id);
  eliminations.push({
    stateId: id,
    rule,
    formula: state.tuples.length > 0 ? state.tuples[0]!.frm : STop,
    stateFormulas: state.formulas,
  });
}

// ============================================================
// E2: Complete successors
// ============================================================

/**
 * Check if a state has complete successors (all required move vectors covered).
 *
 * A state is complete if for EVERY move vector that was generated during
 * construction, there exists at least one non-suppressed successor.
 *
 * Reference: TATL elimination_star.ml — is_complet_succ
 *   Movecs.equal ens_succ_mv (Graph_tableau.V.label v).assoc_movecs
 */
function isCompletSucc(
  stateId: NodeId,
  state: State,
  edges: SolidEdge[],
  suppressed: Set<NodeId>,
  allAgents: Coalition
): boolean {
  const info = state as State & Partial<StateNextInfo>;
  const moveVecCount = info._moveVecCount;

  if (moveVecCount === undefined) return true; // No next-time info

  // Collect all surviving move vectors (those with at least one non-suppressed successor)
  const survivingMoveVecs = new Set<string>();
  for (const edge of edges) {
    if (edge.from === stateId && !suppressed.has(edge.to)) {
      survivingMoveVecs.add(edge.label.join(","));
    }
  }

  // Generate all required move vectors and check each one
  const n = allAgents.length;
  const totalRequired = Math.pow(moveVecCount, n);

  for (let i = 0; i < totalRequired; i++) {
    // Convert index to move vector
    const mv: number[] = [];
    let remaining = i;
    for (let j = n - 1; j >= 0; j--) {
      mv.unshift(remaining % moveVecCount);
      remaining = Math.floor(remaining / moveVecCount);
    }
    if (!survivingMoveVecs.has(mv.join(","))) {
      return false;
    }
  }

  return true;
}

// ============================================================
// E3: Eventuality realization via whatfalse residuals
// ============================================================

/**
 * Simplify AndP with State(Top) handling.
 *
 * Reference: TATL elimination_star.ml — simpl_andp
 */
function simplAndP(phi1: PathFormula, phi2: PathFormula): PathFormula {
  if (phi1.kind === "state" && phi1.sub.kind === "top") {
    if (phi2.kind === "state" && phi2.sub.kind === "top") return PState(STop);
    return phi2;
  }
  if (phi2.kind === "state" && phi2.sub.kind === "top") return phi1;
  return { kind: "andp", left: phi1, right: phi2 };
}

/**
 * Simplify OrP with State(Top) handling.
 *
 * Reference: TATL elimination_star.ml — simpl_orp
 */
function simplOrP(phi1: PathFormula, phi2: PathFormula): PathFormula {
  if (phi1.kind === "state" && phi1.sub.kind === "top") return PState(STop);
  if (phi2.kind === "state" && phi2.sub.kind === "top") return PState(STop);
  return { kind: "orp", left: phi1, right: phi2 };
}

/**
 * Compute what part of a path formula is NOT yet realized at a state.
 * Returns the residual path formula. State(Top) means fully realized.
 *
 * Reference: TATL elimination_star.ml — whatfalse
 */
function whatfalse(
  path: PathFormula,
  ensFrm: StateFormulaSet,
  pathFrm: PathFormulaSet
): PathFormula {
  function wf(pathEv: PathFormula): PathFormula {
    switch (pathEv.kind) {
      case "andp":
        return simplAndP(wf(pathEv.left), wf(pathEv.right));

      case "orp":
        return simplOrP(wf(pathEv.left), wf(pathEv.right));

      case "state":
        // If the state formula is in the formula set, or the path formula
        // State(s) is in the tracked path formulas, it's realized
        if (ensFrm.has(pathEv.sub) || pathFrm.has(pathEv)) {
          return PState(STop);
        }
        return pathEv;

      case "next":
        // Next formulas are structurally handled — realized
        return PState(STop);

      case "always":
        // Always formulas are structurally handled — realized
        return PState(STop);

      case "until":
        // Until(p1, p2): check if the goal (p2) is satisfied
        if (pathEv.right.kind === "state") {
          if (ensFrm.has(pathEv.right.sub) || pathFrm.has(PState(pathEv.right.sub))) {
            return PState(STop);
          }
        } else {
          if (pathFrm.has(pathEv.right)) {
            return PState(STop);
          }
        }
        return pathEv;

      default:
        // NegP should not appear after NNF
        throw new Error(`whatfalse: unexpected path formula kind ${pathEv.kind}`);
    }
  }

  return wf(path);
}

/**
 * Check if an eventuality is immediately realized at a state.
 *
 * Reference: TATL elimination_star.ml — is_imm_real
 */
function isImmReal(
  ev: FormulaTuple,
  ensFrm: StateFormulaSet
): { realized: boolean; residual: PathFormula } {
  const path = getEventualityPath(ev.frm);
  const residual = whatfalse(path, ensFrm, ev.pathFrm);

  if (residual.kind === "state" && residual.sub.kind === "top") {
    return { realized: true, residual: PState(STop) };
  }
  return { realized: false, residual };
}

/**
 * Extract the path formula from an eventuality (Coal or CoCoal).
 */
function getEventualityPath(f: StateFormula): PathFormula {
  if (f.kind === "coal" || f.kind === "cocoal") {
    return f.path;
  }
  throw new Error("getEventualityPath: not a coalition formula");
}

/**
 * Get eventualities that are NOT immediately realized at a state.
 *
 * Reference: TATL elimination_star.ml — get_ev_non_imm_real
 */
function getEvNonImmReal(
  state: State,
  suppressed: Set<NodeId>
): Array<{ ev: FormulaTuple; residual: PathFormula }> {
  const result: Array<{ ev: FormulaTuple; residual: PathFormula }> = [];

  for (const ev of state.tuples) {
    const { realized, residual } = isImmReal(ev, state.formulas);
    if (!realized) {
      result.push({ ev, residual });
    }
  }

  return result;
}

/**
 * Find the eventuality tuple in a state's event list that matches a formula.
 *
 * Reference: TATL elimination_star.ml — get_tuple
 */
function getTuple(frm: StateFormula, eventList: FormulaTuple[]): FormulaTuple | null {
  for (const ev of eventList) {
    if (stateKey(ev.frm) === stateKey(frm)) {
      return ev;
    }
  }
  return null;
}

/**
 * Verify all non-immediately-realized eventualities of a state.
 *
 * Reference: TATL elimination_star.ml — verif_ev_non_imm_real
 */
function verifEvNonImmReal(
  lstEv: Array<{ ev: FormulaTuple; residual: PathFormula }>,
  stateId: NodeId,
  state: State,
  states: Map<NodeId, State>,
  edges: SolidEdge[],
  allAgents: Coalition,
  suppressed: Set<NodeId>
): boolean {
  for (const { ev, residual } of lstEv) {
    // Fresh memoization tables for each eventuality verification
    const hPst = new Map<string, PstEntry>();
    const hSt = new Set<string>();

    hSt.add(memoKeySt(stateId, residual));

    const ok = verifSucc(ev, stateId, state, residual, states, edges, allAgents, suppressed, hPst, hSt);
    if (!ok) return false;
  }
  return true;
}

/** Memoization entry for prestate verification */
interface PstEntry {
  value: number; // 0=exploring, 1=OK, 2=FAIL
  lst: Array<{ state: State; evTuple: FormulaTuple }>;
  lst2: Array<{ state: State; evTuple: FormulaTuple }>;
}

function memoKeyPst(prestateId: NodeId, path: PathFormula): string {
  return `${prestateId}|${pathKey(path)}`;
}

function memoKeySt(stateId: NodeId, path: PathFormula): string {
  return `${stateId}|${pathKey(path)}`;
}

/**
 * Check if an edge (set of move vectors) is consistent with an eventuality.
 *
 * For enforceable (Coal): all agents in A must play the eventuality's index.
 * For agents unavoidable (CoCoal with all agents): always consistent.
 * For proper unavoidable (CoCoal with A != allAgents): Co(sigma) = index AND complement ⊆ N(sigma).
 *
 * Reference: TATL elimination_star.ml — verif_edge
 */
function verifEdge(
  state: State,
  edgeLabel: MoveVector,
  ev: FormulaTuple,
  numEv: number,
  allAgents: Coalition
): boolean {
  const info = state as State & Partial<StateNextInfo>;
  const nbPos = info._nbPos ?? 0;
  const nbNeg = info._nbNeg ?? 0;

  // Convert edge label (move vector numbers) to (agent, move) pairs
  const movec: Array<[Agent, number]> = allAgents.map((a, i) => [a, edgeLabel[i]!]);

  if (ev.frm.kind === "coal") {
    // Enforceable: all agents in coalition must play numEv
    const la = ev.frm.coalition;
    return movec.every(([a, m]) => {
      if (la.includes(a)) return m === numEv;
      return true;
    });
  } else if (ev.frm.kind === "cocoal") {
    const la = ev.frm.coalition;
    if (coalitionEqual(la, allAgents)) {
      // Agents unavoidable: always consistent
      return true;
    }
    // Proper unavoidable
    const coSigma = functionCoSigma(movec, nbPos, nbNeg);
    const nSigma = functionNSigma(movec, nbPos);
    const complement = coalitionComplement(la, allAgents);
    return coSigma === numEv && complement.every(a => nSigma.has(a));
  }
  return false;
}

/**
 * Get the number/index of the next-time formula for an eventuality in a state.
 *
 * Reference: TATL elimination_star.ml — get_num_next_ev
 */
function getNumNextEv(
  nextFrm: StateFormula,
  state: State,
  allAgents: Coalition
): number {
  const info = state as State & Partial<StateNextInfo>;
  const lstNextPos = info._nextPos ?? [];
  const lstNextNeg = info._nextNeg ?? [];

  if (nextFrm.kind === "coal") {
    // Look for Coal(la, Next(State(nextFrm))) in enforceable list
    const wrappedKey = stateKey(Coal(nextFrm.coalition, PNext(PState(nextFrm))));
    for (const [n, f] of lstNextPos) {
      if (stateKey(f) === wrappedKey) return n;
    }
    return -2; // not found
  } else if (nextFrm.kind === "cocoal") {
    if (coalitionEqual(nextFrm.coalition, allAgents)) {
      return -1; // agents unavoidable
    }
    // Look for CoCoal(la, Next(State(nextFrm))) in proper unavoidable list
    const wrappedKey = stateKey(CoCoal(nextFrm.coalition, PNext(PState(nextFrm))));
    for (const [n, f] of lstNextNeg) {
      if (stateKey(f) === wrappedKey) return n;
    }
    return -2; // not found
  }
  return -2;
}

/**
 * Get successor prestates to verify for eventuality realization.
 * Returns prestates that:
 * - Are reached via edges consistent with the eventuality
 * - Contain the eventuality's next formula
 * - Are not suppressed
 *
 * Reference: TATL elimination_star.ml — get_succ_to_be_verified_simpl
 */
function getSuccToBeVerified(
  ev: FormulaTuple,
  stateId: NodeId,
  state: State,
  edges: SolidEdge[],
  allAgents: Coalition,
  suppressed: Set<NodeId>
): NodeId[] {
  const numEv = getNumNextEv(ev.nextFrm, state, allAgents);
  if (numEv === -2) return [];
  if (!isEventuality(ev.nextFrm)) return [];

  const result: NodeId[] = [];
  const seen = new Set<NodeId>();

  for (const edge of edges) {
    if (edge.from !== stateId) continue;
    if (!edge.viaPrestate) continue;
    if (suppressed.has(edge.viaPrestate)) continue;

    const prestateId = edge.viaPrestate;
    if (seen.has(prestateId)) continue;

    // Check if the edge is consistent with the eventuality
    if (numEv !== -1 && !verifEdge(state, edge.label, ev, numEv, allAgents)) {
      continue;
    }

    seen.add(prestateId);
    result.push(prestateId);
  }

  return result;
}

/**
 * Get successor states from a prestate for eventuality verification.
 *
 * Reference: TATL elimination_star.ml — get_succ_prestates
 */
function getSuccPrestates(
  ev: FormulaTuple,
  prestateId: NodeId,
  edges: SolidEdge[],
  states: Map<NodeId, State>,
  suppressed: Set<NodeId>
): Array<{ state: State; evTuple: FormulaTuple }> {
  const result: Array<{ state: State; evTuple: FormulaTuple }> = [];
  const seen = new Set<NodeId>();

  for (const edge of edges) {
    // Find edges where the viaPrestate is our prestate (these are state->state edges)
    if (edge.viaPrestate !== prestateId) continue;
    if (suppressed.has(edge.to)) continue;
    if (seen.has(edge.to)) continue;
    seen.add(edge.to);

    const succState = states.get(edge.to);
    if (!succState) continue;

    // Find the matching eventuality tuple in the successor state
    const evNext = getTuple(ev.nextFrm, succState.tuples);
    if (evNext) {
      result.push({ state: succState, evTuple: evNext });
    }
  }

  return result;
}

/**
 * DFS verification of eventuality realization through successor chains.
 *
 * For a state s with an eventuality ev and residual path formula:
 * 1. Get consistent successor prestates
 * 2. For EACH prestate (universal), find at least one successor state (existential)
 *    where either:
 *    - whatfalse reduces the residual to State(Top) (realized), or
 *    - recursive verification succeeds
 *
 * Reference: TATL elimination_star.ml — verif_succ (the core DFS with memoization)
 */
function verifSucc(
  ev: FormulaTuple,
  stateId: NodeId,
  state: State,
  path: PathFormula,
  states: Map<NodeId, State>,
  edges: SolidEdge[],
  allAgents: Coalition,
  suppressed: Set<NodeId>,
  hPst: Map<string, PstEntry>,
  hSt: Set<string>
): boolean {
  // Get consistent successor prestates
  const lstPrestateSucc = getSuccToBeVerified(ev, stateId, state, edges, allAgents, suppressed);

  // For each prestate (universal): must find one successor state that works
  return verifPrestate(lstPrestateSucc, ev, path, states, edges, allAgents, suppressed, hPst, hSt);
}

/**
 * Universal check over prestates: ALL prestates must be satisfiable.
 *
 * Reference: TATL elimination_star.ml — verif_prestate (inner function of verif_succ)
 */
function verifPrestate(
  lstPrestate: NodeId[],
  ev: FormulaTuple,
  path: PathFormula,
  states: Map<NodeId, State>,
  edges: SolidEdge[],
  allAgents: Coalition,
  suppressed: Set<NodeId>,
  hPst: Map<string, PstEntry>,
  hSt: Set<string>
): boolean {
  for (let i = 0; i < lstPrestate.length; i++) {
    const pId = lstPrestate[i]!;
    const pKey = memoKeyPst(pId, path);

    // Check if we've already explored this prestate with this path
    const cached = hPst.get(pKey);
    if (cached) {
      if (cached.value === 1) {
        // Already verified OK
        continue;
      }
      if (cached.value === 2) {
        // Already verified FAIL
        return false;
      }
      // value === 0: still exploring, try next state in list
      if (cached.lst.length === 0) {
        hPst.set(pKey, { value: 2, lst: [], lst2: [] });
        return false;
      }

      // Try next state from the cached list
      const stateV = cached.lst[0]!;
      const tail = cached.lst.slice(1);
      const sKey = memoKeySt(stateV.state.id, path);

      if (hSt.has(sKey)) {
        // Already visited this state — skip and try another
        const newTail = tail;
        const newLst2 = cached.lst2.length === 0 && tail.length === 0 ? [] : [...cached.lst2, stateV];
        hPst.set(pKey, { value: 0, lst: newTail, lst2: newLst2 });
        // Retry this prestate with remaining states
        i--; // retry current prestate
        continue;
      }

      hSt.add(sKey);
      hPst.set(pKey, { value: 0, lst: tail, lst2: cached.lst2 });

      if (verifState(stateV.state, stateV.evTuple, path, states, edges, allAgents, suppressed, hPst, hSt)) {
        hPst.set(pKey, { value: 1, lst: tail, lst2: cached.lst2 });
        continue; // This prestate is OK, move to next
      } else {
        // Retry from the beginning of the full prestate list
        return verifPrestate(lstPrestate, ev, path, states, edges, allAgents, suppressed, hPst, hSt);
      }
    } else {
      // First visit: get successor states from this prestate
      const lstSucc = getSuccPrestates(ev, pId, edges, states, suppressed);

      if (lstSucc.length === 0) {
        return false; // No successor states — fail
      }

      const stateV = lstSucc[0]!;
      const tail = lstSucc.slice(1);
      const sKey = memoKeySt(stateV.state.id, path);

      if (hSt.has(sKey)) {
        // Already visited this state — skip
        const newLst2 = tail.length === 0 ? [] : [stateV];
        hPst.set(pKey, { value: 0, lst: tail, lst2: newLst2 });
        // Retry this prestate
        i--;
        continue;
      }

      hPst.set(pKey, { value: 0, lst: tail, lst2: [] });
      hSt.add(sKey);

      if (verifState(stateV.state, stateV.evTuple, path, states, edges, allAgents, suppressed, hPst, hSt)) {
        hPst.set(pKey, { value: 1, lst: tail, lst2: [] });
        continue; // This prestate OK
      } else {
        // Retry from the beginning
        return verifPrestate(lstPrestate, ev, path, states, edges, allAgents, suppressed, hPst, hSt);
      }
    }
  }

  return true; // All prestates verified
}

/**
 * Existential check over states: at least ONE state must realize the eventuality.
 *
 * Reference: TATL elimination_star.ml — verif_state (inner function of verif_succ)
 */
function verifState(
  s: State,
  evTuple: FormulaTuple,
  path: PathFormula,
  states: Map<NodeId, State>,
  edges: SolidEdge[],
  allAgents: Coalition,
  suppressed: Set<NodeId>,
  hPst: Map<string, PstEntry>,
  hSt: Set<string>
): boolean {
  const ensFrm = s.formulas;
  const residual = whatfalse(path, ensFrm, evTuple.pathFrm);

  if (residual.kind === "state" && residual.sub.kind === "top") {
    // Fully realized!
    return true;
  }

  // Continue search with the new residual
  return verifSucc(evTuple, s.id, s, residual, states, edges, allAgents, suppressed, hPst, hSt);
}
