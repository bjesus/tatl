/**
 * Main tableau procedure for CMAEL(CD) satisfiability checking.
 *
 * Three phases:
 * 1. Construction phase: Build pretableau P^θ using rules (SR) and (DR)
 * 2. Prestate elimination phase: Remove prestates to get initial tableau T^θ_0
 * 3. State elimination phase: Remove bad states to get final tableau T^θ
 *
 * References:
 * - Section 4 (p.14-21) of the paper
 * - Rule (SR) p.18, Rule (DR) p.18
 * - Rule (PR) p.19
 * - Rule (E1) p.20, Rule (E2) p.20
 * - Definition 16 (eventuality realization) p.20
 */

import {
  type Formula,
  type Coalition,
  type NodeId,
  type PreState,
  type State,
  type DashedEdge,
  type SolidEdge,
  type Pretableau,
  type Tableau,
  type TableauResult,
  type EliminationRecord,
  FormulaSet,
  Not,
  D,
  formulaKey,
  formulaEqual,
  coalitionSubset,
  coalitionIntersects,
  normalizeCoalition,
} from "./types.ts";
import { cutSaturatedExpansion } from "./expansion.ts";
import {
  isPatentlyInconsistent,
  isEventuality,
  isDiamond,
  getEventualities,

} from "./formula.ts";

// Counter for generating unique node IDs
let nodeCounter = 0;

function freshNodeId(prefix: string): NodeId {
  return `${prefix}${nodeCounter++}`;
}

function resetNodeCounter(): void {
  nodeCounter = 0;
}

/**
 * Main entry point: run the tableau procedure on a formula.
 *
 * @param theta - The input formula to test for satisfiability
 * @param useRestrictedCuts - Whether to use restricted C1/C2 conditions (default: true)
 * @returns TableauResult with all phases recorded
 */
export function runTableau(
  theta: Formula,
  useRestrictedCuts: boolean = true,
  onProgress?: (stage: string) => void
): TableauResult {
  resetNodeCounter();

  // Phase 1: Construction
  if (onProgress) onProgress("Phase 1: Construction");
  const pretableau = constructionPhase(theta, useRestrictedCuts);

  // Phase 2: Prestate elimination
  if (onProgress) onProgress("Phase 2: Prestate Elimination");
  const initialTableau = prestateEliminationPhase(pretableau);

  // Phase 3: State elimination
  if (onProgress) onProgress("Phase 3: State Elimination");
  const { tableau: finalTableau, eliminations } = stateEliminationPhase(initialTableau);

  // Check if open: does any surviving state contain θ?
  if (onProgress) onProgress("Checking Satisfiability");
  let satisfiable = false;
  for (const [, state] of finalTableau.states) {
    if (state.formulas.has(theta)) {
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
    eliminations,
  };
}

// ============================================================
// Phase 1: Construction Phase
// ============================================================

/**
 * Construction phase: builds the pretableau P^θ.
 *
 * Starts with a single prestate {θ}, then alternates (SR) and (DR)
 * until no new prestates or states are created.
 */
function constructionPhase(
  theta: Formula,
  useRestrictedCuts: boolean
): Pretableau {
  const pretableau: Pretableau = {
    prestates: new Map(),
    states: new Map(),
    dashedEdges: [],
    solidEdges: [],
  };

  // Maps from formula set key → node ID for reuse
  const prestateIndex = new Map<string, NodeId>();
  const stateIndex = new Map<string, NodeId>();

  // Create initial prestate {θ}
  const initialSet = new FormulaSet([theta]);
  const initialId = addPrestate(pretableau, prestateIndex, initialSet);

  // Work queue: prestates needing (SR), states needing (DR)
  let prestatesToExpand: NodeId[] = [initialId];
  let statesToExpand: { stateId: NodeId; formula: Formula }[] = [];

  while (prestatesToExpand.length > 0 || statesToExpand.length > 0) {
    // Apply (SR) to all pending prestates
    const newStates: NodeId[] = [];
    for (const psId of prestatesToExpand) {
      const ps = pretableau.prestates.get(psId)!;
      const expanded = applySR(pretableau, stateIndex, ps, useRestrictedCuts);
      newStates.push(...expanded);
    }
    prestatesToExpand = [];

    // Find new (DR) applications for the newly created states
    statesToExpand = [];
    for (const stId of newStates) {
      const state = pretableau.states.get(stId)!;
      for (const f of state.formulas) {
        if (isDiamond(f)) {
          // Check if (DR) has already been applied to this state with this formula
          const alreadyApplied = pretableau.solidEdges.some(
            (e) => e.from === stId && formulaEqual(e.label, f)
          );
          if (!alreadyApplied) {
            statesToExpand.push({ stateId: stId, formula: f });
          }
        }
      }
    }

    // Apply (DR) to all pending states
    const newPrestates: NodeId[] = [];
    for (const { stateId, formula } of statesToExpand) {
      const result = applyDR(pretableau, prestateIndex, stateId, formula);
      if (result !== null) {
        newPrestates.push(result);
      }
    }
    prestatesToExpand = newPrestates;
  }

  return pretableau;
}

/**
 * Rule (SR) — expand a prestate into states (p.18).
 *
 * 1. Compute all CS-expansions of Γ; declare these to be states.
 * 2. For each state Δ, put Γ ⤏ Δ.
 * 3. If a state Δ' = Δ already exists, reuse it.
 *
 * Returns IDs of newly created states.
 */
function applySR(
  pretableau: Pretableau,
  stateIndex: Map<string, NodeId>,
  prestate: PreState,
  useRestrictedCuts: boolean
): NodeId[] {
  const expansions = cutSaturatedExpansion(prestate.formulas, useRestrictedCuts);
  const newStateIds: NodeId[] = [];

  for (const expansion of expansions) {
    const key = expansion.key();
    let stateId: NodeId;

    if (stateIndex.has(key)) {
      // State already exists — reuse
      stateId = stateIndex.get(key)!;
    } else {
      // Create new state
      stateId = freshNodeId("s");
      const state: State = {
        id: stateId,
        formulas: expansion,
        kind: "state",
      };
      pretableau.states.set(stateId, state);
      stateIndex.set(key, stateId);
      newStateIds.push(stateId);
    }

    // Add dashed edge Γ ⤏ Δ
    pretableau.dashedEdges.push({
      from: prestate.id,
      to: stateId,
    });
  }

  return newStateIds;
}

/**
 * Rule (DR) — create a prestate from a state based on a diamond formula (p.18).
 *
 * Given state Δ and ¬D_A φ ∈ Δ:
 * 1. Create prestate Γ = {¬φ} ∪ {D_{A'} ψ ∈ Δ | A' ⊆ A}
 *                            ∪ {¬D_{A'} ψ ∈ Δ | A' ⊆ A and ¬D_{A'} ψ ≠ ¬D_A φ}
 *                            ∪ {¬C_{A'} ψ ∈ Δ | A' ∩ A ≠ ∅}
 * 2. Put Δ →[¬D_A φ] Γ
 * 3. Reuse existing prestate if equal.
 *
 * Returns the ID of the created/reused prestate, or null if not applicable.
 */
function applyDR(
  pretableau: Pretableau,
  prestateIndex: Map<string, NodeId>,
  stateId: NodeId,
  diamondFormula: Formula
): NodeId | null {
  if (diamondFormula.kind !== "not" || diamondFormula.sub.kind !== "D") {
    throw new Error("applyDR called with non-diamond formula");
  }

  const state = pretableau.states.get(stateId)!;
  const A = diamondFormula.sub.coalition; // The coalition in ¬D_A φ
  const phi = diamondFormula.sub.sub; // The φ in ¬D_A φ

  // Build the prestate content
  const prestateFormulas = new FormulaSet();

  // Add ¬φ
  prestateFormulas.add(Not(phi));

  for (const f of state.formulas) {
    // D_{A'} ψ ∈ Δ where A' ⊆ A → add
    if (f.kind === "D" && coalitionSubset(f.coalition, A)) {
      prestateFormulas.add(f);
    }

    // ¬D_{A'} ψ ∈ Δ where A' ⊆ A and ¬D_{A'} ψ ≠ ¬D_A φ → add
    if (
      f.kind === "not" &&
      f.sub.kind === "D" &&
      coalitionSubset(f.sub.coalition, A) &&
      !formulaEqual(f, diamondFormula)
    ) {
      prestateFormulas.add(f);
    }

    // ¬C_{A'} ψ ∈ Δ where A' ∩ A ≠ ∅ → add
    if (
      f.kind === "not" &&
      f.sub.kind === "C" &&
      coalitionIntersects(f.sub.coalition, A)
    ) {
      prestateFormulas.add(f);
    }
  }

  // Check for reuse
  const key = prestateFormulas.key();
  let prestateId: NodeId;

  if (prestateIndex.has(key)) {
    prestateId = prestateIndex.get(key)!;
  } else {
    prestateId = addPrestate(pretableau, prestateIndex, prestateFormulas);
  }

  // Add solid edge Δ →[¬D_A φ] Γ
  pretableau.solidEdges.push({
    from: stateId,
    to: prestateId,
    label: diamondFormula,
  });

  return prestateIndex.has(key) && pretableau.prestates.has(prestateId)
    ? prestateId
    : prestateId;
}

/**
 * Helper: add a prestate to the pretableau.
 */
function addPrestate(
  pretableau: Pretableau,
  prestateIndex: Map<string, NodeId>,
  formulas: FormulaSet
): NodeId {
  const key = formulas.key();
  if (prestateIndex.has(key)) {
    return prestateIndex.get(key)!;
  }
  const id = freshNodeId("p");
  const ps: PreState = { id, formulas, kind: "prestate" };
  pretableau.prestates.set(id, ps);
  prestateIndex.set(key, id);
  return id;
}

// ============================================================
// Phase 2: Prestate Elimination Phase
// ============================================================

/**
 * Prestate elimination phase (Rule PR, p.19).
 *
 * For every prestate Γ in P^θ:
 * 1. Remove Γ
 * 2. If state Δ →[χ] Γ, then for every Δ' ∈ states(Γ), put Δ →[χ] Δ'
 *
 * Result: initial tableau T^θ_0 with only states and solid state→state edges.
 */
function prestateEliminationPhase(pretableau: Pretableau): Tableau {
  const tableau: Tableau = {
    states: new Map(pretableau.states),
    edges: [],
  };

  // Build map: prestate ID → set of state IDs it expands to
  const prestateToStates = new Map<NodeId, Set<NodeId>>();
  for (const edge of pretableau.dashedEdges) {
    if (!prestateToStates.has(edge.from)) {
      prestateToStates.set(edge.from, new Set());
    }
    prestateToStates.get(edge.from)!.add(edge.to);
  }

  // For each solid edge Δ →[χ] Γ (where Γ is a prestate),
  // replace with edges Δ →[χ] Δ' for each Δ' ∈ states(Γ)
  for (const edge of pretableau.solidEdges) {
    const targetStates = prestateToStates.get(edge.to);
    if (targetStates) {
      for (const stateId of targetStates) {
        tableau.edges.push({
          from: edge.from,
          to: stateId,
          label: edge.label,
        });
      }
    }
    // If the prestate has no states (all expansions were inconsistent),
    // no edges are created — this is correct.
  }

  return tableau;
}

// ============================================================
// Phase 3: State Elimination Phase
// ============================================================

/**
 * State elimination phase (p.20-21).
 *
 * Two elimination rules applied in dovetailed cycles:
 * (E1): Remove state if a diamond formula has no surviving successors.
 * (E2): Remove state if an eventuality is not realized.
 *
 * Cycles through all eventualities, alternating (E2) then (E1),
 * until a full cycle with no removals.
 */
function stateEliminationPhase(initialTableau: Tableau): { tableau: Tableau; eliminations: EliminationRecord[] } {
  // Work on a mutable copy
  const states = new Map(initialTableau.states);
  let edges = [...initialTableau.edges];
  const eliminations: EliminationRecord[] = [];

  // Collect all eventualities appearing in any state
  const allEventualities = collectAllEventualities(states);

  if (allEventualities.length === 0) {
    // No eventualities — only need to check (E1)
    eliminations.push(...applyE1UntilFixpoint(states, edges));
    edges = edges.filter((e) => states.has(e.from) && states.has(e.to));
    return { tableau: { states, edges }, eliminations };
  }

  // Dovetailed cycles through eventualities
  let removedInCycle = true;
  while (removedInCycle) {
    removedInCycle = false;

    for (const eventuality of allEventualities) {
      // Apply (E2) for this eventuality
      const e2Records = applyE2(states, edges, eventuality);
      if (e2Records.length > 0) {
        eliminations.push(...e2Records);
        removedInCycle = true;
        edges = edges.filter((e) => states.has(e.from) && states.has(e.to));
      }

      // Apply (E1) until no more removals
      const e1Records = applyE1UntilFixpoint(states, edges);
      if (e1Records.length > 0) {
        eliminations.push(...e1Records);
        removedInCycle = true;
        edges = edges.filter((e) => states.has(e.from) && states.has(e.to));
      }
    }
  }

  edges = edges.filter((e) => states.has(e.from) && states.has(e.to));
  return { tableau: { states, edges }, eliminations };
}

/**
 * Collect all distinct eventualities from all states.
 */
function collectAllEventualities(states: Map<NodeId, State>): Formula[] {
  const seen = new Set<string>();
  const result: Formula[] = [];
  for (const [, state] of states) {
    for (const f of state.formulas) {
      if (isEventuality(f)) {
        const key = formulaKey(f);
        if (!seen.has(key)) {
          seen.add(key);
          result.push(f);
        }
      }
    }
  }
  return result;
}

/**
 * Rule (E1) — eliminate states with unsatisfied diamond formulas (p.20).
 *
 * If Δ contains ¬D_A φ but there is no Δ →[¬D_A φ] Δ' where Δ' survives,
 * eliminate Δ.
 *
 * Apply repeatedly until fixpoint. Returns true if any state was removed.
 */
function applyE1UntilFixpoint(
  states: Map<NodeId, State>,
  edges: SolidEdge[]
): EliminationRecord[] {
  const records: EliminationRecord[] = [];
  let changed = true;

  while (changed) {
    changed = false;
    const toRemove: { id: NodeId; formula: Formula }[] = [];

    for (const [id, state] of states) {
      for (const f of state.formulas) {
        if (isDiamond(f)) {
          // Check if there's a surviving successor for this diamond
          const hasSuccessor = edges.some(
            (e) =>
              e.from === id &&
              formulaEqual(e.label, f) &&
              states.has(e.to)
          );
          if (!hasSuccessor) {
            toRemove.push({ id, formula: f });
            break; // No need to check other diamonds
          }
        }
      }
    }

    for (const { id, formula } of toRemove) {
      const state = states.get(id)!;
      records.push({
        stateId: id,
        rule: "E1",
        formula,
        stateFormulas: state.formulas.clone(),
      });
      states.delete(id);
      changed = true;
    }
  }

  return records;
}

/**
 * Rule (E2) — eliminate states with unrealized eventualities (p.20).
 *
 * Uses the marking procedure described on p.20:
 * 1. Mark all states containing ¬φ (where the eventuality is ¬C_A φ)
 * 2. Repeatedly: mark unmarked state Δ if ¬C_A φ ∈ Δ and there exists
 *    Δ →[¬D_a ψ] Δ' where a ∈ A and Δ' is marked.
 * 3. Eliminate all unmarked states containing ¬C_A φ.
 *
 * Returns true if any state was removed.
 */
function applyE2(
  states: Map<NodeId, State>,
  edges: SolidEdge[],
  eventuality: Formula
): EliminationRecord[] {
  if (eventuality.kind !== "not" || eventuality.sub.kind !== "C") {
    throw new Error("applyE2 called with non-eventuality");
  }

  const A = eventuality.sub.coalition;
  const phi = eventuality.sub.sub;
  const negPhi = Not(phi);

  // Find all states containing this eventuality
  const statesWithEventuality = new Set<NodeId>();
  for (const [id, state] of states) {
    if (state.formulas.has(eventuality)) {
      statesWithEventuality.add(id);
    }
  }

  if (statesWithEventuality.size === 0) return [];

  // Marking procedure
  const marked = new Set<NodeId>();

  // Step 1: Mark all states containing ¬φ
  for (const [id, state] of states) {
    if (state.formulas.has(negPhi)) {
      marked.add(id);
    }
  }

  // Step 2: Fixpoint marking
  let changed = true;
  while (changed) {
    changed = false;
    for (const id of statesWithEventuality) {
      if (marked.has(id)) continue;
      if (!states.has(id)) continue;

      // Check if there's an edge to a marked state via ¬D_{A'} ψ where A' ∩ A ≠ ∅
      for (const edge of edges) {
        if (edge.from !== id) continue;
        if (!states.has(edge.to)) continue;
        if (!marked.has(edge.to)) continue;

        if (
          edge.label.kind === "not" &&
          edge.label.sub.kind === "D"
        ) {
          const edgeCoalition = edge.label.sub.coalition;
          // The condition B ∩ A ≠ ∅ is a sound generalization of the paper's
          // single-agent formulation (see detailed comments in prior version).
          if (coalitionIntersects(edgeCoalition, A)) {
            marked.add(id);
            changed = true;
            break;
          }
        }
      }
    }
  }

  // Step 3: Eliminate unmarked states that contain the eventuality
  const records: EliminationRecord[] = [];
  for (const id of statesWithEventuality) {
    if (!marked.has(id) && states.has(id)) {
      const state = states.get(id)!;
      records.push({
        stateId: id,
        rule: "E2",
        formula: eventuality,
        stateFormulas: state.formulas.clone(),
      });
      states.delete(id);
    }
  }

  return records;
}
