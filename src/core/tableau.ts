/**
 * Main tableau procedure for ATL satisfiability checking.
 *
 * Three phases:
 * 1. Construction phase: Build pretableau using rules (SR) and (Next)
 * 2. Prestate elimination phase: Remove prestates to get initial tableau
 * 3. State elimination phase: Remove bad states (E1: inconsistency/no states,
 *    E2: missing successors, E3: unrealized eventualities)
 *
 * References:
 * - Goranko & Shkatov 2009, Section 4 (pp.14-24)
 * - Rule (SR) p.18, Rule (Next) p.18-19
 * - Rule (E1) p.20, Rule (E2) p.20, Rule (E3) p.20-21
 * - Definition 4.6 (eventuality realization) p.20
 */

import {
  type Formula,
  type Coalition,
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
  FormulaSet,
  Not,
  Next,
  formulaKey,
  formulaEqual,
  coalitionSubset,
  coalitionEqual,
  coalitionComplement,
  normalizeCoalition,
} from "./types.ts";
import { fullExpansion } from "./expansion.ts";
import {
  isPatentlyInconsistent,
  isEventuality,
  eventualityGoal,
  eventualityCoalition,
  eventualityNextFormula,
  isPositiveNext,
  isNegativeNext,
  isNextTime,
  agentsInFormula,
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
 * @returns TableauResult with all phases recorded
 */
export function runTableau(
  theta: Formula,
  onProgress?: (stage: string) => void
): TableauResult {
  resetNodeCounter();

  // Compute all agents from the formula (tight satisfiability)
  const allAgents = normalizeCoalition([...agentsInFormula(theta)]);

  // Phase 1: Construction
  if (onProgress) onProgress("Phase 1: Construction");
  const pretableau = constructionPhase(theta, allAgents);

  // Phase 2: Prestate elimination
  if (onProgress) onProgress("Phase 2: Prestate Elimination");
  const initialTableau = prestateEliminationPhase(pretableau, allAgents);

  // Phase 3: State elimination
  if (onProgress) onProgress("Phase 3: State Elimination");
  const { tableau: finalTableau, eliminations } = stateEliminationPhase(initialTableau, allAgents);

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
 * Starts with a single prestate {θ}, then alternates (SR) and (Next)
 * until no new prestates or states are created.
 *
 * (SR) expands prestates into states via full expansion.
 * (Next) creates successor prestates for each state based on move vectors.
 */
function constructionPhase(
  theta: Formula,
  allAgents: Coalition
): Pretableau {
  const pretableau: Pretableau = {
    prestates: new Map(),
    states: new Map(),
    dashedEdges: [],
    solidEdges: [],
    allAgents,
  };

  // Maps from formula set key → node ID for reuse
  const prestateIndex = new Map<string, NodeId>();
  const stateIndex = new Map<string, NodeId>();

  // Create initial prestate {θ}
  const initialSet = new FormulaSet([theta]);
  const initialId = addPrestate(pretableau, prestateIndex, initialSet);

  // Work queue
  let prestatesToExpand: NodeId[] = [initialId];

  while (prestatesToExpand.length > 0) {
    // Apply (SR) to all pending prestates
    const newStates: NodeId[] = [];
    for (const psId of prestatesToExpand) {
      const ps = pretableau.prestates.get(psId)!;
      const expanded = applySR(pretableau, stateIndex, ps);
      newStates.push(...expanded);
    }
    prestatesToExpand = [];

    // Apply (Next) to all newly created states
    const newPrestates: NodeId[] = [];
    for (const stId of newStates) {
      const state = pretableau.states.get(stId)!;
      // Check if this state already has successors (was processed before)
      const alreadyProcessed = pretableau.solidEdges.some((e) => e.from === stId);
      if (!alreadyProcessed) {
        const result = applyNextRule(pretableau, prestateIndex, stId, state, allAgents);
        newPrestates.push(...result);
      }
    }
    prestatesToExpand = newPrestates;
  }

  return pretableau;
}

/**
 * Rule (SR) — expand a prestate into states (p.18).
 *
 * Compute all full expansions of Γ; declare these to be states.
 * Returns IDs of newly created states.
 */
function applySR(
  pretableau: Pretableau,
  stateIndex: Map<string, NodeId>,
  prestate: PreState
): NodeId[] {
  const expansions = fullExpansion(prestate.formulas);
  const newStateIds: NodeId[] = [];

  for (const expansion of expansions) {
    const key = expansion.key();
    let stateId: NodeId;

    if (stateIndex.has(key)) {
      stateId = stateIndex.get(key)!;
    } else {
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

    // Add dashed edge: prestate ⤏ state
    pretableau.dashedEdges.push({
      from: prestate.id,
      to: stateId,
    });
  }

  return newStateIds;
}

/**
 * Rule (Next) — create successor prestates for a state based on move vectors.
 *
 * This is the key difference from CMAEL(CD). In ATL:
 * 1. Collect all next-time formulas from the state:
 *    - Positive: ⟨⟨A⟩⟩○ϕ  (the coalition votes FOR ϕ)
 *    - Negative: ¬⟨⟨A⟩⟩○ψ  (the counter-coalition can avoid ψ)
 *
 * 2. Generate all move vectors σ ∈ {0,...,k-1}^|Σ| where k = max(m+l, 1),
 *    m = # positive next-time formulas, l = # negative next-time formulas
 *
 * 3. For each move vector σ, compute the successor prestate Γ_σ:
 *    - Include ϕ for each ⟨⟨A⟩⟩○ϕ ∈ Δ where σ ∈ D(Δ, ⟨⟨A⟩⟩○ϕ)
 *    - Include ¬ψ for each ¬⟨⟨A⟩⟩○ψ ∈ Δ where σ ∈ D(Δ, ¬⟨⟨A⟩⟩○ψ)
 *
 * Reference: Section 4.2, pp. 18-19 of the paper.
 */
function applyNextRule(
  pretableau: Pretableau,
  prestateIndex: Map<string, NodeId>,
  stateId: NodeId,
  state: State,
  allAgents: Coalition
): NodeId[] {
  // Classify next-time formulas into three categories (matching TATL):
  //
  // 1. Enforceable (positive): ⟨⟨A⟩⟩○ϕ — indexed 0..m-1
  //    Fires when ALL agents in A play the formula's index.
  //
  // 2. Proper unavoidable (negative): ¬⟨⟨A⟩⟩○ψ where A ≠ Σ — indexed 0..l-1
  //    Fires when Co(σ) = index AND Σ\A ⊆ N(σ).
  //
  // 3. Agents unavoidable: ¬⟨⟨Σ⟩⟩○ψ where A = Σ (all agents) — NOT indexed
  //    Inner formula ¬ψ is ALWAYS included in every successor unconditionally.
  //    These do NOT contribute to move vector dimensionality.

  const enforceable: Formula[] = [];         // ⟨⟨A⟩⟩○ϕ
  const properUnavoidable: Formula[] = [];   // ¬⟨⟨A⟩⟩○ψ where A ≠ Σ
  const agentsUnavoidable: Formula[] = [];   // ¬⟨⟨Σ⟩⟩○ψ where A = Σ

  for (const f of state.formulas) {
    if (isPositiveNext(f)) {
      enforceable.push(f);
    } else if (isNegativeNext(f)) {
      // Distinguish proper unavoidable vs agents unavoidable
      if (f.kind === "not" && f.sub.kind === "next") {
        if (coalitionEqual(
          normalizeCoalition([...f.sub.coalition]),
          allAgents
        )) {
          agentsUnavoidable.push(f);
        } else {
          properUnavoidable.push(f);
        }
      }
    }
  }

  const m = enforceable.length;
  const l = properUnavoidable.length;

  // If no next-time formulas at all (including agents unavoidable),
  // add a default successor with empty set
  if (m === 0 && l === 0 && agentsUnavoidable.length === 0) {
    const successorFormulas = new FormulaSet();
    const key = successorFormulas.key();
    let psId: NodeId;
    if (prestateIndex.has(key)) {
      psId = prestateIndex.get(key)!;
    } else {
      psId = addPrestate(pretableau, prestateIndex, successorFormulas);
    }
    pretableau.solidEdges.push({
      from: stateId,
      to: psId,
      label: [],
    });
    return prestateIndex.has(key) ? [] : [psId];
  }

  const k = Math.max(m + l, 1); // Total moves per agent (at least 1)
  const n = allAgents.length;

  // Generate all move vectors σ ∈ {0,...,k-1}^n
  const moveVectors = generateMoveVectors(n, k);

  const newPrestateIds: NodeId[] = [];

  for (const sigma of moveVectors) {
    const successorFormulas = new FormulaSet();

    // Part 1: Enforceable formulas — ⟨⟨A⟩⟩○ϕ at index i
    // Include ϕ if ALL agents in A play i
    for (let i = 0; i < enforceable.length; i++) {
      const f = enforceable[i]!;
      if (f.kind !== "next") continue;
      if (inD_positive(sigma, f.coalition, i, allAgents, m)) {
        successorFormulas.add(f.sub);
      }
    }

    // Part 2: Proper unavoidable formulas — ¬⟨⟨A⟩⟩○ψ where A ≠ Σ at index j
    // Include ¬ψ if Co(σ) = j AND Σ\A ⊆ N(σ)
    for (let j = 0; j < properUnavoidable.length; j++) {
      const f = properUnavoidable[j]!;
      if (f.kind !== "not" || f.sub.kind !== "next") continue;
      const A = f.sub.coalition;
      if (inD_negative(sigma, A, j, allAgents, m, l)) {
        successorFormulas.add(Not(f.sub.sub));
      }
    }

    // Part 3: Agents unavoidable formulas — ¬⟨⟨Σ⟩⟩○ψ
    // ALWAYS include ¬ψ unconditionally in every successor
    for (const f of agentsUnavoidable) {
      if (f.kind !== "not" || f.sub.kind !== "next") continue;
      successorFormulas.add(Not(f.sub.sub));
    }

    // Check for reuse
    const key = successorFormulas.key();
    let psId: NodeId;

    if (prestateIndex.has(key)) {
      psId = prestateIndex.get(key)!;
    } else {
      psId = addPrestate(pretableau, prestateIndex, successorFormulas);
      newPrestateIds.push(psId);
    }

    // Add solid edge: state →[σ] prestate
    pretableau.solidEdges.push({
      from: stateId,
      to: psId,
      label: [...sigma],
    });
  }

  return newPrestateIds;
}

/**
 * Check if move vector σ ∈ D(Δ, ⟨⟨A⟩⟩○ϕ) — positive case.
 *
 * D(Δ, ⟨⟨A⟩⟩○ϕ) is the set of move vectors where ALL agents in A
 * vote for the i-th positive formula (their move component = i).
 *
 * Each agent votes for a positive formula by playing move i (0-indexed).
 */
function inD_positive(
  sigma: MoveVector,
  coalition: Coalition,
  formulaIndex: number,
  allAgents: Coalition,
  _m: number
): boolean {
  for (const agent of coalition) {
    const agentIdx = allAgents.indexOf(agent);
    if (agentIdx < 0) return false; // Agent not in Σ
    if (sigma[agentIdx] !== formulaIndex) return false;
  }
  return true;
}

/**
 * Check if move vector σ ∈ D(Δ, ¬⟨⟨A⟩⟩○ψ) — negative case.
 *
 * D(Δ, ¬⟨⟨A'⟩⟩○ψ) is the set of move vectors where:
 *   neg(σ) = j (the j-th negative formula) AND
 *   Σ\A' ⊆ N(σ)  (all agents NOT in A' play "negative" moves)
 *
 * Where:
 *   N(σ) = set of agents i where σ_i ≥ m (playing a "negative" move)
 *   neg(σ) = [Σ_{i∈N(σ)} (σ_i - m)] mod l
 *
 * Reference: Section 4.2, Definition 4.7, p.18-19
 */
function inD_negative(
  sigma: MoveVector,
  coalitionA: Coalition,
  negFormulaIndex: number,
  allAgents: Coalition,
  m: number,
  l: number
): boolean {
  if (l === 0) return false;

  // Compute N(σ): agents playing negative moves (σ_i ≥ m)
  const negAgents = new Set<string>();
  for (let i = 0; i < allAgents.length; i++) {
    if (sigma[i]! >= m) {
      negAgents.add(allAgents[i]!);
    }
  }

  // Check: Σ\A' ⊆ N(σ) — all agents NOT in A' must play negative moves
  const complementA = coalitionComplement(coalitionA, allAgents);
  for (const agent of complementA) {
    if (!negAgents.has(agent)) return false;
  }

  // Compute neg(σ) = [Σ_{i∈N(σ)} (σ_i - m)] mod l
  let negSum = 0;
  for (let i = 0; i < allAgents.length; i++) {
    if (sigma[i]! >= m) {
      negSum += sigma[i]! - m;
    }
  }
  const negResult = negSum % l;

  return negResult === negFormulaIndex;
}

/**
 * Generate all move vectors in {0,...,k-1}^n.
 */
function generateMoveVectors(n: number, k: number): MoveVector[] {
  if (n === 0) return [[]];
  if (k === 0) return [];

  const result: MoveVector[] = [];
  const current = new Array(n).fill(0);

  while (true) {
    result.push([...current]);

    // Increment (like counting in base k)
    let carry = true;
    for (let i = n - 1; i >= 0 && carry; i--) {
      current[i]++;
      if (current[i]! >= k) {
        current[i] = 0;
      } else {
        carry = false;
      }
    }
    if (carry) break; // Overflow — done
  }

  return result;
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
 * Prestate elimination phase (Rule PR).
 *
 * For every prestate Γ:
 * 1. Remove Γ
 * 2. If state Δ →[σ] Γ, then for every Δ' ∈ states(Γ), put Δ →[σ] Δ'
 *
 * Result: initial tableau with only states and direct state→state edges.
 */
function prestateEliminationPhase(pretableau: Pretableau, allAgents: Coalition): Tableau {
  const tableau: Tableau = {
    states: new Map(pretableau.states),
    edges: [],
    allAgents,
  };

  // Build map: prestate ID → set of state IDs it expands to
  const prestateToStates = new Map<NodeId, Set<NodeId>>();
  for (const edge of pretableau.dashedEdges) {
    if (!prestateToStates.has(edge.from)) {
      prestateToStates.set(edge.from, new Set());
    }
    prestateToStates.get(edge.from)!.add(edge.to);
  }

  // For each solid edge Δ →[σ] Γ, replace with Δ →[σ] Δ' for each Δ' ∈ states(Γ)
  // Preserve viaPrestate so E3 can group edges by the prestate they passed through.
  // This is needed for the ∀-prestates, ∃-states pattern in eventuality realization.
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
 * Three elimination rules applied in dovetailed cycles:
 * (E1): Remove states that are patently inconsistent
 *       (this shouldn't happen if expansion is correct, but just in case)
 * (E2): Remove states where a next-time formula has no surviving successor
 *       for the required move vectors.
 * (E3): Remove states where an eventuality is not realized.
 *
 * For ATL, E2 checks: for each positive next-time formula ⟨⟨A⟩⟩○ϕ in state Δ,
 * there must exist at least one move vector σ ∈ D(Δ, ⟨⟨A⟩⟩○ϕ) such that
 * Δ →[σ] Δ' where Δ' survives. Similarly for negative.
 *
 * Actually, the paper says (Definition 4.9, p.19):
 * E2: eliminate state Δ if there exists a move vector σ such that
 *     Δ has no σ-successor in the tableau.
 *
 * That is: EVERY move vector must have at least one surviving successor.
 */
function stateEliminationPhase(initialTableau: Tableau, allAgents: Coalition): { tableau: Tableau; eliminations: EliminationRecord[] } {
  const states = new Map(initialTableau.states);
  let edges = [...initialTableau.edges];
  const eliminations: EliminationRecord[] = [];

  // Collect all eventualities appearing in any state
  const allEventualities = collectAllEventualities(states);

  // Dovetailed elimination loop
  let removedInCycle = true;
  while (removedInCycle) {
    removedInCycle = false;

    // Apply E2 (missing successors for move vectors)
    const e2Records = applyE2(states, edges, allAgents);
    if (e2Records.length > 0) {
      eliminations.push(...e2Records);
      removedInCycle = true;
      edges = edges.filter((e) => states.has(e.from) && states.has(e.to));
    }

    // Apply E3 for each eventuality
    for (const eventuality of allEventualities) {
      const e3Records = applyE3(states, edges, eventuality, allAgents);
      if (e3Records.length > 0) {
        eliminations.push(...e3Records);
        removedInCycle = true;
        edges = edges.filter((e) => states.has(e.from) && states.has(e.to));
      }

      // Re-apply E2 after E3 eliminations
      const e2After = applyE2(states, edges, allAgents);
      if (e2After.length > 0) {
        eliminations.push(...e2After);
        removedInCycle = true;
        edges = edges.filter((e) => states.has(e.from) && states.has(e.to));
      }
    }
  }

  edges = edges.filter((e) => states.has(e.from) && states.has(e.to));
  return { tableau: { states, edges, allAgents }, eliminations };
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
 * Rule (E2) — eliminate states where some move vector has no surviving successor.
 *
 * Definition 4.9 from the paper (p.19-20):
 * Eliminate state Δ if there exists a move vector σ ∈ {0,...,k-1}^|Σ|
 * such that Δ has no σ-successor in the tableau.
 *
 * In other words: EVERY move vector that should exist from this state
 * must have at least one surviving successor. If any move vector's
 * successors have all been eliminated, the state itself is eliminated.
 *
 * The required move vectors for a state are ALL vectors in {0,...,k-1}^n
 * where k = max(m+l, 1), m = # positive next-time formulas, l = # negative.
 */
function applyE2(
  states: Map<NodeId, State>,
  edges: SolidEdge[],
  allAgents: Coalition
): EliminationRecord[] {
  const records: EliminationRecord[] = [];
  let changed = true;

  while (changed) {
    changed = false;
    const toRemove: { id: NodeId; sigma: MoveVector }[] = [];

    for (const [id, state] of states) {
      // Count next-time formulas using three-category classification
      let m = 0; // enforceable (positive) next-time formulas
      let l = 0; // proper unavoidable (negative, coalition ≠ Σ)
      let agentsCount = 0; // agents unavoidable (negative, coalition = Σ)
      for (const f of state.formulas) {
        if (isPositiveNext(f)) {
          m++;
        } else if (isNegativeNext(f)) {
          if (f.kind === "not" && f.sub.kind === "next" &&
              coalitionEqual(normalizeCoalition([...f.sub.coalition]), allAgents)) {
            agentsCount++;
          } else {
            l++;
          }
        }
      }

      if (m === 0 && l === 0 && agentsCount === 0) continue; // No next-time formulas

      const k = Math.max(m + l, 1);
      const n = allAgents.length;
      const requiredMoveVectors = generateMoveVectors(n, k);

      // For each required move vector, check if there's a surviving successor
      for (const sigma of requiredMoveVectors) {
        const sigmaKey = sigma.join(",");
        const hasSurvivor = edges.some((e) => {
          if (e.from !== id) return false;
          if (!states.has(e.to)) return false;
          return e.label.join(",") === sigmaKey;
        });
        if (!hasSurvivor) {
          toRemove.push({ id, sigma });
          break; // One missing move vector is enough to eliminate
        }
      }
    }

    for (const { id, sigma } of toRemove) {
      if (!states.has(id)) continue;
      const state = states.get(id)!;
      records.push({
        stateId: id,
        rule: "E2",
        formula: state.formulas.toArray()[0]!, // Representative formula
        stateFormulas: state.formulas.clone(),
      });
      states.delete(id);
      changed = true;
    }
  }

  return records;
}

/**
 * Rule (E3) — eliminate states with unrealized eventualities.
 *
 * For ATL, the eventualities are:
 * - ⟨⟨A⟩⟩(ϕ U ψ): needs ψ to eventually hold along a strategic path
 * - ¬⟨⟨A⟩⟩□ϕ: needs ¬ϕ to eventually hold along a strategic path
 *
 * CRITICAL: The marking procedure must only follow edges that are
 * consistent with the eventuality's coalition strategy. Specifically:
 *
 * For eventuality ⟨⟨A⟩⟩(ϕ U ψ), which unfolds to ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ),
 * we can only follow edges whose move vector σ ∈ D(Δ, ⟨⟨A⟩⟩○⟨⟨A⟩⟩(ϕ U ψ)).
 *
 * For eventuality ¬⟨⟨A⟩⟩□ϕ, which unfolds to ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ,
 * we can only follow edges whose move vector σ ∈ D(Δ, ¬⟨⟨A⟩⟩○⟨⟨A⟩⟩□ϕ).
 *
 * This matches the TATL OCaml implementation (verif_edge / get_succ_to_be_verified_simpl).
 *
 * Marking procedure:
 * 1. Mark all states where the eventuality's goal is immediately realized
 * 2. Fixpoint: mark state Δ if it contains the eventuality and has a
 *    coalition-consistent edge to a marked successor
 * 3. Eliminate all unmarked states containing the eventuality
 */
function applyE3(
  states: Map<NodeId, State>,
  edges: SolidEdge[],
  eventuality: Formula,
  allAgents: Coalition
): EliminationRecord[] {
  const goal = eventualityGoal(eventuality);
  const nextFormula = eventualityNextFormula(eventuality);

  // Find all states containing this eventuality
  const statesWithEventuality = new Set<NodeId>();
  for (const [id, state] of states) {
    if (state.formulas.has(eventuality)) {
      statesWithEventuality.add(id);
    }
  }

  if (statesWithEventuality.size === 0) return [];

  // Marking procedure
  //
  // CRITICAL: Uses the ∀-prestates, ∃-states pattern from TATL.
  //
  // After prestate elimination, edges carry viaPrestate info. Two edges from
  // state S with the same viaPrestate correspond to different states expanded
  // from the same prestate. These are alternatives (∃: at least one must work).
  // But different prestates represent different strategic outcomes (∀: all must work).
  //
  // So to mark state S: for EACH consistent prestate P reachable from S,
  // there must exist at least one edge S→[σ]→S' via P where S' is marked.
  const marked = new Set<NodeId>();

  // Step 1: Mark all states containing the goal
  for (const [id, state] of states) {
    if (state.formulas.has(goal)) {
      marked.add(id);
    }
  }

  // Step 2: Fixpoint marking — ∀-prestates, ∃-states
  let fixpointChanged = true;
  while (fixpointChanged) {
    fixpointChanged = false;
    for (const id of statesWithEventuality) {
      if (marked.has(id)) continue;
      if (!states.has(id)) continue;

      const state = states.get(id)!;

      // Find the index of the next-time formula in this state's next-time formulas.
      const nextFormulaIndex = findNextFormulaIndex(state, nextFormula, allAgents);
      if (nextFormulaIndex === null) continue;

      // Collect all coalition-consistent edges from this state, grouped by viaPrestate.
      // Each group represents a prestate — ALL groups must have at least one marked successor.
      const prestateGroups = new Map<string, SolidEdge[]>();

      for (const edge of edges) {
        if (edge.from !== id) continue;
        if (!states.has(edge.to)) continue;

        if (isEdgeConsistentWithEventuality(edge.label, nextFormula, nextFormulaIndex, state, allAgents)) {
          const groupKey = edge.viaPrestate ?? edge.to; // fallback to edge.to if no prestate info
          if (!prestateGroups.has(groupKey)) {
            prestateGroups.set(groupKey, []);
          }
          prestateGroups.get(groupKey)!.push(edge);
        }
      }

      // If no consistent edges at all, can't mark
      if (prestateGroups.size === 0) continue;

      // ALL prestate groups must have at least one marked successor
      let allGroupsSatisfied = true;
      for (const [, groupEdges] of prestateGroups) {
        const groupHasMarked = groupEdges.some(e => marked.has(e.to));
        if (!groupHasMarked) {
          allGroupsSatisfied = false;
          break;
        }
      }

      if (allGroupsSatisfied) {
        marked.add(id);
        fixpointChanged = true;
      }
    }
  }

  // Step 3: Eliminate unmarked states containing the eventuality
  const records: EliminationRecord[] = [];
  for (const id of statesWithEventuality) {
    if (!marked.has(id) && states.has(id)) {
      const state = states.get(id)!;
      records.push({
        stateId: id,
        rule: "E3",
        formula: eventuality,
        stateFormulas: state.formulas.clone(),
      });
      states.delete(id);
    }
  }

  return records;
}

/**
 * Find the index of a next-time formula among a state's next-time formulas,
 * using the three-category classification.
 *
 * Returns { type, index } or null if not found.
 * - "positive": enforceable, indexed among enforceable formulas
 * - "negative": proper unavoidable (coalition ≠ Σ), indexed among proper unavoidable
 * - "agents": agents unavoidable (coalition = Σ), always fires — no index needed
 */
function findNextFormulaIndex(
  state: State,
  nextFormula: Formula,
  allAgents: Coalition
): { type: "positive" | "negative" | "agents"; index: number } | null {
  let posIdx = 0;
  let negIdx = 0;

  for (const f of state.formulas) {
    if (isPositiveNext(f)) {
      if (formulaEqual(f, nextFormula)) {
        return { type: "positive", index: posIdx };
      }
      posIdx++;
    } else if (isNegativeNext(f)) {
      const isAgentsUnavoidable = f.kind === "not" && f.sub.kind === "next" &&
        coalitionEqual(normalizeCoalition([...f.sub.coalition]), allAgents);
      if (formulaEqual(f, nextFormula)) {
        if (isAgentsUnavoidable) {
          return { type: "agents", index: 0 };
        }
        return { type: "negative", index: negIdx };
      }
      if (!isAgentsUnavoidable) {
        negIdx++;
      }
    }
  }

  return null;
}

/**
 * Check if an edge's move vector is consistent with an eventuality's coalition strategy.
 *
 * For a positive next-time formula ⟨⟨A⟩⟩○ϕ at index i:
 *   All agents in A must play i (vote for this formula).
 *
 * For a negative next-time formula ¬⟨⟨A'⟩⟩○ψ at index j:
 *   neg(σ) = j AND Σ\A' ⊆ N(σ)
 */
function isEdgeConsistentWithEventuality(
  sigma: MoveVector,
  nextFormula: Formula,
  nextFormulaIndex: { type: "positive" | "negative" | "agents"; index: number },
  state: State,
  allAgents: Coalition
): boolean {
  // Agents unavoidable: always fires — all edges are consistent
  if (nextFormulaIndex.type === "agents") {
    return true;
  }

  // Count enforceable / proper unavoidable next-time formulas (three-category)
  let m = 0;
  let l = 0;
  for (const f of state.formulas) {
    if (isPositiveNext(f)) {
      m++;
    } else if (isNegativeNext(f)) {
      const isAgentsUnav = f.kind === "not" && f.sub.kind === "next" &&
        coalitionEqual(normalizeCoalition([...f.sub.coalition]), allAgents);
      if (!isAgentsUnav) l++;
    }
  }

  if (nextFormulaIndex.type === "positive") {
    if (nextFormula.kind !== "next") return false;
    return inD_positive(sigma, nextFormula.coalition, nextFormulaIndex.index, allAgents, m);
  } else {
    if (nextFormula.kind !== "not" || nextFormula.sub.kind !== "next") return false;
    const A = nextFormula.sub.coalition;
    return inD_negative(sigma, A, nextFormulaIndex.index, allAgents, m, l);
  }
}
