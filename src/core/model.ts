/**
 * Model extraction: a small concurrent game structure satisfying the input
 * formula, read off an open final tableau.
 *
 * The final tableau is not itself a model: it is the union of every
 * consistent bookkeeping state, and a state's eventualities are only
 * guaranteed realizable along *some* successors. A model picks, for every
 * state and every move vector, one successor, in such a way that every
 * eventuality is eventually realized. This is the construction of the
 * completeness proof, made concrete:
 *
 *   - a model state is a tableau state together with the *chains* it still
 *     owes: eventualities (with their residual) carried from earlier states,
 *     oldest first;
 *   - the oldest chain is in focus. For move vectors consistent with it, the
 *     successor is chosen from the realization oracle's witness, always
 *     stepping to a strictly lower rank, so the chain dies in finitely many
 *     steps on every path that keeps it. Other chains ride along;
 *   - for other move vectors the successor is free, and is chosen to close
 *     the structure as early as possible.
 *
 * Every chain becomes the oldest one eventually, so every eventuality of
 * every state is realized. The structure is then minimised by bisimulation
 * over literal labels and move-labelled transitions.
 */

import {
  type StateFormula,
  type PathFormula,
  type FormulaTuple,
  type Coalition,
  type MoveVector,
  type NodeId,
  type State,
  type SolidEdge,
  type TableauResult,
  stateKey,
  pathKey,
} from "./types.ts";
import { isEventuality } from "./formula.ts";
import {
  RealizationOracle,
  realizationKey,
  whatfalse,
  getTuple,
  getSuccToBeVerified,
  getEvNonImmReal,
  type StateNextInfo,
} from "./tableau.ts";

// ============================================================
// Public types
// ============================================================

export interface ModelState {
  id: string;
  /** Literals (p, ¬p) true at this state */
  literals: StateFormula[];
  /** Tableau states this model state was built from */
  tableauStates: NodeId[];
}

export interface ModelEdge {
  from: string;
  to: string;
  label: MoveVector;
}

export interface Model {
  states: ModelState[];
  edges: ModelEdge[];
  initial: string;
  agents: Coalition;
  /** Size of the structure before bisimulation minimisation */
  unminimisedStates: number;
}

/** Give up beyond this many product nodes rather than hang the UI. */
const MAX_NODES = 4000;

// ============================================================
// Chains
// ============================================================

interface Chain {
  tuple: FormulaTuple;
  residual: PathFormula;
}

function chainKey(c: Chain): string {
  return `${stateKey(c.tuple.frm)}|${pathKey(c.residual)}`;
}

interface Node {
  key: string;
  stateId: NodeId;
  chains: Chain[];
}

function nodeKey(stateId: NodeId, chains: Chain[]): string {
  return `${stateId}#${chains.map(chainKey).join(";")}`;
}

/**
 * Carry a chain from state `from` through prestate `via` to state `to`.
 * Returns null when the chain is realized or drops (the move is not one the
 * chain's eventuality constrains).
 */
function carry(
  chain: Chain,
  from: State,
  via: NodeId,
  to: State,
  edges: SolidEdge[],
  allAgents: Coalition,
  suppressed: Set<NodeId>
): Chain | null {
  const consistent = getSuccToBeVerified(chain.tuple, from.id, from, edges, allAgents, suppressed);
  if (!consistent.includes(via)) return null;
  if (!isEventuality(chain.tuple.nextFrm)) return null;
  const evTuple = getTuple(chain.tuple.nextFrm, to.tuples);
  if (!evTuple) return null;
  const residual = whatfalse(chain.residual, to.formulas, evTuple.pathFrm);
  if (residual.kind === "state" && residual.sub.kind === "top") return null;
  return { tuple: evTuple, residual };
}

/** The chains a state owes on its own account. */
function ownChains(state: State, suppressed: Set<NodeId>): Chain[] {
  return getEvNonImmReal(state, suppressed).map(({ ev, residual }) => ({ tuple: ev, residual }));
}

function allMoveVectors(state: State, allAgents: Coalition): MoveVector[] {
  const info = state as State & Partial<StateNextInfo>;
  const k = info._moveVecCount ?? 1;
  const n = allAgents.length;
  const total = Math.pow(k, n);
  const out: MoveVector[] = [];
  for (let i = 0; i < total; i++) {
    const mv: number[] = [];
    let rem = i;
    for (let j = n - 1; j >= 0; j--) {
      mv.unshift(rem % k);
      rem = Math.floor(rem / k);
    }
    out.push(mv);
  }
  return out;
}

// ============================================================
// Extraction
// ============================================================

export function extractModel(result: TableauResult): Model | null {
  if (!result.satisfiable) return null;
  const oracle = result.realization as RealizationOracle;
  const tableau = result.finalTableau;
  const allAgents = result.allAgents;
  const suppressed = new Set<NodeId>();
  const edges = tableau.edges;

  // Successors of a state per move vector: prestate and candidate states
  const succIndex = new Map<string, { via: NodeId; states: NodeId[] }>();
  for (const e of edges) {
    const k = `${e.from}|${e.label.join(",")}`;
    let entry = succIndex.get(k);
    if (!entry) {
      entry = { via: e.viaPrestate ?? "", states: [] };
      succIndex.set(k, entry);
    }
    if (!entry.states.includes(e.to)) entry.states.push(e.to);
  }

  const literalsOf = (s: State) =>
    s.formulas.toArray().filter((f) => f.kind === "atom" || (f.kind === "neg" && f.sub.kind === "atom"));

  // Initial state: the surviving initial state with the least to do
  const initialCandidates = result.initialStateIds
    .filter((id) => tableau.states.has(id))
    .map((id) => tableau.states.get(id)!);
  if (initialCandidates.length === 0) return null;
  initialCandidates.sort((a, b) =>
    ownChains(a, suppressed).length - ownChains(b, suppressed).length ||
    literalsOf(a).length - literalsOf(b).length ||
    a.formulas.size - b.formulas.size);
  const initialState = initialCandidates[0]!;

  const nodes = new Map<string, Node>();
  const transitions = new Map<string, Map<string, string>>(); // node key -> mv key -> node key
  const mvOf = new Map<string, MoveVector>();

  const mkNode = (stateId: NodeId, chains: Chain[]): Node => {
    const key = nodeKey(stateId, chains);
    let n = nodes.get(key);
    if (!n) {
      n = { key, stateId, chains };
      nodes.set(key, n);
    }
    return n;
  };

  const initial = mkNode(initialState.id, ownChains(initialState, suppressed));
  const queue: Node[] = [initial];
  let qi = 0;

  while (qi < queue.length) {
    const node = queue[qi++]!;
    if (transitions.has(node.key)) continue;
    if (nodes.size > MAX_NODES) return null;
    const state = tableau.states.get(node.stateId)!;
    const out = new Map<string, string>();
    transitions.set(node.key, out);

    for (const mv of allMoveVectors(state, allAgents)) {
      const mvKey = mv.join(",");
      mvOf.set(mvKey, mv);
      const succ = succIndex.get(`${node.stateId}|${mvKey}`);
      if (!succ || succ.states.length === 0) continue; // cannot happen in a final tableau (E2)

      // Chains carried to each candidate successor
      const candidates = succ.states.map((id) => {
        const t = tableau.states.get(id)!;
        const carried: Chain[] = [];
        for (const c of node.chains) {
          const c2 = carry(c, state, succ.via, t, edges, allAgents, suppressed);
          if (c2) carried.push(c2);
        }
        const present = new Set(carried.map(chainKey));
        for (const c of ownChains(t, suppressed)) {
          const k = chainKey(c);
          if (!present.has(k)) { present.add(k); carried.push(c); }
        }
        return { id, state: t, chains: carried };
      });

      // Focus: the oldest chain. If this move is one it constrains, follow
      // the oracle's witness: an option of strictly lower rank.
      let chosen: typeof candidates[number] | null = null;
      const focus = node.chains[0];
      if (focus) {
        const key = realizationKey(node.stateId, focus.tuple.frm, focus.residual);
        oracle.realizableNode(node.stateId, focus.tuple, focus.residual);
        const group = oracle.groupsOf(key).find((g) => g.prestateId === succ.via);
        if (group) {
          const myRank = oracle.rankOf(key);
          let best: { id: NodeId; rank: number } | null = null;
          for (const opt of group.options) {
            const r = oracle.rankOf(opt.key);
            if (r < myRank && (!best || r < best.rank)) best = { id: opt.stateId, rank: r };
          }
          if (best) chosen = candidates.find((c) => c.id === best!.id) ?? null;
        }
      }

      if (!chosen) {
        // Free choice: close the structure if possible, else keep it small
        const scored = candidates.map((c) => ({
          c,
          existing: nodes.has(nodeKey(c.id, c.chains)) ? 0 : 1,
          chains: c.chains.length,
          literals: literalsOf(c.state).length,
          size: c.state.formulas.size,
        }));
        scored.sort((x, y) => x.existing - y.existing || x.chains - y.chains || x.literals - y.literals || x.size - y.size);
        chosen = scored[0]!.c;
      }

      const target = mkNode(chosen.id, chosen.chains);
      out.set(mvKey, target.key);
      if (!transitions.has(target.key)) queue.push(target);
    }
  }

  // ------------------------------------------------------------
  // Bisimulation minimisation
  // ------------------------------------------------------------

  const nodeList = [...nodes.values()].filter((n) => transitions.has(n.key));
  const literalKey = (n: Node) =>
    literalsOf(tableau.states.get(n.stateId)!).map(stateKey).sort().join(",");

  let block = new Map<string, number>();
  {
    const byLabel = new Map<string, number>();
    for (const n of nodeList) {
      const lk = literalKey(n) + "#" + [...transitions.get(n.key)!.keys()].sort().join("|");
      if (!byLabel.has(lk)) byLabel.set(lk, byLabel.size);
      block.set(n.key, byLabel.get(lk)!);
    }
  }
  while (true) {
    const signature = new Map<string, number>();
    const next = new Map<string, number>();
    for (const n of nodeList) {
      const sig = block.get(n.key) + "#" +
        [...transitions.get(n.key)!.entries()]
          .sort(([a], [b]) => (a < b ? -1 : 1))
          .map(([mv, tk]) => `${mv}>${block.get(tk)}`)
          .join("|");
      if (!signature.has(sig)) signature.set(sig, signature.size);
      next.set(n.key, signature.get(sig)!);
    }
    // Refinement only ever splits blocks, so it is stable once the count stops growing
    const stable = new Set(next.values()).size === new Set(block.values()).size;
    block = next;
    if (stable) break;
  }

  // Number the blocks in BFS order from the initial node
  const idOf = new Map<number, string>();
  const order: number[] = [];
  const seen = new Set<number>();
  const bq = [block.get(initial.key)!];
  seen.add(bq[0]!);
  const repOf = new Map<number, Node>();
  for (const n of nodeList) if (!repOf.has(block.get(n.key)!)) repOf.set(block.get(n.key)!, n);
  // a representative per block whose transitions we follow for BFS order
  while (bq.length > 0) {
    const b = bq.shift()!;
    order.push(b);
    const rep = repOf.get(b)!;
    for (const [, tk] of [...transitions.get(rep.key)!.entries()].sort(([a], [c]) => (a < c ? -1 : 1))) {
      const tb = block.get(tk)!;
      if (!seen.has(tb)) { seen.add(tb); bq.push(tb); }
    }
  }
  order.forEach((b, i) => idOf.set(b, `m${i}`));

  const states: ModelState[] = order.map((b) => {
    const members = nodeList.filter((n) => block.get(n.key) === b);
    const tableauStates = [...new Set(members.map((n) => n.stateId))].sort();
    return {
      id: idOf.get(b)!,
      literals: literalsOf(tableau.states.get(members[0]!.stateId)!),
      tableauStates,
    };
  });

  const edgeSet = new Map<string, ModelEdge>();
  for (const n of nodeList) {
    const from = idOf.get(block.get(n.key)!)!;
    for (const [mvKey, tk] of transitions.get(n.key)!) {
      const to = idOf.get(block.get(tk)!)!;
      const k = `${from}|${mvKey}|${to}`;
      if (!edgeSet.has(k)) edgeSet.set(k, { from, to, label: mvOf.get(mvKey)! });
    }
  }
  const edges2 = [...edgeSet.values()].sort((a, b) =>
    a.from.localeCompare(b.from, undefined, { numeric: true }) ||
    a.label.join(",").localeCompare(b.label.join(",")) ||
    a.to.localeCompare(b.to, undefined, { numeric: true }));

  return {
    states,
    edges: edges2,
    initial: idOf.get(block.get(initial.key)!)!,
    agents: allAgents,
    unminimisedStates: nodeList.length,
  };
}
