/**
 * Text-based visualization of tableau results for CLI output.
 * Also generates DOT (Graphviz) format for graph rendering.
 */

import {
  type Pretableau,
  type Tableau,
  type TableauResult,
  type StateFormula,
  type StateFormulaSet,
  type Coalition,
  type MoveVector,
  type SolidEdge,
  type NodeId,
  type EliminationRecord,
  type RealizationFailure,
  stateKey,
} from "../core/types.ts";
import { printFormula, printFormulaSet, printFormulaUnicode, printMoveVector, printPathAscii, printPathUnicode, type Notation } from "../core/printer.ts";
import { extractModel, type Model } from "../core/model.ts";

// ============================================================
// Model
// ============================================================

export function textModel(model: Model, notation: Notation): string {
  const lines: string[] = [];
  lines.push(`Model (${model.states.length} state${model.states.length === 1 ? "" : "s"}, initial ${model.initial}):`);
  for (const st of model.states) {
    const lits = st.literals.length > 0 ? st.literals.map((l) => printFormula(l, notation)).join(", ") : "(any valuation)";
    lines.push(`  ${st.id}: ${lits}`);
  }
  for (const e of model.edges) {
    lines.push(`  ${e.from} --[${printMoveVector(e.label, model.agents)}]--> ${e.to}`);
  }
  return lines.join("\n");
}

export function modelToDot(model: Model, notation: Notation): string {
  const lines: string[] = [];
  lines.push("digraph model {");
  lines.push("  rankdir=LR;");
  lines.push("  bgcolor=transparent;");
  lines.push('  node [shape=circle, style="filled", fillcolor="#f8f9fa", color="#d0d0d0", fontsize=11, fontname="Helvetica"];');
  lines.push('  edge [fontsize=9, fontname="Helvetica", color="#888"];');
  lines.push('  "__start" [shape=point, style=invis];');
  for (const st of model.states) {
    const lits = st.literals.map((l) => printFormulaUnicode(l, notation)).join(", ");
    const label = `${st.id}\n${lits}`;
    const initial = st.id === model.initial;
    lines.push(`  "${st.id}" [label="${escDot(label)}", fillcolor="${initial ? "#dcfce7" : "#f8f9fa"}", color="${initial ? "#86d997" : "#d0d0d0"}", penwidth=${initial ? 2 : 1}, tooltip="${escDot("built from tableau states " + st.tableauStates.join(", "))}"];`);
  }
  lines.push(`  "__start" -> "${model.initial}";`);
  // Merge parallel edges between the same states into one label
  const merged = new Map<string, { from: string; to: string; labels: string[] }>();
  for (const e of model.edges) {
    const k = `${e.from}|${e.to}`;
    if (!merged.has(k)) merged.set(k, { from: e.from, to: e.to, labels: [] });
    merged.get(k)!.labels.push(formatMoveVector(e.label, model.agents));
  }
  const singleMove = model.states.every((st) => model.edges.filter((e) => e.from === st.id).length <= 1);
  for (const e of merged.values()) {
    const label = singleMove ? "" : ` ${e.labels.join(" | ")} `;
    lines.push(`  "${e.from}" -> "${e.to}" [label="${escDot(label)}", color="#2e7d57", fontcolor="#2e7d57"];`);
  }
  lines.push("}");
  return lines.join("\n");
}

// ============================================================
// Proof of unsatisfiability
// ============================================================

/**
 * The elimination of the initial states, explained: each initial state's
 * record, then the records it depends on, as an indented tree. A state is
 * explained once; later references point back to it.
 */
export function textProof(result: TableauResult, notation: Notation): string {
  const lines: string[] = [];
  const byId = new Map<NodeId, EliminationRecord>();
  for (const rec of result.eliminations) if (!byId.has(rec.stateId)) byId.set(rec.stateId, rec);

  if (result.inputFormula.kind === "bot") {
    lines.push("The formula simplifies to ⊥ (it contains a formula together with its negation).");
    return lines.join("\n");
  }
  if (result.initialStateIds.length === 0) {
    lines.push("Every expansion of the input formula is patently inconsistent: no state could be built.");
    return lines.join("\n");
  }

  lines.push(`Proof: every initial state (${result.initialStateIds.join(", ")}) is eliminated.`);
  const explained = new Set<NodeId>();

  const stateLabel = (id: NodeId) => {
    const st = result.initialTableau.states.get(id);
    return st ? printFormulaSet(st.formulas, notation) : "";
  };

  const explainState = (id: NodeId, indent: string): void => {
    const rec = byId.get(id);
    if (!rec) { lines.push(`${indent}${id} survives`); return; }
    if (explained.has(id)) { lines.push(`${indent}${id}: eliminated (see above)`); return; }
    explained.add(id);
    const ex = rec.explanation;
    if (!ex) { lines.push(`${indent}${id}: eliminated by ${rec.rule}`); return; }
    if (ex.kind === "E2") {
      lines.push(`${indent}${id} ${stateLabel(id)}`);
      lines.push(`${indent}  E2: move ${printMoveVector(ex.moveVector, result.allAgents)} has no surviving successor. Its candidates:`);
      if (ex.successors.length === 0) lines.push(`${indent}    (none: the successor prestate expanded to nothing consistent)`);
      for (const succ of ex.successors) explainState(succ, indent + "    ");
    } else {
      lines.push(`${indent}${id} ${stateLabel(id)}`);
      lines.push(`${indent}  E3: eventuality ${printFormula(ex.eventuality, notation)} cannot be realized; pending: ${printPathAscii(ex.residual, notation)}`);
      explainFailure(ex.failure, indent + "    ");
    }
  };

  const explainFailure = (f: RealizationFailure, indent: string): void => {
    if (f.seeAbove) {
      lines.push(`${indent}(explained above)`);
      return;
    }
    if (f.prestateId === null) {
      lines.push(`${indent}no successor prestate is consistent with the eventuality`);
      return;
    }
    if (f.options.length === 0) {
      lines.push(`${indent}via ${f.prestateId}: no surviving successor carries the eventuality`);
      return;
    }
    lines.push(`${indent}via ${f.prestateId}, every successor fails:`);
    for (const opt of f.options) {
      const pend = printPathAscii(opt.residual, notation);
      switch (opt.status) {
        case "eliminated":
          lines.push(`${indent}  ${opt.stateId}: eliminated`);
          explainState(opt.stateId, indent + "    ");
          break;
        case "cycle":
          lines.push(`${indent}  ${opt.stateId}: returns to a state already on this path with ${pend} still pending`);
          break;
        case "truncated":
          lines.push(`${indent}  ${opt.stateId}: still pending ${pend} (explanation truncated)`);
          break;
        case "unrealizable":
          lines.push(`${indent}  ${opt.stateId}: still pending ${pend}`);
          if (opt.failure) explainFailure(opt.failure, indent + "    ");
          break;
      }
    }
  };

  for (const id of result.initialStateIds) explainState(id, "  ");
  return lines.join("\n");
}

/**
 * Generate a complete text summary of a tableau result.
 */
export function textSummary(result: TableauResult, notation: Notation = "atl"): string {
  const lines: string[] = [];

  lines.push("=".repeat(60));
  lines.push("ATL* Tableau Decision Procedure");
  lines.push("=".repeat(60));
  lines.push("");
  lines.push(`Input formula: ${printFormula(result.originalFormula, notation)}`);
  if (stateKey(result.originalFormula) !== stateKey(result.inputFormula)) {
    lines.push(`Simplified to:  ${printFormula(result.inputFormula, notation)}`);
  }
  const agents = [...result.allAgents];
  lines.push(`Agents: {${agents.join(", ")}}`);
  lines.push("");

  // Pretableau summary
  lines.push("--- Phase 1: Construction (Pretableau) ---");
  lines.push(`  Prestates: ${result.pretableau.prestates.size}`);
  lines.push(`  States: ${result.pretableau.states.size}`);
  lines.push(`  Dashed edges (search): ${result.pretableau.dashedEdges.length}`);
  lines.push(`  Solid edges (transitions): ${result.pretableau.solidEdges.length}`);
  lines.push("");

  // Initial tableau summary
  lines.push("--- Phase 2: Prestate Elimination (Initial Tableau) ---");
  lines.push(`  States: ${result.initialTableau.states.size}`);
  lines.push(`  Edges: ${result.initialTableau.edges.length}`);
  lines.push("");

  // Final tableau summary
  lines.push("--- Phase 3: State Elimination (Final Tableau) ---");
  lines.push(`  States: ${result.finalTableau.states.size}`);
  lines.push(`  Edges: ${result.finalTableau.edges.length}`);
  if (result.unreachable.length > 0) {
    lines.push(`  Dropped as unreachable from the initial states: ${result.unreachable.length}`);
  }
  lines.push("");

  // Result
  lines.push("=".repeat(60));
  if (result.satisfiable) {
    lines.push("RESULT: SATISFIABLE");
    lines.push("");
    lines.push("Satisfying initial states:");
    for (const id of result.initialStateIds) {
      const state = result.finalTableau.states.get(id);
      if (state) lines.push(`  ${id}: ${printFormulaSet(state.formulas, notation)}`);
    }
    lines.push("");
    const model = extractModel(result);
    if (model) {
      lines.push(textModel(model, notation));
    } else {
      lines.push("Model: too large to extract");
    }
  } else {
    lines.push("RESULT: UNSATISFIABLE");
    lines.push("");
    lines.push(textProof(result, notation));
  }
  lines.push("=".repeat(60));

  return lines.join("\n");
}

/**
 * Generate verbose text showing all states in each phase.
 */
export function textVerbose(result: TableauResult, notation: Notation = "atl"): string {
  const lines: string[] = [textSummary(result, notation), ""];

  // Pretableau detail
  lines.push("=== Pretableau States ===");
  for (const [id, state] of result.pretableau.states) {
    lines.push(`  ${id}: ${printFormulaSet(state.formulas, notation)}`);
  }
  lines.push("");
  lines.push("=== Pretableau Prestates ===");
  for (const [id, ps] of result.pretableau.prestates) {
    lines.push(`  ${id}: ${printFormulaSet(ps.formulas, notation)}`);
  }
  lines.push("");

  // Initial tableau states
  lines.push("=== Initial Tableau States ===");
  for (const [id, state] of result.initialTableau.states) {
    lines.push(`  ${id}: ${printFormulaSet(state.formulas, notation)}`);
  }
  lines.push("");
  lines.push("=== Initial Tableau Edges ===");
  for (const edge of result.initialTableau.edges) {
    lines.push(`  ${edge.from} --[${printMoveVector(edge.label, result.allAgents)}]--> ${edge.to}`);
  }
  lines.push("");

  // Final tableau states
  lines.push("=== Final Tableau States ===");
  if (result.finalTableau.states.size === 0) {
    lines.push("  (empty)");
  }
  for (const [id, state] of result.finalTableau.states) {
    lines.push(`  ${id}: ${printFormulaSet(state.formulas, notation)}`);
  }
  lines.push("");
  lines.push("=== Final Tableau Edges ===");
  if (result.finalTableau.edges.length === 0) {
    lines.push("  (none)");
  }
  for (const edge of result.finalTableau.edges) {
    lines.push(`  ${edge.from} --[${printMoveVector(edge.label, result.allAgents)}]--> ${edge.to}`);
  }

  return lines.join("\n");
}

/** Options for DOT generation */
export interface DotOptions {
  /** Show full formula sets in node labels instead of just counts */
  detailedLabels?: boolean;
  /** Show eliminated states (only for "final" phase) as faded red nodes */
  showEliminated?: boolean;
  /** Surface syntax for coalition operators (default: ATL* brackets) */
  notation?: Notation;
}

/**
 * Format a formula set for DOT tooltip (one formula per line, Unicode).
 */
function formulaSetTooltip(fs: StateFormulaSet, notation: Notation): string {
  return fs.toArray().map((f) => printFormulaUnicode(f, notation)).join("\n");
}

/**
 * Generate a compact label: state ID + formula count.
 */
function compactLabel(id: string, fs: StateFormulaSet): string {
  return `${id}\n(${fs.size} formulas)`;
}

/**
 * Generate a detailed label: state ID + all formulas.
 */
function detailedLabel(id: string, fs: StateFormulaSet, notation: Notation): string {
  const formulas = fs.toArray().map((f) => printFormulaUnicode(f, notation));
  return id + "\n" + "\u2500".repeat(Math.min(id.length + 6, 20)) + "\n" + formulas.join("\n");
}

/**
 * Build a node label based on options.
 */
function nodeLabel(id: string, fs: StateFormulaSet, detailed: boolean, notation: Notation): string {
  return detailed ? detailedLabel(id, fs, notation) : compactLabel(id, fs);
}

/**
 * Escape text for HTML-like labels in DOT.
 */
function escapeHtml(s: string): string {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

/**
 * Format move vector for display.
 */
function formatMoveVector(mv: MoveVector, agents?: Coalition): string {
  if (agents && agents.length === mv.length) {
    return mv.map((v, i) => `${agents[i]}:${v}`).join(",");
  }
  return mv.join(",");
}

/**
 * Generate DOT (Graphviz) format for a tableau.
 */
export function toDot(
  result: TableauResult,
  phase: "pretableau" | "initial" | "final" = "final",
  options: DotOptions = {}
): string {
  const detailed = options.detailedLabels ?? false;
  const showEliminated = options.showEliminated ?? false;
  const notation = options.notation ?? "atl";
  const allAgents = result.allAgents;
  const lines: string[] = [];
  lines.push("digraph tableau {");
  lines.push("  rankdir=TB;");
  lines.push("  bgcolor=transparent;");
  lines.push("  newrank=true;");
  lines.push('  node [shape=box, style="filled,rounded", fillcolor="#f8f9fa", color="#d0d0d0", fontsize=11, fontname="Helvetica"];');
  lines.push('  edge [fontsize=9, fontname="Helvetica", color="#888"];');
  lines.push("");

  if (phase === "pretableau") {
    // Prestates as dashed ellipses
    for (const [id, ps] of result.pretableau.prestates) {
      const tooltip = formulaSetTooltip(ps.formulas, notation);
      const label = nodeLabel(id, ps.formulas, detailed, notation);
      lines.push(`  "${id}" [label="${escDot(label)}", shape=ellipse, style="dashed,filled", fillcolor="#fafafa", tooltip="${escDot(tooltip)}"];`);
    }
    // States as boxes
    for (const [id, state] of result.pretableau.states) {
      const tooltip = formulaSetTooltip(state.formulas, notation);
      const hasInput = state.formulas.has(result.inputFormula);
      const fill = hasInput ? "#d4edda" : "#f8f9fa";
      const border = hasInput ? "#82c091" : "#d0d0d0";
      const label = nodeLabel(id, state.formulas, detailed, notation);
      lines.push(`  "${id}" [label="${escDot(label)}", fillcolor="${fill}", color="${border}", tooltip="${escDot(tooltip)}"];`);
    }
    // Dashed edges (prestate → state expansion)
    for (const edge of result.pretableau.dashedEdges) {
      lines.push(`  "${edge.from}" -> "${edge.to}" [style=dashed, color="#bbb"];`);
    }
    // Solid edges (state → prestate transitions with move vectors)
    for (const edge of result.pretableau.solidEdges) {
      const mvLabel = formatMoveVector(edge.label, allAgents);
      lines.push(`  "${edge.from}" -> "${edge.to}" [label=" ${escDot(mvLabel)} ", color="#2e7d57", fontcolor="#2e7d57"];`);
    }
  } else {
    const tableau = phase === "initial" ? result.initialTableau : result.finalTableau;

    // Build elimination lookup for the final phase
    const eliminationMap = new Map<string, string>();
    if (showEliminated && phase === "final" && result.eliminations) {
      for (const rec of result.eliminations) {
        if (!eliminationMap.has(rec.stateId)) {
          const reason = rec.rule === "E2"
            ? `E2: next-time formula ${printFormulaUnicode(rec.formula, notation)} has no successor`
            : rec.rule === "E3"
              ? `E3: eventuality ${printFormulaUnicode(rec.formula, notation)} unrealized`
              : `E1: patent inconsistency`;
          eliminationMap.set(rec.stateId, reason);
        }
      }
    }

    // Surviving states
    for (const [id, state] of tableau.states) {
      const tooltip = formulaSetTooltip(state.formulas, notation);
      const hasInput = state.formulas.has(result.inputFormula);
      const fill = hasInput ? "#dcfce7" : "#f8f9fa";
      const border = hasInput ? "#86d997" : "#d0d0d0";
      const penwidth = hasInput ? "2" : "1";
      const label = nodeLabel(id, state.formulas, detailed, notation);
      lines.push(`  "${id}" [label="${escDot(label)}", fillcolor="${fill}", color="${border}", penwidth=${penwidth}, tooltip="${escDot(tooltip)}"];`);
    }

    // Eliminated states (shown as faded red)
    if (showEliminated && phase === "final") {
      for (const [id, state] of result.initialTableau.states) {
        if (tableau.states.has(id)) continue;
        const reason = eliminationMap.get(id) || "eliminated";
        const elimLabel = detailed
          ? detailedLabel(id + " \u2717", state.formulas, notation)
          : `${id} \u2717\n${reason}`;
        const tooltip = reason + "\n\n" + formulaSetTooltip(state.formulas, notation);
        lines.push(`  "${id}" [label="${escDot(elimLabel)}", fillcolor="#fee2e2", color="#e5a0a0", fontcolor="#999", style="filled,rounded,dashed", tooltip="${escDot(tooltip)}"];`);
      }

      // Show edges involving eliminated states as dashed
      for (const edge of result.initialTableau.edges) {
        if (tableau.states.has(edge.from) && tableau.states.has(edge.to)) continue;
        const mvLabel = formatMoveVector(edge.label, allAgents);
        lines.push(`  "${edge.from}" -> "${edge.to}" [label=" ${escDot(mvLabel)} ", fontcolor="#88888866", color="#88888866", style=dashed];`);
      }
    }

    // Surviving edges
    for (const edge of tableau.edges) {
      const mvLabel = formatMoveVector(edge.label, allAgents);
      lines.push(`  "${edge.from}" -> "${edge.to}" [label=" ${escDot(mvLabel)} ", color="#2e7d57", fontcolor="#2e7d57"];`);
    }
  }

  lines.push("}");
  return lines.join("\n");
}

function escDot(s: string): string {
  return s.replace(/\\/g, "\\\\").replace(/"/g, '\\"').replace(/\n/g, "\\n");
}
