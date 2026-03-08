/**
 * Text-based visualization of tableau results for CLI output.
 * Also generates DOT (Graphviz) format for graph rendering.
 */

import {
  type Pretableau,
  type Tableau,
  type TableauResult,
  type Formula,
  type FormulaSet,
  type Coalition,
  type SolidEdge,
} from "../core/types.ts";
import { printFormula, printFormulaSet, printFormulaUnicode } from "../core/printer.ts";
import { agentsInFormula } from "../core/formula.ts";

/**
 * Generate a complete text summary of a tableau result.
 */
export function textSummary(result: TableauResult): string {
  const lines: string[] = [];

  lines.push("=".repeat(60));
  lines.push("CMAEL(CD) Tableau Decision Procedure");
  lines.push("=".repeat(60));
  lines.push("");
  lines.push(`Input formula: ${printFormula(result.inputFormula)}`);
  const agents = [...agentsInFormula(result.inputFormula)].sort();
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
  lines.push("");

  // Result
  lines.push("=".repeat(60));
  if (result.satisfiable) {
    lines.push("RESULT: SATISFIABLE");
    lines.push("");
    lines.push("Satisfying states:");
    for (const [id, state] of result.finalTableau.states) {
      if (state.formulas.has(result.inputFormula)) {
        lines.push(`  ${id}: ${printFormulaSet(state.formulas)}`);
      }
    }
  } else {
    lines.push("RESULT: UNSATISFIABLE");
  }
  lines.push("=".repeat(60));

  return lines.join("\n");
}

/**
 * Generate verbose text showing all states in each phase.
 */
export function textVerbose(result: TableauResult): string {
  const lines: string[] = [textSummary(result), ""];

  // Pretableau detail
  lines.push("=== Pretableau States ===");
  for (const [id, state] of result.pretableau.states) {
    lines.push(`  ${id}: ${printFormulaSet(state.formulas)}`);
  }
  lines.push("");
  lines.push("=== Pretableau Prestates ===");
  for (const [id, ps] of result.pretableau.prestates) {
    lines.push(`  ${id}: ${printFormulaSet(ps.formulas)}`);
  }
  lines.push("");

  // Initial tableau states
  lines.push("=== Initial Tableau States ===");
  for (const [id, state] of result.initialTableau.states) {
    lines.push(`  ${id}: ${printFormulaSet(state.formulas)}`);
  }
  lines.push("");
  lines.push("=== Initial Tableau Edges ===");
  for (const edge of result.initialTableau.edges) {
    lines.push(`  ${edge.from} --[${printFormula(edge.label)}]--> ${edge.to}`);
  }
  lines.push("");

  // Final tableau states
  lines.push("=== Final Tableau States ===");
  if (result.finalTableau.states.size === 0) {
    lines.push("  (empty)");
  }
  for (const [id, state] of result.finalTableau.states) {
    lines.push(`  ${id}: ${printFormulaSet(state.formulas)}`);
  }
  lines.push("");
  lines.push("=== Final Tableau Edges ===");
  if (result.finalTableau.edges.length === 0) {
    lines.push("  (none)");
  }
  for (const edge of result.finalTableau.edges) {
    lines.push(`  ${edge.from} --[${printFormula(edge.label)}]--> ${edge.to}`);
  }

  return lines.join("\n");
}

/** Options for DOT generation */
export interface DotOptions {
  /** Show full formula sets in node labels instead of just counts */
  detailedLabels?: boolean;
  /** Show eliminated states (only for "final" phase) as faded red nodes */
  showEliminated?: boolean;
}

/**
 * Format a formula set for DOT tooltip (one formula per line, Unicode).
 */
function formulaSetTooltip(fs: FormulaSet): string {
  return fs.toArray().map(printFormulaUnicode).join("\n");
}

/**
 * Generate a compact label: state ID + formula count.
 */
function compactLabel(id: string, fs: FormulaSet): string {
  return `${id}\n(${fs.size} formulas)`;
}

/**
 * Generate a detailed label: state ID + all formulas.
 * Uses \l for left-aligned lines in DOT.
 */
function detailedLabel(id: string, fs: FormulaSet): string {
  const formulas = fs.toArray().map(printFormulaUnicode);
  return id + "\n" + "─".repeat(Math.min(id.length + 6, 20)) + "\n" + formulas.join("\n");
}

/**
 * Build a node label based on options.
 */
function nodeLabel(id: string, fs: FormulaSet, detailed: boolean): string {
  return detailed ? detailedLabel(id, fs) : compactLabel(id, fs);
}

/**
 * Color palette for coalition/agent edges.
 */
const COALITION_COLORS = [
  '#e41a1c', // red
  '#377eb8', // blue
  '#4daf4a', // green
  '#984ea3', // purple
  '#ff7f00', // orange
  '#f4a582', // light orange
  '#a65628', // brown
  '#f781bf', // pink
  '#999999', // gray
  '#000000', // black
];

/**
 * Extract the coalition from a diamond formula (¬D_A φ).
 */
function extractCoalitionFromFormula(f: Formula): Coalition | null {
  if (f.kind === 'not' && f.sub.kind === 'D') {
    return f.sub.coalition;
  }
  return null;
}

/**
 * Extract all unique coalitions from edges in a tableau phase.
 */
function extractCoalitions(edges: SolidEdge[]): Coalition[] {
  const coalitionSet = new Map<string, Coalition>();
  
  for (const edge of edges) {
    const coalition = extractCoalitionFromFormula(edge.label);
    if (coalition) {
      const key = [...coalition].join(',');
      coalitionSet.set(key, coalition);
    }
  }
  
  // Sort: by size first, then lexicographically
  const coalitions = Array.from(coalitionSet.values());
  coalitions.sort((a, b) => {
    if (a.length !== b.length) return a.length - b.length;
    return [...a].join(',').localeCompare([...b].join(','));
  });
  
  return coalitions;
}

/**
 * Assign colors to coalitions.
 */
function assignColors(coalitions: Coalition[]): Map<string, string> {
  const colorMap = new Map<string, string>();
  
  for (let i = 0; i < coalitions.length; i++) {
    const coalition = coalitions[i]!;
    const key = [...coalition].join(',');
    const color = i < COALITION_COLORS.length
      ? COALITION_COLORS[i]!
      : `hsl(${(i * 360) / coalitions.length}, 70%, 50%)`;
    colorMap.set(key, color);
  }
  
  return colorMap;
}

/**
 * Format coalition for legend display.
 */
function formatCoalitionForLegend(coalition: Coalition): string {
  if (coalition.length === 1) {
    return coalition[0]!;
  }
  return `{${[...coalition].join(',')}}`;
}

/**
 * Escape text for HTML-like labels in DOT.
 */
function escapeHtml(s: string): string {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

/**
 * Generate DOT legend as HTML table.
 */
function generateLegend(coalitions: Coalition[], colorMap: Map<string, string>): string {
  if (coalitions.length === 0) return '';
  
  let rows = '';
  for (const coalition of coalitions) {
    const key = [...coalition].join(',');
    const color = colorMap.get(key);
    if (!color) continue;
    const label = formatCoalitionForLegend(coalition);
    rows += `    <TR><TD WIDTH="24" HEIGHT="16" BGCOLOR="${color}"></TD><TD ALIGN="LEFT">${escapeHtml(label)}</TD></TR>\n`;
  }
  
  return `  {
    rank=min;
    legend [shape=none, margin=0, label=<
      <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0" CELLPADDING="4">
        <TR><TD COLSPAN="2" BGCOLOR="#f5f5f5"><B>Agents</B></TD></TR>
${rows}      </TABLE>
    >];
  }\n`;
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
  const lines: string[] = [];
  lines.push("digraph tableau {");
  lines.push("  rankdir=TB;");
  lines.push("  bgcolor=transparent;");
  lines.push("  newrank=true;");
  lines.push('  node [shape=box, style="filled,rounded", fillcolor="#f8f9fa", color="#d0d0d0", fontsize=11, fontname="Helvetica"];');
  lines.push('  edge [fontsize=9, fontname="Helvetica", color="#888"];');
  lines.push("");

  // Extract coalitions and assign colors
  const edges = phase === "pretableau" 
    ? result.pretableau.solidEdges 
    : phase === "initial" 
      ? result.initialTableau.edges 
      : result.finalTableau.edges;
  const coalitions = extractCoalitions(edges);
  const colorMap = assignColors(coalitions);

  // Add legend if there are any coalitions
  if (coalitions.length > 0) {
    lines.push(generateLegend(coalitions, colorMap));
  }

  if (phase === "pretableau") {
    // Prestates as dashed ellipses
    for (const [id, ps] of result.pretableau.prestates) {
      const tooltip = formulaSetTooltip(ps.formulas);
      const label = nodeLabel(id, ps.formulas, detailed);
      lines.push(`  "${id}" [label="${escDot(label)}", shape=ellipse, style="dashed,filled", fillcolor="#fafafa", tooltip="${escDot(tooltip)}"];`);
    }
    // States as boxes
    for (const [id, state] of result.pretableau.states) {
      const tooltip = formulaSetTooltip(state.formulas);
      const hasInput = state.formulas.has(result.inputFormula);
      const fill = hasInput ? "#dbeafe" : "#f8f9fa";
      const border = hasInput ? "#93b5e6" : "#d0d0d0";
      const label = nodeLabel(id, state.formulas, detailed);
      lines.push(`  "${id}" [label="${escDot(label)}", fillcolor="${fill}", color="${border}", tooltip="${escDot(tooltip)}"];`);
    }
    // Dashed edges (prestate → state expansion)
    for (const edge of result.pretableau.dashedEdges) {
      lines.push(`  "${edge.from}" -> "${edge.to}" [style=dashed, color="#bbb"];`);
    }
    // Solid edges (state → prestate transitions)
    for (const edge of result.pretableau.solidEdges) {
      const label = printFormulaUnicode(edge.label);
      const coalition = extractCoalitionFromFormula(edge.label);
      const color = coalition ? colorMap.get([...coalition].join(',')) || "#4a6fa5" : "#4a6fa5";
      lines.push(`  "${edge.from}" -> "${edge.to}" [label=" ${escDot(label)} ", color="${color}", fontcolor="${color}"];`);
    }
  } else {
    const tableau = phase === "initial" ? result.initialTableau : result.finalTableau;

    // Build elimination lookup for the final phase
    const eliminationMap = new Map<string, string>();
    if (showEliminated && phase === "final" && result.eliminations) {
      for (const rec of result.eliminations) {
        if (!eliminationMap.has(rec.stateId)) {
          const reason = rec.rule === "E1"
            ? `E1: ${printFormulaUnicode(rec.formula)} has no successor`
            : `E2: eventuality ${printFormulaUnicode(rec.formula)} unrealized`;
          eliminationMap.set(rec.stateId, reason);
        }
      }
    }

    // Surviving states
    for (const [id, state] of tableau.states) {
      const tooltip = formulaSetTooltip(state.formulas);
      const hasInput = state.formulas.has(result.inputFormula);
      const fill = hasInput ? "#dcfce7" : "#f8f9fa";
      const border = hasInput ? "#86d997" : "#d0d0d0";
      const penwidth = hasInput ? "2" : "1";
      const label = nodeLabel(id, state.formulas, detailed);
      lines.push(`  "${id}" [label="${escDot(label)}", fillcolor="${fill}", color="${border}", penwidth=${penwidth}, tooltip="${escDot(tooltip)}"];`);
    }

    // Eliminated states (shown as faded red, only for final phase)
    if (showEliminated && phase === "final") {
      for (const [id, state] of result.initialTableau.states) {
        if (tableau.states.has(id)) continue; // still alive, skip
        const reason = eliminationMap.get(id) || "eliminated";
        const elimLabel = detailed
          ? detailedLabel(id + " ✗", state.formulas)
          : `${id} ✗\n${reason}`;
        const tooltip = reason + "\n\n" + formulaSetTooltip(state.formulas);
        lines.push(`  "${id}" [label="${escDot(elimLabel)}", fillcolor="#fee2e2", color="#e5a0a0", fontcolor="#999", style="filled,rounded,dashed", tooltip="${escDot(tooltip)}"];`);
      }

      // Show edges involving eliminated states as dashed with reduced opacity
      for (const edge of result.initialTableau.edges) {
        if (tableau.states.has(edge.from) && tableau.states.has(edge.to)) continue; // already shown below
        const label = printFormulaUnicode(edge.label);
        const coalition = extractCoalitionFromFormula(edge.label);
        const baseColor = coalition ? colorMap.get([...coalition].join(',')) || "#888" : "#888";
        // Create lighter version by using opacity in hex (add 99 for ~60% opacity)
        const lightColor = baseColor + "66";
        lines.push(`  "${edge.from}" -> "${edge.to}" [label=" ${escDot(label)} ", fontcolor="${lightColor}", color="${lightColor}", style=dashed];`);
      }
    }

    // Surviving edges
    for (const edge of tableau.edges) {
      const label = printFormulaUnicode(edge.label);
      const coalition = extractCoalitionFromFormula(edge.label);
      const color = coalition ? colorMap.get([...coalition].join(',')) || "#4a6fa5" : "#4a6fa5";
      lines.push(`  "${edge.from}" -> "${edge.to}" [label=" ${escDot(label)} ", color="${color}", fontcolor="${color}"];`);
    }
  }

  lines.push("}");
  return lines.join("\n");
}

function escDot(s: string): string {
  return s.replace(/\\/g, "\\\\").replace(/"/g, '\\"').replace(/\n/g, "\\n");
}
