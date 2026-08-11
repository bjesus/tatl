/**
 * Browser entry point for the ATL* Tableau Solver.
 * Runs as a Web Worker to keep the UI responsive.
 */

import { parseFormula, systemAgents, type System } from "../core/parser.ts";
import { printFormula, printFormulaSet, printFormulaLatex, printFormulaSetLatex, printMoveVector, printMoveVectorLatex, notationFor, type Notation } from "../core/printer.ts";
import { runTableau } from "../core/tableau.ts";
import { toDot } from "../viz/text.ts";
import type { TableauResult } from "../core/types.ts";

// Helper to access worker global scope safely
const ctx: any = self;

// Load Viz.js (Synchronous import for classic workers)
importScripts('https://cdn.jsdelivr.net/npm/@viz-js/viz@3.11.0/lib/viz-standalone.js');

let vizPromise: Promise<any> | null = null;
function getViz() {
  if (!vizPromise) {
    vizPromise = ctx.Viz.instance();
  }
  return vizPromise;
}

ctx.onmessage = async (e: MessageEvent) => {
  const msg = e.data;

  if (msg.type === 'solve') {
    try {
      ctx.postMessage({ type: 'status', stage: 'Parsing formula...' });
      const system: System = msg.system || 'atl';
      const formula = parseFormula(msg.formula, system);

      // LTL and CTL are read over a single agent; ATL* also takes any agents
      // the user declared by hand.
      const agents = [...systemAgents(system), ...(msg.agents ?? [])];

      const result = runTableau(formula, agents, (stage: string) => {
        ctx.postMessage({ type: 'status', stage });
      });

      ctx.postMessage({ type: 'status', stage: 'Preparing results...' });
      const serialized = serializeResult(result, notationFor(system));

      ctx.postMessage({ type: 'result', result: serialized });

    } catch (err: any) {
      ctx.postMessage({ type: 'error', message: err.message });
    }
  } else if (msg.type === 'render') {
    try {
      const viz = await getViz();
      const svg = await viz.renderString(msg.dot, { format: 'svg' });
      ctx.postMessage({ type: 'svg', svg, id: msg.id });
    } catch (err: any) {
      ctx.postMessage({ type: 'svg-error', message: err.message, id: msg.id });
    }
  }
};

function serializeResult(result: TableauResult, notation: Notation) {
  const inputKey = result.inputFormula;
  const inputLatex = printFormulaLatex(result.inputFormula, notation);
  const allAgents = result.allAgents;

  function serializeStates(states: typeof result.pretableau.states) {
    const out: Record<string, { formulas: string; formulasLatex: string; hasInput: boolean }> = {};
    for (const [id, state] of states) {
      out[id] = {
        formulas: printFormulaSet(state.formulas, notation),
        formulasLatex: printFormulaSetLatex(state.formulas, notation),
        hasInput: state.formulas.has(inputKey),
      };
    }
    return out;
  }

  function serializeEdges(edges: typeof result.initialTableau.edges) {
    return edges.map((e) => ({
      from: e.from,
      to: e.to,
      label: printMoveVector(e.label, allAgents),
      labelLatex: printMoveVectorLatex(e.label, allAgents),
    }));
  }

  const pretableauPrestates: Record<string, { formulas: string; formulasLatex: string }> = {};
  for (const [id, ps] of result.pretableau.prestates) {
    pretableauPrestates[id] = {
      formulas: printFormulaSet(ps.formulas, notation),
      formulasLatex: printFormulaSetLatex(ps.formulas, notation),
    };
  }

  // Serialize elimination records
  const eliminations = result.eliminations.map((rec) => ({
    stateId: rec.stateId,
    rule: rec.rule,
    formulaLatex: printFormulaLatex(rec.formula, notation),
    formulaAscii: printFormula(rec.formula, notation),
    stateFormulasLatex: printFormulaSetLatex(rec.stateFormulas, notation),
  }));

  return {
    satisfiable: result.satisfiable,
    inputLatex,
    allAgents: [...allAgents],
    stats: {
      pretableauStates: result.pretableau.states.size,
      pretableauPrestates: result.pretableau.prestates.size,
      initialStates: result.initialTableau.states.size,
      initialEdges: result.initialTableau.edges.length,
      finalStates: result.finalTableau.states.size,
      finalEdges: result.finalTableau.edges.length,
      eliminationsE2: eliminations.filter((e) => e.rule === "E2").length,
      eliminationsE3: eliminations.filter((e) => e.rule === "E3").length,
    },
    eliminations,
    pretableau: {
      states: serializeStates(result.pretableau.states),
      prestates: pretableauPrestates,
      solidEdges: serializeEdges(result.pretableau.solidEdges),
    },
    initialTableau: {
      states: serializeStates(result.initialTableau.states),
      edges: serializeEdges(result.initialTableau.edges),
    },
    finalTableau: {
      states: serializeStates(result.finalTableau.states),
      edges: serializeEdges(result.finalTableau.edges),
    },
    // DOT variants
    dots: {
      pretableau: toDot(result, "pretableau", { notation }),
      initial: toDot(result, "initial", { notation }),
      final: toDot(result, "final", { notation }),
      pretableauDetailed: toDot(result, "pretableau", { notation, detailedLabels: true }),
      initialDetailed: toDot(result, "initial", { notation, detailedLabels: true }),
      finalDetailed: toDot(result, "final", { notation, detailedLabels: true }),
      finalEliminated: toDot(result, "final", { notation, showEliminated: true }),
      finalDetailedEliminated: toDot(result, "final", { notation, detailedLabels: true, showEliminated: true }),
    },
  };
}
