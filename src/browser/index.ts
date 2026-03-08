/**
 * Browser entry point for the CMAEL(CD) Tableau Solver.
 * Runs as a Web Worker to keep the UI responsive.
 */

import { parseFormula } from "../core/parser.ts";
import { printFormula, printFormulaSet, printFormulaLatex, printFormulaSetLatex } from "../core/printer.ts";
import { runTableau } from "../core/tableau.ts";
import { toDot } from "../viz/text.ts";
import type { TableauResult } from "../core/types.ts";

// Helper to access worker global scope safely
const ctx: any = self;

// Load Viz.js (Synchronous import for classic workers)
// This adds 'Viz' to the global scope
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
      const formula = parseFormula(msg.formula);

      const result = runTableau(formula, msg.restrictedCuts, (stage) => {
        ctx.postMessage({ type: 'status', stage });
      });

      ctx.postMessage({ type: 'status', stage: 'Preparing results...' });
      const serialized = serializeResult(result);

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

function serializeResult(result: TableauResult) {
  const inputKey = result.inputFormula;
  const inputLatex = printFormulaLatex(result.inputFormula);

  function serializeStates(states: typeof result.pretableau.states) {
    const out: Record<string, { formulas: string; formulasLatex: string; hasInput: boolean }> = {};
    for (const [id, state] of states) {
      out[id] = {
        formulas: printFormulaSet(state.formulas),
        formulasLatex: printFormulaSetLatex(state.formulas),
        hasInput: state.formulas.has(inputKey),
      };
    }
    return out;
  }

  function serializeEdges(edges: typeof result.initialTableau.edges) {
    return edges.map((e) => ({
      from: e.from,
      to: e.to,
      label: printFormula(e.label),
      labelLatex: printFormulaLatex(e.label),
    }));
  }

  const pretableauPrestates: Record<string, { formulas: string; formulasLatex: string }> = {};
  for (const [id, ps] of result.pretableau.prestates) {
    pretableauPrestates[id] = {
      formulas: printFormulaSet(ps.formulas),
      formulasLatex: printFormulaSetLatex(ps.formulas),
    };
  }

  // Serialize elimination records
  const eliminations = result.eliminations.map((rec) => ({
    stateId: rec.stateId,
    rule: rec.rule,
    formulaLatex: printFormulaLatex(rec.formula),
    formulaAscii: printFormula(rec.formula),
    stateFormulasLatex: printFormulaSetLatex(rec.stateFormulas),
  }));

  return {
    satisfiable: result.satisfiable,
    inputLatex,
    stats: {
      pretableauStates: result.pretableau.states.size,
      pretableauPrestates: result.pretableau.prestates.size,
      initialStates: result.initialTableau.states.size,
      initialEdges: result.initialTableau.edges.length,
      finalStates: result.finalTableau.states.size,
      finalEdges: result.finalTableau.edges.length,
      eliminationsE1: eliminations.filter((e) => e.rule === "E1").length,
      eliminationsE2: eliminations.filter((e) => e.rule === "E2").length,
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
    // DOT variants: compact and detailed, plus eliminated variants for final
    dots: {
      pretableau: toDot(result, "pretableau"),
      initial: toDot(result, "initial"),
      final: toDot(result, "final"),
      pretableauDetailed: toDot(result, "pretableau", { detailedLabels: true }),
      initialDetailed: toDot(result, "initial", { detailedLabels: true }),
      finalDetailed: toDot(result, "final", { detailedLabels: true }),
      finalEliminated: toDot(result, "final", { showEliminated: true }),
      finalDetailedEliminated: toDot(result, "final", { detailedLabels: true, showEliminated: true }),
    },
  };
}
