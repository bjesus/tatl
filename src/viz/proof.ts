/**
 * HTML rendering of the unsatisfiability proof and of the extracted model
 * for the web UI. Formulas are emitted as `data-tex` attributes that the page
 * typesets with KaTeX.
 */

import {
  type TableauResult,
  type NodeId,
  type EliminationRecord,
  type RealizationFailure,
} from "../core/types.ts";
import {
  printFormulaLatex,
  printFormulaSetLatex,
  printMoveVectorLatex,
  printPathLatex,
  type Notation,
} from "../core/printer.ts";
import type { Model } from "../core/model.ts";

function esc(s: string): string {
  return s.replace(/&/g, "&amp;").replace(/"/g, "&quot;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}

function tex(latex: string): string {
  return `<span data-tex="${esc(latex)}"></span>`;
}

function id(x: string): string {
  return `<span class="proof-id">${esc(x)}</span>`;
}

/**
 * The proof as nested lists. Mirrors textProof in text.ts.
 */
export function proofHtml(result: TableauResult, notation: Notation): string {
  const parts: string[] = [];
  const byId = new Map<NodeId, EliminationRecord>();
  for (const rec of result.eliminations) if (!byId.has(rec.stateId)) byId.set(rec.stateId, rec);

  if (result.inputFormula.kind === "bot") {
    return `<p>The formula simplifies to ${tex("\\bot")}: it contains a formula together with its negation.</p>`;
  }
  if (result.initialStateIds.length === 0) {
    return "<p>Every expansion of the input formula is patently inconsistent, so no state could be built.</p>";
  }

  parts.push(`<p>Every initial state (${result.initialStateIds.map(id).join(", ")}) is eliminated:</p>`);
  const explained = new Set<NodeId>();

  const stateLabel = (sid: NodeId) => {
    const st = result.initialTableau.states.get(sid);
    return st ? tex(printFormulaSetLatex(st.formulas, notation)) : "";
  };

  const explainState = (sid: NodeId): string => {
    const rec = byId.get(sid);
    if (!rec) return `<li>${id(sid)} survives</li>`;
    if (explained.has(sid)) return `<li>${id(sid)}: eliminated (explained above)</li>`;
    explained.add(sid);
    const ex = rec.explanation;
    if (!ex) return `<li>${id(sid)}: eliminated by ${rec.rule}</li>`;
    if (ex.kind === "E2") {
      let h = `<li><div class="proof-state">${id(sid)} ${stateLabel(sid)}</div>`;
      h += `<div class="proof-reason"><span class="elim-badge e2">E2</span> move ${tex(printMoveVectorLatex(ex.moveVector, result.allAgents))} has no surviving successor.`;
      if (ex.successors.length === 0) {
        h += ` The successor prestate expanded to nothing consistent.</div>`;
      } else {
        h += ` Its candidates:</div><ul>${ex.successors.map(explainState).join("")}</ul>`;
      }
      return h + "</li>";
    }
    let h = `<li><div class="proof-state">${id(sid)} ${stateLabel(sid)}</div>`;
    h += `<div class="proof-reason"><span class="elim-badge e3">E3</span> eventuality ${tex(printFormulaLatex(ex.eventuality, notation))} cannot be realized; still pending: ${tex(printPathLatex(ex.residual, notation))}</div>`;
    h += explainFailure(ex.failure);
    return h + "</li>";
  };

  const explainFailure = (f: RealizationFailure): string => {
    if (f.seeAbove) return `<ul><li>(explained above)</li></ul>`;
    if (f.prestateId === null) return `<ul><li>no successor prestate is consistent with the eventuality</li></ul>`;
    if (f.options.length === 0) return `<ul><li>via ${id(f.prestateId)}: no surviving successor carries the eventuality</li></ul>`;
    let h = `<ul><li>via ${id(f.prestateId)}, every successor fails:<ul>`;
    for (const opt of f.options) {
      const pend = tex(printPathLatex(opt.residual, notation));
      switch (opt.status) {
        case "eliminated":
          h += `<li>${id(opt.stateId)}: eliminated<ul>${explainState(opt.stateId)}</ul></li>`;
          break;
        case "cycle":
          h += `<li>${id(opt.stateId)}: returns to a state already on this path with ${pend} still pending</li>`;
          break;
        case "truncated":
          h += `<li>${id(opt.stateId)}: still pending ${pend} (explanation truncated)</li>`;
          break;
        case "unrealizable":
          h += `<li>${id(opt.stateId)}: still pending ${pend}${opt.failure ? explainFailure(opt.failure) : ""}</li>`;
          break;
      }
    }
    return h + "</ul></li></ul>";
  };

  parts.push(`<ul class="proof-tree">${result.initialStateIds.map(explainState).join("")}</ul>`);
  return parts.join("");
}

export interface SerializedModel {
  states: Array<{ id: string; literalsLatex: string; literals: string; tableauStates: string[]; initial: boolean }>;
  edges: Array<{ from: string; to: string; label: string; labelLatex: string }>;
  initial: string;
  unminimisedStates: number;
}

export function serializeModel(model: Model, notation: Notation, printAscii: (f: any, n: Notation) => string): SerializedModel {
  return {
    states: model.states.map((s) => ({
      id: s.id,
      literalsLatex: s.literals.length > 0
        ? s.literals.map((l) => printFormulaLatex(l, notation)).join(",\\; ")
        : "\\text{any valuation}",
      literals: s.literals.length > 0 ? s.literals.map((l) => printAscii(l, notation)).join(", ") : "(any valuation)",
      tableauStates: s.tableauStates,
      initial: s.id === model.initial,
    })),
    edges: model.edges.map((e) => ({
      from: e.from,
      to: e.to,
      label: `(${e.label.join(",")})`,
      labelLatex: printMoveVectorLatex(e.label, model.agents),
    })),
    initial: model.initial,
    unminimisedStates: model.unminimisedStates,
  };
}
