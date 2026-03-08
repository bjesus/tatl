/**
 * Generate a standalone HTML file for visualizing tableau results.
 * Clean, light design aimed at logic students. Uses KaTeX for formula rendering.
 */

import { type TableauResult } from "../core/types.ts";
import {
  printFormula,
  printFormulaSet,
  printFormulaLatex,
} from "../core/printer.ts";
import { toDot } from "./text.ts";

export function generateHTML(result?: TableauResult): string {
  return `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>CMAEL(CD) Tableau Solver</title>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css">
<script src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js"></script>
<style>
:root {
  --bg: #f4f5f7;
  --surface: #ffffff;
  --surface-alt: #f0f1f3;
  --border: #dfe1e6;
  --text: #2c3e50;
  --text-muted: #7a8599;
  --accent: #4a6fa5;
  --accent-light: #e8eef6;
  --sat: #2e7d32;
  --sat-bg: #e8f5e9;
  --unsat: #c62828;
  --unsat-bg: #ffebee;
  --highlight: #fff3e0;
  --radius: 8px;
  --shadow: 0 1px 3px rgba(0,0,0,0.06);
  --left-width: 380px;
}
* { box-sizing: border-box; margin: 0; padding: 0; }
html, body { height: 100%; overflow: hidden; }
body {
  font-family: 'Segoe UI', system-ui, -apple-system, sans-serif;
  background: var(--bg); color: var(--text);
  line-height: 1.6;
}

/* === Two-column layout === */
.app-layout {
  display: flex; height: 100vh; width: 100%;
}

/* --- Left panel --- */
.left-panel {
  width: var(--left-width); min-width: var(--left-width); max-width: var(--left-width);
  height: 100vh; display: flex; flex-direction: column;
  background: var(--surface); border-right: 1px solid var(--border);
  overflow: hidden; flex-shrink: 0;
}
.left-scroll {
  flex: 1; overflow-y: auto; padding: 24px 20px 20px;
}

/* Header area within left panel */
.app-header {
  padding: 24px 20px 16px; border-bottom: 1px solid var(--border);
  background: var(--accent); color: white;
}
.app-header h1 { font-size: 1.15em; font-weight: 700; letter-spacing: 0.01em; line-height: 1.3; }
.app-header .subtitle {
  font-size: 0.78em; opacity: 0.85; margin-top: 4px; line-height: 1.5;
}
.app-header .katex { color: white; font-size: 0.95em; }
.app-header .credit {
  font-size: 0.72em; opacity: 0.65; margin-top: 8px; line-height: 1.4;
}
.app-header .credit a { color: white; text-decoration: underline; text-underline-offset: 2px; }
.left-footer {
  padding: 8px 12px; border-top: 1px solid var(--border);
  display: flex; gap: 8px; flex-shrink: 0;
}
.footer-btn {
  flex: 1; display: inline-flex; align-items: center; justify-content: center;
  padding: 6px 0; font-size: 0.76em; font-family: inherit; font-weight: 500;
  color: var(--accent); background: var(--accent-light); border: 1px solid var(--border);
  border-radius: 6px; cursor: pointer; text-decoration: none; transition: all 0.15s;
}
.footer-btn:hover { background: var(--accent); color: white; border-color: var(--accent); }

/* Sections in left panel */
.left-section {
  margin-bottom: 20px;
}
.left-section:last-child { margin-bottom: 0; }
.section-title {
  font-size: 0.72em; text-transform: uppercase; letter-spacing: 0.1em;
  color: var(--text-muted); margin-bottom: 10px; font-weight: 700;
}

/* Formula input */
.formula-input-wrap { position: relative; }
input[type="text"] {
  width: 100%; padding: 10px 32px 10px 14px; border: 1.5px solid var(--border);
  border-radius: 6px; font-size: 14px; font-family: 'JetBrains Mono', 'Fira Code', 'Consolas', monospace;
  background: var(--surface); color: var(--text); transition: border-color 0.15s;
}
input[type="text"]:focus { outline: none; border-color: var(--accent); box-shadow: 0 0 0 3px var(--accent-light); }
input[type="text"]::placeholder { color: #bbb; }
.input-clear {
  position: absolute; right: 6px; top: 50%; transform: translateY(-50%);
  width: 22px; height: 22px; border: none; background: var(--surface-alt);
  border-radius: 50%; cursor: pointer; display: none; align-items: center;
  justify-content: center; font-size: 13px; color: var(--text-muted);
  line-height: 1; transition: all 0.15s;
}
.input-clear:hover { background: var(--border); color: var(--text); }
.formula-input-wrap.has-value .input-clear { display: flex; }

.actions { display: flex; align-items: center; gap: 12px; margin-top: 12px; flex-wrap: wrap; }
.btn {
  display: inline-flex; align-items: center; gap: 6px;
  padding: 9px 20px; background: var(--accent); color: white; border: none;
  border-radius: 6px; cursor: pointer; font-size: 0.85em; font-weight: 600;
  font-family: inherit; transition: background 0.15s; white-space: nowrap;
}
.btn:hover { background: #3d5d8a; }
.btn:active { transform: translateY(1px); }
.checkbox-label {
  display: inline-flex; align-items: center; gap: 5px;
  font-size: 0.8em; color: var(--text-muted); cursor: pointer; user-select: none;
}
.checkbox-label input { accent-color: var(--accent); }
.loading { display: none; color: var(--text-muted); font-style: italic; font-size: 0.82em; }

/* Parse error */
.parse-error {
  color: var(--unsat); font-size: 0.82em; margin-top: 8px; display: none;
}

/* Syntax reference */
.syntax-ref {
  display: grid; grid-template-columns: 1fr; gap: 5px;
  font-size: 0.78em; color: var(--text-muted);
}
.syntax-ref code {
  background: var(--surface-alt); padding: 1px 5px; border-radius: 3px;
  font-family: 'JetBrains Mono', 'Fira Code', monospace; font-size: 0.95em; color: var(--text);
}
.syntax-item { display: flex; align-items: baseline; gap: 6px; }
.syntax-item .katex { font-size: 0.9em; }

/* Examples */
.examples { display: flex; flex-wrap: wrap; gap: 5px; }
.example-btn {
  padding: 4px 10px; background: var(--accent-light); border: 1px solid var(--border);
  color: var(--accent); border-radius: 14px; cursor: pointer; font-size: 0.74em;
  font-family: inherit; transition: all 0.15s; white-space: nowrap;
}
.example-btn:hover { background: var(--accent); color: white; border-color: var(--accent); }

/* --- Right panel (results) --- */
.right-panel {
  flex: 1; height: 100vh; display: flex; flex-direction: column;
  overflow: hidden; min-width: 0;
}
.right-scroll {
  flex: 1; overflow-y: auto; padding: 24px 28px;
}

/* Empty state for right panel */
.right-empty {
  display: flex; flex-direction: column; align-items: center; justify-content: center;
  height: 100%; color: var(--text-muted); text-align: center; padding: 40px;
}
.right-empty .placeholder-icon {
  font-size: 3em; opacity: 0.25; margin-bottom: 16px;
}
.right-empty h2 { font-size: 1.1em; font-weight: 600; color: var(--text-muted); margin-bottom: 8px; }
.right-empty p { font-size: 0.88em; max-width: 360px; line-height: 1.6; }

/* Cards in the right panel */
.card {
  background: var(--surface); border: 1px solid var(--border);
  border-radius: var(--radius); padding: 20px;
  margin-bottom: 16px; box-shadow: var(--shadow);
}
.card h2 {
  font-size: 0.78em; text-transform: uppercase; letter-spacing: 0.08em;
  color: var(--text-muted); margin-bottom: 14px; font-weight: 600;
}

/* Result banner */
.result-banner.loading {
  background: var(--surface-alt);
  color: var(--text-muted);
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 12px;
}
.spinner {
  display: inline-block;
  width: 20px;
  height: 20px;
  border: 2px solid var(--border);
  border-top-color: var(--text);
  border-radius: 50%;
  animation: spin 0.6s linear infinite;
}
@keyframes spin { to { transform: rotate(360deg); } }

.result-banner {
  padding: 14px 18px; border-radius: var(--radius); margin-bottom: 16px;
  display: flex; align-items: center; gap: 12px; font-weight: 600; font-size: 0.95em;
}
.result-banner.sat { background: var(--sat-bg); color: var(--sat); border: 1px solid #c8e6c9; }
.result-banner.unsat { background: var(--unsat-bg); color: var(--unsat); border: 1px solid #ffcdd2; }
.result-banner .icon { font-size: 1.3em; }
.result-formula { margin-top: 4px; font-weight: 400; }
.result-banner .banner-stats {
  margin-left: auto; display: flex; gap: 14px; flex-shrink: 0;
}
.result-banner .banner-stat { text-align: center; line-height: 1.2; cursor: help; }
.result-banner .banner-stat .num { font-size: 1.1em; font-weight: 700; opacity: 0.7; }
.result-banner .banner-stat .label {
  font-size: 0.6em; font-weight: 500; text-transform: uppercase;
  letter-spacing: 0.04em; opacity: 0.6;
}

/* Phase tabs */
.phase-tabs { display: flex; border-bottom: 2px solid var(--border); margin-bottom: 14px; }
.phase-tab {
  padding: 7px 16px; background: none; border: none; color: var(--text-muted);
  cursor: pointer; font-family: inherit; font-size: 0.82em; font-weight: 500;
  border-bottom: 2px solid transparent; margin-bottom: -2px; transition: all 0.15s;
}
.phase-tab:hover { color: var(--text); }
.phase-tab.active { color: var(--accent); border-bottom-color: var(--accent); }

/* State list */
.state-list { display: flex; flex-direction: column; gap: 7px; }
.state-item {
  padding: 9px 12px; background: var(--surface-alt); border-radius: 6px;
  border-left: 3px solid var(--border); font-size: 0.88em;
  overflow-x: auto;
}
.state-item.has-input { border-left-color: var(--accent); background: var(--highlight); }
.state-id { font-weight: 600; color: var(--accent); font-size: 0.78em; margin-bottom: 3px; }
.state-formulas .katex { font-size: 0.85em; }
.edge-item {
  padding: 7px 12px; background: var(--surface-alt); border-radius: 6px;
  font-size: 0.82em; display: flex; align-items: center; gap: 8px; flex-wrap: wrap;
}
.edge-arrow { color: var(--text-muted); font-weight: 500; }
.edge-label { color: var(--accent); }

.empty-notice {
  padding: 20px; text-align: center; color: var(--text-muted);
  font-style: italic; font-size: 0.88em;
}

.section-label {
  font-size: 0.72em; text-transform: uppercase; letter-spacing: 0.08em;
  color: var(--text-muted); font-weight: 600; margin: 14px 0 8px;
}

/* DOT output */
.dot-toggle {
  font-size: 0.78em; color: var(--accent); cursor: pointer; background: none;
  border: none; font-family: inherit; text-decoration: underline; margin-top: 10px;
}
.dot-box {
  margin-top: 8px; background: var(--surface-alt); border-radius: 6px; padding: 12px;
  font-family: 'JetBrains Mono', monospace; font-size: 0.72em; white-space: pre-wrap;
  max-height: 200px; overflow: auto; display: none;
}

/* View toggle */
.view-toggle { display: inline-flex; border: 1px solid var(--border); border-radius: 6px; overflow: hidden; margin-left: auto; }
.view-toggle-btn {
  padding: 4px 12px; background: var(--surface); border: none; cursor: pointer;
  font-family: inherit; font-size: 0.78em; font-weight: 500; color: var(--text-muted);
  transition: all 0.15s; border-right: 1px solid var(--border);
}
.view-toggle-btn:last-child { border-right: none; }
.view-toggle-btn:hover { background: var(--surface-alt); }
.view-toggle-btn.active { background: var(--accent); color: white; }

/* Graph view */
.graph-container {
  overflow: auto; background: var(--surface-alt); border-radius: 6px;
  border: 1px solid var(--border); padding: 12px; margin-bottom: 12px;
  min-height: 100px; text-align: center; cursor: pointer; position: relative;
}
.graph-container svg { max-width: 100%; height: auto; }
.graph-loading { color: var(--text-muted); font-style: italic; font-size: 0.82em; padding: 20px; }
.graph-hint {
  position: absolute; bottom: 8px; right: 12px; font-size: 0.7em;
  color: var(--text-muted); opacity: 0.7; pointer-events: none;
}

/* Fullscreen overlay */
.graph-fullscreen {
  display: none; position: fixed; inset: 0; z-index: 9999;
  background: rgba(255,255,255,0.97); flex-direction: column;
}
.graph-fullscreen.open { display: flex; }
.graph-fs-toolbar {
  display: flex; align-items: center; gap: 12px; padding: 12px 20px;
  background: var(--surface); border-bottom: 1px solid var(--border);
  flex-shrink: 0;
}
.graph-fs-toolbar .title { font-weight: 600; font-size: 0.9em; color: var(--text); }
.graph-fs-toolbar .hint { font-size: 0.78em; color: var(--text-muted); margin-left: auto; }
.graph-fs-close {
  padding: 6px 16px; background: var(--surface-alt); border: 1px solid var(--border);
  border-radius: 6px; cursor: pointer; font-family: inherit; font-size: 0.82em;
  color: var(--text); transition: background 0.15s;
}
.graph-fs-close:hover { background: var(--border); }
.graph-fs-viewport {
  flex: 1; overflow: hidden; cursor: grab; position: relative;
}
.graph-fs-viewport:active { cursor: grabbing; }
.graph-fs-viewport svg {
  position: absolute; transform-origin: 0 0;
}

/* About modal */
.modal-backdrop {
  display: none; position: fixed; inset: 0; z-index: 8888;
  background: rgba(0,0,0,0.4); justify-content: center; align-items: flex-start;
  padding: 40px 20px; overflow-y: auto;
}
.modal-backdrop.open { display: flex; }
.modal {
  background: var(--surface); border-radius: 12px; box-shadow: 0 8px 40px rgba(0,0,0,0.18);
  max-width: 720px; width: 100%; padding: 32px; position: relative;
  animation: modalIn 0.2s ease-out;
}
@keyframes modalIn {
  from { opacity: 0; transform: translateY(-12px); }
  to { opacity: 1; transform: translateY(0); }
}
.modal-close {
  position: absolute; top: 16px; right: 16px; background: var(--surface-alt);
  border: 1px solid var(--border); border-radius: 6px; width: 32px; height: 32px;
  display: flex; align-items: center; justify-content: center; cursor: pointer;
  font-size: 1.1em; color: var(--text-muted); transition: all 0.15s;
}
.modal-close:hover { background: var(--border); color: var(--text); }
.modal h2 { font-size: 1.15em; font-weight: 700; color: var(--text); margin-bottom: 20px; }
.about-section { margin-bottom: 24px; }
.about-section h3 { font-size: 0.95em; font-weight: 600; color: var(--text); margin-bottom: 8px; }
.about-section p { font-size: 0.88em; color: var(--text); line-height: 1.7; }
.about-section .katex { font-size: 0.92em; }
.phase-explain { display: flex; flex-direction: column; gap: 14px; margin: 12px 0; }
.phase-step { display: flex; gap: 14px; align-items: flex-start; }
.phase-num {
  flex-shrink: 0; width: 28px; height: 28px; border-radius: 50%;
  background: var(--accent); color: white; display: flex; align-items: center;
  justify-content: center; font-size: 0.8em; font-weight: 700; margin-top: 2px;
}
.phase-step div:last-child { font-size: 0.88em; line-height: 1.65; }
.about-table { width: 100%; border-collapse: collapse; font-size: 0.88em; margin-top: 8px; }
.about-table th {
  text-align: left; padding: 8px 12px; background: var(--surface-alt);
  border-bottom: 2px solid var(--border); font-weight: 600; font-size: 0.8em;
  text-transform: uppercase; letter-spacing: 0.05em; color: var(--text-muted);
}
.about-table td { padding: 8px 12px; border-bottom: 1px solid var(--border); }
.about-table code {
  background: var(--surface-alt); padding: 2px 6px; border-radius: 3px;
  font-family: 'JetBrains Mono', monospace; font-size: 0.95em;
}
.about-credits {
  padding: 12px 16px; background: var(--surface-alt); border-radius: 6px;
  border-left: 3px solid var(--accent);
}
.about-credits p { font-size: 0.85em; line-height: 1.7; }

/* Graph options bar */
.graph-options {
  display: flex; gap: 14px; margin-bottom: 10px; flex-wrap: wrap; align-items: center;
}
.graph-options label {
  display: flex; align-items: center; gap: 5px; font-size: 0.78em;
  color: var(--text-muted); cursor: pointer; user-select: none;
}
.graph-options input[type="checkbox"] { cursor: pointer; }
.graph-options .download-btns { margin-left: auto; display: flex; gap: 6px; }
.graph-dl-btn {
  padding: 3px 10px; font-size: 0.72em; font-family: inherit; font-weight: 600;
  color: var(--accent); background: var(--accent-light); border: 1px solid var(--border);
  border-radius: 4px; cursor: pointer; transition: all 0.15s;
}
.graph-dl-btn:hover:not(:disabled) { background: var(--accent); color: white; border-color: var(--accent); }
.graph-dl-btn:disabled { opacity: 0.5; cursor: not-allowed; }
.spinner-sm {
  display: inline-block; width: 10px; height: 10px;
  border: 1.5px solid var(--border); border-top-color: var(--accent);
  border-radius: 50%; animation: spin 0.6s linear infinite;
  vertical-align: middle;
}

/* Hide graph title text inside the inline graph view (visible in fullscreen/export) */
#graph-view .graph > text { display: none; }

/* Elimination trace */
.elimination-card {
  background: var(--surface); border: 1px solid #e5a0a0;
  border-radius: 8px; padding: 18px; margin-bottom: 16px;
  border-left: 4px solid var(--unsat);
}
.elimination-card h3 { font-size: 0.92em; font-weight: 600; color: var(--text); margin-bottom: 10px; }
.elimination-card .elim-summary {
  font-size: 0.82em; color: var(--text-muted); margin-bottom: 12px; line-height: 1.6;
}
.elim-list { display: flex; flex-direction: column; gap: 8px; }
.elim-item {
  display: flex; gap: 10px; align-items: flex-start; padding: 9px 11px;
  background: var(--surface-alt); border-radius: 6px; font-size: 0.82em;
}
.elim-badge {
  flex-shrink: 0; padding: 2px 7px; border-radius: 4px; font-size: 0.76em;
  font-weight: 600; letter-spacing: 0.03em;
}
.elim-badge.e1 { background: #fef3c7; color: #92400e; }
.elim-badge.e2 { background: #fee2e2; color: #991b1b; }
.elim-id { font-weight: 600; color: var(--text); min-width: 28px; }
.elim-reason { color: var(--text-muted); line-height: 1.5; }
.elim-reason .katex { font-size: 0.88em; }
.elim-formulas {
  margin-top: 6px; padding-top: 6px; border-top: 1px solid var(--border);
  color: var(--text-muted); font-size: 0.9em;
}

#result-section { display: none; }

/* Loading */

/* === Responsive: single column on mobile === */
@media (max-width: 768px) {
  html, body { overflow: auto; height: auto; }
  .app-layout { flex-direction: column; height: auto; }
  .left-panel {
    width: 100%; min-width: 0; max-width: 100%;
    height: auto; border-right: none; border-bottom: 1px solid var(--border);
    overflow: visible;
  }
  .left-scroll { overflow: visible; }
  .right-panel { height: auto; overflow: visible; }
  .right-scroll { overflow: visible; padding: 16px; }
  .right-empty { display: none; }
  .result-banner { flex-wrap: wrap; }
  .result-banner .banner-stats { width: 100%; justify-content: space-around; margin-top: 8px; }
}
</style>
</head>
<body>

<div class="app-layout">

  <!-- ======= LEFT PANEL ======= -->
  <div class="left-panel">
    <div class="app-header">
      <h1>Epistemic Logic Tableau Solver</h1>
      <div class="subtitle">
        This tool checks whether a formula of <strong title="Complete Multiagent Epistemic Logic with Common and Distributed knowledge" style="cursor:help;text-decoration:underline;text-decoration-style:dotted;text-underline-offset:2px">CMAEL(CD)</strong> is <em>satisfiable</em>: that is,
        whether there exists a Kripke model and a state where the formula is true.
        CMAEL(CD) extends standard multiagent epistemic logic with operators for <em>common knowledge</em>
        (<span class="katex-placeholder" data-tex="\\mathbf{C}_A \\varphi"></span> &mdash; every agent in coalition
        <span class="katex-placeholder" data-tex="A"></span> knows <span class="katex-placeholder" data-tex="\\varphi"></span>,
        and everyone knows that everyone knows it, ad infinitum) and <em>distributed knowledge</em>
        (<span class="katex-placeholder" data-tex="\\mathbf{D}_A \\varphi"></span> &mdash; <span class="katex-placeholder" data-tex="\\varphi"></span>
        follows from the combined knowledge of all agents in <span class="katex-placeholder" data-tex="A"></span>).
      </div>
      <div class="credit">
        Based on <a href="https://arxiv.org/abs/1201.5346" target="_blank" rel="noopener">Ajspur, Goranko &amp; Shkatov (2012)</a>
      </div>
    </div>

    <div class="left-scroll">

      <!-- Formula Input -->
      <div class="left-section">
        <div class="section-title">Formula</div>
        <div class="formula-input-wrap" id="formula-input-wrap">
          <input type="text" id="formula-input" placeholder="e.g.  (Ka p & ~Kb p)" autocomplete="off" spellcheck="false" />
          <button class="input-clear" id="input-clear" onclick="clearInput()" title="Clear">&times;</button>
        </div>
        <div class="actions">
          <button class="btn" id="solve-btn" onclick="solve()">Check Satisfiability</button>
          <label class="checkbox-label">
            <input type="checkbox" id="restricted-cuts" checked />
            Restricted cuts (C1/C2)
          </label>
          <span class="loading" id="loading">Solving...</span>
        </div>
        <div id="parse-error" class="parse-error"></div>
      </div>

      <!-- Examples -->
      <div class="left-section">
        <div class="section-title">Examples</div>
        <div class="examples">
          <button class="example-btn" onclick="setExample('(Ka p & ~Kb p)')">Ka p and not Kb p</button>
          <button class="example-btn" onclick="setExample('C{a,b} p')">Common knowledge</button>
          <button class="example-btn" onclick="setExample('(Ka p & ~p)')">Veridicality</button>
          <button class="example-btn" onclick="setExample('(~D{a,c} C{a,b} p & C{a,b} (p & q))')">Paper Ex. 3</button>
          <button class="example-btn" onclick="setExample('(~D{a,b} p & ~D{a,c} ~Ka p)')">Paper Ex. 4</button>
          <button class="example-btn" onclick="setExample('(C{a,b} Ka p -> ~C{b,c} Kb p)')">Paper Ex. 5</button>
        </div>
      </div>

      <!-- Syntax Reference -->
      <div class="left-section">
        <div class="section-title">Syntax Reference</div>
        <div class="syntax-ref">
          <div class="syntax-item"><code>p</code> &mdash; atomic proposition</div>
          <div class="syntax-item"><code>~p</code> &mdash; <span class="katex-placeholder" data-tex="\\neg p"></span></div>
          <div class="syntax-item"><code>(p & q)</code> &mdash; <span class="katex-placeholder" data-tex="(p \\wedge q)"></span></div>
          <div class="syntax-item"><code>(p | q)</code> &mdash; <span class="katex-placeholder" data-tex="(p \\vee q)"></span></div>
          <div class="syntax-item"><code>(p -> q)</code> &mdash; <span class="katex-placeholder" data-tex="(p \\to q)"></span></div>
          <div class="syntax-item"><code>Ka p</code> &mdash; <span class="katex-placeholder" data-tex="\\mathbf{K}_a\\, p"></span> (agent <em>a</em> knows <em>p</em>)</div>
          <div class="syntax-item"><code>K{a,b} p</code> &mdash; <span class="katex-placeholder" data-tex="(\\mathbf{K}_a\\, p \\wedge \\mathbf{K}_b\\, p)"></span> (a and b knows)</div>
          <div class="syntax-item"><code>D{a,b} p</code> &mdash; <span class="katex-placeholder" data-tex="\\mathbf{D}_{\\{a,b\\}}\\, p"></span> (distributed knowledge)</div>
          <div class="syntax-item"><code>C{a,b} p</code> &mdash; <span class="katex-placeholder" data-tex="\\mathbf{C}_{\\{a,b\\}}\\, p"></span> (common knowledge)</div>
        </div>
      </div>

    </div>
    <div class="left-footer">
      <button class="footer-btn" onclick="openAboutModal()">How it works</button>
      <a class="footer-btn" href="https://github.com/bjesus/cmaelcd" target="_blank" rel="noopener">Source code</a>
    </div>
  </div>

  <!-- ======= RIGHT PANEL ======= -->
  <div class="right-panel">
    <div class="right-scroll">

      <!-- Empty state placeholder -->
      <div class="right-empty" id="right-empty">
        <div class="placeholder-icon">&vellip;</div>
        <h2>Results will appear here</h2>
        <p>Enter a formula on the left and click <strong>Check Satisfiability</strong>, or try one of the examples.</p>
      </div>

      <!-- Result section (hidden until solve) -->
      <div id="result-section">

        <div id="result-banner" class="result-banner"></div>

        <div id="elimination-trace" style="display:none"></div>

        <div class="card">
          <div style="display:flex;align-items:center;margin-bottom:14px">
            <h2 style="margin-bottom:0">Tableau Details</h2>
            <div class="view-toggle">
              <button class="view-toggle-btn" id="view-list-btn" onclick="setView('list')">List</button>
              <button class="view-toggle-btn active" id="view-graph-btn" onclick="setView('graph')">Graph</button>
            </div>
          </div>
          <div class="phase-tabs">
            <button class="phase-tab active" data-phase="final" onclick="showPhase('final', this)">Final Tableau</button>
            <button class="phase-tab" data-phase="initial" onclick="showPhase('initial', this)">Initial Tableau</button>
            <button class="phase-tab" data-phase="pretableau" onclick="showPhase('pretableau', this)">Pretableau</button>
          </div>
          <div class="graph-options" id="graph-options" style="display:none">
            <label><input type="checkbox" id="opt-detailed" onchange="onGraphOptionChange()"> Detailed labels</label>
            <label id="opt-eliminated-label" style="display:none"><input type="checkbox" id="opt-eliminated" onchange="onGraphOptionChange()"> Show eliminated states</label>
            <span class="download-btns">
              <button class="graph-dl-btn" id="dl-svg-btn" onclick="downloadSVG()">SVG</button>
              <button class="graph-dl-btn" id="dl-png-btn" onclick="downloadPNG()">PNG</button>
            </span>
          </div>
          <div id="graph-view" class="graph-container" onclick="openFullscreen()">
            <div class="graph-loading">Rendering graph...</div>
            <div class="graph-hint">Click to expand</div>
          </div>
          <div id="phase-content" style="display:none"></div>
          <button class="dot-toggle" onclick="toggleDot()">Show DOT (Graphviz) output</button>
          <div id="dot-box" class="dot-box"></div>
        </div>
      </div>

    </div>
  </div>

</div>

<!-- About / How It Works Modal -->
<div class="modal-backdrop" id="about-modal" onclick="if(event.target===this)closeAboutModal()">
  <div class="modal">
    <button class="modal-close" onclick="closeAboutModal()">&times;</button>
    <h2>How It Works</h2>

    <div class="about-section">
      <h3>The Algorithm</h3>
      <p>The algorithm is a <em>tableau-based decision procedure</em> that works in three phases:</p>
      <div class="phase-explain">
        <div class="phase-step">
          <div class="phase-num">1</div>
          <div>
            <strong>Construction (Pretableau)</strong><br>
            Starting from the input formula, the algorithm builds a graph of <em>prestates</em> and <em>states</em>.
            A prestate is a set of formulas waiting to be expanded. Each prestate is expanded into one or more
            <em>fully expanded, downward saturated</em> states by applying logical decomposition rules
            (splitting conjunctions, branching on disjunctions, and handling modal operators).
            For each diamond formula (<span class="katex-placeholder" data-tex="\\neg \\mathbf{D}_A \\varphi"></span>)
            in a state, a new prestate is created as a successor, ensuring the model has the required transitions.
            The process continues until no new prestates or states need to be created. This builds the <em>pretableau</em>.
          </div>
        </div>
        <div class="phase-step">
          <div class="phase-num">2</div>
          <div>
            <strong>Prestate Elimination</strong><br>
            Prestates served as intermediate construction artifacts. In this phase, every prestate is removed
            and edges are rewired: if state <em>s</em> pointed to prestate <em>p</em>, and <em>p</em> expanded
            to state <em>t</em>, then <em>s</em> now points directly to <em>t</em>.
            This produces the <em>initial tableau</em>: a graph consisting only of states and direct transition edges.
          </div>
        </div>
        <div class="phase-step">
          <div class="phase-num">3</div>
          <div>
            <strong>State Elimination</strong><br>
            The algorithm iteratively removes &ldquo;defective&rdquo; states. Two types of defects are checked in a dovetailed loop:
            <ul style="margin:8px 0 4px 20px">
              <li><strong>E1:</strong> If a state contains a diamond formula but has no matching successor, it is eliminated.</li>
              <li><strong>E2:</strong> <em>Eventualities</em> (arising from negated common knowledge formulas like
                <span class="katex-placeholder" data-tex="\\neg \\mathbf{C}_A \\varphi"></span>) must be
                <em>realized</em>: there must be a finite path of accessible states witnessing the eventuality.
                States where an eventuality cannot be realized are eliminated.</li>
            </ul>
            This loop continues until no more states can be removed, yielding the <em>final tableau</em>.
          </div>
        </div>
      </div>
      <p style="margin-top:12px">
        The input formula is <strong>satisfiable</strong> if and only if the final tableau still contains a state
        that includes the input formula. The tool also supports <strong>restricted cut conditions (C1/C2)</strong>,
        an optimization from the paper that dramatically reduces the number of states explored (e.g., from 113 to 30 states
        in Example 5) without affecting correctness.
      </p>
    </div>

    <div class="about-section">
      <h3>Operators at a glance</h3>
      <table class="about-table">
        <tr><th>Operator</th><th>Syntax</th><th>Meaning</th></tr>
        <tr>
          <td><span class="katex-placeholder" data-tex="\\mathbf{K}_a \\varphi"></span></td>
          <td><code>Ka p</code></td>
          <td>Agent <em>a</em> knows <span class="katex-placeholder" data-tex="\\varphi"></span></td>
        </tr>
        <tr>
          <td><span class="katex-placeholder" data-tex="\\bigwedge_{a \\in A} \\mathbf{K}_a \\varphi"></span></td>
          <td><code>K{a,b} p</code></td>
          <td>Every agent in <span class="katex-placeholder" data-tex="A"></span> individually knows <span class="katex-placeholder" data-tex="\\varphi"></span></td>
        </tr>
        <tr>
          <td><span class="katex-placeholder" data-tex="\\mathbf{D}_A \\varphi"></span></td>
          <td><code>D{a,b} p</code></td>
          <td>It is distributed knowledge among <span class="katex-placeholder" data-tex="A"></span> that <span class="katex-placeholder" data-tex="\\varphi"></span></td>
        </tr>
        <tr>
          <td><span class="katex-placeholder" data-tex="\\mathbf{C}_A \\varphi"></span></td>
          <td><code>C{a,b} p</code></td>
          <td>It is common knowledge among <span class="katex-placeholder" data-tex="A"></span> that <span class="katex-placeholder" data-tex="\\varphi"></span></td>
        </tr>
      </table>
      <p style="margin-top:8px;font-size:0.88em;color:var(--text-muted)">
        Note: <code>Ka p</code> is equivalent to <code>D{a} p</code> &mdash; individual knowledge is distributed knowledge for a singleton coalition.
        <code>K{a,b} p</code> is syntactic sugar for <code>(Ka p &amp; Kb p)</code>.
      </p>
    </div>

    <div class="about-section about-credits">
      <h3>Reference</h3>
      <p>
        <strong>Tableau-based decision procedure for the multiagent epistemic logic with all coalitional operators
        for common and distributed knowledge</strong><br>
        Mai Ajspur, Valentin Goranko, and Dmitry Shkatov (2012)<br>
        <a href="https://arxiv.org/abs/1201.5346" target="_blank" rel="noopener" style="color:var(--accent)">arXiv:1201.5346v1</a>
      </p>
    </div>
  </div>
</div>

<!-- Fullscreen graph overlay -->
<div class="graph-fullscreen" id="graph-fullscreen">
  <div class="graph-fs-toolbar">
    <span class="title" id="graph-fs-title">Tableau Graph</span>
    <span class="hint">Scroll to zoom &middot; Drag to pan &middot; Esc to close</span>
    <button class="graph-fs-close" onclick="closeFullscreen()">Close</button>
  </div>
  <div class="graph-fs-viewport" id="graph-fs-viewport"></div>
</div>

<script>
let lastResult = null;
let currentPhase = 'final';
let currentView = 'graph';
// Worker communication state
var renderCallbacks = {};
var renderIdCounter = 0;
var pendingSolve = null;

// Set up the worker message handler. Called from DOMContentLoaded
// so that the second script block (which creates window.__solverWorker)
// has already executed.
function initWorkerHandler() {
  if (!window.__solverWorker) return;
  window.__solverWorker.onmessage = function(e) {
    var msg = e.data;
    if (msg.type === 'status') {
      var el = document.getElementById('solve-status');
      if (el) el.textContent = msg.stage;
    } else if (msg.type === 'result') {
      showSolving(false);
      lastResult = msg.result; // Store global result
      displayResult(msg.result, pendingSolve);
      pendingSolve = null;
    } else if (msg.type === 'error') {
      showSolving(false);
      showSolveError(msg.message);
      pendingSolve = null;
    } else if (msg.type === 'svg') {
      if (renderCallbacks[msg.id]) {
        renderCallbacks[msg.id](msg.svg, null);
        delete renderCallbacks[msg.id];
      }
    } else if (msg.type === 'svg-error') {
      if (renderCallbacks[msg.id]) {
        renderCallbacks[msg.id](null, msg.message);
        delete renderCallbacks[msg.id];
      }
    }
  };
}

function requestSvg(dot) {
  return new Promise(function(resolve, reject) {
    var id = ++renderIdCounter;
    renderCallbacks[id] = function(svg, err) {
      if (err) reject(new Error(err));
      else resolve(svg);
    };
    window.__solverWorker.postMessage({type:'render', dot:dot, id:id});
  });
}

function showSolving(show) {
  var section = document.getElementById('result-section');
  var empty = document.getElementById('right-empty');
  var banner = document.getElementById('result-banner');
  var btn = document.getElementById('solve-btn');
  
  if (show) {
    section.style.display = 'block';
    if (empty) empty.style.display = 'none';
    banner.className = 'result-banner loading';
    banner.innerHTML = '<span class="spinner"></span><div><div id="solve-status">Starting solver...</div></div>';
    if (btn) btn.disabled = true;
    
    // Clear previous results while loading
    document.getElementById('phase-content').innerHTML = '';
    document.getElementById('graph-view').innerHTML = '<div class="graph-loading">Waiting for results...</div>';
     document.getElementById('elimination-trace').innerHTML = '';
  } else {
    if (btn) btn.disabled = false;
  }
}

function showSolveError(msg) {
  var errorEl = document.getElementById('parse-error');
  errorEl.textContent = msg;
  errorEl.style.display = 'block';
  var section = document.getElementById('result-section');
  section.style.display = 'none';
  var btn = document.getElementById('solve-btn');
  if (btn) btn.disabled = false;
}

function getDotKey() {
  var detailed = document.getElementById('opt-detailed').checked;
  var eliminated = document.getElementById('opt-eliminated').checked;
  if (currentPhase === 'pretableau') return detailed ? 'pretableauDetailed' : 'pretableau';
  if (currentPhase === 'initial') return detailed ? 'initialDetailed' : 'initial';
  // final phase has more variants
  var key = 'final';
  if (detailed) key += 'Detailed';
  if (eliminated) key += 'Eliminated';
  return key;
}

function onGraphOptionChange() {
  if (currentView === 'graph' && lastResult) {
    renderGraph(lastResult, currentPhase);
  }
  // Update DOT output too
  if (lastResult) {
    var dotBox = document.getElementById('dot-box');
    dotBox.textContent = lastResult.dots[getDotKey()] || '';
  }
}

function updateGraphOptionsVisibility() {
  document.getElementById('graph-options').style.display = currentView === 'graph' ? 'flex' : 'none';
  // Show "eliminated" checkbox only on final phase and when there are eliminations
  var showElimLabel = document.getElementById('opt-eliminated-label');
  var hasElims = lastResult && lastResult.eliminations && lastResult.eliminations.length > 0;
  showElimLabel.style.display = (currentPhase === 'final' && hasElims) ? '' : 'none';
}

function setView(view) {
  currentView = view;
  document.getElementById('view-list-btn').classList.toggle('active', view === 'list');
  document.getElementById('view-graph-btn').classList.toggle('active', view === 'graph');
  document.getElementById('phase-content').style.display = view === 'list' ? 'block' : 'none';
  document.getElementById('graph-view').style.display = view === 'graph' ? 'block' : 'none';
  updateGraphOptionsVisibility();
  if (view === 'graph' && lastResult) {
    renderGraph(lastResult, currentPhase);
  }
}

var graphPhaseNames = { final: 'Final Tableau', initial: 'Initial Tableau', pretableau: 'Pretableau' };

function addDotTitle(dot, formula, phase) {
  var title = (formula ? formula + '  \\u2014  ' : '') + (graphPhaseNames[phase] || '');
  return dot.replace('digraph tableau {', 'digraph tableau {\\n  label="' + escDotStr(title) + '"; labelloc=t; fontsize=16; fontname="Helvetica";');
}

// Track which dotKey is currently rendered in graph-view
var renderedDotKey = null;

function renderGraph(result, phase) {
  const container = document.getElementById('graph-view');
  const dotKey = getDotKey();
  const dot = result.dots[dotKey];
  if (!dot) {
    container.innerHTML = '<div class="graph-loading">No graph data available</div>';
    renderedDotKey = null;
    return;
  }
  
  // Skip re-render if the same dotKey is already displayed
  if (dotKey === renderedDotKey && container.querySelector('svg')) return;
  
  var formula = document.getElementById('formula-input').value.trim();
  var titledDot = addDotTitle(dot, formula, phase);
  
  container.innerHTML = '<div class="graph-loading">Rendering graph...</div><div class="graph-hint">Click to expand</div>';
  renderedDotKey = null;
  requestSvg(titledDot).then(function(svg) {
    injectGraphSvg(svg);
    renderedDotKey = dotKey;
  }).catch(function(e) {
    container.innerHTML = '<div class="graph-loading">Error rendering graph: ' + e.message + '</div>';
    renderedDotKey = null;
  });
}

function injectGraphSvg(svgStr) {
  var container = document.getElementById('graph-view');
  if (!container) return;
  
  container.innerHTML = '<div class="graph-hint">Click to expand</div>';
  // Check if svgStr is a string or an object?
  // worker sends string via renderString, but in browser context viz.renderSVGElement returns Element.
  // worker Viz.renderString returns string. So svgStr is a string.
  container.insertAdjacentHTML('beforeend', svgStr);
  
  // The inserted SVG needs to be styled/sized if needed?
  // Previous code used container.insertBefore(svg, container.firstChild).
}

function getDownloadFilename(ext) {
  return 'tableau-' + currentPhase + (document.getElementById('opt-detailed').checked ? '-detailed' : '') + '.' + ext;
}

function getGraphSvgString() {
  // Clone the already-rendered SVG from graph-view (includes title, hidden by CSS)
  var svg = document.querySelector('#graph-view svg');
  if (!svg) return null;
  var clone = svg.cloneNode(true);
  // Preserve explicit width/height so Image can determine naturalWidth/naturalHeight
  var wAttr = svg.getAttribute('width');
  var hAttr = svg.getAttribute('height');
  if (!wAttr || !hAttr) {
    var vb = svg.viewBox.baseVal;
    if (vb && vb.width && vb.height) {
      clone.setAttribute('width', vb.width + 'pt');
      clone.setAttribute('height', vb.height + 'pt');
    }
  }
  // Add white background for export
  clone.setAttribute('style', (clone.getAttribute('style') || '') + '; background: white;');
  // Use XMLSerializer to ensure xmlns="http://www.w3.org/2000/svg" is included.
  // outerHTML in HTML documents omits namespace declarations, producing invalid
  // standalone SVG that browsers cannot load as an Image (breaks PNG export).
  return new XMLSerializer().serializeToString(clone);
}

function escDotStr(s) {
  return s.replace(/\\\\/g, '\\\\\\\\').replace(/"/g, '\\\\"');
}

function setButtonLoading(btn, loading) {
  if (loading) {
    btn._origHTML = btn.innerHTML;
    btn.innerHTML = '<span class="spinner-sm"></span>';
    btn.disabled = true;
  } else {
    btn.innerHTML = btn._origHTML || btn.innerHTML;
    btn.disabled = false;
  }
}

function triggerDownload(blob, filename) {
  var url = URL.createObjectURL(blob);
  var a = document.createElement('a');
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}

function downloadSVG() {
  var btn = document.getElementById('dl-svg-btn');
  var svgStr = getGraphSvgString();
  if (!svgStr) return;
  setButtonLoading(btn, true);
  try {
    triggerDownload(new Blob([svgStr], { type: 'image/svg+xml' }), getDownloadFilename('svg'));
  } finally {
    setButtonLoading(btn, false);
  }
}

function downloadPNG() {
  var btn = document.getElementById('dl-png-btn');
  var svgStr = getGraphSvgString();
  if (!svgStr) return;
  setButtonLoading(btn, true);
  var blob = new Blob([svgStr], { type: 'image/svg+xml' });
  var url = URL.createObjectURL(blob);
  var img = new Image();
  img.onload = function() {
    var scale = 2; // 2x for crisp output
    var canvas = document.createElement('canvas');
    canvas.width = img.naturalWidth * scale;
    canvas.height = img.naturalHeight * scale;
    var ctx = canvas.getContext('2d');
    ctx.fillStyle = 'white';
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    ctx.drawImage(img, 0, 0, canvas.width, canvas.height);
    canvas.toBlob(function(pngBlob) {
      triggerDownload(pngBlob, getDownloadFilename('png'));
      setButtonLoading(btn, false);
    }, 'image/png');
    URL.revokeObjectURL(url);
  };
  img.onerror = function() {
    URL.revokeObjectURL(url);
    setButtonLoading(btn, false);
  };
  img.src = url;
}

// Fullscreen graph state
let fsScale = 1;
let fsPanX = 0;
let fsPanY = 0;
let fsDragging = false;
let fsDragStartX = 0;
let fsDragStartY = 0;
let fsPanStartX = 0;
let fsPanStartY = 0;

function setupFsSvg(svg, viewport) {
  // Reset transform
  fsScale = 1;
  fsPanX = 0;
  fsPanY = 0;

  // Get intrinsic size from width/height attributes (Viz.js uses "Xpt" units)
  // parseFloat handles the "pt" suffix. Fall back to viewBox or defaults.
  var sw, sh;
  var wAttr = svg.getAttribute('width');
  var hAttr = svg.getAttribute('height');
  if (wAttr && hAttr) {
    sw = parseFloat(wAttr);
    sh = parseFloat(hAttr);
  } else {
    var vb = svg.viewBox.baseVal;
    sw = (vb && vb.width) || 100;
    sh = (vb && vb.height) || 100;
  }

  // Set explicit pixel dimensions (not %) so the SVG has a known size
  // that we control entirely via CSS transform for pan/zoom
  svg.removeAttribute('width');
  svg.removeAttribute('height');
  svg.style.width = sw + 'px';
  svg.style.height = sh + 'px';
  svg.style.overflow = 'visible';

  const vw = viewport.clientWidth;
  const vh = viewport.clientHeight;

  // Initial scale to fit viewport
  const scaleX = vw / sw;
  const scaleY = vh / sh;
  fsScale = Math.min(scaleX, scaleY) * 0.9;
  
  // Initial center
  fsPanX = (vw - sw * fsScale) / 2;
  fsPanY = (vh - sh * fsScale) / 2;

  updateFsTransform();
}

function openFullscreen() {
  if (!lastResult) return;

  const overlay = document.getElementById('graph-fullscreen');
  const viewport = document.getElementById('graph-fs-viewport');
  document.getElementById('graph-fs-title').textContent = graphPhaseNames[currentPhase] || 'Graph';

  overlay.classList.add('open');
  document.body.style.overflow = 'hidden';

  // Reuse the SVG already rendered in graph-view by cloning it
  var existingSvg = document.querySelector('#graph-view svg');
  if (existingSvg) {
    var clone = existingSvg.cloneNode(true);
    viewport.innerHTML = '';
    viewport.appendChild(clone);
    setupFsSvg(clone, viewport);
  } else {
    viewport.innerHTML = '<div class="graph-loading">No graph available</div>';
  }
}

function closeFullscreen() {
  const overlay = document.getElementById('graph-fullscreen');
  overlay.classList.remove('open');
  document.body.style.overflow = '';
  document.getElementById('graph-fs-viewport').innerHTML = '';
}

function updateFsTransform() {
  applyFsTransform(getFsSvg());
}

function applyFsTransform(svg) {
  if (!svg) return;
  svg.style.transform = 'translate(' + fsPanX + 'px, ' + fsPanY + 'px) scale(' + fsScale + ')';
}

function getFsSvg() {
  return document.querySelector('#graph-fs-viewport svg');
}

// Wheel zoom
document.addEventListener('wheel', function(e) {
  const overlay = document.getElementById('graph-fullscreen');
  if (!overlay.classList.contains('open')) return;
  const viewport = document.getElementById('graph-fs-viewport');
  if (!viewport.contains(e.target) && e.target !== viewport) return;

  e.preventDefault();
  const svg = getFsSvg();
  if (!svg) return;

  const rect = viewport.getBoundingClientRect();
  const mx = e.clientX - rect.left;
  const my = e.clientY - rect.top;

  const oldScale = fsScale;
  const zoomFactor = e.deltaY < 0 ? 1.12 : 1 / 1.12;
  fsScale = Math.max(0.1, Math.min(10, fsScale * zoomFactor));

  // Zoom toward cursor position
  fsPanX = mx - (mx - fsPanX) * (fsScale / oldScale);
  fsPanY = my - (my - fsPanY) * (fsScale / oldScale);

  applyFsTransform(svg);
}, { passive: false });

// Mouse drag pan
document.addEventListener('mousedown', function(e) {
  const overlay = document.getElementById('graph-fullscreen');
  if (!overlay.classList.contains('open')) return;
  const viewport = document.getElementById('graph-fs-viewport');
  if (!viewport.contains(e.target) && e.target !== viewport) return;

  fsDragging = true;
  fsDragStartX = e.clientX;
  fsDragStartY = e.clientY;
  fsPanStartX = fsPanX;
  fsPanStartY = fsPanY;
  e.preventDefault();
});

document.addEventListener('mousemove', function(e) {
  if (!fsDragging) return;
  fsPanX = fsPanStartX + (e.clientX - fsDragStartX);
  fsPanY = fsPanStartY + (e.clientY - fsDragStartY);
  const svg = getFsSvg();
  if (svg) applyFsTransform(svg);
});

document.addEventListener('mouseup', function() {
  fsDragging = false;
});

// Esc to close overlays
document.addEventListener('keydown', function(e) {
  if (e.key === 'Escape') {
    const graphOverlay = document.getElementById('graph-fullscreen');
    if (graphOverlay.classList.contains('open')) {
      closeFullscreen();
      e.preventDefault();
      return;
    }
    const aboutModal = document.getElementById('about-modal');
    if (aboutModal.classList.contains('open')) {
      closeAboutModal();
      e.preventDefault();
    }
  }
});

let aboutRendered = false;
function openAboutModal() {
  const modal = document.getElementById('about-modal');
  modal.classList.add('open');
  document.body.style.overflow = 'hidden';
  // Render KaTeX in the modal on first open
  if (!aboutRendered) {
    modal.querySelectorAll('.katex-placeholder').forEach(function(el) {
      if (el.dataset.tex) {
        renderLatex(el, el.dataset.tex);
        el.classList.remove('katex-placeholder');
      }
    });
    aboutRendered = true;
  }
}
function closeAboutModal() {
  const modal = document.getElementById('about-modal');
  modal.classList.remove('open');
  // Only restore scroll if fullscreen graph isn't also open
  if (!document.getElementById('graph-fullscreen').classList.contains('open')) {
    document.body.style.overflow = '';
  }
}

function setExample(formula) {
  document.getElementById('formula-input').value = formula;
  updateClearBtn();
  solve();
}

function clearInput() {
  var input = document.getElementById('formula-input');
  input.value = '';
  updateClearBtn();
  input.focus();
  document.getElementById('parse-error').style.display = 'none';
  var section = document.getElementById('result-section');
  if (section) section.style.display = 'none';
  var empty = document.getElementById('right-empty');
  if (empty) empty.style.display = '';
  // Reset URL to bare path
  history.pushState(null, '', window.location.pathname);
}

function buildUrl(formula, restrictedCuts) {
  var params = new URLSearchParams();
  if (formula) params.set('formula', formula);
  if (!restrictedCuts) params.set('rc', '0');
  var qs = params.toString();
  return window.location.pathname + (qs ? '?' + qs : '');
}

function updateClearBtn() {
  var wrap = document.getElementById('formula-input-wrap');
  var input = document.getElementById('formula-input');
  wrap.classList.toggle('has-value', input.value.length > 0);
}

function renderLatex(container, tex) {
  try {
    katex.render(tex, container, { throwOnError: false, displayMode: false });
  } catch(e) {
    container.textContent = tex;
  }
}

// Render all placeholders on load; check URL for initial formula
document.addEventListener('DOMContentLoaded', function() {
  initWorkerHandler();
  document.querySelectorAll('.katex-placeholder').forEach(function(el) {
    renderLatex(el, el.dataset.tex);
  });
  var input = document.getElementById('formula-input');
  input.addEventListener('input', updateClearBtn);

  // Check URL for ?formula= parameter
  var params = new URLSearchParams(window.location.search);
  var initFormula = params.get('formula');
  if (initFormula) {
    input.value = initFormula;
    if (params.get('rc') === '0') {
      document.getElementById('restricted-cuts').checked = false;
    }
    updateClearBtn();
    // Replace current history entry with state so popstate works
    var rc = document.getElementById('restricted-cuts').checked;
    history.replaceState({ formula: initFormula, rc: rc }, '', buildUrl(initFormula, rc));
    solve(true);
  } else {
    input.focus();
  }
});

// Navigate back/forward between previously solved formulas
window.addEventListener('popstate', function(e) {
  var state = e.state;
  if (state && state.formula) {
    document.getElementById('formula-input').value = state.formula;
    document.getElementById('restricted-cuts').checked = state.rc !== false;
    updateClearBtn();
    solve(true);
  } else {
    // No formula — reset to empty state
    document.getElementById('formula-input').value = '';
    updateClearBtn();
    document.getElementById('parse-error').style.display = 'none';
    var section = document.getElementById('result-section');
    if (section) section.style.display = 'none';
    var empty = document.getElementById('right-empty');
    if (empty) empty.style.display = '';
    document.getElementById('formula-input').focus();
  }
});

// Enter key to solve
document.addEventListener('keydown', function(e) {
  if (e.key === 'Enter' && document.activeElement && document.activeElement.id === 'formula-input') {
    solve();
  }
});

function showPhase(phase, btn) {
  currentPhase = phase;
  document.querySelectorAll('.phase-tab').forEach(t => t.classList.remove('active'));
  if (btn) btn.classList.add('active');
  updateGraphOptionsVisibility();
  if (lastResult) {
    displayPhase(lastResult, phase);
    if (currentView === 'graph') {
      renderGraph(lastResult, phase);
    }
  }
}

function displayPhase(result, phase) {
  const container = document.getElementById('phase-content');
  let html = '';

  let states, edges;
  if (phase === 'pretableau') {
    states = result.pretableau.states;
    edges = result.pretableau.solidEdges;
    const prestates = result.pretableau.prestates;

    html += '<div class="section-label">States (' + Object.keys(states).length + ')</div>';
    html += '<div class="state-list">';
    if (Object.keys(states).length === 0) {
      html += '<div class="empty-notice">No states were created (all expansions were inconsistent)</div>';
    }
    for (const [id, s] of Object.entries(states)) {
      html += '<div class="state-item' + (s.hasInput ? ' has-input' : '') + '">';
      html += '<div class="state-id">' + id + '</div>';
      html += '<div class="state-formulas" data-tex="' + escAttr(s.formulasLatex) + '"></div>';
      html += '</div>';
    }
    html += '</div>';

    html += '<div class="section-label">Prestates (' + Object.keys(prestates).length + ')</div>';
    html += '<div class="state-list">';
    for (const [id, s] of Object.entries(prestates)) {
      html += '<div class="state-item" style="border-left-color:#999;border-style:dashed">';
      html += '<div class="state-id">' + id + ' (prestate)</div>';
      html += '<div class="state-formulas" data-tex="' + escAttr(s.formulasLatex) + '"></div>';
      html += '</div>';
    }
    html += '</div>';
  } else {
    const tab = phase === 'initial' ? result.initialTableau : result.finalTableau;
    states = tab.states;
    edges = tab.edges;

    html += '<div class="section-label">States (' + Object.keys(states).length + ')</div>';
    html += '<div class="state-list">';
    if (Object.keys(states).length === 0) {
      html += '<div class="empty-notice">All states were eliminated &mdash; the formula is unsatisfiable</div>';
    }
    for (const [id, s] of Object.entries(states)) {
      html += '<div class="state-item' + (s.hasInput ? ' has-input' : '') + '">';
      html += '<div class="state-id">' + id + (s.hasInput ? ' (contains input formula)' : '') + '</div>';
      html += '<div class="state-formulas" data-tex="' + escAttr(s.formulasLatex) + '"></div>';
      html += '</div>';
    }
    html += '</div>';

    html += '<div class="section-label">Edges (' + edges.length + ')</div>';
    html += '<div class="state-list">';
    if (edges.length === 0 && Object.keys(states).length > 0) {
      html += '<div class="empty-notice">No transition edges</div>';
    } else if (edges.length === 0) {
      html += '<div class="empty-notice">No edges remain</div>';
    }
    for (const e of edges) {
      html += '<div class="edge-item">';
      html += '<span style="font-weight:600;color:var(--accent)">' + e.from + '</span>';
      html += '<span class="edge-arrow">&xrarr;</span>';
      html += '<span style="font-weight:600;color:var(--accent)">' + e.to + '</span>';
      html += '<span style="color:var(--text-muted);font-size:0.85em">via</span>';
      html += '<span class="edge-label" data-tex="' + escAttr(e.labelLatex) + '"></span>';
      html += '</div>';
    }
    html += '</div>';
  }

  container.innerHTML = html;

  // Render KaTeX in new elements
  container.querySelectorAll('[data-tex]').forEach(function(el) {
    renderLatex(el, el.dataset.tex);
  });

  // Update DOT
  const dotBox = document.getElementById('dot-box');
  dotBox.textContent = result.dots[getDotKey()] || '';
}

function escAttr(s) {
  return s.replace(/&/g,'&amp;').replace(/"/g,'&quot;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
}

function toggleDot() {
  const box = document.getElementById('dot-box');
  box.style.display = box.style.display === 'none' || !box.style.display ? 'block' : 'none';
}

function renderEliminationTrace(result) {
  const container = document.getElementById('elimination-trace');

  if (result.satisfiable) {
    container.style.display = 'none';
    container.innerHTML = '';
    return;
  }

  var html = '<div class="elimination-card">';
  html += '<h3>Why is this unsatisfiable?</h3>';

  if (result.stats.pretableauStates === 0) {
    // No states were ever created — patent inconsistency during expansion
    html += '<div class="elim-summary">';
    html += 'All formula expansions led to <strong>contradictions</strong>. ';
    html += 'Every possible assignment of truth values to subformulas resulted in a set containing both ';
    html += '<em>&phi;</em> and <em>&not;&phi;</em> for some formula &phi;, making the formula unsatisfiable ';
    html += 'without even needing to build a tableau.';
    html += '</div>';
  } else if (result.eliminations.length === 0) {
    // States existed in initial tableau but all ended up eliminated (edge case)
    html += '<div class="elim-summary">';
    html += 'All ' + result.stats.initialStates + ' states from the initial tableau were eliminated.';
    html += '</div>';
  } else {
    var e1Count = result.stats.eliminationsE1 || 0;
    var e2Count = result.stats.eliminationsE2 || 0;
    html += '<div class="elim-summary">';
    html += 'All ' + result.stats.initialStates + ' states from the initial tableau were eliminated during Phase 3:';
    if (e1Count > 0) html += '<br><strong>' + e1Count + '</strong> by rule <strong>E1</strong> (diamond formula had no valid successor)';
    if (e2Count > 0) html += '<br><strong>' + e2Count + '</strong> by rule <strong>E2</strong> (eventuality could not be realized)';
    html += '</div>';

    html += '<div class="elim-list">';
    for (var i = 0; i < result.eliminations.length; i++) {
      var e = result.eliminations[i];
      html += '<div class="elim-item">';
      html += '<span class="elim-badge ' + e.rule.toLowerCase() + '">' + e.rule + '</span>';
      html += '<span class="elim-id">' + e.stateId + '</span>';
      html += '<div class="elim-reason">';
      if (e.rule === 'E1') {
        html += 'Diamond formula <span data-tex="' + escAttr(e.formulaLatex) + '"></span> had no surviving successor state';
      } else {
        html += 'Eventuality <span data-tex="' + escAttr(e.formulaLatex) + '"></span> could not be realized (no finite witness path)';
      }
      html += '<div class="elim-formulas">State contained: <span data-tex="' + escAttr(e.stateFormulasLatex) + '"></span></div>';
      html += '</div>';
      html += '</div>';
    }
    html += '</div>';
  }

  html += '</div>';
  container.innerHTML = html;
  container.style.display = 'block';

  // Render KaTeX
  container.querySelectorAll('[data-tex]').forEach(function(el) {
    renderLatex(el, el.dataset.tex);
  });
}

function displayResult(result, solveState) {
  const section = document.getElementById('result-section');
  section.style.display = 'block';
  var empty = document.getElementById('right-empty');
  if (empty) empty.style.display = 'none';

  const banner = document.getElementById('result-banner');
  var pretableauNodes = result.stats.pretableauStates + result.stats.pretableauPrestates;
  var statsHtml = '<div class="banner-stats">' +
    '<div class="banner-stat" title="Phase 1 (Construction): Total nodes in the pretableau graph (' + result.stats.pretableauPrestates + ' prestates + ' + result.stats.pretableauStates + ' states). Prestates are intermediate expansion nodes; states are fully expanded possible worlds."><div class="num">' + pretableauNodes + '</div><div class="label">Pretableau</div></div>' +
    '<div class="banner-stat" title="Phase 2 (Prestate Elimination): States remaining after removing prestates and rewiring edges into direct state-to-state transitions. This is the starting point for state elimination."><div class="num">' + result.stats.initialStates + '</div><div class="label">Initial</div></div>' +
    '<div class="banner-stat" title="Phase 3 (State Elimination): States surviving after removing defective states via rules E1 (missing successor) and E2 (unrealized eventuality). The formula is satisfiable iff this is greater than 0."><div class="num">' + result.stats.finalStates + '</div><div class="label">Final</div></div>' +
    '</div>';
  if (result.satisfiable) {
    banner.className = 'result-banner sat';
    banner.innerHTML = '<span class="icon">&#10003;</span><div><div>Satisfiable</div>' +
      '<div class="result-formula" data-tex="' + escAttr(result.inputLatex) + '"></div></div>' + statsHtml;
  } else {
    banner.className = 'result-banner unsat';
    banner.innerHTML = '<span class="icon">&#10007;</span><div><div>Unsatisfiable</div>' +
      '<div class="result-formula" data-tex="' + escAttr(result.inputLatex) + '"></div></div>' + statsHtml;
  }
  banner.querySelectorAll('[data-tex]').forEach(function(el) {
    renderLatex(el, el.dataset.tex);
  });

  // Render elimination trace
  renderEliminationTrace(result);

  // Reset graph options
  document.getElementById('opt-detailed').checked = false;
  document.getElementById('opt-eliminated').checked = false;

  // Reset to final tab
  currentPhase = 'final';
  document.querySelectorAll('.phase-tab').forEach(t => t.classList.remove('active'));
  document.querySelector('.phase-tab[data-phase="final"]').classList.add('active');
  renderedDotKey = null; // Reset so renderGraph does not skip
  updateGraphOptionsVisibility();
  displayPhase(result, 'final');
  // Render graph with title (title hidden in web view via CSS, visible on export/fullscreen)
  renderGraph(result, 'final');
  
  // Update browser URL and history
  if (solveState && !solveState.fromHistory) {
    var stateObj = { formula: solveState.formula, rc: solveState.restrictedCuts };
    history.pushState(stateObj, '', buildUrl(solveState.formula, solveState.restrictedCuts));
    section.scrollIntoView({ behavior: 'smooth', block: 'start' });
  }
}

function restartWorker() {
  if (window.__solverWorker) {
    window.__solverWorker.terminate();
  }
  // Clear any pending render callbacks
  for (var id in renderCallbacks) {
    delete renderCallbacks[id];
  }
  window.__solverWorker = new Worker(window.__workerBlobUrl);
  initWorkerHandler();
}

function solve(fromHistory) {
  const formula = document.getElementById('formula-input').value.trim();
  if (!formula) return;

  const restrictedCuts = document.getElementById('restricted-cuts').checked;
  const errorEl = document.getElementById('parse-error');
  errorEl.style.display = 'none';

  // If a previous solve is in-flight, terminate and restart the worker
  if (pendingSolve) {
    restartWorker();
  }

  showSolving(true);
  pendingSolve = { formula: formula, restrictedCuts: restrictedCuts, fromHistory: fromHistory };
  
  if (window.__solverWorker) {
    window.__solverWorker.postMessage({
      type: 'solve', formula: formula, restrictedCuts: restrictedCuts
    });
  } else {
    showSolveError("Solver worker not initialized. Reload page.");
  }
}

// Placeholder solver — replaced by bundled code
function solveFormula(f, a, r) {
  throw new Error('Solver not loaded. Build with: bun run src/build-html.ts');
}
<\/script>
</body>
</html>`;
}
