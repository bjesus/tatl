# CMAEL(CD) Tableau Solver

A tableau-based satisfiability checker for **CMAEL(CD)** — Complete Multiagent Epistemic Logic with Common and Distributed knowledge.

Given a formula, the solver determines whether it is *satisfiable*: whether there exists a Kripke model and a state where the formula is true. It provides full tableau construction details, statistics, and graph visualization.

Available as both a **command-line tool** and a **web interface**.

## Based on

> **Tableau-based decision procedure for the multiagent epistemic logic with all coalitional operators for common and distributed knowledge**
> Mai Ajspur, Valentin Goranko, and Dmitry Shkatov (2012)
> [arXiv:1201.5346v1](https://arxiv.org/abs/1201.5346)

The implementation faithfully follows the paper's algorithm, including the restricted cut conditions (C1/C2) that dramatically reduce the state space without affecting correctness.

## Formula syntax

The input syntax uses ASCII characters only — no special symbols needed:

| Operator | Syntax | Meaning |
|---|---|---|
| Atom | `p`, `q`, `myProp` | Propositional variable |
| Negation | `~p` | not p |
| Conjunction | `(p & q)` | p and q |
| Disjunction | `(p \| q)` | p or q (desugars to `~(~p & ~q)`) |
| Implication | `(p -> q)` | p implies q (desugars to `~(p & ~q)`) |
| Individual knowledge | `Ka p` | Agent *a* knows *p* (equivalent to `D{a} p`) |
| Distributed knowledge | `D{a,b} p` | Distributed knowledge of coalition {a,b} |
| Common knowledge | `C{a,b} p` | Common knowledge of coalition {a,b} |

Binary connectives must be wrapped in parentheses: `(p & q)`, not `p & q`.

## Getting started

### Prerequisites

[Bun](https://bun.sh) v1.0 or later.

### Install

```bash
bun install
```

### Run tests

```bash
bun test
```

## Web interface

### Build and serve locally

```bash
bun run build:web     # produces dist/index.html
bun run serve.ts      # serves on http://localhost:3000
```

### Static deployment

The build produces a single self-contained `dist/index.html` file with the solver bundled inline. Deploy it to any static host (GitHub Pages, Netlify, Vercel, S3, etc.) — no server required.

The only external dependencies are KaTeX and viz.js loaded from CDN.

### Features

- Satisfiability checking with result banner
- Toggle between restricted and unrestricted cut conditions
- Tableau statistics across all three phases
- List view showing all states and edges with KaTeX-rendered formulas
- Graph view rendering the tableau as an interactive SVG via Graphviz (viz.js)
- Fullscreen graph mode with pan and zoom (click graph to expand, Esc to close)
- Example formulas from the paper (Examples 3, 4, 5)

## CLI

### One-shot mode

```bash
bun run src/index.ts "(Ka p & ~Kb p)"
```

Exit code: `0` if satisfiable, `1` if unsatisfiable.

### Options

```
--verbose, -v                     Show detailed output for all phases
--dot [pretableau|initial|final]  Output DOT (Graphviz) graph
--html                            Output standalone HTML visualization
--no-restricted-cuts              Disable C1/C2 cut restrictions
--interactive, -i                 Interactive REPL mode
```

### Examples

```bash
# Check satisfiability (SAT — agent a knows p, agent b doesn't)
bun run src/index.ts "(Ka p & ~Kb p)"

# Unsatisfiable — violates veridicality (knowledge implies truth)
bun run src/index.ts "(Ka p & ~p)"

# Paper Example 3 (unsatisfiable)
bun run src/index.ts "(~D{a,c} C{a,b} p & C{a,b} (p & q))"

# Verbose output showing all states in each phase
bun run src/index.ts "C{a,b} p" --verbose

# Generate DOT graph of the final tableau
bun run src/index.ts "(Ka p & ~Kb p)" --dot final > graph.dot
dot -Tsvg graph.dot -o graph.svg

# Interactive mode
bun run src/index.ts --interactive
```

### Compiled binary

```bash
bun run build:cli     # produces ./cmael binary
./cmael "(Ka p & ~Kb p)"
```

## How the algorithm works

The solver implements a three-phase tableau decision procedure:

**Phase 1 — Construction (Pretableau).** Starting from the input formula, the algorithm builds a graph of *prestates* and *states*. Prestates are expanded into fully-expanded, downward-saturated states by decomposing formulas (splitting conjunctions, branching on disjunctions, handling modal operators). For each diamond formula in a state, a successor prestate is created. This continues until no new nodes are needed.

**Phase 2 — Prestate Elimination.** Prestates are removed and edges rewired: if state *s* pointed to prestate *p*, and *p* expanded to state *t*, then *s* now points directly to *t*. This produces the *initial tableau*.

**Phase 3 — State Elimination.** Defective states are iteratively removed in a dovetailed loop:
- **E1:** States with diamond formulas but no matching successors are eliminated.
- **E2:** Eventualities (from negated common knowledge, e.g. `~C{a,b} p`) must be *realized* via a finite witness path. States with unrealizable eventualities are eliminated.

The input formula is **satisfiable** iff the final tableau still contains a state with the input formula.

## Project structure

```
src/
  index.ts              CLI entry point
  core/
    types.ts            Formula AST, FormulaSet, tableau graph types
    parser.ts           Recursive-descent parser
    printer.ts          Pretty-printer (ASCII, Unicode, LaTeX)
    classify.ts         Alpha/beta classification (Table 1 from paper)
    formula.ts          Closure, extended closure, subformulas, agents
    expansion.ts        FullExpansion (Def 9), Cut-Saturated Expansion (Def 14)
    tableau.ts          Three-phase procedure: construction, prestate elim, state elim
  viz/
    text.ts             Text summary + DOT (Graphviz) output
    html.ts             Standalone HTML page generator
  browser/
    index.ts            Browser entry point (exposes solver globally)
  build-html.ts         Bundles browser entry into dist/index.html
tests/
  formula.test.ts       Unit tests (parser, classifier, closure, expansion)
  examples.test.ts      Integration tests (paper examples, epistemic properties)
serve.ts                Dev server (serves dist/index.html on port 3000)
dist/
  index.html            Built standalone web interface
```

## License

MIT
