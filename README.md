# ATL Tableau Solver

A tableau-based satisfiability checker for **ATL** — Alternating-time Temporal Logic.

Given a formula, the solver determines whether it is *satisfiable*: whether there exists a concurrent game structure and a state where the formula is true. It provides full tableau construction details, statistics, and graph visualization.

Available as both a **command-line tool** and a **web interface**.

## Based on

> **Tableau-based decision procedure for full coalitional multiagent temporal logic**
> Valentin Goranko and Dmitry Shkatov (2009)

The implementation faithfully follows the paper's three-phase tableau algorithm with move vectors for the Next rule. Results have been cross-validated against the TATL OCaml reference implementation (59 formulas, all matching).

## Formula syntax

The input syntax uses ASCII characters only — no special symbols needed:

| Operator | Syntax | Meaning |
|---|---|---|
| Atom | `p`, `q`, `myvar` | Propositional variable (lowercase) |
| Negation | `~p` | not p |
| Conjunction | `(p & q)` | p and q |
| Disjunction | `(p \| q)` | p or q (desugars to `~(~p & ~q)`) |
| Implication | `(p -> q)` | p implies q (desugars to `~(p & ~q)`) |
| Coalition Next | `<<a,b>>X p` | Coalition {a,b} can enforce p at the next step |
| Coalition Always | `<<a>>G p` | Coalition {a} can enforce p forever |
| Coalition Until | `<<a>>(p U q)` | Coalition {a} can enforce p until q |
| Coalition Eventually | `<<a>>F p` | Coalition {a} can enforce p eventually (sugar for `<<a>>(_top U p)`) |
| Empty coalition | `<<>>X p` | The empty coalition can enforce p next |

Binary connectives must be wrapped in parentheses: `(p & q)`, not `p & q`.

Agent names are lowercase alphanumeric: `a`, `b`, `agent1`, etc.

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

107 tests across 2 test files, cross-validated against the TATL OCaml implementation.

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
- Tableau statistics across all three phases
- List view showing all states and edges with KaTeX-rendered formulas
- Graph view rendering the tableau as an interactive SVG via Graphviz (viz.js)
- Fullscreen graph mode with pan and zoom (click graph to expand, Esc to close)
- Example formulas with explanations

## CLI

### One-shot mode

```bash
bun run src/index.ts "<<a>>G p"
```

Exit code: `0` if satisfiable, `1` if unsatisfiable.

### Options

```
--verbose, -v                     Show detailed output for all phases
--dot [pretableau|initial|final]  Output DOT (Graphviz) graph
--html                            Output standalone HTML visualization
--interactive, -i                 Interactive REPL mode
```

### Examples

```bash
# Check satisfiability (SAT — agent a can enforce p always)
bun run src/index.ts "<<a>>G p"

# Unsatisfiable — <<a>>G p requires p now, but ~p contradicts that
bun run src/index.ts "(<<a>>G p & ~p)"

# SAT — different strategies can coexist in ATL
bun run src/index.ts "(<<a>>G p & <<a>>F ~p)"

# UNSAT — conflicting agents (a enforces p, b enforces ~p, but outcomes conflict)
bun run src/index.ts "(<<a>>X p & <<b>>X ~p)"

# Verbose output showing all states in each phase
bun run src/index.ts "<<a>>(p U q)" --verbose

# Generate DOT graph of the final tableau
bun run src/index.ts "<<a>>G p" --dot final > graph.dot
dot -Tsvg graph.dot -o graph.svg

# Interactive mode
bun run src/index.ts --interactive
```

### Compiled binary

```bash
bun run build:cli     # produces ./atl binary
./atl "<<a>>G p"
```

## How the algorithm works

The solver implements a three-phase tableau decision procedure for ATL satisfiability (tight satisfiability — the set of agents is exactly those appearing in the formula).

**Phase 1 — Construction (Pretableau).** Starting from the input formula, the algorithm builds a graph of *prestates* and *states*. Prestates are expanded into fully-expanded states by decomposing formulas using alpha/beta rules. For each state, the **Next rule** generates successor prestates using *move vectors* — tuples of agent actions from `{0,...,k-1}` where `k = m + l` (m positive next-time formulas, l negative). Each move vector determines which successor formulas are included based on coalition membership and voting patterns.

**Phase 2 — Prestate Elimination.** Prestates are removed and edges rewired: if state *s* pointed to prestate *p*, and *p* expanded to state *t*, then *s* now points directly to *t*. This produces the *initial tableau*.

**Phase 3 — State Elimination.** Defective states are iteratively removed:
- **E2 (Missing successors):** Every move vector in `{0,...,k-1}^|agents|` must have at least one surviving successor state. If any move vector has no remaining successor, the state is eliminated.
- **E3 (Unrealized eventualities):** Eventualities (`<<A>>(p U q)` needs `q` eventually; `~<<A>>G p` needs `~p` eventually) must be *realized* via a reachable state containing the goal. States with unrealizable eventualities are eliminated.

The input formula is **satisfiable** iff the final tableau still contains a state with the input formula.

## Key ATL properties

- `<<A>>G p & <<A>>F ~p` is **satisfiable** — these describe *different strategies* that can coexist.
- `<<a>>X p & <<b>>X ~p` is **unsatisfiable** (with agents {a,b}) — the move vector where both agents vote for their formula leads to a contradiction (p & ~p).
- `<<a>>X p & <<a>>X ~p` is **satisfiable** (single agent) — agent a can play different moves leading to different successors.
- `<<a,b>>X p & ~<<a>>X p` is **satisfiable** — the grand coalition is strictly more powerful than individual agents.
- Empty coalitions `<<>>` have no power to choose actions — outcomes depend entirely on the adversary.

## Project structure

```
src/
  index.ts              CLI entry point
  core/
    types.ts            Formula AST (ATL), FormulaSet, MoveVector, tableau graph types
    parser.ts           Recursive-descent parser for <<A>>X/G/F/(U) syntax
    printer.ts          Pretty-printer (ASCII, Unicode, LaTeX) + move vector labels
    classify.ts         Alpha/beta classification for ATL formulas
    formula.ts          Closure, subformulas, agents, eventualities, next-time detection
    expansion.ts        Full expansion (alpha/beta rules, no analytic cuts)
    tableau.ts          Three-phase procedure: construction, prestate elim, state elim
  viz/
    text.ts             Text summary + DOT (Graphviz) output
    html.ts             Standalone HTML page generator
  browser/
    index.ts            Browser entry point (exposes solver globally)
  build-html.ts         Bundles browser entry into dist/index.html
tests/
  formula.test.ts       Unit tests (parser, classifier, closure, expansion)
  examples.test.ts      Integration tests (59 formulas cross-validated against TATL)
serve.ts                Dev server (serves dist/index.html on port 3000)
dist/
  index.html            Built standalone web interface
```

## License

MIT
