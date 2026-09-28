# ATL* Tableau Solver

A tableau-based satisfiability checker for **ATL\*** — the full Alternating-time Temporal Logic.

Given a formula, the solver determines whether it is *satisfiable*: whether there exists a concurrent game structure and a state where the formula is true. It provides full tableau construction details, statistics, and graph visualization.

ATL\* extends basic ATL by allowing **arbitrary path formulas** inside coalition operators. For example, `<<a>>(G p & F q)` expresses that coalition `{a}` has a *single strategy* ensuring `p` always holds *and* `q` eventually holds — on the same execution path. This is strictly more expressive than ATL, where each temporal operator must be directly under a coalition quantifier.

Available as both a **command-line tool** and a **web interface**.

## References

This is a from-scratch TypeScript reimplementation of [**TATL**](https://github.com/theoremprover-museum/TATL), originally written in OCaml by Amélie David.

The algorithm is based on:

> Goranko, V., Shkatov, D. (2009). **Tableau-based decision procedures for logics of strategic ability in multi-agent systems.** *ACM Trans. Comput. Log.* 11(1). [doi:10.1145/1614431.1614434](https://dl.acm.org/doi/abs/10.1145/1614431.1614434)

The ATL\* extension and the original OCaml implementation are described in:

> David, A. (2015). **Deciding ATL\* satisfiability by tableaux.** PhD thesis, Université d'Évry-Val d'Essonne. [HAL tel-01176908](https://theses.hal.science/tel-01176908)

This implementation faithfully follows the TATL algorithm's three-phase tableau with gamma-decomposition for complex path formulas and whatfalse-residual E3 elimination. Results have been extensively cross-validated against the [original TATL OCaml implementation](https://github.com/theoremprover-museum/TATL) — 5,000 systematically enumerated formulas plus 2,000+ randomly generated formulas (fuzz testing), all matching.

## Formula syntax

The input syntax uses ASCII characters only — no special symbols needed:

| Operator | Syntax | Meaning |
|---|---|---|
| Atom | `p`, `q`, `myvar` | Propositional variable (lowercase) |
| Negation | `~p` | not p |
| Conjunction | `(p & q)` | p and q |
| Disjunction | `(p \| q)` | p or q |
| Implication | `(p -> q)` | p implies q |
| Coalition Next | `<<a,b>>X p` | Coalition {a,b} can enforce p at the next step |
| Coalition Always | `<<a>>G p` | Coalition {a} can enforce p forever |
| Coalition Until | `<<a>>(p U q)` | Coalition {a} can enforce p until q |
| Coalition Eventually | `<<a>>F p` | Coalition {a} can enforce p eventually |
| Empty coalition | `<<>>X p` | The empty coalition can enforce p next |
| Complex path (ATL\*) | `<<a>>(G p & F q)` | Same strategy ensures always p *and* eventually q |
| Nested temporal (ATL\*) | `<<a>>(G F p)` | Coalition {a} can enforce infinitely often p |

Binary connectives must be wrapped in parentheses: `(p & q)`, not `p & q`.

Agent names are lowercase alphanumeric: `a`, `b`, `agent1`, `0`, `1`, etc.

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

319 tests across 7 test files, cross-validated against the TATL OCaml implementation.

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
--plain                           Run the plain procedure with no optimisation
--dot [model|pretableau|initial|final]  Output DOT (Graphviz) graph
--html                            Output standalone HTML visualization
--interactive, -i                 Interactive REPL mode
```

### Examples

```bash
# Check satisfiability (SAT — agent a can enforce p always)
bun run src/index.ts "<<a>>G p"

# ATL*: single strategy ensures always p AND eventually q (SAT)
bun run src/index.ts "<<a>>(G p & F q)"

# ATL*: single strategy ensures always p AND eventually not-p (UNSAT — contradictory)
bun run src/index.ts "<<a>>(G p & F ~p)"

# Different strategies can coexist (SAT — two separate strategies)
bun run src/index.ts "(<<a>>G p & <<a>>F ~p)"

# ATL*: infinitely often p (SAT)
bun run src/index.ts "<<a>>(G F p)"

# UNSAT — conflicting agents
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

The solver implements a three-phase tableau decision procedure for ATL\* satisfiability (tight satisfiability — the set of agents is exactly those appearing in the formula).

**Phase 1 — Construction (Pretableau).** Starting from the input formula, the algorithm builds a graph of *prestates* and *states*. Prestates are expanded into fully-expanded states by applying saturation (Rule SR): alpha/beta decomposition for boolean connectives, and *gamma-decomposition* for coalition formulas — which recursively decomposes complex path formulas into *formula tuples* carrying state formulas, path formula sets, and next-time formulas. For the **Next rule**, each state's next-time formulas are used to create successor prestates via *move vectors* — tuples of agent actions where each combination determines which successor formulas are included based on coalition membership.

**Phase 2 — Prestate Elimination.** Prestates are removed and edges rewired: if state *s* pointed to prestate *p*, and *p* expanded to state *t*, then *s* now points directly to *t*. This produces the *initial tableau*.

**Phase 3 — State Elimination.** Defective states are iteratively removed:
- **E2 (Missing successors):** Every move vector must have at least one surviving successor state. If any move vector has no remaining successor, the state is eliminated.
- **E3 (Unrealized eventualities):** Eventualities (arising from Until operators within path formulas) must be *realized*. The algorithm computes *residual path formulas* (whatfalse) to check whether a finite path of accessible states can witness each eventuality. States with unrealizable eventualities are eliminated.

The input formula is **satisfiable** iff the final tableau still contains a state with the input formula.

### Optimisations

The procedure above is the plain one from the papers. On top of it the solver
applies a set of optimisations that shrink the tableau without changing any
verdict. Each is an ATL* equivalence or a change of the tableau's *shape*, and
each sits behind a flag in `src/core/options.ts` so it can be switched off:

| Flag | What it does |
|---|---|
| `simplify` | Propositional and temporal simplification of the input: constants, idempotence, complementary pairs (`GF p → GF p` becomes ⊤), absorption (`G p & F p` becomes `G p`), exact canonicalisation of small propositional subformulas (`(p & q) \| (p & ~q)` becomes `p`), temporal distribution (`GF p \| GF q` becomes `GF (p \| q)`, so `GF p \| GF ~p` becomes ⊤; likewise `FG`, `X`, `G` and Untils sharing a side), `⟨⟨A⟩⟩φ → φ` for state formulas, co-coalition normalisation |
| `liftDisjunctions` | `⟨⟨Σ⟩⟩(π₁ ∨ π₂) → ⟨⟨Σ⟩⟩π₁ ∨ ⟨⟨Σ⟩⟩π₂` for the grand coalition Σ (E distributes over ∨), in LTL, CTL* and ATL* alike |
| `acKeys` | ∧ and ∨ are associative and commutative when comparing formulas, so re-associated conjunctions name the same prestate |
| `semanticBranching` | Branching on `φ ∨ ψ` with φ propositional adds `¬φ` to the ψ branch, so the branches describe disjoint worlds |
| `semanticBranchingTemporal` | The same for a non-propositional φ whose negation introduces no eventuality, such as `F ℓ` (negation `G ¬ℓ`); slightly larger pretableau, smaller final tableau |
| `clauseSubsumption` | A next-obligation clause that is a superset of another clause is dropped |
| `alwaysClosure` | Labels are closed under `□(… ∧ ◇π ∧ …) ⇒ ◇π`, so the "just fulfilled" and "pending" states of a □ formula share a label |
| `earlyInconsistency` | A state whose universal next-time obligations are already contradictory is dropped at creation instead of after its successors are built |
| `labelAbsorption` | In a next obligation, a conjunct entailed by another conjunct through a □-free entailment is dropped |

Rewrites that absorb one conjunct into another are applied to the *input*
only, never to labels the construction produces: a label such as
`⟨⟨a⟩⟩(□◇p ∧ ◇p)` carries `◇p` as an obligation marker that the E3 check
relies on.

The hedging term of the OrP decomposition (⊕) is skipped when the coalition
is the grand coalition, which has nobody to hedge against.

### Models and proofs

The final tableau is not a model: it is the union of every consistent
bookkeeping state. For a satisfiable formula the solver reads a small
**model** off the final tableau, following the realization witnesses of the
E3 check so that every eventuality is fulfilled, and minimises it by
bisimulation. States are labelled by the literals true there and edges by
move vectors. `G F p` gives a single state with `p` and a self-loop.

For an unsatisfiable formula the solver prints a **proof**: why each initial
state was eliminated, following E2 and E3 dependencies down to the states or
cycles that fail.

### Differential testing

```bash
bun run difftest.ts --count 2000 --seed 7 --max-depth 5
```

generates random LTL, CTL, CTL* and ATL* formulas and checks that every
optimisation, alone and all together, gives the same verdict as the plain
procedure, and that verdicts are invariant under renaming atoms and agents.
A small corpus runs as part of `bun test`. Each verdict runs under a node and
time budget, so the plain procedure's blow-ups are skipped rather than
waited for; to also cap memory on Linux, wrap the run in a cgroup:

```bash
systemd-run --user --scope -p MemoryMax=2G bun run difftest.ts --count 2000
```

## Key ATL\* properties

- `<<a>>(G p & F q)` is **satisfiable** — a single strategy can enforce always-p and eventually-q.
- `<<a>>(G p & F ~p)` is **unsatisfiable** — no single strategy can ensure both always-p and eventually-not-p.
- `(<<a>>G p & <<a>>F ~p)` is **satisfiable** — these describe *different strategies* that can coexist.
- `(<<a>>X p & <<b>>X ~p)` is **unsatisfiable** (with agents {a,b}) — the move vector where both agents vote for their formula leads to a contradiction.
- `(<<a>>X p & <<a>>X ~p)` is **satisfiable** (single agent) — agent a can play different moves leading to different successors.
- `<<a>>(G F p)` is **satisfiable** — a strategy ensuring p holds infinitely often.
- Empty coalitions `<<>>` have no power to choose actions — outcomes depend entirely on the adversary.

## Cross-validation

The solver has been extensively validated against the original TATL OCaml implementation:

```bash
# Systematic: 5000 enumerated formulas (atoms, temporals, conjunctions, ATL*-specific)
bun run crossval.ts

# Fuzz testing: random formulas with configurable depth and agent count
bun run fuzz.ts --count=1000 --seed=42
bun run fuzz.ts --count=2000 --agents=3
```

## Project structure

```
src/
  index.ts              CLI entry point
  core/
    types.ts            Two-sorted AST (StateFormula + PathFormula), FormulaTuple, graph types
    parser.ts           Recursive-descent parser with NNF at parse time
    printer.ts          Pretty-printer (ASCII, Unicode, LaTeX)
    nnf.ts              Negation Normal Form transformation + simplification
    classify.ts         State-level alpha/beta/gamma classification
    decomposition.ts    Gamma-decomposition (gammaSets, otimes, oplus, gammaComp)
    formula.ts          Agents, inconsistency, eventualities, next-time detection
    expansion.ts        Saturation (Rule SR), TupleSet, SetOfTupleSets
    tableau.ts          Three-phase procedure: construction, prestate elim, state elim (E2+E3)
    options.ts          Optimisation flags (plain procedure vs optimised)
    simplify.ts         Input preprocessing: simplification, lifting, □-closure
    model.ts            Model extraction from an open final tableau
    difftest.ts         Random formulas and the differential checks
  viz/
    text.ts             Text summary, model, proof + DOT (Graphviz) output
    proof.ts            HTML rendering of the proof and the model
    html.ts             Standalone HTML page generator
  browser/
    index.ts            Browser entry point (Web Worker)
  build-html.ts         Bundles browser entry into dist/index.html
tests/
  foundation.test.ts    Unit tests (parser, types, NNF, classification, decomposition, expansion)
  formula.test.ts       Unit tests (parser, classifier, formula utilities)
  examples.test.ts      Integration tests (78 formulas cross-validated against TATL)
  optimisations.test.ts Optimisations, models, proofs and a differential corpus
crossval.ts             Systematic cross-validation against TATL (5000 formulas)
difftest.ts             Differential testing of the optimisations against the plain procedure
fuzz.ts                 Fuzz testing with random formula generation
serve.ts                Dev server (serves dist/index.html on port 3000)
dist/
  index.html            Built standalone web interface
```

## License

MIT
