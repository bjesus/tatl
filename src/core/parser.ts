/**
 * Recursive-descent parser for ATL* formulas.
 *
 * Two-sorted grammar:
 *
 * State formulas (top level):
 *   atom       := [a-z0-9][a-z0-9_]*
 *   coalition  := '<<' (agent (',' agent)*)? '>>'
 *   cocoal     := '[[' (agent (',' agent)*)? ']]'
 *   agent      := [a-z0-9][a-z0-9_]*
 *
 *   primary    := atom
 *              | '~' primary              // negation
 *              | coalition pathExpr       // ⟨⟨A⟩⟩π
 *              | cocoal pathExpr          // [[A]]π
 *              | '(' expr ')'
 *
 *   expr       := primary (('&' | '|' | '->') primary)*
 *
 * Path formulas (after <<A>> or [[A]]):
 *   pathPrimary := 'X' pathPrimary       // next
 *               | 'G' pathPrimary        // always
 *               | 'F' pathPrimary        // eventually (sugar for ⊤ U π)
 *               | '~' pathPrimary        // path negation
 *               | '(' pathExpr ')'       // grouping or until
 *               | '(' pathExpr 'U' pathExpr ')'  // until
 *               | atom                   // auto-lifted to State(Prop(x))
 *               | coalition pathExpr     // nested coalition (auto-lifted)
 *               | cocoal pathExpr        // nested co-coalition (auto-lifted)
 *
 *   pathExpr   := pathPrimary (('&' | '|' | '->' | 'U' | 'R') pathPrimary)*
 *
 * NNF is applied after parsing.
 *
 * Backward compatible: <<a>>G p, <<a>>(p U q), etc. all still work.
 * New ATL* forms: <<a>>(Gp & Fq), <<a>>GFp, etc.
 *
 * The parser also reads the two single-agent fragments, translating them into
 * ATL* (see `System`):
 *
 *   LTL: the whole input is a path formula
 *     ltlFormula := pathExpr                      => <<a>>pathExpr
 *
 *   CTL: every temporal operator is paired with a path quantifier
 *     ctlPrimary := 'A' ctlPath | 'E' ctlPath | atom | '~' ctlPrimary | '(' expr ')'
 *     ctlPath    := 'X' ctlPrimary | 'G' ctlPrimary | 'F' ctlPrimary
 *                 | '[' expr 'U' expr ']' | '(' expr 'U' expr ')'
 *     with 'A' => <<>> and 'E' => <<a>>
 */

import {
  type StateFormula,
  type PathFormula,
  type Agent,
  type Coalition,
  Atom, Neg, SAnd, SOr, SImplies, Coal, CoCoal,
  PState, PNeg, PAnd, POr, PNext, PAlways, PUntil, PEvent,
  STop,
} from "./types.ts";
import { toNNF } from "./nnf.ts";

class ParseError extends Error {
  constructor(message: string, public pos: number) {
    super(message);
    this.name = "ParseError";
  }
}

/**
 * The logical system an input formula is written in.
 *
 * LTL and CTL are both fragments of ATL* interpreted over a model with exactly
 * one agent. With a single agent, that agent alone determines the play, so its
 * strategies correspond to paths:
 *
 *   <<a>>π   there is a path satisfying π    (existential path quantifier, E)
 *   <<>>π    every path satisfies π          (universal path quantifier, A)
 *
 * which gives the translations
 *
 *   LTL   π           =>  <<a>>π      (π is read on a single path)
 *   CTL   A π / E π   =>  <<>>π / <<a>>π   (π one paired temporal operator)
 *   CTL*  A π / E π   =>  <<>>π / <<a>>π   (π an arbitrary path formula)
 *
 * CTL* is exactly the one-agent fragment of ATL*: with a single agent the only
 * coalitions are {} and {a}, which are the two path quantifiers, and path
 * formulas are already unrestricted. The co-coalition [[A]]π adds nothing here
 * either, since [[A]]π = ~<<A>>~π makes [[a]] and [[]] the duals of E and A.
 *
 * All of these embeddings are only faithful when the agent set is exactly {a};
 * see `systemAgents`.
 */
export type System = "atl" | "ctlstar" | "ctl" | "ltl";

/** The single agent that LTL and CTL formulas are interpreted over. */
export const SYSTEM_AGENT: Agent = "a";

/**
 * Agents that must be present in the model for a system, whatever the formula
 * mentions. A CTL formula built only from A translates to <<>> and so names no
 * agent at all, but the embedding needs exactly one agent to exist.
 */
export function systemAgents(system: System): readonly Agent[] {
  return system === "atl" ? [] : [SYSTEM_AGENT];
}

/** Systems whose path quantifiers are written A and E. */
function usesPathQuantifiers(system: System): boolean {
  return system === "ctl" || system === "ctlstar";
}

class Parser {
  private pos: number = 0;
  private input: string;
  private system: System;

  constructor(input: string, system: System = "atl") {
    this.input = input;
    this.system = system;
  }

  // ============================================================
  // State formula parsing (top level)
  // ============================================================

  parse(): StateFormula {
    this.skipWhitespace();
    // An LTL formula is a path formula; it is satisfiable iff some path of a
    // one-agent model satisfies it, which is exactly <<a>>π.
    const result = this.system === "ltl"
      ? Coal([SYSTEM_AGENT], this.parsePathExpr())
      : this.parseStateExpr();
    this.skipWhitespace();
    if (this.pos < this.input.length) {
      throw this.trailingError();
    }
    return result;
  }

  /** Error for input left over once a complete formula has been parsed. */
  private trailingError(): ParseError {
    const ch = this.input[this.pos]!;
    if (usesPathQuantifiers(this.system) && (ch === "U" || ch === "W")) {
      return new ParseError(this.unpairedMessage(ch), this.pos);
    }
    return new ParseError(
      `Unexpected character '${ch}' at position ${this.pos}`,
      this.pos
    );
  }

  private systemLabel(): string {
    return this.system === "ctlstar" ? "CTL*" : this.system.toUpperCase();
  }

  /** Message for a temporal operator that is not under a path quantifier. */
  private unpairedMessage(op: string): string {
    return this.system === "ctl"
      ? `In CTL, '${op}' must be paired with a path quantifier: write A[p ${op} q] or E[p ${op} q]`
      : `In CTL*, '${op}' must appear inside a path quantifier: write A(p ${op} q) or E(p ${op} q)`;
  }

  private parseStateExpr(): StateFormula {
    let left = this.parseStatePrimary();

    while (true) {
      this.skipWhitespace();
      if (this.pos >= this.input.length) break;

      if (this.lookAhead("->")) {
        this.advance(2);
        this.skipWhitespace();
        const right = this.parseStatePrimary();
        left = SImplies(left, right);
      } else if (this.peek() === "|") {
        this.advance(1);
        this.skipWhitespace();
        const right = this.parseStatePrimary();
        left = SOr(left, right);
      } else if (this.peek() === "&") {
        this.advance(1);
        this.skipWhitespace();
        const right = this.parseStatePrimary();
        left = SAnd(left, right);
      } else {
        break;
      }
    }

    return left;
  }

  private parseStatePrimary(): StateFormula {
    this.skipWhitespace();

    if (this.pos >= this.input.length) {
      throw new ParseError("Unexpected end of input", this.pos);
    }

    const ch = this.peek()!;

    // Negation
    if (ch === "~" || ch === "!") {
      this.advance(1);
      this.skipWhitespace();
      const sub = this.parseStatePrimary();
      return Neg(sub);
    }

    // CTL and CTL*: path quantifiers replace the coalition operators
    if (usesPathQuantifiers(this.system)) {
      if (ch === "A" || ch === "E") {
        return this.system === "ctl"
          ? this.parseCtlQuantifier()
          : this.parseCtlStarQuantifier();
      }
      if (ch === "X" || ch === "G" || ch === "F") {
        throw new ParseError(
          this.system === "ctl"
            ? `In CTL, '${ch}' must be preceded by a path quantifier: write A${ch} or E${ch}`
            : `In CTL*, '${ch}' must appear inside a path quantifier: write A(${ch} ...) or E(${ch} ...)`,
          this.pos
        );
      }
      if (this.lookAhead("<<") || ch === "[") {
        throw new ParseError(
          `Coalition operators belong to ATL*; in ${this.systemLabel()} use the path quantifiers A and E`,
          this.pos
        );
      }
    }

    // Coalition operator: <<...>>π
    if (this.lookAhead("<<")) {
      return this.parseCoalitionOp();
    }

    // Co-coalition operator: [[...]]π
    if (this.lookAhead("[[")) {
      return this.parseCoCoalitionOp();
    }

    // Parenthesized expression
    if (ch === "(") {
      this.advance(1);
      this.skipWhitespace();
      const inner = this.parseStateExpr();
      this.skipWhitespace();
      this.expect(")");
      return inner;
    }

    // Atom
    if (this.isAgentChar(ch)) {
      return Atom(this.parseAgent());
    }

    throw new ParseError(
      `Unexpected character '${ch}' at position ${this.pos}`,
      this.pos
    );
  }

  /**
   * Parse <<A>>π — coalition with a path formula.
   *
   * The path formula after <<A>> is a "path primary" — it handles prefix
   * operators (X, G, F, ~) and parenthesized expressions, but NOT infix
   * operators (&, |, U). To use infix operators, wrap in parens:
   *   <<a>>(G p & F q)    -- OK: parens contain the full expression
   *   <<a>>G p & <<b>>F q -- OK: parses as (<<a>>G p) & (<<b>>F q)
   *   <<a>>G p & F q      -- error: the trailing F q would be state-level, and
   *                          temporal operators may not appear there
   */
  private parseCoalitionOp(): StateFormula {
    this.expect("<");
    this.expect("<");
    const coalition = this.parseCoalitionBody();
    this.expect(">");
    this.expect(">");
    this.skipWhitespace();

    const path = this.parsePathPrimary();
    return Coal(coalition, path);
  }

  /**
   * Parse [[A]]π — co-coalition with a path formula.
   * Same scoping rules as <<A>>π.
   */
  private parseCoCoalitionOp(): StateFormula {
    this.expect("[");
    this.expect("[");
    const coalition = this.parseCoalitionBody();
    this.expect("]");
    this.expect("]");
    this.skipWhitespace();

    const path = this.parsePathPrimary();
    return CoCoal(coalition, path);
  }

  /**
   * Parse a CTL formula Qπ, where Q is A or E.
   *
   * CTL pairs each path quantifier with exactly one temporal operator, and the
   * operands of that operator are themselves state formulas:
   *
   *   AX φ  EX φ  AG φ  EG φ  AF φ  EF φ  A[φ U ψ]  E[φ U ψ]
   *
   * Parentheses are accepted in place of brackets for the until form. Anything
   * looser (an unpaired U, or several temporal operators under one quantifier)
   * is CTL* rather than CTL and is rejected.
   */
  private parseCtlQuantifier(): StateFormula {
    const quantifier = this.peek()!; // 'A' or 'E'
    this.advance(1);
    this.skipWhitespace();

    // A quantifies over all paths (<<>>), E over some path (<<a>>)
    const coalition: Coalition = quantifier === "A" ? [] : [SYSTEM_AGENT];
    const ch = this.peek();

    if (ch === "X" || ch === "G" || ch === "F") {
      this.advance(1);
      const arg = PState(this.parseStatePrimary());
      const path =
        ch === "X" ? PNext(arg) : ch === "G" ? PAlways(arg) : PEvent(arg);
      return Coal(coalition, path);
    }

    // A[φ U ψ] / A(φ U ψ)
    if (ch === "[" || ch === "(") {
      const close = ch === "[" ? "]" : ")";
      this.advance(1);
      const left = this.parseStateExpr();
      this.skipWhitespace();
      if (this.peek() !== "U") {
        throw new ParseError(
          `Expected 'U' in ${quantifier}[... U ...] at position ${this.pos}`,
          this.pos
        );
      }
      this.advance(1);
      const right = this.parseStateExpr();
      this.skipWhitespace();
      this.expect(close);
      return Coal(coalition, PUntil(PState(left), PState(right)));
    }

    throw new ParseError(
      `In CTL, '${quantifier}' must be followed by X, G, F or [... U ...]`,
      this.pos
    );
  }

  /**
   * Parse a CTL* formula Qπ, where Q is A or E.
   *
   * Unlike CTL, π is an arbitrary path formula: temporal operators may be
   * nested and combined under a single quantifier, as in A(G F p) or
   * E(G p & F q). This is the same shape as ATL*'s <<A>>π, which is why CTL*
   * is precisely the one-agent fragment of ATL*.
   */
  private parseCtlStarQuantifier(): StateFormula {
    const quantifier = this.peek()!; // 'A' or 'E'
    this.advance(1);
    this.skipWhitespace();
    const coalition: Coalition = quantifier === "A" ? [] : [SYSTEM_AGENT];
    return Coal(coalition, this.parsePathPrimary());
  }

  // ============================================================
  // Path formula parsing (after <<A>> or [[A]])
  // ============================================================

  private parsePathExpr(): PathFormula {
    let left = this.parsePathPrimary();

    while (true) {
      this.skipWhitespace();
      if (this.pos >= this.input.length) break;

      if (this.lookAhead("->")) {
        this.advance(2);
        this.skipWhitespace();
        const right = this.parsePathPrimary();
        // π₁ → π₂ = ¬π₁ ∨ π₂
        left = POr(PNeg(left), right);
      } else if (this.peek() === "|") {
        this.advance(1);
        this.skipWhitespace();
        const right = this.parsePathPrimary();
        left = POr(left, right);
      } else if (this.peek() === "&") {
        this.advance(1);
        this.skipWhitespace();
        const right = this.parsePathPrimary();
        left = PAnd(left, right);
      } else if (this.peek() === "U") {
        // Infix U: π₁ U π₂
        this.advance(1);
        this.skipWhitespace();
        const right = this.parsePathPrimary();
        left = PUntil(left, right);
      } else if (this.peek() === "R") {
        // Infix R (release): π₁ R π₂ — will be eliminated by NNF
        // π₁ R π₂ ≡ ¬(¬π₁ U ¬π₂)
        this.advance(1);
        this.skipWhitespace();
        const right = this.parsePathPrimary();
        left = PNeg(PUntil(PNeg(left), PNeg(right)));
      } else {
        break;
      }
    }

    return left;
  }

  private parsePathPrimary(): PathFormula {
    this.skipWhitespace();

    if (this.pos >= this.input.length) {
      throw new ParseError("Unexpected end of input in path formula", this.pos);
    }

    const ch = this.peek()!;

    // Path negation
    if (ch === "~" || ch === "!") {
      this.advance(1);
      this.skipWhitespace();
      const sub = this.parsePathPrimary();
      return PNeg(sub);
    }

    // LTL has no path quantifiers: a formula is read on one path
    if (this.system === "ltl") {
      if (ch === "A" || ch === "E") {
        throw new ParseError(
          `'${ch}' is a CTL path quantifier; an LTL formula describes a single path. Switch the system to CTL to use A and E.`,
          this.pos
        );
      }
      if (this.lookAhead("<<") || ch === "[") {
        throw new ParseError(
          "Coalition operators belong to ATL*; an LTL formula has no path quantifiers",
          this.pos
        );
      }
    }

    // CTL*: a quantifier may be nested inside a path formula, and since there
    // are no co-coalitions here, [...] is free to group like (...)
    if (this.system === "ctlstar") {
      if (this.lookAhead("<<") || this.lookAhead("[[")) {
        throw new ParseError(
          "Coalition operators belong to ATL*; in CTL* use the path quantifiers A and E",
          this.pos
        );
      }
      if (ch === "A" || ch === "E") {
        return PState(this.parseCtlStarQuantifier());
      }
      if (ch === "[") {
        this.advance(1);
        this.skipWhitespace();
        const inner = this.parsePathExpr();
        this.skipWhitespace();
        this.expect("]");
        return inner;
      }
    }

    // Temporal operators are uppercase and atoms are lowercase, so an operator
    // letter can never begin a name: no lookahead is needed to tell them apart.

    // Next: X π
    if (ch === "X") {
      this.advance(1);
      this.skipWhitespace();
      const sub = this.parsePathPrimary();
      return PNext(sub);
    }

    // Always: G π
    if (ch === "G") {
      this.advance(1);
      this.skipWhitespace();
      const sub = this.parsePathPrimary();
      return PAlways(sub);
    }

    // Eventually: F π (sugar for ⊤ U π)
    if (ch === "F") {
      this.advance(1);
      this.skipWhitespace();
      const sub = this.parsePathPrimary();
      return PEvent(sub);
    }

    // Parenthesized path expression (may contain U)
    if (ch === "(") {
      this.advance(1);
      this.skipWhitespace();
      const inner = this.parsePathExpr();
      this.skipWhitespace();
      this.expect(")");
      return inner;
    }

    // Nested coalition in path context → auto-lifted: <<A>>π becomes State(Coal(A, π))
    if (this.lookAhead("<<")) {
      const coal = this.parseCoalitionOp();
      return PState(coal);
    }

    // Nested co-coalition in path context → auto-lifted
    if (this.lookAhead("[[")) {
      const cocoal = this.parseCoCoalitionOp();
      return PState(cocoal);
    }

    // Atom in path context → auto-lifted: p becomes State(Prop(p))
    if (this.isAgentChar(ch)) {
      const name = this.parseAgent();
      return PState(Atom(name));
    }

    throw new ParseError(
      `Unexpected character '${ch}' at position ${this.pos} in path formula`,
      this.pos
    );
  }

  // ============================================================
  // Coalition body parsing
  // ============================================================

  private parseCoalitionBody(): Coalition {
    this.skipWhitespace();
    // Empty coalition: <<>> or [[]]
    if (this.lookAhead(">>") || this.lookAhead("]]")) {
      return [];
    }

    const agents: Agent[] = [];
    agents.push(this.parseAgent());
    this.skipWhitespace();
    while (this.peek() === ",") {
      this.advance(1);
      this.skipWhitespace();
      agents.push(this.parseAgent());
      this.skipWhitespace();
    }
    return agents;
  }

  // ============================================================
  // Utilities
  // ============================================================

  private parseAgent(): string {
    const start = this.pos;
    while (this.pos < this.input.length && this.isAgentChar(this.input[this.pos]!)) {
      this.pos++;
    }
    if (this.pos === start) {
      throw new ParseError(`Expected agent name at position ${this.pos}`, this.pos);
    }
    return this.input.slice(start, this.pos);
  }

  private isAgentChar(ch: string): boolean {
    return /[a-z0-9_]/.test(ch);
  }

  private peek(): string | undefined {
    return this.input[this.pos];
  }

  private lookAhead(s: string): boolean {
    return this.input.slice(this.pos, this.pos + s.length) === s;
  }

  private advance(n: number): void {
    this.pos += n;
  }

  private expect(ch: string): void {
    if (this.pos >= this.input.length || this.input[this.pos] !== ch) {
      const got = this.input[this.pos] ?? "EOF";
      // A stray U/W almost always means a temporal operator that is not under a
      // path quantifier, the single most common mistake when writing CTL.
      if (usesPathQuantifiers(this.system) && (got === "U" || got === "W")) {
        throw new ParseError(this.unpairedMessage(got), this.pos);
      }
      throw new ParseError(
        `Expected '${ch}' at position ${this.pos}, got '${got}'`,
        this.pos
      );
    }
    this.pos++;
  }

  private skipWhitespace(): void {
    while (this.pos < this.input.length && /\s/.test(this.input[this.pos]!)) {
      this.pos++;
    }
  }
}

/**
 * Parse a formula string into a StateFormula AST, then apply NNF transformation.
 *
 * LTL and CTL inputs are translated into their ATL* equivalents over a single
 * agent, so the result is always an ATL* formula regardless of `system`.
 */
export function parseFormula(input: string, system: System = "atl"): StateFormula {
  const parser = new Parser(input.trim(), system);
  const raw = parser.parse();
  return toNNF(raw);
}

/**
 * Parse a formula string WITHOUT applying NNF (useful for testing the parser).
 */
export function parseFormulaRaw(input: string, system: System = "atl"): StateFormula {
  const parser = new Parser(input.trim(), system);
  return parser.parse();
}
