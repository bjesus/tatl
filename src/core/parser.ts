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

class Parser {
  private pos: number = 0;
  private input: string;

  constructor(input: string) {
    this.input = input;
  }

  // ============================================================
  // State formula parsing (top level)
  // ============================================================

  parse(): StateFormula {
    this.skipWhitespace();
    const result = this.parseStateExpr();
    this.skipWhitespace();
    if (this.pos < this.input.length) {
      throw new ParseError(
        `Unexpected character '${this.input[this.pos]}' at position ${this.pos}`,
        this.pos
      );
    }
    return result;
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
   *   <<a>>G p & F q      -- parses as (<<a>>G p) & (F q) -- F q is state-level
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
      } else if (this.peek() === "U" && !this.isAgentChar(this.input[this.pos + 1] ?? "")) {
        // Infix U: π₁ U π₂
        this.advance(1);
        this.skipWhitespace();
        const right = this.parsePathPrimary();
        left = PUntil(left, right);
      } else if (this.peek() === "R" && !this.isAgentChar(this.input[this.pos + 1] ?? "")) {
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

    // Next: X π
    if (ch === "X" && !this.isAgentChar(this.input[this.pos + 1] ?? "")) {
      this.advance(1);
      this.skipWhitespace();
      const sub = this.parsePathPrimary();
      return PNext(sub);
    }

    // Always: G π
    if (ch === "G" && !this.isAgentChar(this.input[this.pos + 1] ?? "")) {
      this.advance(1);
      this.skipWhitespace();
      const sub = this.parsePathPrimary();
      return PAlways(sub);
    }

    // Eventually: F π (sugar for ⊤ U π)
    if (ch === "F" && !this.isAgentChar(this.input[this.pos + 1] ?? "")) {
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
      throw new ParseError(
        `Expected '${ch}' at position ${this.pos}, got '${this.input[this.pos] ?? "EOF"}'`,
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
 */
export function parseFormula(input: string): StateFormula {
  const parser = new Parser(input.trim());
  const raw = parser.parse();
  return toNNF(raw);
}

/**
 * Parse a formula string WITHOUT applying NNF (useful for testing the parser).
 */
export function parseFormulaRaw(input: string): StateFormula {
  const parser = new Parser(input.trim());
  return parser.parse();
}
