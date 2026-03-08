/**
 * Recursive-descent parser for ATL formulas.
 *
 * Syntax (all ASCII, no special symbols needed):
 *
 *   atom       := [a-z][a-z0-9_]*   (except reserved: _top)
 *   coalition  := '<<' (agent (',' agent)*)? '>>'
 *   agent      := [a-z][a-z0-9_]*
 *
 *   primary    := atom
 *              | '~' primary                    // negation
 *              | coalition 'X' primary          // next: <<A>>X ϕ
 *              | coalition 'G' primary          // always: <<A>>G ϕ
 *              | coalition 'F' primary          // eventually: <<A>>F ϕ (sugar for <<A>>(⊤ U ϕ))
 *              | coalition '(' expr 'U' expr ')'  // until: <<A>>(ϕ U ψ)
 *              | '(' expr ')'
 *
 *   expr       := primary (('&' | '|' | '->') primary)*
 *
 * Sugar:
 *   ϕ | ψ        desugars to  ~(~ϕ & ~ψ)
 *   ϕ -> ψ       desugars to  ~(ϕ & ~ψ)
 *   <<A>>F ϕ     desugars to  <<A>>(_top U ϕ)
 *
 * Operator precedence (high to low):
 *   ~ (prefix), <<A>>X/G/F/U (prefix), &, |, ->
 *
 * Examples:
 *   "p"
 *   "~p"
 *   "(p & q)"
 *   "(p | q)"
 *   "(p -> q)"
 *   "<<a>>X p"
 *   "<<a,b>>G p"
 *   "<<>>F p"
 *   "<<a>>(p U q)"
 *   "(<<a>>X p & ~<<b>>G q)"
 */

import {
  type Formula,
  type Agent,
  type Coalition,
  Atom,
  Not,
  And,
  Or,
  Implies,
  Next,
  Always,
  Until,
  Eventually,
} from "./types.ts";

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

  parse(): Formula {
    this.skipWhitespace();
    const result = this.parseExpr();
    this.skipWhitespace();
    if (this.pos < this.input.length) {
      throw new ParseError(
        `Unexpected character '${this.input[this.pos]}' at position ${this.pos}`,
        this.pos
      );
    }
    return result;
  }

  private parseExpr(): Formula {
    let left = this.parsePrimary();

    while (true) {
      this.skipWhitespace();
      if (this.pos >= this.input.length) break;

      if (this.lookAhead("->")) {
        this.advance(2);
        this.skipWhitespace();
        const right = this.parsePrimary();
        left = Implies(left, right);
      } else if (this.peek() === "|") {
        this.advance(1);
        this.skipWhitespace();
        const right = this.parsePrimary();
        left = Or(left, right);
      } else if (this.peek() === "&") {
        this.advance(1);
        this.skipWhitespace();
        const right = this.parsePrimary();
        left = And(left, right);
      } else {
        break;
      }
    }

    return left;
  }

  private parsePrimary(): Formula {
    this.skipWhitespace();

    if (this.pos >= this.input.length) {
      throw new ParseError("Unexpected end of input", this.pos);
    }

    const ch = this.peek();

    // Negation
    if (ch === "~" || ch === "!") {
      this.advance(1);
      this.skipWhitespace();
      const sub = this.parsePrimary();
      return Not(sub);
    }

    // Coalition operator: <<...>>
    if (this.lookAhead("<<")) {
      return this.parseCoalitionOp();
    }

    // Parenthesized expression
    if (ch === "(") {
      this.advance(1);
      this.skipWhitespace();
      const inner = this.parseExpr();
      this.skipWhitespace();
      this.expect(")");
      return inner;
    }

    // Atom
    if (this.isAgentChar(ch!)) {
      return Atom(this.parseAgent());
    }

    throw new ParseError(
      `Unexpected character '${ch}' at position ${this.pos}`,
      this.pos
    );
  }

  /**
   * Parse a coalition operator: <<A>>X ϕ, <<A>>G ϕ, <<A>>F ϕ, or <<A>>(ϕ U ψ)
   */
  private parseCoalitionOp(): Formula {
    this.expect("<");
    this.expect("<");
    const coalition = this.parseCoalitionBody();
    this.expect(">");
    this.expect(">");
    this.skipWhitespace();

    if (this.pos >= this.input.length) {
      throw new ParseError("Expected temporal operator (X, G, F, or '(... U ...)') after coalition", this.pos);
    }

    const op = this.peek()!;

    if (op === "X") {
      // <<A>>X ϕ
      this.advance(1);
      this.skipWhitespace();
      const sub = this.parsePrimary();
      return Next(coalition, sub);
    }

    if (op === "G") {
      // <<A>>G ϕ
      this.advance(1);
      this.skipWhitespace();
      const sub = this.parsePrimary();
      return Always(coalition, sub);
    }

    if (op === "F") {
      // <<A>>F ϕ — sugar for <<A>>(⊤ U ϕ)
      this.advance(1);
      this.skipWhitespace();
      const sub = this.parsePrimary();
      return Eventually(coalition, sub);
    }

    if (op === "(") {
      // <<A>>(ϕ U ψ)
      this.advance(1);
      this.skipWhitespace();
      const left = this.parseExpr();
      this.skipWhitespace();

      // Expect 'U'
      if (this.pos >= this.input.length || this.peek() !== "U") {
        throw new ParseError(
          `Expected 'U' in until expression at position ${this.pos}, got '${this.input[this.pos] ?? "EOF"}'`,
          this.pos
        );
      }
      this.advance(1); // skip 'U'
      this.skipWhitespace();

      const right = this.parseExpr();
      this.skipWhitespace();
      this.expect(")");
      return Until(coalition, left, right);
    }

    throw new ParseError(
      `Expected temporal operator (X, G, F, or '(... U ...)') after '>>', got '${op}' at position ${this.pos}`,
      this.pos
    );
  }

  /**
   * Parse the body of a coalition: empty or comma-separated agent names.
   * Does NOT consume the >> delimiters.
   */
  private parseCoalitionBody(): Coalition {
    this.skipWhitespace();
    // Empty coalition: <<>>
    if (this.lookAhead(">>")) {
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
 * Parse a formula string into a Formula AST.
 */
export function parseFormula(input: string): Formula {
  const parser = new Parser(input.trim());
  return parser.parse();
}
