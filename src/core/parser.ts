/**
 * Recursive-descent parser for CMAEL(CD) formulas.
 *
 * Syntax (all ASCII, no special symbols needed):
 *
 *   atom       := [a-z][a-z0-9_]*
 *   coalition  := '{' agent (',' agent)* '}'
 *   agent      := [a-z][a-z0-9_]*
 *
 *   primary    := atom
 *              | '~' primary                    // negation
 *              | 'D' coalition primary           // distributed knowledge
 *              | 'C' coalition primary           // common knowledge
 *              | 'K' coalition primary           // everyone knows (sugar)
 *              | 'K' agent primary               // individual knowledge (sugar for D{a})
 *              | '(' expr ')'
 *
 *   expr       := primary (('&' | '|' | '->') primary)*
 *
 * Sugar:
 *   φ | ψ       desugars to  ~(~φ & ~ψ)
 *   φ -> ψ      desugars to  ~(φ & ~ψ)
 *   Ka φ        desugars to  D{a} φ
 *   K{a,b} φ    desugars to  (Ka φ & Kb φ)
 *
 * Operator precedence (high to low):
 *   ~ (prefix), D/C/K (prefix), &, |, ->
 *
 * Examples:
 *   "p"
 *   "~p"
 *   "(p & q)"
 *   "(p | q)"
 *   "(p -> q)"
 *   "Ka p"
 *   "D{a,b} p"
 *   "C{a,b} (p & q)"
 *   "(~D{a,c} C{a,b} p & C{a,b} (p & q))"
 */

import {
  type Formula,
  type Agent,
  type Coalition,
  Atom,
  Not,
  And,
  D,
  C,
  Or,
  Implies,
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

    // Parenthesized expression
    if (ch === "(") {
      this.advance(1);
      this.skipWhitespace();
      const inner = this.parseExpr();
      this.skipWhitespace();
      this.expect(")");
      return inner;
    }

    // D{...} — distributed knowledge
    if (ch === "D" && this.pos + 1 < this.input.length && this.input[this.pos + 1] === "{") {
      this.advance(1); // skip 'D'
      const coalition = this.parseCoalition();
      this.skipWhitespace();
      const sub = this.parsePrimary();
      return D(coalition, sub);
    }

    // C{...} — common knowledge
    if (ch === "C" && this.pos + 1 < this.input.length && this.input[this.pos + 1] === "{") {
      this.advance(1); // skip 'C'
      const coalition = this.parseCoalition();
      this.skipWhitespace();
      const sub = this.parsePrimary();
      return C(coalition, sub);
    }

    // K{...} — everyone knows (sugar: K{a,b} φ => (Ka φ & Kb φ))
    if (ch === "K" && this.pos + 1 < this.input.length && this.input[this.pos + 1] === "{") {
      this.advance(1); // skip 'K'
      const coalition = this.parseCoalition();
      if (coalition.length === 0) {
        throw new ParseError("K{} requires at least one agent", this.pos);
      }
      this.skipWhitespace();
      const sub = this.parsePrimary();
      // Fold into conjunction: (Ka φ & (Kb φ & ...))
      let result: Formula = D([coalition[coalition.length - 1]!], sub);
      for (let i = coalition.length - 2; i >= 0; i--) {
        result = And(D([coalition[i]!], sub), result);
      }
      return result;
    }

    // K<agent> — individual knowledge (sugar for D{agent})
    if (ch === "K" && this.pos + 1 < this.input.length && this.isAgentChar(this.input[this.pos + 1]!)) {
      this.advance(1); // skip 'K'
      const agent = this.parseAgent();
      this.skipWhitespace();
      const sub = this.parsePrimary();
      return D([agent], sub);
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

  private parseCoalition(): Coalition {
    this.expect("{");
    const agents: Agent[] = [];
    this.skipWhitespace();
    agents.push(this.parseAgent());
    this.skipWhitespace();
    while (this.peek() === ",") {
      this.advance(1);
      this.skipWhitespace();
      agents.push(this.parseAgent());
      this.skipWhitespace();
    }
    this.expect("}");
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
