# Shallot + Lens — The Guide

**English** | [日本語](../index.html)

**What does it take to flatly say "this parser is correct"?** This is a guided
tour of a project that answered the question the hard way — with the Lean 4
theorem prover.

The target reader **knows PEGs (Parsing Expression Grammars) well but is not
familiar with Lean or theorem proving**. If you have implemented a parser
generator or read Ford's paper, you are exactly who this was written for.

## The chapters (best read in order)

1. [Introduction — what "correct" means for a parser](01-intro.html)
2. [A minimal Lean 4 primer — theorem proving for BNF people](02-lean-primer.html)
3. [PEG formal semantics — transcribing Ford's semantics into Lean](03-peg-semantics.html)
4. [The Shallot language — the typechecker/interpreter/compiler proof stack](04-shallot.html)
5. [The Lens extractor — carrying proven Lean code into Scala 3](05-lens.html)
6. [A reading guide — how to walk the source tree](06-reading-guide.html)
7. [In practice — building a verified JSON parser](07-json.html)
8. [In practice — formalizing macro_peg's call-by-name semantics](08-macro-peg.html)

## Reference material

- [Theorem inventory (machine-audited)](../theorems.html) *(Japanese)*
- [The extractable subset](../extractable-subset.html) *(Japanese)*
- [Development roadmap](../roadmap.html) *(Japanese)*
- [The repository](https://github.com/kmizu/lean4-claude-code)

## In three lines

- The parser, typechecker, interpreter and compiler of a small functional
  language called Shallot are **implemented AND proven correct in Lean 4**,
  with zero `sorry` (proof holes)
- The parser is *the verified generic PEG interpreter applied to a grammar
  value*, so PEG soundness/completeness/determinism transfer to it for free
- The verified Lean code is **extracted to Scala 3 by a home-grown extractor
  (Lens)**, and both sides run the same 60-case table with mechanically
  checked agreement
