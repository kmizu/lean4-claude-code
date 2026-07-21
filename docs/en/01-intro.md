# 1. Introduction — what "correct" means for a parser

**English** | [日本語](../guide/01-intro.html) | [Table of contents](index.html) | [Chapter 2 →](02-lean-primer.html)

## 1.1 The gap between passing tests and being correct

Let me start with a true story.

This project has 60 differential test cases that run the parser, typechecker,
and interpreter through two implementations (Lean, and Scala generated from it)
and compare the results. All of them were green. And yet, in the final stretch
of development, while trying to prove the theorem that re-parsing a printed
program gives back the original, I found **one case where the proof simply
would not go through**. Digging in, it turned out to be not a technical
difficulty in the proof, but **a boundary condition that really exists in the
grammar itself**. When a function definition's body ends in a bare variable and
the next expression begins with `(`, PEG's prioritized choice reads across the
function boundary and consumes both as a "function call" — a shape none of the
60 test cases ever hit (details in [Chapter 4](04-shallot.html)).

Tests can only say "it is correct for the inputs we tried." So what do you do
if you want to say "it is correct for **every** input"? The answer is a
**machine-checked proof**, and that is exactly what this project did for a PEG
parser.

## 1.2 Breaking down parser "correctness"

Let's break "this parser is correct" down into an implementer's everyday terms.

- **Soundness** — Does every result the parser returns (success and failure
  alike) match what the grammar's specification prescribes? "Is what it
  accepts really something the grammar admits?"
- **Determinism** — For a given input, does the specification determine
  exactly one result? Is it unique down to the parse tree (absence of
  ambiguity)?
- **Completeness** — For every input where the specification determines a
  result, does the implementation always finish processing it? Can "the spec
  admits it but the implementation never returns it" ever happen?
- **Roundtrip** — If you print an AST and parse it again, do you get the
  original AST back?

In this project, all four are proven as Lean 4 theorems. And the object of the
proofs is Ford's PEG formal semantics (POPL 2004) — those inference rules that
any reader of this document has read at least once.

## 1.3 The project at a glance

There are two protagonists.

**Shallot** is a small first-order functional language with int and bool, and
its complete toolchain — PEG parser, typechecker, interpreter, constant-folding
optimizer, stack-VM compiler — is written in Lean 4, with the correctness of
each part proven. The proofs contain zero holes (`sorry`), and every theorem's
axiom dependencies are machine-checked at build time.

**Lens** is a home-grown extractor that translates Lean 4 code into Scala 3.
It carries the proven toolchain out as code that runs on the JVM. A CLI called
`shallot-cli` lets you actually execute `.shl` files — parsing goes through the
formally verified PEG interpreter, and typechecking through a checker proven
sound and complete.

The overall flow looks like this:

```
lean/Shallot (spec + implementation + proofs)
   │  lake build = checks all proofs + axiom audit
   │
   ├─ lake exe extract (Lens extractor) ──→ scala/generated (~1,300 lines of Scala 3)
   │                                        │
   │                                        └─→ shallot-cli (run / eval / dump)
   │
   └─ shallot-runner ──┐
                       ├──→ differential harness (60 cases, Lean run ≡ Scala run)
   shallot-cli dump ───┘
```

And here is the most beautiful piece of the project's design: **the Shallot
parser does nothing but hand grammar data to the verified generic PEG
interpreter** (`lean/Shallot/Syntax/TreeToAst.lean`):

```lean
/-- The Shallot parser: the VERIFIED generic PEG interpreter applied to
`shallotGrammar`, then tree extraction. -/
def parseShallot (fuel : Nat) (s : String) : Except ParseErr Program :=
  match pegRun shallotGrammar fuel (.nt NT.program) s.toList with
  | none => .error .fuelOut
  | some .fail => .error .syntaxErr
  | some (.ok (.nodeNT _ t) _) => treeToAst t
  | some (.ok _ _) => .error .shape
```

Instead of a parser generator emitting code, **the theorems are inherited by
the grammar value**. The soundness, completeness, and determinism proven for
the generic interpreter `pegRun` hold for any grammar value, so they hold for
`shallotGrammar` automatically. A "verified parser" is not some specially
hardened piece of code — it is this structure of inheritance.

## 1.4 How to read this series

- **[Chapter 2](02-lean-primer.html)** installs the bare minimum you need to
  read Lean. You do not need to learn to write it. Two reading rules are all it
  takes: "inductive is BNF; an inductive predicate is an inference rule"
- **[Chapter 3](03-peg-semantics.html)** is the core: how Ford's semantics is
  written in Lean, and what has been proven. If you know PEG, you can read all
  of it
- **[Chapter 4](04-shallot.html)** is the proof stack for the language
  toolchain. The full story of the "grammar hole the proof found" from the top
  of this chapter is there too
- **[Chapter 5](05-lens.html)** covers Lean → Scala extraction, and an honest
  line-drawing of how far it can be trusted
- **[Chapter 6](06-reading-guide.html)** is how to walk the source tree

One thing worth saying up front: formal verification is not a "zero-bug
warranty." The line between what the proofs cover and what rests on trust — the
trusted computing base (TCB) — is faced head-on in Chapter 5. If, that
line-drawing included, you come away with a concrete feel for what kind of
undertaking proving a parser is, this series has done its job.

---

[Table of contents](index.html) | [Chapter 2: A minimal Lean 4 primer — theorem proving for BNF people →](02-lean-primer.html)
