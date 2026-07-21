# 6. Reading Guide — How to Walk Through the Source

**English** | [日本語](../guide/06-reading-guide.html) | [← Chapter 5](05-lens.html) | [Table of Contents](index.html)

Finally, here is a map for anyone who wants to walk through the
[repository](https://github.com/kmizu/lean4-claude-code) on their own.

## 6.1 The Map

```
lean/
├── Shallot/
│   ├── Peg/        # generic PEG: Syntax → Semantics → Interp → four theorem files
│   ├── Syntax/     # Shallot concrete syntax: Grammar (grammar value) / Printer / TreeToAst
│   │               #   / Lexemes / RoundtripExpr / Roundtrip (three-layer roundtrip proof)
│   ├── Lang/       # AST / Typing / TypeCheck (+Verify) / Eval / TypeSound
│   ├── Opt/        # constant folding + preservation theorem
│   ├── Vm/         # stack VM: Machine / Compile / Correct (correctness proof)
│   └── Data/       # red-black trees: RBMap / RBVerify / RBBalance
├── Lens/           # extractor: Translate / Equations / Matcher decomposition / Printer …
└── Audit.lean      # axiom audit of every flagship theorem (#guard_msgs)
scala/
├── runtime/        # handwritten prelude (TCB)
├── generated/      # Lens output (committed, with drift checking)
└── shallot-cli/    # CLI + ScalaCheck properties
corpus/             # differential-harness goldens (60 cases)
docs/theorems.md    # theorem inventory (also usable as an index for this guide)
```

Scale: about 11,800 lines of Lean (roughly 8,000 of them proofs), about 4,000 lines
of extractor code, and about 1,300 lines of generated Scala.

## 6.2 Three Reading Tracks

**(i) The 30-minute PEG-only track.** Read `Peg/Syntax.lean` → `Peg/Semantics.lean` →
`Peg/Interp.lean` in that order (the primary sources for Chapter 3). For the four
theorem files (`Fuel` / `Soundness` / `Determinism` / `Completeness`), it is enough
to read **only the header docstrings and the theorem statement lines**.

**(ii) The theorem tour track.** Using [docs/theorems.md](../theorems.html) *(Japanese)*
as your index, open `lean/Audit.lean`. The targets of the `#print axioms` commands
lined up there are exactly the flagship theorems, so jump to each file by name and
read the statement. You don't need to read the proof bodies — **the statements and
docstrings are the text; the proofs are footnotes for the machine.**
(RoundtripExpr.lean runs to 1,700 lines, but the only thing you need to read is the final theorem statement.)

**(iii) The hands-on track.** Set up the environment following the steps in the
repository's README and run `make verify`. In fail-fast order:

```make
verify: audit lean lake-test check-drift scala diff
```

`audit` (are the sources free of sorry and the like?) → `lean` (`lake build` =
**re-checking every proof plus the axiom audit**) → `lake-test` (extractor goldens) →
`check-drift` (does the committed generated code match a fresh extraction?) →
`scala` (sbt tests) → `diff` (the 60-case Lean ≡ Scala comparison). The verification
pipeline itself explains what, exactly, is being "verified."

After that, try something like `sbt "shallotCli/run run ../examples/collatz.shl"`
and watch the proven stack actually run.

## 6.3 Header Docstrings Are Design Notes

Many of the quotations in this series were, in fact, **header comments** from the
source files. In this repository, the opening docstring of each file records why
the design is the way it is, and what is claimed and what is not. The fuel
convention in `Peg/Interp.lean`, the full story of the boundary conditions in
`Syntax/Roundtrip.lean`, the hand-audit declaration in `Lens/Builtins.lean` —
**skimming just the headers** is the most efficient way to walk this codebase.

## 6.4 Going Further

- **Ford, "Parsing Expression Grammars" (POPL 2004)** — the original source of this
  project's `Derives`. Rereading it, you should be able to see how each rule maps
  into Lean one by one
- **Theorem Proving in Lean 4** (the official Lean tutorial) — for when you want to
  properly continue where Chapter 2 left off
- **[docs/roadmap.md](../roadmap.html)** *(Japanese)* — a record of every milestone
  in this project. The story of flushing out 17 extractor bugs through adversarial
  review, the design change in the compiler correctness proof, and more — it serves
  as the project's development log
- Formalizing left-recursion PEGs (the packrat extension of Warth et al.), a
  roundtrip for a precedence-preserving pretty-printer, and other **unexplored
  topics that can be built on this foundation** — plenty remain. `Derives` was
  designed as a starting point for exactly that

## In Closing

In this repository, the fact that `lake build` succeeds is itself the peer review.
If you are unsure where to start trusting and reading, the answer is concentrated
in a single file — `lean/Audit.lean`. Enjoy.

---

[← Chapter 5: The Lens extractor — carrying proven Lean code into Scala 3](05-lens.html) | [Table of Contents](index.html)
