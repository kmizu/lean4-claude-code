# 7. In practice — building a verified JSON parser

**English** | [日本語](../guide/07-json.html) | [← Chapter 6](06-reading-guide.html) | [Table of contents](index.html)

Chapter 6 closed by noting that plenty of unexplored topics that can be built
on this foundation remain. This chapter is the first answer to that: on top of
the Chapter 3 PEG framework, we built **a verified parser for a real-world
format** — RFC 8259 JSON. It doubles as a field report on how much of the
investment in a generic framework can be recovered.

## 7.1 Writing the grammar = inheriting the theorems

The first step is nothing more than transcribing the ABNF of RFC 8259 into a
`PExp` value (`lean/Json/Grammar.lean`). The RFC pins down even the placement
of whitespace in its ABNF (`begin-object = ws %x7B ws` — whitespace lives
inside the structural tokens), so we copy it verbatim. The file's header
carries a 1:1 correspondence table against the ABNF.

And the picture from Chapter 1 applies unchanged: **the parser is just the
verified generic `pegRun` applied to this grammar value**, so soundness (T1),
determinism including the tree (T2), and completeness (T3) are theorems about
the JSON parser the moment the grammar is written. Zero additional lines of
proof.

## 7.2 Designing the AST: staying faithful to the syntax

The interesting part was, if anything, the AST design decisions
(`lean/Json/Ast.lean`).

**Numbers are kept syntax-verbatim.** RFC 8259 deliberately does not specify
an internal representation for numbers. Collapsing them to floating point at
parse time would smuggle in an implementation decision, so we keep the sign,
integer part, fraction, and exponent **as sequences of digits**. As a result,
even the distinctions between `1E5` and `1e5`, or `1e+5` and `1e5`, are
preserved, and the roundtrip theorem becomes a **strict equality** with no
"up to normalization" caveat. In fact, during development, a printing fixpoint
check (`#guard`) detected that an uppercase `E` came back lowercased, forcing
us to add a field to the AST that preserves the case of the exponent marker —
an episode where a build-time test corrected the design.

**Strings are decoded code point sequences.** `\uXXXX` escapes are resolved at
parse time, up to and including the combining of surrogate pairs. Lone
surrogates are **rejected** (the RFC leaves this implementation-defined, so we
took the conservative choice and recorded it as a design decision in the
source code).

## 7.3 Battle testing: JSONTestSuite

Formal verification and empirical testing are not at odds. We run
nst/JSONTestSuite (318 files), the de facto conformance test for JSON parsers,
through runners on both sides: the Lean-native verified parser and the Scala
version extracted by Lens. The results:

- **y_ (must-accept) violations: 0. n_ (must-reject) violations: 0.**
- i_ (implementation-defined): 11 accepted / 24 rejected, exactly in line with
  the lone-surrogate rejection policy
- **The Lean version and the extracted Scala version agree on the verdict for
  all 318 files**
  (down to the handling of invalid UTF-8 byte sequences)

That a grammar transcribed straight from the RFC's ABNF scored like this on
the first run is, I think, the power of being able to write the spec as the
spec. This check is a permanent part of `make verify` and keeps running
against every change from here on.

## 7.4 The roundtrip theorem

The finale is a theorem of the same shape as in Chapter 4
(`lean/Json/Roundtrip.lean`, 1,367 lines):

```lean
theorem parse_print_json (v : JValue) (hwf : wfValue v = true) :
    ∃ fuel, ∀ fuel', fuel ≤ fuel' → parseJson fuel' (printJson v) = .ok v
```

Any well-formed JSON value, canonically printed and read back by the verified
parser, comes back as **exactly the original value**. What deserves attention
is how light the hypothesis `wfValue` is. All it says is that the digits of
numbers have the RFC's shape — **there are no assumptions on strings at all**.
That is because the type itself — strings as code point sequences — guarantees
their well-formedness, and because we proved that the four-way branch of
escape handling (quote, backslash, control character, pass-through)
corresponds 1:1 to the parse shapes of the grammar's char rule.

In the Shallot roundtrip (Chapter 4), a PEG boundary condition turned up and a
separation guard became necessary; in JSON, **no such traps appeared** — a
grammar in which every delimiter is explicit is strong in exactly this
respect. Though this, too, is something you can only assert once you have
written the proof.

## 7.5 The investment recovered

The new code for this parser — grammar data, AST, tree extractor, printer,
well-formedness predicates, lexical lemmas, and the roundtrip proof combined —
comes to about 2,600 lines. What was **reused**: the PEG semantics and its
four theorems, the patterns for constructing derivations, the entire Lens
extractor, the differential-harness machinery, and the whole design vocabulary
of the proofs (the fuel convention, canonical printing, fail-loud). This is
how cheap a second parser is — and this is the point of building a generic
framework, with proofs, once.

To use it from the JVM:

```sh
cd scala
sbt "shallotCli/run json '{\"a\": [1, 2.5e3]}'"   # => ok:{"a":[1,2.5e3]}
```

The code executing this parse is code extracted from Lean, with soundness,
completeness, determinism, and roundtrip all proven.

---

[← Chapter 6: A reading guide](06-reading-guide.html) | [Table of contents](index.html)
