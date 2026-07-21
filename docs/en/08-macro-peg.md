# 8. In practice — formalizing macro_peg's call-by-name semantics

**English** | [日本語](../guide/08-macro-peg.html) | [← Chapter 7](07-json.html) | [Table of contents](index.html)

Chapter 7 reconfirmed, using JSON as a real-world format, the picture set up in
Chapter 1: hand the verified generic `pegRun` a grammar value, and the
theorems come along for free. This chapter is about the opposite case —
**where that picture breaks down**.
[kmizu/macro_peg](https://github.com/kmizu/macro_peg) is a library that
extends PEG with "parameterized rules," and once parameters enter the picture
as a new syntactic element, the existing `PExp`/`Derives`/`pegRun` can no
longer be reused as-is. This chapter's subject is tracking what changes and
what doesn't.

## 8.1 Reading the reference implementation: three evaluation strategies and `extract()`

Reading macro_peg's `Evaluator.scala` shows that there are three strategies
for handling a macro call's actual arguments (`EvaluationStrategy.scala`).
The default, `CallByName`, is genuine call-by-name: it passes the argument
**unevaluated, as raw syntax**. `CallByValueSeq`/`CallByValuePar` instead
evaluate the argument first while consuming input, passing the consumed
substring as a value — and even between these two there's a difference
between "sequential consumption" and "lookahead extraction at the same
position." Every test backing the claims in the README's headline (that it
can recognize palindromes and the copy language `{ww}` — expressive power
beyond plain PEG) is a `CallByName` example, so this formalization narrows
its scope to that one strategy alone.

`CallByName`'s implementation threads an environment through evaluation,
with `bindings : Map[Symbol, Expression]` housing both rule names and
parameter names together. What stands out here is a function called
`extract()`. When evaluating a macro call `P(w "a")`, it first **closes the
free variable `w` inside the argument `w "a"` over the bindings in effect at
the call site**, then passes the result as a fresh binding — skip this, and
the meaning attached to the same name `w` would drift with every recursive
call (name collision / variable capture). This hand-rolled hygiene code is
necessary precisely because parameters are represented **by name** and
share a namespace with global rule names.

## 8.2 De Bruijn-indexing — making `extract()` disappear entirely

On the Lean side, we applied the same convention that the existing `PExp.nt`
already used for non-terminals — referring to them by a `Nat` index — to
parameter references as well. `.param k` is a single-level de Bruijn index
meaning "the k-th actual argument of the currently active rule"
(`lean/MacroPeg/Syntax.lean:56`). Because rule bodies don't nest in the core
of macro_peg (the part excluding the higher-order function layer) — there is
no lambda — a single de Bruijn level is enough.

```lean
inductive MExp where
  ...
  | param (k : Nat)
  | call (i : Nat) (args : List MExp)
  ...
```

Substitution, `MExp.subst`, then becomes plain structural rewriting that
needs neither names nor an environment
(`lean/MacroPeg/Syntax.lean:110-133`). An out-of-range `.param k` reference
(an ill-formed rule that contradicts its declared arity — which can't
actually happen, since arity is already checked on the `call` side) is
mapped, without adding a new AST constructor, to the always-false expression
`.notP .eps`, built from existing constructors
(`lean/MacroPeg/Syntax.lean:82`) — a natural extension of the "zero
well-formedness assumptions" principle established in Chapter 3 (a missing
non-terminal has an explicit failure rule). **This single level of
de Bruijn-indexing alone is enough to make the hand-rolled hygiene code
equivalent to `extract()` completely unnecessary — plain substitution is
capture-free on its own.** It's a small but essential difference that
becomes visible only by comparing against the reference implementation.

## 8.3 Building a new `Derives` — a contrast with JSON

Chapter 7's JSON was a case where the existing `PExp`/`Derives`/`pegRun`
could be reused **as-is**. macro_peg doesn't get that luxury. Since it needs
syntax that `PExp` doesn't have — `.param` and `.call` (with arguments) — it
requires an independent module, `lean/MacroPeg/`, with its **own new AST,
new `Derives`, and new interpreter** (Lean's inductive types have no notion
of subtyped extension, so this isn't an "extension" in the type-theoretic
sense, but a parallel implementation that follows the same design
principles).

`MDerives` (`lean/MacroPeg/Semantics.lean:35`) copies the nine rules
`eps`/`any`/`chr`/`range`/`lit`/`seq`/`alt`/`star`/`notP` verbatim from
`Derives`, and adds six new ones:

- `dbg` (:60): `Debug(e)` succeeds unconditionally without evaluating `e` —
  a direct reflection of the reference implementation's no-op
- `paramFail` (:62): a raw `.param k` fails unconditionally. It's never
  actually reached, since substitution in `call` is guaranteed to eliminate
  it, but since soundness needs to hold for every `MExp`, this rule is
  required on the `MDerives` side too — symmetric to the dead branch in the
  generic interpreter (the same treatment as the inner `some .fail` in
  `star`)
- `callOk`/`callFail` (:64, :69): given rule `i`, assuming the declared
  arity matches the number of actual arguments, derive from
  `MExp.subst args r.body` (the body **after** substitution). **The
  arguments are not evaluated here** — this is the essence of call-by-name
- `callMissing`/`callArity` (:74, :77): a missing rule or an arity mismatch
  is an explicit, hypothesis-free failure rule

`mpegRun` (`lean/MacroPeg/Interp.lean:21`) is fuel-based structural
recursion of the same shape as `pegRun`. The `.call` case is isomorphic to
the `.nt` case (look up the rule, consume one unit of fuel, recurse into the
substituted body), and the `.param` case (:43) is the dead branch mentioned
above — unreachable but required for genericity.

The proof patterns carried over directly. The proof technique for T0–T3
(fuel monotonicity, the suffix invariant, soundness, determinism,
completeness) itself takes the shape of "strong induction on fuel, with an
inductive hypothesis for an arbitrary expression at each step" — and the
`pegRun`/`Derives` proofs were already in this shape, given that the `.nt`
case already demands the same hypothesis for the expression it refers to.
The `call` case only had to apply that same hypothesis to a "different
expression," namely `subst args r.body`, so there was zero novelty here.

## 8.4 The headline theorem: proving the copy language under universal quantification

Here is the grammar, found in `NonTrivialLanguagesSpec.scala`, that
recognizes the copy language `{ww | w ∈ {a,b}*}` — the textbook witness for
a non-context-free language:

```
Copy(w) = "a" Copy(w "a") / "b" Copy(w "b") / w
```

The Scala test suite confirms that this grammar correctly accepts a finite
set of strings such as `"aa"`, `"bb"`, `"abab"`, and correctly rejects
strings such as `"ab"`, `"aba"`. What the proof gets to state goes further —
that it holds for **every** `u ∈ {a,b}*`:

```lean
theorem copy_language_ww (u : List Char) (hu : ∀ c ∈ u, c = 'a' ∨ c = 'b') :
    ∃ t, MDerives copyGrammar (.call copyIdx [.lit []]) (u ++ u) (.ok t [])
```

(`lean/MacroPeg/Examples.lean:326`). Not a finite set of test cases, but
every `u` over `{a,b}*`.

### The accumulator argument never stays flat

The natural proof strategy is induction on `u`. But `Copy`'s recursive call
argument, `w "a"`, is passed **unevaluated, as raw syntax**, because of
call-by-name — in Lean terms, `.seq (.param 0) (.chr 'a')`. With each level
of recursion, the next activation's `.param 0` gets bound not to a flat
`.lit` but to a `.seq` node, and by the second, third level it grows into a
chain of `.seq` nodes nesting leftward. In other words, induction of the
form "the accumulator is `.lit w`" doesn't hold.

What we interposed instead is `ExactMatch` — an invariant stating that
"`wexp` is behaviorally identical to `.lit w`" (`lean/MacroPeg/Examples.lean:108`):

```lean
structure ExactMatch (wexp : MExp) (w : List Char) : Prop where
  succ : ∀ rest, ∃ t, MDerives copyGrammar wexp (w ++ rest) (.ok t rest)
  fail : ∀ z, (∀ p, z ≠ w ++ p) → MDerives copyGrammar wexp z .fail
```

`exactMatch_step` (:120) proves a preservation law — "if `wexp` exactly
matches `w`, then `.seq wexp (.chr c)` exactly matches `w ++ [c]`" — and
with this, induction goes through across `Copy`'s recursive calls. The
punchline of this section is that the proof side had to confront the same
phenomenon — the argument's syntax changing on every call — that the
reference implementation solved with `extract()`.

### Two holes discovered only by writing it

The first draft had two genuine logical holes.

The first was a **missing alphabet restriction**. Because `Copy`'s grammar
only branches on `'a'`/`'b'`, `copy_language_ww` doesn't hold if `u`
contains any other character. The theorem statement needed
`(hu : ∀ c ∈ u, c = 'a' ∨ c = 'b')` added to it — an example where "for
every `u`," which looked obvious before writing the proof, turned out to
demand an implicit hypothesis once actually written down.

The second was a lemma, `copy_fail_short`, that became necessary to fill the
gap (`lean/MacroPeg/Examples.lean:154`):

```lean
theorem copy_fail_short {wexp : MExp} {w : List Char} (hm : ExactMatch wexp w) :
    ∀ z : List Char, z.length < w.length →
      MDerives copyGrammar (.call copyIdx [wexp]) z .fail
```

In the base case of `copy_gen` (the body of the induction, :225), when
`Copy(w)` is applied to an input of exactly length `|w|`, we need to show
that both of the two "growing" branches (the ones that read `'a'`/`'b'` and
recurse) fail, leaving only the third branch (matching `wexp` itself).
After consuming one character, the remaining input has length `|w|-1`, but
the recursive `Copy` call is for a string of length `|w|+1` — so **the
input is, in principle, too short to succeed**. This fact — that anything
too short fails — requires no argument about the content of the characters
at all, purely one about length. Noticing that this lemma was missing, too,
only happened once we actually tried to write the proof all the way
through.

This project has seen this pattern play out several times before — sepOkB
(Chapter 4), the uppercase `E` (Chapter 7) — moments where writing the
proof uncovered a hole in the spec. This time is a variation on that theme,
with one difference: **the hole wasn't a flaw in the implementation, but
slackness in the theorem statement itself**. You could also put it this
way: the act of writing a universally quantified theorem is what forced the
question "does this really hold for every `u`?" to be thought through to
the end.

## 8.5 Lens extraction and the differential harness

Since `mpegRun` is fuel-based structural recursion isomorphic in shape to
`pegRun`, the extractor Lens's equation-lemma route went through as-is,
with no new accommodations needed — except for one snag against the
existing whitelist. Writing the arity check as Prop's `≠` (via
`Decidable`) fails extraction, because `instDecidableNot` isn't registered
in Lens's built-in table. Rewriting it to use Bool's `==` instead, in the
same style as `beqChar`/`leChar`, made it go through — the same pattern
that `.chr`/`.range` already follow.

The differential harness also follows the existing design as-is. The
`shallot-cli macro-dump` subcommand runs the extracted `MacroPeg_mpegRun`,
and `make verify` continuously checks three-way agreement — Lean-native
execution ≡ golden ≡ extracted-Scala execution — against
`corpus/golden/macro_peg.jsonl` (eight copy-language witnesses).

## 8.6 What was left out of scope this time

- **The `CallByValueSeq`/`CallByValuePar` strategies**: these would require
  generalizing `MDerives` with a strategy parameter, which we've carved out
  as a future milestone
- **The higher-order function layer** (lambdas `(x -> e)`, currying,
  first-class function values): even in the reference implementation, this
  isn't a native feature of `Evaluator`; it only works through a separate
  utility, `MacroExpander`, via a syntactic inlining pass that "expands
  everything before the call," which carries a non-termination risk (and
  can't be used with recursive macros). This time, we scoped the work to
  just the core that backs macro_peg's headline expressive-power claim:
  "recursive macros that take expression parameters as data values"

---

[← Chapter 7: In practice — building a verified JSON parser](07-json.html) | [Table of contents](index.html)
