# 8. In practice — formalizing macro_peg's evaluation strategies

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
beyond plain PEG) is a `CallByName` example. This chapter starts by
formalizing `CallByName` alone (8.1–8.4), then generalizes `MDerives`/
`mpegRun` with a `Strategy` parameter to add the remaining two strategies
(8.5) — by the end, all three are formalized.

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

## 8.5 Threading `Strategy` through — `CallByValuePar` and `CallByValueSeq`

Up to this point, `MDerives`/`mpegRun` were `CallByName`-only. Adding the
remaining two strategies requires a destructive retrofit of the signature
itself — Lean's `inductive`/`mutual` requires declaring every constructor in
one place, so there's no option to grow a new `call` rule later on.
`MDerives (g : MGrammar) : ...` becomes `MDerives (g : MGrammar) (s :
Strategy) : ...`, and nearly every file under `MacroPeg/` — including the
already-proved T0–T3 theorems — has to be rewritten.

```lean
inductive Strategy where
  | callByName
  | callByValuePar
  | callByValueSeq
  deriving DecidableEq
```

The existing fifteen rules just thread `s` through unchanged (only `.call`
is strategy-dependent). `callOk`/`callFail` get renamed to
`callNameOk`/`callNameFail`, gaining a `hs : s = .callByName` hypothesis,
and each of the two new strategies gets its own auxiliary relation plus
three constructors (success, body failure, argument failure).

`CallByValuePar` (arguments evaluated independently, each against the
**same** input position — a backreference-like strategy) adds
`DerivesArgsPar`:

```lean
inductive DerivesArgsPar (g : MGrammar) (s : Strategy) (input : List Char) :
    List MExp → List MExp → Prop where
  | nil : DerivesArgsPar g s input [] []
  | cons (a : MExp) (as : List MExp) (p rest : List Char) (t : MTree) (vs : List MExp)
      (h1 : MDerives g s a input (.ok t rest))
      (hp : input = p ++ rest)
      (h2 : DerivesArgsPar g s input as vs) :
      DerivesArgsPar g s input (a :: as) (.lit p :: vs)
```

`input` stays fixed across every argument — each one is evaluated
independently, starting from the same position. `CallByValueSeq`
(arguments evaluated **left to right**, threading the consumed input
position through each in turn), by contrast, carries `final` — the
position left over after every argument has been evaluated — instead of a
fixed `input`:

```lean
inductive DerivesArgsSeq (g : MGrammar) (s : Strategy) :
    List Char → List MExp → List MExp → List Char → Prop where
  | nil (input : List Char) : DerivesArgsSeq g s input [] [] input
  | cons (a : MExp) (as : List MExp) (input p rest final : List Char) (t : MTree) (vs : List MExp)
      (h1 : MDerives g s a input (.ok t rest))
      (hp : input = p ++ rest)
      (h2 : DerivesArgsSeq g s rest as vs final) :
      DerivesArgsSeq g s input (a :: as) (.lit p :: vs) final
```

The one essential difference from `DerivesArgsPar` is that `cons`'s
recursive call evaluates the next argument against `rest` — the position
left over after the current one. `CallByValueSeq`'s call rule, `callSeqOk`,
derives the rule body from this `final` (called `mid` in the invocation
site) — in contrast to `CallByValuePar`'s `callParOk`, which always derives
the body from the **original** `input`.

### Getting "if any argument fails, the whole call fails" right

The first draft of `callParArgFail` (the rule that fails the whole call
when any one argument fails) only required `badArg ∈ args` — some argument
in the list fails — with no constraint on the arguments before it. The
agent trying to prove completeness (T3) mechanically discovered that this
rule **contradicts the reference implementation's left-to-right
short-circuit evaluation**: if a non-terminating argument sits before
`badArg`, a derivation exists, yet `mpegRun` can never realize that `.fail`
at any fuel level (it returns `none` forever) — a counterexample the agent
constructed. Rather than papering over it with `sorry`, it reported a
provable disproof, and the rule was fixed:

```lean
| callParArgFail (i : Nat) (pre : List MExp) (badArg : MExp) (post : List MExp) (r : MRule)
    (input : List Char) (preVals : List MExp)
    (hs : s = .callByValuePar)
    (hr : ruleAtM g.rules i = some r)
    (ha : r.arity = (pre ++ badArg :: post).length)
    (hpre : DerivesArgsPar g s input pre preVals)
    (hfail : MDerives g s badArg input .fail) :
    MDerives g s (.call i (pre ++ badArg :: post)) input .fail
```

Requiring an explicit split `args = pre ++ badArg :: post`, together with
`hpre : DerivesArgsPar g s input pre preVals` (evidence that everything
before `badArg` succeeded), makes the rule match `evalArgsPar`'s
left-to-right short-circuit evaluation exactly.

`CallByValueSeq`'s `callSeqArgFail`, written after this bug had already
been hit once, sidesteps the same trap proactively — it was written from
the start with the correct shape, `pre ++ badArg :: post` plus `hpre :
DerivesArgsSeq g s input pre preVals mid` (evidence that everything before
`badArg` succeeded, threaded all the way to `mid`), so no rework was needed
during the completeness proof. Following sepOkB (Chapter 4), the uppercase
`E` (Chapter 7), and the `{a,b}*` restriction (8.4), this is another
instance of a pattern this project keeps running into — a spec hole that
only surfaces once you actually write the proof — but also, unusually, a
case where a hole found once was documented into the next design and
didn't recur.

### P1 becomes non-trivial under `CallByValueSeq`

The proof of P1 (`mderives_suffix`: a successful derivation consumes a
prefix of the input) uses mutual induction via `MDerives.rec`, which
requires `motive_2` (for `DerivesArgsPar`) and `motive_3` (for
`DerivesArgsSeq`). Every `CallByValuePar` constructor reduces to the same
argument as `CallByName` — "the body's sub-derivation consumes the input"
— so `motive_2` could stay the trivial `True`. But `callSeqOk` derives the
body from the **final threaded position** `mid` reached after evaluating
the arguments, so its sub-derivation only yields `mid = p ++ rest`.
Recovering `input = _ ++ rest` needs a separate fact — that evaluating the
arguments in sequence itself consumed the prefix from `input` to `mid` —
which can be assembled from the `hp : input = p ++ rest` carried by each
`DerivesArgsSeq` `cons` step. So `motive_3` had to become the non-trivial
predicate `∃ q, input = q ++ final`, carried as the induction hypothesis.
Even for the "same" auxiliary argument relation, whether or not the
position gets threaded changes how much information the proof needs to
carry.

The proof technique for T0–T3 itself (strong induction on fuel, mutual
induction on derivation structure) carried over unchanged from the
`CallByName` stage. What was genuinely new boils down to the two things
seen here: getting the shape of "the whole call fails if any one argument
does" right, and how threading the position changes what information the
proof needs.

## 8.6 Formalizing a slice of the higher-order layer — and catching a prior scoping mistake

Up to this point, this chapter (and earlier versions of it, and
`docs/roadmap.md`) scoped out macro_peg's entire higher-order layer
(lambdas, passing named rules as values). The reason given was: "even the
reference `Evaluator` doesn't support it natively — it only works through
a separate utility, `MacroExpander`, an eager whole-grammar inlining pass
that carries a non-termination risk." **That understanding was wrong.**

### What re-reading the reference implementation turned up

When the time actually came to tackle the higher-order layer, we re-read
`Evaluator.scala`/`MacroExpander.scala`/`Parser.scala` closely and verified
against the running code via `sbt console`. What we found:

- `Evaluator.scala` already supports invoking a callable bound to a
  parameter (whether a named-rule reference or a lambda literal) from
  inside the same call — NATIVELY — via `FUNS` (a map from rule names to
  `Function` values) threaded through `bindings`. Calling `Evaluator`
  directly, skipping `MacroExpander.expandGrammar` entirely, reproduces
  all six shipped higher-order tests' results bit-for-bit
- `MacroExpander` is genuinely load-bearing for exactly one pattern: a rule
  call returning a closure as a VALUE, later applied from a DIFFERENT call
  site — true environment capture. This is expressible in the AST but has
  zero shipped test coverage. A hand-written test exercising it (something
  like `MakeAdder(x: ?) = (y -> x y); UseCurried(f: ?, y: ?) = f(y);`,
  returning a closure and applying it elsewhere) reliably crashes with a
  `ClassCastException` when `MacroExpander` is skipped
- The test claiming to exercise currying (`Curry(f: ?) = (x -> (y -> f(x,
  y)))`, invoked as `Curry((x,y->x y))("a")("b")`) turns out to be
  misnamed. `Call`'s grammar production only accepts `identifier(args)` —
  there is no syntax for chaining another application onto an arbitrary
  result — so `Curry(...)` just zero-width-matches as a lambda value, and
  the trailing `("a")("b")` are parsed as plain string-literal sequencing,
  not application. No currying and no application ever actually happens

So the pattern "invoke a passed-in callable from inside the same call
tree" can be formalized natively, with no non-termination risk — that's
the starting point for the M-PEG-4 milestone.

### `.lam` / `.callParam` / `.invoke`

This project has no `.peg` surface parser — `Examples.lean` builds `MExp`
terms directly in Lean. So "pass a named rule as a value" and "pass a
lambda literal" don't even need to be distinguished — both reduce to the
same `.lam arity body` shape:

```lean
| lam (arity : Nat) (body : MExp)
| callParam (k : Nat) (args : List MExp)
| invoke (arity : Nat) (body : MExp) (args : List MExp)
```

`.lam` is a callable value, evaluated as an unconditional zero-width
success exactly like `.dbg` (values don't consume input). Its `body`'s
`.param` references are relative to the lambda's own scope, independent of
the enclosing rule's — every shipped lambda literal is self-contained (no
free-variable capture), so `subst` treats `.lam` as a LEAF, exactly like
`.lit`, never recursing into it. That's what makes the absence of capture
structural rather than conventional.

`.callParam k args` is the syntax "invoke the callable bound to the
current rule's k-th actual parameter, with these args" — what
`Examples.lean` writes directly. `subst` always resolves it: if `.param
k`'s position holds a `.lam ar bod`, it rewrites to `.invoke ar bod
(the substituted args)`; otherwise (a type mismatch, or out of range) it
collapses to `MExp.failAlways`, the same fallback an out-of-range `.param`
already uses.

`.invoke` is nearly isomorphic to `.call`, except `body`/`arity` are
already in hand rather than looked up in the grammar's rule table. **One
design correction happened while implementing it**: the original plan was
"`.invoke` needs only one rule, regardless of `Strategy`" — but that
contradicts the existing invariant that a single derivation commits to ONE
`Strategy` for its entire run. A call reached through a passed-in callable
should honor the same argument-passing convention as a call reached
through a named rule. We redesigned it with the same three-way split as
`.call` (`invokeNameOk`/`Fail`, `invokeParOk`/`Fail`/`ArgFail`,
`invokeSeqOk`/`Fail`/`ArgFail`, `invokeArity`), reusing the existing
`DerivesArgsPar`/`DerivesArgsSeq`/`evalArgsPar`/`evalArgsSeq` as-is — no
new auxiliary relations were needed.

### `CallByValuePar`/`CallByValueSeq` faithfully reproduce a degenerate reference behavior for lambda arguments

Because the reference implementation evaluates a lambda VALUE as a
zero-width match when it's matched directly, passing a lambda as an actual
parameter under `CallByValuePar`/`CallByValueSeq` makes argument evaluation
zero-width-match it too — the consumed substring (empty) is what gets
bound as the value, and **the lambda's actual content vanishes,
indistinguishable from passing an empty string**. This combination has
zero shipped test coverage — it's genuinely undefined, degenerate
behavior.

Rather than invent a smarter new semantics that diverges from the
reference, we chose to faithfully reproduce this degeneration. `.lam` is a
single "unconditional zero-width success" rule, exactly like `.dbg`, and
`evalArgsPar`/`evalArgsSeq` were left completely untouched. If the
resulting degenerate value (`.lit []`) is later "invoked" via
`.callParam`/`.invoke`, it automatically fails under the existing
zero-well-formedness-assumptions discipline (the same treatment an
out-of-range `.param` already gets) — no special-casing was needed at all.

### Extending T0–T3, and smoke tests

Extending the proof files (`Fuel`/`Props`/`Soundness`/`Determinism`/
`Completeness`) was largely mechanical, since each `.invoke` case is nearly
isomorphic to its `.call` counterpart. `invokeParArgFail`/
`invokeSeqArgFail` were designed from the start with the lesson M-PEG-2's
`callParArgFail` learned mid-completeness-proof (the `args = pre ++ badArg
:: post` + explicit `pre`-success-witnessed shape) already baked in, so no
rework was needed this time.

`Examples.lean` gained two smoke tests: a named-rule-reference pattern
(mirroring `Double(Plus1, "aa")` — `Double(f,s) = f(f(s))` doubles `"aa"`
twice into `"aaaaaaaa"`) and a multi-argument lambda-literal pattern
(mirroring `Map2((x,y -> x y x), "a", "b")` — matches `"a" ++ "b" ++ "a"` =
`"aba"`). Both `#guard`s passed on the first try, confirming the
hand-traced derivations were correct.

## 8.7 Lens extraction and the differential harness

Since `mpegRun` is fuel-based structural recursion isomorphic in shape to
`pegRun`, the extractor Lens's equation-lemma route went through as-is,
with no new accommodations needed — except for one snag against the
existing whitelist. Writing the arity check as Prop's `≠` (via
`Decidable`) fails extraction, because `instDecidableNot` isn't registered
in Lens's built-in table. Rewriting it to use Bool's `==` instead, in the
same style as `beqChar`/`leChar`, made it go through — the same pattern
that `.chr`/`.range` already follow (and the same pattern `.invoke`'s
arity check reuses directly).

The differential harness also follows the existing design as-is. The
`shallot-cli macro-dump` subcommand runs the extracted `MacroPeg_mpegRun`
against a single `MacroPeg_mCases` table (holding witnesses for every
strategy and feature together), and `make verify` continuously checks
three-way agreement — Lean-native execution ≡ golden ≡ extracted-Scala
execution — against `corpus/golden/macro_peg.jsonl` (8 `CallByName` cases,
3 `CallByValuePar` cases, 3 `CallByValueSeq` cases, 6 higher-order cases —
20 total). Adding each new feature left the three-way-agreement machinery
itself untouched — a new constructor just means new rows in
`MacroPeg_mCases`.

## 8.8 What was left out of scope this time

- **Closures returned as values, applied elsewhere** (true environment
  capture): a rule call returning a closure as a VALUE, later applied from
  a DIFFERENT call site. This is expressible in the AST, but even in the
  reference implementation it requires `MacroExpander` (an eager
  whole-grammar inlining pass that carries a non-termination risk and
  can't be used with self-recursive rules), and has zero shipped test
  coverage (verified directly in 8.6 — though the "crashes" verdict from
  that verification is corrected in 8.9). Every other way of using higher-
  order functions — invoking a passed-in callable from inside the same
  call tree that received it — is fully formalized in this chapter

## 8.9 One more correction — the closure-return pattern turned out to already be formalized

While scoping the next milestone (M-PEG-5), re-verifying against the
reference implementation overturned what 8.6/8.8 said: that closure-return-
and-reapply "crashes with a `ClassCastException`" without `MacroExpander`.

Evaluating `Baz(f: ?) = f; Apply(f: ?, s: ?) = f(s); S = Apply(Baz((x ->
x)), "a")` directly through `Evaluator` alone via `sbt console` doesn't
crash at all — it returns a clean, deterministic `Failure`. As it turns
out, `Interpreter` never calls `MacroExpander` in the first place (the
commit titled "hide `MacroExpander` inside `Interpreter`" turned out not to
actually call it — another thing this re-verification surfaced).

This is exactly the behavior `.callParam`'s `subst` (`MacroPeg/Syntax.lean`)
already had, by construction: under `CallByName`, whatever gets bound to
`Apply`'s `f` is the unevaluated `.call` expression `Baz(...)`, not a
`.lam` — so `.callParam` falls through to its existing `MExp.failAlways`
fallback. No new constructor, no new proof rule — just a smoke test added
to `Examples.lean`/`Corpus.lean` (corpus ID `335-mpeg-hof-return-reject-a`)
to make the fact machine-checked.

So M-PEG-4 already correctly formalized more ground than we thought. What
genuinely remains unformalized is the case where `MacroExpander`'s eager
whole-grammar inlining actually SUCCEEDS — safe and terminating whenever
the macro-call graph is acyclic — and that's what M-PEG-5 targets.

## 8.10 M-PEG-5 — walking on top of an acyclic graph

`MacroExpander.expandGrammar` is a naive pass: it syntactically inlines
macro calls wherever it finds them. For a non-recursive macro like
`Baz`/`Apply`, that turns `Failure` into `Success` just fine. But for
something as ordinary as `Rec(n: ?) = "a" Rec(n)` — not even
left-recursive, and perfectly well-behaved under normal evaluation — it
inlines itself forever and never terminates. We confirmed a real 60+
second hang against the actual reference implementation. M-PEG-5
formalizes this `expandGrammar` under the well-formedness condition that a
parameterized rule's call graph is acyclic, and proves it always
terminates under that condition.

### Using `rank` directly as the termination measure

Every other function in this project has secured termination the same
simple way: give up once fuel runs out. M-PEG-5 deliberately didn't take
that route. Instead, it uses the "rank" derived from the acyclic graph
itself — for each rule, one more than the highest rank among whatever it
calls, computed via DFS — directly as the `termination_by` measure. The
point was to prove the real claim ("acyclicity genuinely guarantees
termination") word for word, rather than falling back to a safety net
that just bounds how far things unfold.

The centerpiece is `rank_lt_of_acyclic`: in an acyclic graph, if rule `i`
calls rule `j`, then `rank j < rank i`, always. The proof splits into two
monotonicity lemmas. One says more fuel never changes an already-successful
result — `Fuel.lean`'s `mpegRun_mono` is a direct template, low risk. The
other says shrinking the `visiting` set can only help (more successes, and
never a larger value) — this is the project's first piece of genuine graph
theory, with no local precedent, flagged at design time as the single
riskiest item in the whole milestone.

That intuition turned out to be correct, and the proof went through — but
not on the first try, and only after two design pivots. The first: switching
`foldl` to `foldr`, so that `cons` unfolds directly into `max x (xs.foldr
max 0)` — with `foldl`, the proof kept getting tangled in which side the
accumulator landed on. The second: after getting stuck on `List.contains`
lemma names, switching to a hand-rolled `natElem` function in the same
style as `argAt` — written as an `if`-expression, it turned out to play
far better with `simp`/`split`.

As a small side benefit, a quick `#eval` on a diamond-shaped dependency
(`A` calls both `B` and `C`, both of which call `D`) confirmed the
`visiting`-based cycle check doesn't false-positive on it: `D` is reached
independently via two paths (redoing the work, but landing on the same
rank both times) — exactly the right way to tell a shared descendant apart
from a genuine cycle.

### T-fix — substitution preserves call-freedom

We also proved that `expand` genuinely reaches the fixpoint
`MacroExpander` is documented to compute — no calls left anywhere
(`expand_hasCall_eq_false`). Most of that proof was mechanical, but the
`.call i (a::as)` case — where an already-expanded body and already-expanded
actual parameters get joined via `MExp.subst` — demanded a genuinely new
lemma: if both pieces are call-free, so is the substituted result
(`subst_hasCall_eq_false`). We proved it via its own mutual induction,
directly mirroring `MExp.subst`/`substArgs`'s own recursive shape. Mechanical
in the sense that it just retraces existing structure, but a real proof
obligation nonetheless — nothing to skip.

### A Lean 4 rite of passage: `decide` getting stuck

Wherever we needed to actually construct a proof term that a concrete
grammar (`closureReturnGrammar`) is acyclic — to pass to `MExp.expand` —
`by decide` and `by rfl` both got stuck mid-kernel-reduction. Since
`rankGo`/`rankSuccs` compile down to well-founded recursion, the kernel's
`whnf` reduction sometimes can't push all the way through — a reasonably
well-known Lean 4 phenomenon. What's interesting is that `#eval`/`#guard`
(compiled evaluation) have no such trouble at all — the headline `#guard`
below runs just fine. Wherever an actual proof term was unavoidable
(`closureReturnAcyclic` in `Examples.lean`), we drove the computation by
rewriting instead of kernel defeq: `by simp [...]` with every relevant
equation lemma spelled out.

### The headline: `"fail"` becomes `"ok+0"`

One new line landed in `Examples.lean`:

```lean
#guard renderMPeg
  (mpegRun closureReturnGrammar .callByName 200
    (MExp.expand closureReturnGrammar closureReturnAcyclic
      (.call closureReturnApplyIdx
        [.call closureReturnBazIdx [.lam 1 (.param 0)], .lit ['a']]))
    "a".toList) == "ok+0"
```

The exact same expression that stayed `"fail"` throughout M-PEG-4/§8.9 now
evaluates to `"ok+0"` once `expand` runs first. A closure that crosses a
call boundary genuinely works now — that's the substance of this
milestone.

### One more extractor discovery

`expand`/`expandGrammar` themselves extract fine via the equation-lemma
route, but passing a concrete proof term for `acyclicB g = true` as an
argument at a CALL SITE (as `Corpus.lean`'s differential-corpus style would
require) makes the extractor reject it outright: "theorem leaked into
executable code." `Lens/Translate.lean`'s `sigParams` knows how to erase a
Prop parameter from a function's own DEFINITION, but erasing a Prop
argument at a call site isn't implemented yet — a function's own
extractability and its call sites' extractability turned out to be two
separate questions. So the cross-check against the real reference
implementation went through the same technique we'd already leaned on
throughout this project — a one-time `sbt console` verification, run
directly against `MacroExpander.expandGrammar` itself, confirming both that
`Baz`/`Apply` really does become `Success` and that `Rec(n)` really does
hang for 60+ seconds — rather than an automated corpus diff.

---

[← Chapter 7: In practice — building a verified JSON parser](07-json.html) | [Table of contents](index.html)
