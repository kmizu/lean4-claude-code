# 5. The Lens extractor — carrying proven Lean code into Scala 3

**English** | [日本語](../guide/05-lens.html) | [← Ch. 4](04-shallot.html) | [TOC](index.html) | [Ch. 6 →](06-reading-guide.html)

The proofs live entirely inside Lean. But if you want to use the proven parser
in a JVM product, it has to be carried outside of Lean. Lens is a home-grown
extractor that translates the executable part of Shallot into Scala 3.
Coq → OCaml extraction is well known, but **we could find no prior example of a
Lean → Scala/JVM extractor**. This chapter is about how it works, and about
drawing an honest line around "how far can this be trusted."

## 5.1 Why this is not trivial

You might think: "isn't it just a syntactic transformation of Lean function
definitions?" The problem is that what Lean stores is **not the code you
wrote**. To put it in parser-writer terms: this is less like re-printing the
source and more like **recovering the original code from a compiled
intermediate representation**.

Concretely, once a recursive Lean function goes through elaboration
(desugaring and type inference), pattern matches turn into auxiliary functions
(matchers), structural recursion into a recursor called `brecOn`, and
well-founded recursion into a fixpoint combinator called `WellFounded.fix`.
Decompiling readable recursive functions back out of that is grueling work.

## 5.2 The equation-lemma route

Lens's solution is to use the **equation lemmas** from Lean's internal
compiler API (from the header of `lean/Lens/Equations.lean`):

> `Lean.Meta.getEqnsFor?` returns, for structural/well-founded recursion AND
> top-level pattern-matching definitions, one theorem per source alternative
> of the form `∀ vars, f p₁ … pₙ = rhs` — crucially with **direct** recursive
> calls in the RHS (no `brecOn`/`WellFounded.fix` decompilation needed).

In other words, Lean itself hands you a family of theorems saying "under this
pattern, this function equals this right-hand side" — **with the recursive
calls still in direct-call form**. The extractor reads the patterns off the
left-hand side of each equation and the body off the right-hand side, and
reconstructs a Scala `match`. Decompiling `brecOn` becomes entirely
unnecessary.

Look at the before / after. The Lean side (`lean/Shallot/Demo.lean`):

```lean
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def gcd (a b : Nat) : Nat :=
  if a = 0 then b else gcd (b % a) a
termination_by a
```

The generated Scala (`scala/generated/.../Shallot.scala`, reproduced character
for character):

```scala
def fib(x0: BigInt): BigInt =
  (x0 match {
    case _g0 if _g0 == BigInt(0) => BigInt(0)
    case _g0 if _g0 == BigInt(1) => BigInt(1)
    case _g0 if _g0 >= 2 => { val n = _g0 - 2; (fib((n + BigInt(1))) + fib(n)) }
  })

@annotation.tailrec
def gcd(a: BigInt, b: BigInt): BigInt =
  (if (a == BigInt(0)) then b else gcd(RT.natMod(b, a), a))
```

A Peano-number pattern like `n + 2` lowers to a guarded case (`_g0 >= 2` plus
`val n = _g0 - 2`), the well-founded-recursive gcd comes out still as **direct
recursion**, and on top of that, tail-recursion detection has attached
`@annotation.tailrec` (the Scala compiler verifies this annotation, so if the
detection were wrong the compile would fail — fail-loud here too).

## 5.3 The hand-audited zone: Builtins

Saying "map `Nat` onto `BigInt`" is easy, but the semantic details hide
landmines. From the header of `lean/Lens/Builtins.lean`:

> Maps a *minimal* whitelist of Lean core constants onto Scala equivalents.
> - `Nat` subtraction truncates; `Nat`/`Int` division/modulo by zero = 0 / identity
> - `Int` default `/`, `%` are **Euclidean** (`ediv`/`emod`) — remainder is
>   always non-negative. Scala `BigInt` `/`/`%` are T-division, so these go
>   through `RT.intDiv`/`RT.intMod`.

Lean's `Nat` subtraction is truncating at 0 (`3 - 5 = 0`), division by zero
yields 0, and Lean's `Int` `/` and `%` are **Euclidean division** (the
remainder is always non-negative; `(-7) / 2 = -4`). Scala's `BigInt` is
T-division (`-7 / 2 = -3`), so mapping straight onto `/` would give you **a
wrong program under a correct proof**. These correspondences are quarantined
in a small whitelist-style table and pinned down empirically (by
cross-checking against Lean's `#eval`). That table is the zone a human is
meant to read and audit.

## 5.4 The TCB — where proof ends and trust begins

Let me state it plainly: **the extractor is not verified.** What the theorems
guarantee is the semantics inside Lean; there is, logically, no guarantee
that the generated Scala is correct. What must be trusted (the Trusted
Computing Base) is:

- the Lean kernel (the proof checker)
- **the Lens extractor itself**
- the hand-written Scala runtime (`shallot.rt`, about 550 lines — including
  `RT.intDiv` above)
- the Scala compiler and the JVM

Even CompCert (the verified C compiler) keeps its printer and assembler in
the TCB. The honesty of a verification project lies not in saying "we proved
everything" but in **making explicit the line between what is proven and what
is trusted**.

## 5.5 Building the bridge anyway: the differential harness

Where there is no logical guarantee, we aim the strongest empirical checking
we can. The heart of the mechanism is that **the table of test cases itself
is defined exactly once, in Lean, and extracted**
(`lean/Shallot/Corpus.lean`):

```lean
def cases : List (String × String) :=
  [ ("000-nat-sub-underflow", renderNat (clampSub 3 5)),
    ("004-bigint-fact25",     renderNat (fact 25)),
    ("006-fib-20",            renderNat (fib 20)),
    ...
```

The Lean-side runner evaluates this table **natively**, and the Scala-side
CLI evaluates **the same table, extracted**. The two outputs (60 cases of
JSONL) are matched against each other:

```json
{"case":"000-nat-sub-underflow","phase":"eval","status":"ok","result":"0"}
{"case":"004-bigint-fact25","phase":"eval","status":"ok","result":"15511210043330985984000000"}
{"case":"006-fib-20","phase":"eval","status":"ok","result":"6765"}
```

Because the case definitions are a single source, the classic
differential-testing mishap — "the table had drifted out of sync with the
Lean side" — cannot happen. Even the stringification of results is shared,
through a renderer written in Lean and extracted, so **renderer bugs and
extractor bugs alike all surface in the diff**. In fact, a variable-capture
bug in the extractor found during development by adversarial review (the
nasty kind: a function that returns 42 in Lean returned 0 in Scala) is
preserved forever in the corpus along with its reproduction case, and keeps
watching for regressions.

## Takeaway from this chapter

**The "proven" guarantee stops at the extraction boundary. So make the
boundary explicit, and run the identical definitions on both sides of it and
match the results.** Not hiding the seam in the guarantee, and aiming the
strongest empirical checks at that seam — only when both are in place can you
proudly say you "carried a verified X into a practical language."

---

[← Ch. 4 The Shallot language](04-shallot.html) | [TOC](index.html) | [Ch. 6 A reading guide →](06-reading-guide.html)
