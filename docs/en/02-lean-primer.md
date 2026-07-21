# 2. A minimal Lean 4 primer — theorem proving for BNF people

**English** | [日本語](../guide/02-lean-primer.html) | [← Chapter 1](01-intro.html) | [Table of contents](index.html) | [Chapter 3 →](03-peg-semantics.html)

This chapter introduces the bare minimum of Lean 4 you need to *read* this
project's code. You do not need to learn to write Lean. **If you can read BNF,
you can read this project's type definitions; if you can read inference rules,
you can read its semantics** — confirming that is the goal of this chapter.

## 2.1 `inductive` is BNF

Lean's `inductive` (an inductive type) defines a data type. To a parser
person's eye, it should look like this:

```
PExp ::= eps | any | chr Char | range Char Char | lit String
       | nt Nat | seq PExp PExp | alt PExp PExp | star PExp | notP PExp
```

Written in Lean, it becomes (excerpted from `lean/Shallot/Peg/Syntax.lean`):

```lean
inductive PExp where
  | eps
  | any
  | chr (c : Char)
  | range (lo hi : Char)
  | lit (s : List Char)
  | nt (i : Nat)
  | seq (e₁ e₂ : PExp)
  | alt (e₁ e₂ : PExp)
  | star (e : PExp)
  | notP (e : PExp)
```

Alternatives are separated by `|`, and each alternative (called a
**constructor**) can take arguments. It is BNF, exactly. `seq` taking `PExp`
itself as an argument — a recursive grammar definition — can be written just as
directly. As a tool for defining ASTs, you can safely think of it as the
algebraic data types of ML-family languages.

## 2.2 `def` + `match` is a recursive-descent function

Functions are defined with `def`; case analysis is done with `match` (or with
top-level pattern clauses). Take the "prefix match" function everyone has
written at least once:

```lean
/-- `stripPrefix? s input = some rest` iff `input = s ++ rest`. -/
def stripPrefix? : List Char → List Char → Option (List Char)
  | [], rest => some rest
  | _ :: _, [] => none
  | c :: cs, d :: ds => if beqChar c d then stripPrefix? cs ds else none
```

`Option` is the type of computations that may fail: `some x` is success, `none`
is failure. Same as Haskell's `Maybe` and Rust's `Option`. The three clauses
read "if the pattern is empty, return the whole remainder / if the input runs
out, fail / if the heads match, recurse". A building block of a
recursive-descent parser, plain and simple.

One Lean-specific caveat: **every Lean function must terminate**. In
`stripPrefix?`, the list argument gets structurally smaller on every recursive
call, so Lean accepts termination automatically. Where this becomes a problem
is Section 2.4.

## 2.3 `inductive ... Prop` is an inference rule

This is the crux of the chapter. In Lean, **propositions** (Prop) can also be
defined inductively — and that is the tool for writing the inference rules of
an operational semantics. Here is a sneak preview of the opening of `Derives`,
the protagonist of Chapter 3:

```lean
inductive Derives (g : Grammar) : PExp → List Char → Outcome → Prop where
  | eps (input : List Char) :
      Derives g .eps input (.ok (.leaf []) input)
  | anyOk (c : Char) (rest : List Char) :
      Derives g .any (c :: rest) (.ok (.leaf [c]) rest)
  | anyFail :
      Derives g .any [] .fail
```

The reading table:

| Inference rule in the paper | Lean inductive predicate |
|---|---|
| Rule name | Constructor name (`eps`, `anyOk`, …) |
| **Above** the line (premises) | Constructor arguments (those of the form `h : ...`) |
| **Below** the line (conclusion) | Constructor return type |
| "A derivation tree exists" | A value of this type can be constructed |

Written paper-style, `anyOk` reads "(no premises) ───── any consumes c from
c::rest and succeeds". Rules with premises show up in numbers in Chapter 3, but
they read the same way.

**The same tool you write grammars with (inductive) writes the semantics** —
that is the pleasure of Lean. And the rules you write are not decoration: a
"derivation tree" can be constructed and taken apart as a value in your
program, and the machine checks your case analysis for exhaustiveness.

## 2.4 Fuel-based recursion — not a hack but a three-valued semantics

A PEG interpreter does not terminate when handed a left-recursive grammar. But
Lean functions must terminate. How do you resolve the tension? The answer is
**fuel**:

```lean
def pegRun (g : Grammar) : Nat → PExp → List Char → Option Outcome
  | 0, _, _ => none
  | fuel + 1, e, input => ...  -- every recursive call consumes fuel
```

Add one natural-number argument and decrement it on every recursive call; now
all recursion terminates structurally. Think of it as "execution with an upper
bound on the step count".

If that struck you as "a hack that cheats around termination", this is exactly
the point worth stressing: in this project, fuel is taken seriously as a
**three-valued semantics**. The convention in `pegRun`'s file header:

> `none` means "out of fuel" and NOTHING else; `some .fail` is a legitimate
> semantic outcome.

That is, the return value is three-valued — success `some (.ok ...)`, semantic
failure `some .fail`, out of fuel `none` — and **failure and fuel exhaustion
are distinguished at the type level**. Thanks to this distinction, the theorem
statements stay clean: soundness says "if it returned `some`, the result is
right"; completeness says "if a derivation exists, then **with enough fuel** it
returns `some`". Fuel is existentially quantified (∃ fuel) inside the theorems,
backed by a "monotonicity theorem" (adding fuel never changes the result).
Chapter 3 shows the real thing.

## 2.5 `theorem`, `sorry`, and the axiom audit

A **theorem** is a special kind of definition whose type is a proposition and
whose value is its proof:

```lean
theorem pegRun_sound (h : pegRun g f e x = some o) : Derives g e x o := by
  ...
```

You can read it as a function that, from the hypothesis `h` that "`pegRun`
returned `some o`", builds "a derivation of `Derives g e x o` exists" (proofs
= programs). What follows `by` is a proof script written in so-called tactics,
but **readers never need to read the proof body**. If you can read the
statement (the type), you know everything the theorem guarantees. Once Lean
accepts it, the proof is correct — that is the point of using a proof
assistant.

There are, however, two ways to "cheat" that you should know about.

**`sorry`**: Lean has a placeholder that means "I'll write this proof later".
Write `sorry` and any proposition compiles as "proven" — a terrifying thing: a
TODO comment that passes the type checker. That is why "zero sorry" is the
baseline for any verification project, and in this repository a CI-grade script
rejects any `sorry` in the sources.

**Axioms**: eliminating `sorry` means nothing if you have assumed arbitrary
axioms. In Lean you can mechanically query, for any theorem, the list of axioms
it depends on. This repository's `lean/Audit.lean` turns that into a
**snapshot test**:

```lean
/-- info: 'Shallot.derives_det' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.derives_det
```

`#print axioms` prints the theorem's axiom dependencies, and `#guard_msgs`
checks that the output matches this comment character for character. If they
differ, **the build fails**. In other words, `lake build` (Lean's build
command) passing means the axiom dependencies of every theorem are exactly as
declared. Say that the idea of CI snapshot tests has been carried straight into
the world of proofs, and it should click for any engineer.

For the record, Lean's standard axioms are three — `propext`,
`Classical.choice`, and `Quot.sound` — the "standard equipment" of ordinary
mathematics (they demand no extra trust). Every theorem in this project stays
within those three, and `derives_det` above (PEG determinism) is proven with
**zero axioms**.

## 2.6 This is all you need to read the code

To sum up, the vocabulary you need to read this project's code:

- `inductive` = BNF / algebraic data type
- `inductive ... Prop` = a bundle of inference rules. Constructor arguments are
  the premises, the return type is the conclusion
- `def` + pattern clauses = an ordinary function. Totality is mandatory; when
  it gets dicey, fuel
- `Option`/`Except` = computations that can fail (`none` in this project always
  means out of fuel)
- `theorem` = read only the statement (the type). The proof body is a footnote
  for the machine
- zero `sorry` + axiom audit = a mechanical guarantee that nobody cheated

From the next chapter on, we read the formal semantics of PEGs with just this
vocabulary.

---

[← Chapter 1: Introduction — what "correct" means for a parser](01-intro.html) | [Table of contents](index.html) | [Chapter 3: PEG formal semantics — transcribing Ford's semantics into Lean →](03-peg-semantics.html)
