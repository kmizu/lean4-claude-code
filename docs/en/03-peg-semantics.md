# 3. The formal semantics of PEG — transcribing Ford's semantics into Lean

**English** | [日本語](../guide/03-peg-semantics.html) | [← Chapter 2](02-lean-primer.html) | [Contents](index.html) | [Chapter 4 →](04-shallot.html)

This chapter is the core of the series. We formalize the PEG formal semantics of
Ford (POPL 2004) as an inductive predicate in Lean, and prove that the fuel-based
interpreter is **sound**, **complete**, and **deterministic** with respect to that
semantics. If you know PEGs, you should be able to read nearly all of the code in this chapter.

## 3.1 Recap: Ford's ⇒ relation

In Ford's paper, for a parsing expression e and an input, whether "e succeeds by
consuming a prefix of the input" or "fails" is defined as a collection of inference
rules. For example, for the prioritized choice e₁/e₂:

- If e₁ succeeds, e₁/e₂ succeeds with e₁'s result
- If e₁ **fails** and e₂ succeeds, it succeeds with e₂'s result
- If both fail, it fails

Unlike choice in a CFG, the second rule **explicitly requires the premise** that
"e₁ failed" — this was the source of PEG's unambiguity. This project's formalization
adds **exactly one extension** to that semantics: the success outcome
**carries the parse tree**.
This is what later turns the determinism theorem into one that includes
uniqueness of the tree (Section 3.5).

## 3.2 The data types: PExp, PTree, Outcome

Parsing expressions are defined as follows (`lean/Shallot/Peg/Syntax.lean`). As we saw
in Chapter 2, read `inductive` as if it were BNF:

```lean
inductive PExp where
  | eps                       -- ε
  | any                       -- any single character
  | chr (c : Char)            -- character literal
  | range (lo hi : Char)      -- character class [lo-hi]
  | lit (s : List Char)       -- string literal (a primitive!)
  | nt (i : Nat)              -- nonterminal (index into the rule table)
  | seq (e₁ e₂ : PExp)        -- sequence
  | alt (e₁ e₂ : PExp)        -- prioritized choice e₁ / e₂
  | star (e : PExp)           -- e* (primitive, faithful to Ford)
  | notP (e : PExp)           -- not-predicate !e
```

Three design decisions are baked in here.

**String literals are primitive.** A formalization that desugars `lit "if"` into the
sequence `chr 'i' ; chr 'f'` is also possible, but then every keyword adds as many
derivation-tree nodes as it has characters. The roundtrip proof later (Chapter 4)
involves a great deal of building derivations for printed text by hand, so keeping
one keyword = one derivation node translates directly into proof cost.

**star is primitive.** One could desugar `e* = e e* / ε`, but Ford's original
semantics has rules for star, so we adopted it faithfully. The nontermination problem
of a star whose body consumes ε is handled naturally on the semantics side, in the
form "no such derivation exists" (Section 3.6).

**Nonterminals are Nat indices.** A grammar is just a list of rules, and out-of-range
indices are given a rule that "fails explicitly". As a result, **well-formedness
assumptions about the grammar vanish from the theorems entirely** — every theorem
holds for every grammar value, with no "for a well-formed grammar…" proviso.

Parse trees and outcomes look like this:

```lean
inductive PTree where
  | leaf (cs : List Char)       -- the characters consumed by eps/any/chr/range/lit
  | nodeNT (i : Nat) (t : PTree)
  | seq (l r : PTree)
  | choiceL (t : PTree)         -- succeeded on the left of an alt
  | choiceR (t : PTree)         -- succeeded on the right of an alt
  | starNil
  | starCons (hd tl : PTree)    -- tl is the tree for the entire rest of the star
  | notT                        -- success of a not-predicate

inductive Outcome where
  | fail
  | ok (t : PTree) (rest : List Char)
```

`PTree` mirrors the shape of `PExp` exactly. The point is that a "node holding a list
of children" (`List PTree`) is **deliberately not used**: in Lean, an inductive type
that contains lists (a nested inductive type) makes the induction machinery abruptly
harder to work with. With the mirror structure, every induction runs smoothly.

Input positions are also represented as "the remaining input" (a suffix of a
`List Char`). Since we never use indices (character offsets), no index arithmetic
appears anywhere in the semantics or the proofs.

## 3.3 Derives: the 26 inference rules

The body of the semantics is a three-argument inductive predicate. `Derives g e input o`
reads "under grammar g, expression e derives outcome o on input input".
Let's look at some representative rules from the actual code (`lean/Shallot/Peg/Semantics.lean`):

```lean
  | chrOk (c d : Char) (rest : List Char) (h : beqChar c d = true) :
      Derives g (.chr c) (d :: rest) (.ok (.leaf [d]) rest)
  | chrFail (c d : Char) (rest : List Char) (h : beqChar c d = false) :
      Derives g (.chr c) (d :: rest) .fail
```

This is exactly the reading table from Chapter 2: the constructor name is the rule
name, the `h : ...` arguments are the premises (above the line), and the return type
is the conclusion (below the line). Taking the **Bool equation** `beqChar c d = true`
as a premise is a proof-engineering choice: when we case-split later, "the true case /
the false case" can be flipped mechanically.

The three rules for prioritized choice are the essence of what makes a PEG a PEG:

```lean
  | altL (e₁ e₂ : PExp) (input rest : List Char) (t : PTree)
      (h : Derives g e₁ input (.ok t rest)) :
      Derives g (.alt e₁ e₂) input (.ok (.choiceL t) rest)
  | altR (e₁ e₂ : PExp) (input rest : List Char) (t : PTree)
      (h₁ : Derives g e₁ input .fail)
      (h₂ : Derives g e₂ input (.ok t rest)) :
      Derives g (.alt e₁ e₂) input (.ok (.choiceR t) rest)
  | altFail (e₁ e₂ : PExp) (input : List Char)
      (h₁ : Derives g e₁ input .fail)
      (h₂ : Derives g e₂ input .fail) :
      Derives g (.alt e₁ e₂) input .fail
```

Look at `altR`. To succeed on the right, you must hand over
**`h₁ : a derivation that e₁ fails`**.
Where CFG choice only asks that "either side succeed", in a PEG a proof of failure is
a premise of success — a property you knew in words from the textbooks appears here
in the physical form of an **argument** to the rule.

star and the not-predicate:

```lean
  | starNil (e : PExp) (input : List Char)
      (h : Derives g e input .fail) :
      Derives g (.star e) input (.ok .starNil input)
  | starCons (e : PExp) (input rest rest' : List Char) (t ts : PTree)
      (h₁ : Derives g e input (.ok t rest))
      (h₂ : Derives g (.star e) rest (.ok ts rest')) :
      Derives g (.star e) input (.ok (.starCons t ts) rest')
  | notOk (e : PExp) (input rest : List Char) (t : PTree)
      (h : Derives g e input (.ok t rest)) :
      Derives g (.notP e) input .fail
  | notFail (e : PExp) (input : List Char)
      (h : Derives g e input .fail) :
      Derives g (.notP e) input (.ok .notT input)
```

star stops only when its body has **failed** (the premise of `starNil`) — greedy and
non-backtracking, exactly the definition of PEG star. `notP` inverts the outcome,
consumes no input (the input in the conclusion is unchanged), and its tree is the
contentless `notT`. This formalizes the intuition that a tree built inside a
not-predicate never leaks out.

## 3.4 The interpreter: pegRun with fuel

The semantics (a Prop) cannot be executed, so we write an executable function
separately (`lean/Shallot/Peg/Interp.lean`). Here are the prioritized-choice and star clauses:

```lean
    | .alt e₁ e₂ =>
      match pegRun g fuel e₁ input with
      | some (.ok t rest) => some (.ok (.choiceL t) rest)
      | some .fail =>
        match pegRun g fuel e₂ input with
        | some (.ok t rest) => some (.ok (.choiceR t) rest)
        | some .fail => some .fail
        | none => none
      | none => none
    | .star e =>
      match pegRun g fuel e input with
      | some (.ok t rest) =>
        match pegRun g fuel (.star e) rest with
        | some (.ok ts rest') => some (.ok (.starCons t ts) rest')
        | some .fail => some .fail -- semantically unreachable (kept for totality)
        | none => none
      | some .fail => some (.ok .starNil input)
      | none => none
```

You can see the 1:1 correspondence with the rules. The return type is
`Option Outcome`, with the strict convention that **"`none` means out of fuel, and
nothing else"**. `some .fail` is a legitimate semantic failure. This three-way
distinction keeps the theorem statements clean
("if it returns `some`, it is correct; about `none` we say nothing").

The star clause has one branch marked with a "semantically unreachable" comment.
A star never fails semantically (`starNeverFails` in Section 3.5), so the branch
where the inner star returns `some .fail` is never actually taken. But Lean functions
must be total, so we write the branch anyway and show on the proof side that this
branch is never reached.

## 3.5 The four theorems

We quote only the statements from the actual code (the proofs are in the files, but
you don't need to read them — if you can read the statement, you can "use" the theorem).

```lean
-- T0: fuel monotonicity
theorem pegRun_mono (h : pegRun g f e x = some o) :
    pegRun g (f + 1) e x = some o

-- T1: soundness — every result the interpreter returns (ok or fail) is derivable
theorem pegRun_sound (h : pegRun g f e x = some o) : Derives g e x o

-- T2: determinism — the derived outcome is unique (parse tree included!)
theorem derives_det (h₁ : Derives g e x o₁) (h₂ : Derives g e x o₂) : o₁ = o₂

-- T3: completeness — if a derivation exists, some amount of fuel computes it
theorem pegRun_complete (h : Derives g e x o) : ∃ f, pegRun g f e x = some o
```

(The numbering follows the project's theorem index [theorems.md](../theorems.html)
*(Japanese)*. Some of the source files' header comments still carry an older
numbering, but the content is identical.)

Taken together, the three say that `pegRun` is a complete implementation of `Derives` —
`pegRun g f e x = some o` ↔ `Derives g e x o` (→ is T1, ← is T3, and the fact that
the results cannot disagree is T2). There is no gap between the interpreter and the semantics.

Note that **T2 includes uniqueness of the tree**. Since `Outcome.ok` carries the
parse tree, "the outcomes are equal" means "both the amount consumed and the tree are
equal". PEGs are often said to be unambiguous; in this formulation, that fact is
folded into the single equation `o₁ = o₂`. It is an example of a design decision
(stacking the tree onto the outcome) making a theorem cheap.
Incidentally, T2 is proved **without using any axioms at all** (the output of
`#print axioms` is "does not depend on any axioms" — see Chapter 2).

Just to give a feel for the proofs, here is the shortest theorem in the project:

```lean
/-- A star never fails: the only `Derives` rules concluding at a `.star`
expression are `starNil` and `starCons`, and both produce `.ok`. -/
theorem starNeverFails {g : Grammar} {e : PExp} {input : List Char} {o : Outcome}
    (h : Derives g (.star e) input o) : o ≠ .fail := by
  intro hf
  subst hf
  cases h
```

"Assume a derivation for a star (h), and assume the outcome is fail (intro hf,
subst hf); the only rules whose conclusion is a star are starNil and starCons, and
both produce ok, so the case split producing fail is **empty** (cases h closes every
case)." Three lines.
Case analysis on an inductive predicate is work where the machine checks the table
of rules for you.

## 3.6 Honest scope: left recursion and totality

T3 says "if **a derivation exists**, it can be computed" — not "every grammar
terminates". This is a point worth writing down honestly.

Consider a left-recursive grammar (e.g., rule 0 refers to `nt 0` itself at its head).
No combination of `Derives` rules can build a finite derivation tree — the premise of
`ntOk` demands a derivation of the same `nt 0` again, regressing infinitely.
In other words, **no derivation exists**. In that case the interpreter exhausts its
fuel and returns `none`, but that contradicts none of the claims T1–T3
(all three theorems speak only about the `some` case).

TRX (an earlier formalization of PEG in Coq) took the route of formalizing a
well-formedness analysis and proving totality as well; this project instead chose the
lightweight formulation of "fuel + completeness relative to derivation existence".
The Section 3.2 property — all theorems hold without any grammar well-formedness
assumption — is a benefit of this choice. For anyone who wants to formalize
left-recursion support (such as Warth et al.'s packrat extension), this `Derives`
should be just the right starting point.

## Takeaway from this chapter

**The single design move of carrying the parse tree in the outcome is what made the
determinism theorem include uniqueness of the tree.** How you write the specification
(the design of the data types) determines the strength of the later theorems and the
cost of their proofs. Formalization is also a design contest fought before any proof
is written.

---

[← Chapter 2: A minimal Lean 4 primer](02-lean-primer.html) | [Contents](index.html) | [Chapter 4: The Shallot language →](04-shallot.html)
