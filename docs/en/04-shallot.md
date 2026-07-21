# 4. The Shallot language — a proof stack of typechecker, interpreter, and compiler

**English** | [日本語](../guide/04-shallot.html) | [← Chapter 3](03-peg-semantics.html) | [Table of Contents](index.html) | [Chapter 5 →](05-lens.html)

The PEG framework of Chapter 3 was a general-purpose component. In this chapter
we look at how the proofs of a typechecker, an interpreter, and a compiler
stack up on top of **Shallot**, a small language defined with it. We end with
the story of how the roundtrip proof struck a **real hole in the grammar** —
the climax of this series.

## 4.1 A 15-second tour of the language

Shallot is a first-order functional language with nothing but int and bool.
Its concrete syntax looks like this (`examples/fact.shl`):

```
def fact ( n : int ) : int = if n <= 0 then 1 else n * fact ( n - 1 )
fact ( 10 )
```

The grammar is defined as **data**. It is just a matter of assembling values of
Chapter 3's `PExp` (`lean/Shallot/Syntax/Grammar.lean`):

```lean
/-- Keyword: literal + not-followed-by-identifier-char + spacing. -/
def kw (s : String) : PExp :=
  .seq (.lit s.toList) (.seq (.notP idContP) (.nt NT.spacing))

/-- `'=' !'='` then spacing (assignment, not equality). -/
def eqTok : PExp := .seq (.chr '=') (.seq (.notP (.chr '=')) (.nt NT.spacing))

/-- Left-associative operator tier: `Sub (op Sub)*`. -/
def tier (sub : Nat) (ops : PExp) : PExp :=
  .seq (.nt sub) (.star (.seq ops (.nt sub)))
```

`kw` uses negative lookahead to guarantee that a keyword is not immediately
followed by an identifier character (distinguishing `if` from `iffy`), and
`eqTok` sidesteps the collision between `=` and `==` with `!'='` —
idioms every PEG user knows by heart, here turned directly into values. And
because **the parser simply feeds this grammar value to the verified `pegRun`
of Chapter 3**, the soundness, completeness, and determinism theorems apply to
Shallot's parser automatically.

## 4.2 The typechecker: sound *and* complete

The type system is defined in two layers. The **specification** is the
inductive predicate `HasType` (inference rules, read exactly as in Chapter 3);
the **implementation** is `typecheck`, a recursive function returning `Except`.
And the agreement between the two is proved in both directions:

```lean
-- L1 soundness: if the checker says ok, the typing relation really holds
theorem typecheck_sound : typecheck S Γ e = .ok τ → HasType S Γ e τ

-- L2 completeness: if the typing relation holds, the checker always says ok
theorem typecheck_complete : HasType S Γ e τ → typecheck S Γ e = .ok τ
```

Soundness alone leaves room for the checker to be overly cautious (rejecting a
correct program does not break soundness). Only once completeness is added can
we say the checker agrees with the specification exactly, no more and no less.
If an implementation bug accidentally makes it stricter or looser, one of the
two theorems breaks and the bug is detected — write the specification and the
implementation separately, then stitch them together in both directions:
this is the basic pattern of verification.

## 4.3 Type soundness: proving the absence of "runtime type errors"

The interpreter is a fuel-based evaluator with a three-valued convention
(success / semantic error / out of fuel). Its errors comprise the stuck class,
such as `stuckType` (an operation on mismatched types) and `stuckUnbound` (an
unbound variable), plus `divByZero`. Type soundness is stated as follows
(`lean/Shallot/Lang/TypeSound.lean`):

```lean
/-- **L5** — TYPE SOUNDNESS. A well-typed expression of a well-typed
program cannot get stuck: every defined interpreter outcome is either the
allowed `divByZero` error or a value of the expression's static type. -/
theorem eval_sound
    (hwt : WTProg p) (ht : HasType (p.funs.map FunDef.sig) Γ e τ)
    (henv : EnvTy env Γ) (h : eval (mkFunTable p.funs) fuel env e = some r) :
    (∃ er, r = .error er ∧ okErr er) ∨ (∃ v, r = .ok v ∧ ValHasTy v τ)
```

In plain language: "the result of evaluating a well-typed program is either
divByZero or **a value of the static type** — nothing else." Not a single
stuck-class error appears — and its not appearing is a **theorem**. Not "no
error came up in testing," but "no execution that errors can exist." The
raison d'être of a type system, compressed into a single claim — a classic of
PL theory, implemented right here.

## 4.4 Compiler correctness

Shallot also has a compiler to a stack VM. The compiler itself is
straightforward (`lean/Shallot/Vm/Compile.lean`, excerpt):

```lean
mutual
  def compileExpr (σ : List String) : Expr → List Instr
    | .intLit n => [.pushI n]
    | .var x =>
      match idxOf σ x with
      | some i => [.load i]
      | none => [.crash]
    | .binop op l r => compileExpr σ l ++ compileExpr σ r ++ [.binop op]
    | .ite c t e =>
      compileExpr σ c ++ [.branch (compileExpr σ t) (compileExpr σ e)]
    | .letE x bound body =>
      compileExpr σ bound ++ [.bind] ++ compileExpr (x :: σ) body ++ [.unbind]
    | .call f args => compileArgs σ args ++ [.call f (countArgs args)]
  ...
end
```

The correctness statement could not be simpler (`lean/Shallot/Vm/Correct.lean`):

```lean
/-- **V2** — whole-program compiler correctness: if the interpreter runs
the program to a value, the compiled program runs to the SAME value. -/
theorem compile_correct (h : runProgram p fuel = some (.ok v)) :
    ∃ fuel', vmRunProgram p fuel' = some (.ok v)
```

"A program that the interpreter runs to a value v computes the same v when
compiled and run on the VM." The heart of the proof is a **forward
simulation**: the invariant is an index-by-index correspondence between the
compile-time variable environment σ and the runtime locals, threaded along
the structure of the expression.

What makes it interesting as proof engineering is that the simulation lemma is
set up in **continuation-passing style (CPS)**:

```lean
theorem compile_sim_cont ... :
    eval (mkFunTable funs) f env e = some (.ok v) →
    EnvMatch env σ locals →
    vmRun (mkCodeTable funs) fr rest (v :: stack) locals = some (.ok out) →
    ∃ f', vmRun (mkCodeTable funs) f' (compileExpr σ e ++ rest) stack locals
      = some (.ok out)
```

"If the **code rest that follows** e's code reaches the final result out from
a stack with the result value pushed on it, then the whole of
`compileExpr σ e ++ rest` reaches the same out." Why this roundabout shape?
Because the naive lemma — "concatenation of code is concatenation of
executions" — in fact **does not hold**: the `bind`/`unbind` instructions
rewrite the locals, so there is not enough information to hand the state of
the locals after the first half over to the second. The agent writing the
proof discovered this counterexample (`c₁ = [bind]`) and restructured the
lemma into CPS form. The continuation runs with **the same locals** — because
in the compiler's output, bind and unbind always come in pairs. A fine example
of the compiler's discipline determining the shape of the proof.

## 4.5 Roundtrip, and how a hole was found in the specification

The final piece is **roundtrip**: "print an AST in canonical form, read it
back with the verified parser, and the original AST comes back." Printing is a
mechanical canonical form — one space after every token, full parentheses
around every compound expression. The theorem is stated as follows
(`lean/Shallot/Syntax/Roundtrip.lean`):

```lean
theorem parse_print (p : Program) (hp : printableProgB p = true) :
    ∃ fuel, ∀ fuel', fuel ≤ fuel' → parseShallot fuel' (printProgram p) = .ok p
```

The hypothesis `printableProgB` characterizes "canonically printable
programs," with conditions such as identifiers being valid (not keywords, and
so on). So far, all as expected. But partway through the proof, it emerged
that **unless one more condition is added to this hypothesis, the theorem is
false**. Quoting from the comment at the head of the file:

> when the LAST function's body is a bare variable and `main`'s canonical
> text starts with `'('`, the PEG's prioritized `Call / Ident` choice
> extends the body across the boundary (`… = x ( 1 + 2 ) ` parses
> `x ( 1 + 2 )` as a call, and the program parse then FAILS at EOF).
> Checked empirically:
> `parseShallot _ "def f ( ) : int = x ( 1 + 2 ) " = .error .syntaxErr`.

That is: when the last function's body is the **bare variable** `x` and the
following main expression begins with `(`, then `x ( 1 + 2 )` reads as a
function call **across the function boundary** between `x` and `( 1 + 2 )` —
because the PEG's prioritized choice `Call / Ident` greedily tries Call first.
Having consumed it as a call, the parse of the whole program then collapses
at EOF.

This shape can even be produced well-typed (`def id ( a : int ) : int = a`
with a parenthesized main). And **the project's 60 differential test cases had
never once stepped on it**. What found it was not a test but the proof — the
roundtrip induction refused to go through on this case, and digging into why
produced a counterexample that reproduces on the real parser. As the fix, one
separation-guard condition was added to the hypothesis:

```lean
/-- The separation guard: the LAST function's body must not be a bare
variable when `main` prints `'('`-headed. -/
def sepOkB : List FunDef → Expr → Bool
  | [], _ => true
  | [d], m => !(bareVarB d.body && parenHeadB m)
  | _ :: ds, m => sepOkB ds m
```

The guard is not a weakening for the proof's convenience; it is a **precise
characterization of a condition that genuinely exists at the boundary between
the printer and the grammar** (that every other boundary is safe is,
conversely, guaranteed by the proof). "Formal verification finds the holes in
your specification" is a well-worn saying — but that it happened through PEG's
prioritized choice, the mechanism most familiar to this readership, was the
single greatest payoff of this project.

## 4.6 Everything in one theorem: pipeline_correct

The closing theorem is the composition of every layer so far:

```lean
theorem pipeline_correct (p : Program) (τ : Ty) (v : Value) (fuel : Nat)
    (hp : printableProgB p = true)
    (hc : checkProgram p = .ok τ)
    (hr : runProgram p fuel = some (.ok v)) :
    ∃ pf, (∀ pf', pf ≤ pf' → parseShallot pf' (printProgram p) = .ok p) ∧
      WTProg p ∧ ValHasTy v τ ∧ ∃ vmf, vmRunProgram p vmf = some (.ok v)
```

The canonically printed text parses back through the verified parser to
**exactly p**; p is well-typed in the sense of the typing relation; the
evaluation result v conforms to the static type τ; and the compiled VM
computes **the same v**. The theorems for the parser, the typechecker, the
interpreter, and the compiler each flow into one composite theorem — this is
the final form of "a complete specification, a program satisfying it, and the
proofs, as one package."

## This chapter's takeaway

**Where the proof got stuck was exactly where the specification's bug lived.**
Digging into the one case where the roundtrip induction would not go through
turned up a PEG boundary condition that 60 differential tests had missed.
Verification is not the business of stamping approvals — it is an engine that
exhaustively searches out discrepancies between specification and
implementation.

---

[← Chapter 3: PEG formal semantics](03-peg-semantics.html) | [Table of Contents](index.html) | [Chapter 5: The Lens extractor →](05-lens.html)
