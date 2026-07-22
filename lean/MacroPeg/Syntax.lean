import Shallot.Peg.Syntax

/-!
# Macro PEG syntax, parse trees, outcomes

Formalizes two of kmizu/macro_peg's three `Evaluator` strategies (M-PEG-2
adds `CallByValuePar` to M-PEG's `CallByName`; see `Strategy` below and
`MacroPeg/Semantics.lean`'s module docstring for the `.call` semantics each
one gets): PEG extended with parametrized, recursive rules. Under
`CallByName` the actual parameters are spliced into the callee's body as
UNEVALUATED expressions (true macro substitution); under `CallByValuePar`
they are evaluated independently against the SAME starting position (a
lookahead/backreference-style extraction that does not advance the input)
before splicing in the consumed substrings as literal values.
`CallByValueSeq` and the separate `MacroExpander`-based higher-order/lambda
layer remain out of scope — see docs/roadmap.md.

Design, continuing `Shallot.Peg`'s conventions (`Shallot/Peg/Syntax.lean`):
- rules are `Nat`-indexed (`MGrammar.rules : List MRule`), never named — no
  `Symbol`/`Map` anywhere
- a formal parameter is a de Bruijn-style `Nat` index into "the current rule
  activation's argument list" (`.param k`). Because macro_peg rule bodies
  never nest (no lambdas in this scope), ONE de Bruijn level is enough — no
  environment stack, no name, hence no risk of capture. This is what lets
  `MExp.subst` be a plain capture-free structural substitution, in contrast
  to the reference Scala `Evaluator`'s `extract()`, a hand-rolled hygiene
  routine needed there specifically because it binds parameters by name in a
  flat `Map[Symbol, Expression]` shared with rule names.
- zero well-formedness assumptions: a missing rule index, an arity mismatch,
  or an out-of-range `.param` reference all resolve to an explicit failure
  (`.notP .eps`, an always-fail expression built from existing constructors —
  no new AST leaf needed) rather than a side hypothesis. Mirrors `ntMissing`
  in `Shallot/Peg/Semantics.lean`.
- `MTree` mirrors `MExp` structure and carries only ONE child tree per
  `call` node (the substituted body's tree) — call-by-name never derives the
  actual-parameter expressions independently, only wherever `.param`
  occurrences land inside the (substituted) body, so there is nothing else to
  record.
- monomorphic list helpers only (own `argAt`, no `List.getD`/`List.map`),
  matching `ruleAt`/`stripPrefix?` in `Shallot/Peg/Syntax.lean` — keeps the
  extractable subset uniform with the rest of the project.
-/

namespace Shallot.MacroPeg

/-- Which of `Evaluator`'s argument-passing strategies a derivation/run is
under. `callByValueSeq` (sequential input-threading evaluation of actual
parameters) is not yet formalized — a future milestone, see
docs/roadmap.md — so it has no constructor here (an unhandled case is worse
than a missing one). -/
inductive Strategy where
  | callByName
  | callByValuePar
  deriving DecidableEq

inductive MExp where
  /-- ε — always succeeds, consumes nothing. -/
  | eps
  /-- `.` — any single character. -/
  | any
  /-- A single character literal. -/
  | chr (c : Char)
  /-- Character class `[lo-hi]` (inclusive, by codepoint). -/
  | range (lo hi : Char)
  /-- A literal string. -/
  | lit (s : List Char)
  /-- Reference to the k-th actual parameter of the CURRENT rule activation
  (de Bruijn-style; always eliminated by `subst` at the nearest enclosing
  `call`). -/
  | param (k : Nat)
  /-- Call rule `i` with actual-parameter expressions `args`, spliced in
  UNEVALUATED (call-by-name). A 0-arity rule is `call i []`. -/
  | call (i : Nat) (args : List MExp)
  | seq (e₁ e₂ : MExp)
  /-- Prioritized choice `e₁ / e₂`. -/
  | alt (e₁ e₂ : MExp)
  /-- Ford-primitive `e*` (greedy, never fails). -/
  | star (e : MExp)
  /-- Not-predicate `!e` — consumes nothing. -/
  | notP (e : MExp)
  /-- `Debug(e)` — unconditional success, consumes nothing; `e` is NOT
  evaluated (matches the reference `Evaluator`'s no-op: `Debug` is a
  development-time marker with no semantic effect on matching). -/
  | dbg (e : MExp)

/-- And-predicate `&e := !!e`. -/
def MExp.andP (e : MExp) : MExp := .notP (.notP e)

/-- Option `e? := e / ε`. -/
def MExp.opt (e : MExp) : MExp := .alt e .eps

/-- One-or-more `e+ := e e*`. -/
def MExp.plus (e : MExp) : MExp := .seq e (.star e)

/-- The canonical always-fail expression (no dedicated AST leaf needed). -/
def MExp.failAlways : MExp := .notP .eps

structure MRule where
  arity : Nat
  body : MExp

structure MGrammar where
  rules : List MRule

/-- Monomorphic rule lookup (mirrors `Shallot.ruleAt`). -/
def ruleAtM : List MRule → Nat → Option MRule
  | [], _ => none
  | r :: _, 0 => some r
  | _ :: rs, n + 1 => ruleAtM rs n

/-- Monomorphic actual-parameter lookup (mirrors `Shallot.ruleAt`). -/
def argAt : List MExp → Nat → Option MExp
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => argAt as n

/-! Substitute a rule activation's actual parameters into its (or a nested
call's) body. Structural, capture-free — see the module docstring. An
out-of-range `.param k` (a malformed static rule, arity-checked at `call`
sites so this cannot arise from a well-typed program) resolves to
`MExp.failAlways`, continuing the zero-well-formedness-assumption discipline
instead of requiring a side hypothesis. -/
mutual
  def MExp.subst (args : List MExp) : MExp → MExp
    | .eps => .eps
    | .any => .any
    | .chr c => .chr c
    | .range lo hi => .range lo hi
    | .lit s => .lit s
    | .param k =>
      match argAt args k with
      | some a => a
      | none => MExp.failAlways
    | .call i margs => .call i (MExp.substArgs args margs)
    | .seq e₁ e₂ => .seq (MExp.subst args e₁) (MExp.subst args e₂)
    | .alt e₁ e₂ => .alt (MExp.subst args e₁) (MExp.subst args e₂)
    | .star e => .star (MExp.subst args e)
    | .notP e => .notP (MExp.subst args e)
    | .dbg e => .dbg (MExp.subst args e)

  /-- `subst` mapped over an actual-parameter list (own recursion, not
  `List.map`, per the monomorphic-helpers discipline). -/
  def MExp.substArgs (args : List MExp) : List MExp → List MExp
    | [] => []
    | e :: es => MExp.subst args e :: MExp.substArgs args es
end

/-- Parse trees, mirroring `MExp` structure. A `call` node carries only the
substituted body's tree — call-by-name never derives the actual-parameter
expressions on their own. -/
inductive MTree where
  | leaf (cs : List Char)
  | nodeCall (i : Nat) (t : MTree)
  | seq (l r : MTree)
  | choiceL (t : MTree)
  | choiceR (t : MTree)
  | starNil
  /-- `tl` is the tree of the REST of the star. -/
  | starCons (hd tl : MTree)
  /-- Successful not-predicate. -/
  | notT
  /-- Successful `Debug(e)`. -/
  | dbgT

inductive MOutcome where
  | fail
  | ok (t : MTree) (rest : List Char)

end Shallot.MacroPeg
