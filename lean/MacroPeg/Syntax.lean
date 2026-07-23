import Shallot.Peg.Syntax

/-!
# Macro PEG syntax, parse trees, outcomes

Formalizes all three of kmizu/macro_peg's `Evaluator` strategies (M-PEG-2
adds `CallByValuePar`, M-PEG-3 adds `CallByValueSeq`, to M-PEG's
`CallByName`; see `Strategy` below and `MacroPeg/Semantics.lean`'s module
docstring for the `.call` semantics each one gets): PEG extended with
parametrized, recursive rules. Under `CallByName` the actual parameters are
spliced into the callee's body as UNEVALUATED expressions (true macro
substitution); under `CallByValuePar` they are evaluated independently
against the SAME starting position (a lookahead/backreference-style
extraction that does not advance the input) before splicing in the consumed
substrings as literal values; under `CallByValueSeq` they are evaluated
SEQUENTIALLY, each argument against the input remaining after the previous
one matched (exactly like a PEG sequence of the argument expressions),
splicing in each consumed substring as a literal value, and the callee body
is then derived from whatever input remains AFTER all arguments have been
threaded through — contrast `CallByValuePar`, whose body starts from the
ORIGINAL un-threaded input.

M-PEG-4 adds a bounded slice of the higher-order layer: `.lam`/`.callParam`/
`.invoke` (below) let a macro parameter carry a CALLABLE value — either a
literal lambda or a reference to a named rule (the caller embeds
`.lam r.arity r.body` directly; there is no surface `.peg` parser in this
project, so "referencing a named rule as a value" and "writing a lambda
literal" are the SAME `MExp` shape once elaborated) — which the callee body
may then invoke via `.callParam`. What stays OUT of scope is a closure
returned as a value and applied from a DIFFERENT, later call site: the
reference `Evaluator` only supports that through the separate
`MacroExpander` utility, an eager whole-grammar inlining pass that is
genuinely non-terminating on self-recursive rules and — verified against
the shipped Scala test suite — is not exercised by a single shipped test.
Every shipped higher-order test only ever invokes a passed-in callable
immediately, inside the same call tree that received it; see
`docs/theorems.md`/`docs/roadmap.md` for the full audit trail.

Design, continuing `Shallot.Peg`'s conventions (`Shallot/Peg/Syntax.lean`):
- rules are `Nat`-indexed (`MGrammar.rules : List MRule`), never named — no
  `Symbol`/`Map` anywhere
- a formal parameter is a de Bruijn-style `Nat` index into "the current rule
  activation's argument list" (`.param k`). Ordinary macro_peg rule bodies
  never nest, so ONE de Bruijn level is enough for them — no environment
  stack, no name, hence no risk of capture. A `.lam`'s body is its OWN
  independent one-level scope (its `.param k` refers to the LAMBDA's own
  k-th argument, never the enclosing rule's) — every shipped lambda literal
  in the reference test suite is self-contained (no free variable reaching
  into an outer scope), so this project deliberately does not model
  closures/capture: `MExp.subst` treats a `.lam` as an opaque LEAF (exactly
  like `.lit`), never recursing into its body, which is what makes this
  capture-free by construction rather than by convention. This is what lets
  `MExp.subst` be a plain capture-free structural substitution, in contrast
  to the reference Scala `Evaluator`'s `extract()`, a hand-rolled hygiene
  routine needed there specifically because it binds parameters by name in a
  flat `Map[Symbol, Expression]` shared with rule names.
- zero well-formedness assumptions: a missing rule index, an arity mismatch,
  an out-of-range `.param` reference, or a `.callParam` whose target isn't a
  `.lam` value all resolve to an explicit failure (`.notP .eps`, an
  always-fail expression built from existing constructors — no new AST leaf
  needed) rather than a side hypothesis. Mirrors `ntMissing` in
  `Shallot/Peg/Semantics.lean`.
- `MTree` mirrors `MExp` structure and carries only ONE child tree per
  `call`/`invoke` node (the substituted body's tree) — call-by-name never
  derives the actual-parameter expressions independently, only wherever
  `.param` occurrences land inside the (substituted) body, so there is
  nothing else to record.
- monomorphic list helpers only (own `argAt`, no `List.getD`/`List.map`),
  matching `ruleAt`/`stripPrefix?` in `Shallot/Peg/Syntax.lean` — keeps the
  extractable subset uniform with the rest of the project.
-/

namespace Shallot.MacroPeg

/-- Which of `Evaluator`'s argument-passing strategies a derivation/run is
under. `callByValueSeq` evaluates actual parameters SEQUENTIALLY, threading
the input through them (the first against the original input, the next
against whatever remains after it matched, and so on) and derives the callee
body from the FINAL threaded position — contrast `callByValuePar`, which
evaluates every argument against the SAME original input and derives the
body from that un-threaded input. -/
inductive Strategy where
  | callByName
  | callByValuePar
  | callByValueSeq
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
  /-- A CALLABLE value of the given arity — either a lambda literal or a
  named rule referenced as a value (the caller embeds `.lam r.arity
  r.body` directly). Unconditional zero-width success when evaluated
  directly as an expression (mirrors `.dbg` — "values don't consume
  input", matching the reference `Evaluator`'s treatment of `Ast.Function`).
  `body`'s `.param k` refers to THIS lambda's own k-th argument — a fresh,
  independent scope, never the enclosing rule's (see the module docstring:
  no closures/capture are modeled). -/
  | lam (arity : Nat) (body : MExp)
  /-- Invoke the CALLABLE currently bound to the k-th actual parameter of
  the current rule activation, applying `args`. Never appears in a
  derivation/interpreter run directly — `subst` always eliminates it at the
  nearest enclosing `call`/`invoke`, resolving to `.invoke` (if param k
  holds a `.lam`) or `MExp.failAlways` (otherwise — zero well-formedness
  assumptions, same discipline as an out-of-range `.param`). Kept as its
  own constructor (rather than folded into `.param`) so `subst` can be
  total pattern matching without a side condition. -/
  | callParam (k : Nat) (args : List MExp)
  /-- The RESOLVED form of a `.callParam` that `subst` produced by finding
  a `.lam arity body` at the target parameter: carries that `arity`/`body`
  inline (copied, not further substituted — actual substitution of `args`
  into `body` happens at derivation/interpretation time, fuel-gated, the
  same way `.call` defers substituting a rule's body). Unlike `.call`,
  there is no "missing rule" failure mode — `arity`/`body` are already in
  hand by construction — and no per-`Strategy` case split, since by the
  time a `.callParam` resolves to `.invoke`, its `args` have already gone
  through whatever argument-evaluation `.callParam`'s enclosing `.call` used. -/
  | invoke (arity : Nat) (body : MExp) (args : List MExp)

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
    | .lam ar bod => .lam ar bod
    | .callParam k margs =>
      match argAt args k with
      | some (.lam ar bod) => .invoke ar bod (MExp.substArgs args margs)
      | _ => MExp.failAlways
    | .invoke ar bod margs => .invoke ar bod (MExp.substArgs args margs)

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
  /-- Successful `.lam` (a callable value, evaluated directly — zero-width). -/
  | lamT
  /-- Successful `.invoke` — carries only the substituted body's tree, same
  shape as `nodeCall` but with no rule index (the body was already in hand,
  not looked up). -/
  | nodeInvoke (t : MTree)

inductive MOutcome where
  | fail
  | ok (t : MTree) (rest : List Char)

end Shallot.MacroPeg
