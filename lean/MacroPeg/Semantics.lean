import MacroPeg.Syntax

/-!
# Macro PEG formal semantics (call-by-name + call-by-value-par + call-by-value-seq)

Extends `Shallot.Peg`'s `Derives` pattern to `MExp`, now parameterized over
`Strategy` (M-PEG-2 adds `.callByValuePar`, M-PEG-3 adds `.callByValueSeq`,
to M-PEG's `.callByName`). Every rule for the shared constructors
(`eps`/`any`/`chr`/`range`/`lit`/`seq`/`alt`/`star`/`notP`/`dbg`/`paramFail`/
`callMissing`/`callArity`) is strategy-independent — nothing about the base
PEG operators, or about a missing rule / an arity mismatch, cares which
strategy is in effect. `s` is simply threaded through unchanged (it is fixed
for an entire derivation, exactly like `g` — a whole macro_peg program
commits to one strategy at `Evaluator` construction, matching
`Evaluator(grammar, strategy)`).

Strategy only matters at `.call`:

- **`.callByName`** (`callNameOk`/`callNameFail`, `hs : s = .callByName`):
  unchanged from M-PEG — derives `MExp.subst args r.body` directly, the
  actual-parameter expressions spliced in UNEVALUATED.
- **`.callByValuePar`** (`callParOk`/`callParFail`/`callParArgFail`,
  `hs : s = .callByValuePar`): each actual parameter is evaluated
  INDEPENDENTLY against the SAME `input` (a lookahead/backreference-style
  extraction — evaluating the arguments does not by itself advance the
  input), via the mutual `DerivesArgsPar` relation below. If ALL succeed,
  their consumed prefixes become `.lit`-wrapped VALUES substituted into the
  body (via the same capture-free `MExp.subst` — it does not care whether
  an actual argument is a raw expression or a computed `.lit` value), and
  the body is derived starting from the ORIGINAL `input` (not from any
  argument's remainder — matching the reference `Evaluator`'s
  `CallByValuePar` branch, where the bound `input` after evaluating params
  is the untouched outer `input`, not a threaded one). If the body then
  fails, that is `callParFail`. If ANY actual parameter itself fails to
  derive, the whole call fails — `callParArgFail`. This third failure mode
  is not optional bookkeeping: without it, a `.call` whose arguments
  include a failing one would have NO derivation at all (neither `.ok` nor
  `.fail`), breaking totality/completeness, since `DerivesArgsPar` itself
  (built only from all-succeed `cons` steps) is simply undevivable for such
  an args list — there is no rule that concludes it as "partially done,
  then stuck." Crucially, `callParArgFail` requires `args` to split as
  `pre ++ badArg :: post` with `hpre : DerivesArgsPar g s input pre preVals`
  — i.e. every argument BEFORE `badArg` must itself be witnessed as
  succeeding. This is not optional precision: `evalArgsPar` (the
  interpreter counterpart) evaluates arguments strictly left-to-right and
  short-circuits (or diverges) the moment an EARLIER argument fails or
  fails to terminate, so an unconstrained "some argument in the list
  fails, anywhere, regardless of the others" rule is UNSOUND relative to
  what the interpreter can ever actually witness — machine-checked
  disproof during development: a grammar with a non-terminating first
  argument and a failing second argument is derivable as `.fail` under the
  weaker (unconstrained) rule, yet `mpegRun` returns `none` (never
  finishes) at every fuel level for it, since it never gets past the
  non-terminating first argument to see the second one fail. Requiring the
  `pre` prefix to be witnessed rules this out: nothing before `badArg` can
  be non-terminating if it has an actual `DerivesArgsPar` derivation.
- **`.callByValueSeq`** (`callSeqOk`/`callSeqFail`/`callSeqArgFail`,
  `hs : s = .callByValueSeq`): the actual parameters are evaluated
  SEQUENTIALLY — the first against `input`, the next against whatever input
  remains after the first matched, and so on — exactly like a PEG Sequence
  of the argument expressions, via the mutual `DerivesArgsSeq` relation
  below. `DerivesArgsSeq` therefore THREADS the input: unlike
  `DerivesArgsPar` (which fixes `input` and re-runs every argument at that
  same position), its `cons` case recurses on `rest` (the position AFTER
  consuming the current argument) and carries an extra `final` index — the
  input reached after ALL arguments were threaded through. Each consumed
  prefix still becomes a `.lit`-wrapped VALUE substituted into the body (via
  the same capture-free `MExp.subst`), but the body is then derived from
  `mid` (that final threaded position — `callSeqOk`/`callSeqFail`), NOT from
  the original `input`. That is the sole behavioral difference from
  `.callByValuePar`, whose body starts from the untouched `input`.
  `callSeqArgFail` mirrors `callParArgFail`'s hard-won shape exactly and for
  the same soundness reason: `args` must split as `pre ++ badArg :: post`
  with `hpre : DerivesArgsSeq g s input pre preVals mid` witnessing that
  every earlier argument actually succeeded (threading `input` to `mid`),
  and `badArg` fails AT `mid` — the position reached after `pre` was
  consumed IN SEQUENCE — not at the original `input`. An unconstrained "some
  argument fails somewhere" rule would be unsound here too: the interpreter
  (`evalArgsSeq`) can only ever observe an argument's failure after
  everything before it has actually finished threading, so a non-terminating
  earlier argument must never leave a later argument's failure derivable
  with no fuel witness ever realizing it.
-/

namespace Shallot.MacroPeg

mutual

inductive MDerives (g : MGrammar) (s : Strategy) : MExp → List Char → MOutcome → Prop where
  | eps (input : List Char) :
      MDerives g s .eps input (.ok (.leaf []) input)
  | anyOk (c : Char) (rest : List Char) :
      MDerives g s .any (c :: rest) (.ok (.leaf [c]) rest)
  | anyFail :
      MDerives g s .any [] .fail
  | chrOk (c d : Char) (rest : List Char) (h : beqChar c d = true) :
      MDerives g s (.chr c) (d :: rest) (.ok (.leaf [d]) rest)
  | chrFail (c d : Char) (rest : List Char) (h : beqChar c d = false) :
      MDerives g s (.chr c) (d :: rest) .fail
  | chrEmpty (c : Char) :
      MDerives g s (.chr c) [] .fail
  | rangeOk (lo hi d : Char) (rest : List Char)
      (h : (leChar lo d && leChar d hi) = true) :
      MDerives g s (.range lo hi) (d :: rest) (.ok (.leaf [d]) rest)
  | rangeFail (lo hi d : Char) (rest : List Char)
      (h : (leChar lo d && leChar d hi) = false) :
      MDerives g s (.range lo hi) (d :: rest) .fail
  | rangeEmpty (lo hi : Char) :
      MDerives g s (.range lo hi) [] .fail
  | litOk (str input rest : List Char) (h : stripPrefix? str input = some rest) :
      MDerives g s (.lit str) input (.ok (.leaf str) rest)
  | litFail (str input : List Char) (h : stripPrefix? str input = none) :
      MDerives g s (.lit str) input .fail
  | dbg (e : MExp) (input : List Char) :
      MDerives g s (.dbg e) input (.ok .dbgT input)
  | paramFail (k : Nat) (input : List Char) :
      MDerives g s (.param k) input .fail
  | callNameOk (i : Nat) (args : List MExp) (r : MRule) (input rest : List Char) (t : MTree)
      (hs : s = .callByName)
      (hr : ruleAtM g.rules i = some r)
      (ha : r.arity = args.length)
      (hd : MDerives g s (MExp.subst args r.body) input (.ok t rest)) :
      MDerives g s (.call i args) input (.ok (.nodeCall i t) rest)
  | callNameFail (i : Nat) (args : List MExp) (r : MRule) (input : List Char)
      (hs : s = .callByName)
      (hr : ruleAtM g.rules i = some r)
      (ha : r.arity = args.length)
      (hd : MDerives g s (MExp.subst args r.body) input .fail) :
      MDerives g s (.call i args) input .fail
  | callParOk (i : Nat) (args : List MExp) (r : MRule) (input rest : List Char)
      (vals : List MExp) (t : MTree)
      (hs : s = .callByValuePar)
      (hr : ruleAtM g.rules i = some r)
      (ha : r.arity = args.length)
      (hargs : DerivesArgsPar g s input args vals)
      (hd : MDerives g s (MExp.subst vals r.body) input (.ok t rest)) :
      MDerives g s (.call i args) input (.ok (.nodeCall i t) rest)
  | callParFail (i : Nat) (args : List MExp) (r : MRule) (input : List Char) (vals : List MExp)
      (hs : s = .callByValuePar)
      (hr : ruleAtM g.rules i = some r)
      (ha : r.arity = args.length)
      (hargs : DerivesArgsPar g s input args vals)
      (hd : MDerives g s (MExp.subst vals r.body) input .fail) :
      MDerives g s (.call i args) input .fail
  | callParArgFail (i : Nat) (pre : List MExp) (badArg : MExp) (post : List MExp) (r : MRule)
      (input : List Char) (preVals : List MExp)
      (hs : s = .callByValuePar)
      (hr : ruleAtM g.rules i = some r)
      (ha : r.arity = (pre ++ badArg :: post).length)
      (hpre : DerivesArgsPar g s input pre preVals)
      (hfail : MDerives g s badArg input .fail) :
      MDerives g s (.call i (pre ++ badArg :: post)) input .fail
  | callSeqOk (i : Nat) (args : List MExp) (r : MRule) (input mid rest : List Char)
      (vals : List MExp) (t : MTree)
      (hs : s = .callByValueSeq)
      (hr : ruleAtM g.rules i = some r)
      (ha : r.arity = args.length)
      (hargs : DerivesArgsSeq g s input args vals mid)
      (hd : MDerives g s (MExp.subst vals r.body) mid (.ok t rest)) :
      MDerives g s (.call i args) input (.ok (.nodeCall i t) rest)
  | callSeqFail (i : Nat) (args : List MExp) (r : MRule) (input mid : List Char) (vals : List MExp)
      (hs : s = .callByValueSeq)
      (hr : ruleAtM g.rules i = some r)
      (ha : r.arity = args.length)
      (hargs : DerivesArgsSeq g s input args vals mid)
      (hd : MDerives g s (MExp.subst vals r.body) mid .fail) :
      MDerives g s (.call i args) input .fail
  | callSeqArgFail (i : Nat) (pre : List MExp) (badArg : MExp) (post : List MExp) (r : MRule)
      (input mid : List Char) (preVals : List MExp)
      (hs : s = .callByValueSeq)
      (hr : ruleAtM g.rules i = some r)
      (ha : r.arity = (pre ++ badArg :: post).length)
      (hpre : DerivesArgsSeq g s input pre preVals mid)
      (hfail : MDerives g s badArg mid .fail) :
      MDerives g s (.call i (pre ++ badArg :: post)) input .fail
  | callMissing (i : Nat) (args : List MExp) (input : List Char)
      (hr : ruleAtM g.rules i = none) :
      MDerives g s (.call i args) input .fail
  | callArity (i : Nat) (args : List MExp) (r : MRule) (input : List Char)
      (hr : ruleAtM g.rules i = some r) (ha : r.arity ≠ args.length) :
      MDerives g s (.call i args) input .fail
  | seqOk (e₁ e₂ : MExp) (input rest₁ rest₂ : List Char) (t₁ t₂ : MTree)
      (h₁ : MDerives g s e₁ input (.ok t₁ rest₁))
      (h₂ : MDerives g s e₂ rest₁ (.ok t₂ rest₂)) :
      MDerives g s (.seq e₁ e₂) input (.ok (.seq t₁ t₂) rest₂)
  | seqFail₁ (e₁ e₂ : MExp) (input : List Char)
      (h₁ : MDerives g s e₁ input .fail) :
      MDerives g s (.seq e₁ e₂) input .fail
  | seqFail₂ (e₁ e₂ : MExp) (input rest₁ : List Char) (t₁ : MTree)
      (h₁ : MDerives g s e₁ input (.ok t₁ rest₁))
      (h₂ : MDerives g s e₂ rest₁ .fail) :
      MDerives g s (.seq e₁ e₂) input .fail
  | altL (e₁ e₂ : MExp) (input rest : List Char) (t : MTree)
      (h : MDerives g s e₁ input (.ok t rest)) :
      MDerives g s (.alt e₁ e₂) input (.ok (.choiceL t) rest)
  | altR (e₁ e₂ : MExp) (input rest : List Char) (t : MTree)
      (h₁ : MDerives g s e₁ input .fail)
      (h₂ : MDerives g s e₂ input (.ok t rest)) :
      MDerives g s (.alt e₁ e₂) input (.ok (.choiceR t) rest)
  | altFail (e₁ e₂ : MExp) (input : List Char)
      (h₁ : MDerives g s e₁ input .fail)
      (h₂ : MDerives g s e₂ input .fail) :
      MDerives g s (.alt e₁ e₂) input .fail
  | starNil (e : MExp) (input : List Char)
      (h : MDerives g s e input .fail) :
      MDerives g s (.star e) input (.ok .starNil input)
  | starCons (e : MExp) (input rest rest' : List Char) (t ts : MTree)
      (h₁ : MDerives g s e input (.ok t rest))
      (h₂ : MDerives g s (.star e) rest (.ok ts rest')) :
      MDerives g s (.star e) input (.ok (.starCons t ts) rest')
  | notOk (e : MExp) (input rest : List Char) (t : MTree)
      (h : MDerives g s e input (.ok t rest)) :
      MDerives g s (.notP e) input .fail
  | notFail (e : MExp) (input : List Char)
      (h : MDerives g s e input .fail) :
      MDerives g s (.notP e) input (.ok .notT input)

/-- Evaluates a list of actual parameters under `.callByValuePar`: each
`a ∈ args` is derived against the SAME `input` (no threading — parallel,
not sequential), and on success contributes `.lit p` (its consumed prefix,
explicitly witnessed via `hp` rather than extracted from `MDerives`'s own
suffix property, since the latter only gives existence, not a computable
prefix) to the output value list. Total success of every element is
REQUIRED to derive this relation at all — there is deliberately no "some
element fails" case here; that case is `MDerives.callParArgFail` above,
kept separate since it does not produce a value list. -/
inductive DerivesArgsPar (g : MGrammar) (s : Strategy) :
    List Char → List MExp → List MExp → Prop where
  | nil (input : List Char) : DerivesArgsPar g s input [] []
  | cons (a : MExp) (as : List MExp) (input p rest : List Char) (t : MTree) (vs : List MExp)
      (h1 : MDerives g s a input (.ok t rest))
      (hp : input = p ++ rest)
      (h2 : DerivesArgsPar g s input as vs) :
      DerivesArgsPar g s input (a :: as) (.lit p :: vs)

/-- Evaluates a list of actual parameters under `.callByValueSeq`: the
arguments are derived SEQUENTIALLY and the input is THREADED through them —
`a` against `input`, the remaining `as` against `rest` (the position `a`
left off at), and so on, exactly like a PEG Sequence of the argument
expressions. On success each `a` contributes `.lit p` (its consumed prefix,
explicitly witnessed via `hp` rather than extracted from `MDerives`'s own
suffix property) to the output value list, and the relation reports the
`final` input position reached after threading through the WHOLE list — that
extra index is what distinguishes this from `DerivesArgsPar`, which fixes
`input` for every element and yields no threaded remainder. Total success of
every element is REQUIRED to derive this relation at all; the "some element
fails" case is `MDerives.callSeqArgFail` above (kept separate as it produces
no value list, and pins the failure to the threaded `mid` position). -/
inductive DerivesArgsSeq (g : MGrammar) (s : Strategy) :
    List Char → List MExp → List MExp → List Char → Prop where
  | nil (input : List Char) : DerivesArgsSeq g s input [] [] input
  | cons (a : MExp) (as : List MExp) (input p rest final : List Char) (t : MTree) (vs : List MExp)
      (h1 : MDerives g s a input (.ok t rest))
      (hp : input = p ++ rest)
      (h2 : DerivesArgsSeq g s rest as vs final) :
      DerivesArgsSeq g s input (a :: as) (.lit p :: vs) final

end

end Shallot.MacroPeg
