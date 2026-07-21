import MacroPeg.Syntax

/-!
# Macro PEG formal semantics (call-by-name core)

Extends `Shallot.Peg`'s `Derives` pattern to `MExp`. Every rule for the
shared constructors (`eps`/`any`/`chr`/`range`/`lit`/`seq`/`alt`/`star`/
`notP`) is a verbatim transcription of `Shallot.Peg.Semantics.Derives` —
nothing about the base PEG operators changes when parameters are added.

Two rules are genuinely new:
- `dbg`: unconditional success, `e` is never derived (mirrors the reference
  `Evaluator`'s no-op `Debug`).
- `call`: looks up rule `i`, requires the declared arity to match the actual
  parameter count, and derives `MExp.subst args r.body` — the callee's body
  with its formal parameters replaced by the (unevaluated) actual-parameter
  expressions. This substitution IS the call-by-name macro semantics: an
  actual parameter is matched zero, one, or many times, wherever `.param k`
  landed inside the body, exactly as many times as control flow reaches it —
  never "up front" at the call site.

Missing rule / arity mismatch get explicit failure rules (`callMissing`,
`callArity`), continuing `ntMissing`'s zero-well-formedness-assumption
discipline. A bare `.param k` (unreachable in practice — `subst` eliminates
every `.param` before `MDerives` sees the substituted body, exactly as
`mpegRun`'s `.param` case is a dead branch, see `MacroPeg/Interp.lean`) gets
an unconditional-failure rule (`paramFail`) for the same reason `mpegRun`'s
`.param` branch must still return SOMETHING despite being dead: soundness is
stated for ALL `MExp` values, so `MDerives` needs a total answer here too,
not just the interpreter.
-/

namespace Shallot.MacroPeg

inductive MDerives (g : MGrammar) : MExp → List Char → MOutcome → Prop where
  | eps (input : List Char) :
      MDerives g .eps input (.ok (.leaf []) input)
  | anyOk (c : Char) (rest : List Char) :
      MDerives g .any (c :: rest) (.ok (.leaf [c]) rest)
  | anyFail :
      MDerives g .any [] .fail
  | chrOk (c d : Char) (rest : List Char) (h : beqChar c d = true) :
      MDerives g (.chr c) (d :: rest) (.ok (.leaf [d]) rest)
  | chrFail (c d : Char) (rest : List Char) (h : beqChar c d = false) :
      MDerives g (.chr c) (d :: rest) .fail
  | chrEmpty (c : Char) :
      MDerives g (.chr c) [] .fail
  | rangeOk (lo hi d : Char) (rest : List Char)
      (h : (leChar lo d && leChar d hi) = true) :
      MDerives g (.range lo hi) (d :: rest) (.ok (.leaf [d]) rest)
  | rangeFail (lo hi d : Char) (rest : List Char)
      (h : (leChar lo d && leChar d hi) = false) :
      MDerives g (.range lo hi) (d :: rest) .fail
  | rangeEmpty (lo hi : Char) :
      MDerives g (.range lo hi) [] .fail
  | litOk (s input rest : List Char) (h : stripPrefix? s input = some rest) :
      MDerives g (.lit s) input (.ok (.leaf s) rest)
  | litFail (s input : List Char) (h : stripPrefix? s input = none) :
      MDerives g (.lit s) input .fail
  | dbg (e : MExp) (input : List Char) :
      MDerives g (.dbg e) input (.ok .dbgT input)
  | paramFail (k : Nat) (input : List Char) :
      MDerives g (.param k) input .fail
  | callOk (i : Nat) (args : List MExp) (r : MRule) (input rest : List Char) (t : MTree)
      (hr : ruleAtM g.rules i = some r)
      (ha : r.arity = args.length)
      (hd : MDerives g (MExp.subst args r.body) input (.ok t rest)) :
      MDerives g (.call i args) input (.ok (.nodeCall i t) rest)
  | callFail (i : Nat) (args : List MExp) (r : MRule) (input : List Char)
      (hr : ruleAtM g.rules i = some r)
      (ha : r.arity = args.length)
      (hd : MDerives g (MExp.subst args r.body) input .fail) :
      MDerives g (.call i args) input .fail
  | callMissing (i : Nat) (args : List MExp) (input : List Char)
      (hr : ruleAtM g.rules i = none) :
      MDerives g (.call i args) input .fail
  | callArity (i : Nat) (args : List MExp) (r : MRule) (input : List Char)
      (hr : ruleAtM g.rules i = some r) (ha : r.arity ≠ args.length) :
      MDerives g (.call i args) input .fail
  | seqOk (e₁ e₂ : MExp) (input rest₁ rest₂ : List Char) (t₁ t₂ : MTree)
      (h₁ : MDerives g e₁ input (.ok t₁ rest₁))
      (h₂ : MDerives g e₂ rest₁ (.ok t₂ rest₂)) :
      MDerives g (.seq e₁ e₂) input (.ok (.seq t₁ t₂) rest₂)
  | seqFail₁ (e₁ e₂ : MExp) (input : List Char)
      (h₁ : MDerives g e₁ input .fail) :
      MDerives g (.seq e₁ e₂) input .fail
  | seqFail₂ (e₁ e₂ : MExp) (input rest₁ : List Char) (t₁ : MTree)
      (h₁ : MDerives g e₁ input (.ok t₁ rest₁))
      (h₂ : MDerives g e₂ rest₁ .fail) :
      MDerives g (.seq e₁ e₂) input .fail
  | altL (e₁ e₂ : MExp) (input rest : List Char) (t : MTree)
      (h : MDerives g e₁ input (.ok t rest)) :
      MDerives g (.alt e₁ e₂) input (.ok (.choiceL t) rest)
  | altR (e₁ e₂ : MExp) (input rest : List Char) (t : MTree)
      (h₁ : MDerives g e₁ input .fail)
      (h₂ : MDerives g e₂ input (.ok t rest)) :
      MDerives g (.alt e₁ e₂) input (.ok (.choiceR t) rest)
  | altFail (e₁ e₂ : MExp) (input : List Char)
      (h₁ : MDerives g e₁ input .fail)
      (h₂ : MDerives g e₂ input .fail) :
      MDerives g (.alt e₁ e₂) input .fail
  | starNil (e : MExp) (input : List Char)
      (h : MDerives g e input .fail) :
      MDerives g (.star e) input (.ok .starNil input)
  | starCons (e : MExp) (input rest rest' : List Char) (t ts : MTree)
      (h₁ : MDerives g e input (.ok t rest))
      (h₂ : MDerives g (.star e) rest (.ok ts rest')) :
      MDerives g (.star e) input (.ok (.starCons t ts) rest')
  | notOk (e : MExp) (input rest : List Char) (t : MTree)
      (h : MDerives g e input (.ok t rest)) :
      MDerives g (.notP e) input .fail
  | notFail (e : MExp) (input : List Char)
      (h : MDerives g e input .fail) :
      MDerives g (.notP e) input (.ok .notT input)

end Shallot.MacroPeg
