import Shallot.Peg.Syntax

/-!
# PEG formal semantics

Ford's (POPL'04) inductive derivation relation, extended to carry parse
trees in outcomes. Bool side conditions (`beqChar`, `leChar`,
`stripPrefix?`) keep inversion mechanical. Binders are explicit because
`autoImplicit` is disabled project-wide.

Honest scoping (goes in the README): no totality claim for all grammars —
left recursion and ε-body stars simply have no derivation, the fuel
interpreter runs out, and all theorems (soundness / determinism /
completeness-relative-to-derivations) remain true.
-/

namespace Shallot

inductive Derives (g : Grammar) : PExp → List Char → Outcome → Prop where
  | eps (input : List Char) :
      Derives g .eps input (.ok (.leaf []) input)
  | anyOk (c : Char) (rest : List Char) :
      Derives g .any (c :: rest) (.ok (.leaf [c]) rest)
  | anyFail :
      Derives g .any [] .fail
  | chrOk (c d : Char) (rest : List Char) (h : beqChar c d = true) :
      Derives g (.chr c) (d :: rest) (.ok (.leaf [d]) rest)
  | chrFail (c d : Char) (rest : List Char) (h : beqChar c d = false) :
      Derives g (.chr c) (d :: rest) .fail
  | chrEmpty (c : Char) :
      Derives g (.chr c) [] .fail
  | rangeOk (lo hi d : Char) (rest : List Char)
      (h : (leChar lo d && leChar d hi) = true) :
      Derives g (.range lo hi) (d :: rest) (.ok (.leaf [d]) rest)
  | rangeFail (lo hi d : Char) (rest : List Char)
      (h : (leChar lo d && leChar d hi) = false) :
      Derives g (.range lo hi) (d :: rest) .fail
  | rangeEmpty (lo hi : Char) :
      Derives g (.range lo hi) [] .fail
  | litOk (s input rest : List Char) (h : stripPrefix? s input = some rest) :
      Derives g (.lit s) input (.ok (.leaf s) rest)
  | litFail (s input : List Char) (h : stripPrefix? s input = none) :
      Derives g (.lit s) input .fail
  | ntOk (i : Nat) (e : PExp) (input rest : List Char) (t : PTree)
      (hr : ruleAt g.rules i = some e)
      (hd : Derives g e input (.ok t rest)) :
      Derives g (.nt i) input (.ok (.nodeNT i t) rest)
  | ntFail (i : Nat) (e : PExp) (input : List Char)
      (hr : ruleAt g.rules i = some e)
      (hd : Derives g e input .fail) :
      Derives g (.nt i) input .fail
  | ntMissing (i : Nat) (input : List Char) (hr : ruleAt g.rules i = none) :
      Derives g (.nt i) input .fail
  | seqOk (e₁ e₂ : PExp) (input rest₁ rest₂ : List Char) (t₁ t₂ : PTree)
      (h₁ : Derives g e₁ input (.ok t₁ rest₁))
      (h₂ : Derives g e₂ rest₁ (.ok t₂ rest₂)) :
      Derives g (.seq e₁ e₂) input (.ok (.seq t₁ t₂) rest₂)
  | seqFail₁ (e₁ e₂ : PExp) (input : List Char)
      (h₁ : Derives g e₁ input .fail) :
      Derives g (.seq e₁ e₂) input .fail
  | seqFail₂ (e₁ e₂ : PExp) (input rest₁ : List Char) (t₁ : PTree)
      (h₁ : Derives g e₁ input (.ok t₁ rest₁))
      (h₂ : Derives g e₂ rest₁ .fail) :
      Derives g (.seq e₁ e₂) input .fail
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

end Shallot
