import MacroPeg.Semantics
import Shallot.Peg.Semantics

/-!
# T1: embedding plain PEG into first-order call-by-name Macro PEG

Every plain-PEG rule becomes a zero-arity Macro PEG rule (`.nt i ↦ .call i
[]`); since a 0-arity call never substitutes anything, this is a completely
mechanical, structure-preserving embedding — no macro-specific machinery is
exercised at all. Only the direction needed downstream (T3, via the aⁿbⁿcⁿ
witness) is proved: PEG success on `e`/`x` implies Macro PEG success on the
embedded `embedExp e`/`x`.
-/

namespace Shallot.MacroPeg

open Shallot (PExp PTree Outcome Grammar beqChar leChar stripPrefix? ruleAt)

def embedExp : PExp → MExp
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit s => .lit s
  | .nt i => .call i []
  | .seq e₁ e₂ => .seq (embedExp e₁) (embedExp e₂)
  | .alt e₁ e₂ => .alt (embedExp e₁) (embedExp e₂)
  | .star e => .star (embedExp e)
  | .notP e => .notP (embedExp e)

def embedTree : PTree → MTree
  | .leaf cs => .leaf cs
  | .nodeNT i t => .nodeCall i (embedTree t)
  | .seq l r => .seq (embedTree l) (embedTree r)
  | .choiceL t => .choiceL (embedTree t)
  | .choiceR t => .choiceR (embedTree t)
  | .starNil => .starNil
  | .starCons hd tl => .starCons (embedTree hd) (embedTree tl)
  | .notT => .notT

def embedOutcome : Outcome → MOutcome
  | .fail => .fail
  | .ok t rest => .ok (embedTree t) rest

def pegToMacroPeg (g : Grammar) : MGrammar :=
  { rules := g.rules.map (fun e => ({ arity := 0, body := embedExp e } : MRule)) }

/-- `ruleAtM` on the embedded grammar's rules commutes with `ruleAt` on the
original — mirrors `ruleAtM_cfgToMacroPeg` (`Cfg/Cps.lean`), same
index-lookup-commutes-with-map proof. -/
theorem ruleAtM_pegToMacroPeg (g : Grammar) (i : Nat) :
    ruleAtM (pegToMacroPeg g).rules i
      = (ruleAt g.rules i).map (fun e => ({ arity := 0, body := embedExp e } : MRule)) := by
  simp only [pegToMacroPeg]
  induction g.rules generalizing i with
  | nil => cases i <;> rfl
  | cons r rs ih =>
    cases i with
    | zero => rfl
    | succ n => simp only [List.map, ruleAtM, ruleAt]; exact ih n

/-- A 0-arity call substitutes nothing, and `embedExp` never produces a
`.param`/`.lam`/`.callParam`/`.invoke` node, so `subst []` is the identity
on any embedded expression. -/
theorem subst_embedExp : ∀ (e : PExp), MExp.subst [] (embedExp e) = embedExp e
  | .eps => rfl
  | .any => rfl
  | .chr _ => rfl
  | .range _ _ => rfl
  | .lit _ => rfl
  | .nt _ => rfl
  | .seq e₁ e₂ => by simp only [embedExp, MExp.subst]; rw [subst_embedExp e₁, subst_embedExp e₂]
  | .alt e₁ e₂ => by simp only [embedExp, MExp.subst]; rw [subst_embedExp e₁, subst_embedExp e₂]
  | .star e => by simp only [embedExp, MExp.subst]; rw [subst_embedExp e]
  | .notP e => by simp only [embedExp, MExp.subst]; rw [subst_embedExp e]

open Shallot (Derives)

/-- T1's headline: every PEG derivation embeds faithfully into the
zero-arity Macro PEG grammar, under `.callByName` — a rule-for-rule
transcription for the strategy-independent constructors
(`eps`/`any*`/`chr*`/`range*`/`lit*`/`seq*`/`alt*`/`star*`/`not*`, which have
IDENTICAL shape between `Derives` and `MDerives`), plus a rule-lookup
conversion (`ruleAtM_pegToMacroPeg`) and the substitution-is-identity fact
(`subst_embedExp`) for the `nt ↦ call` case. -/
theorem peg_embed_complete {g : Shallot.Grammar} {e : Shallot.PExp} {x : List Char}
    {o : Shallot.Outcome} (h : Derives g e x o) :
    MDerives (pegToMacroPeg g) .callByName (embedExp e) x (embedOutcome o) := by
  induction h with
  | eps input => exact MDerives.eps input
  | anyOk c rest => exact MDerives.anyOk c rest
  | anyFail => exact MDerives.anyFail
  | chrOk c d rest h => exact MDerives.chrOk c d rest h
  | chrFail c d rest h => exact MDerives.chrFail c d rest h
  | chrEmpty c => exact MDerives.chrEmpty c
  | rangeOk lo hi d rest h => exact MDerives.rangeOk lo hi d rest h
  | rangeFail lo hi d rest h => exact MDerives.rangeFail lo hi d rest h
  | rangeEmpty lo hi => exact MDerives.rangeEmpty lo hi
  | litOk s input rest h => exact MDerives.litOk s input rest h
  | litFail s input h => exact MDerives.litFail s input h
  | ntOk i e input rest t hr hd ih =>
      have hr' : ruleAtM (pegToMacroPeg g).rules i
          = some ({ arity := 0, body := embedExp e } : MRule) := by
        rw [ruleAtM_pegToMacroPeg, hr]; rfl
      have hd' : MDerives (pegToMacroPeg g) .callByName (MExp.subst [] (embedExp e)) input
          (.ok (embedTree t) rest) := by rw [subst_embedExp]; exact ih
      exact MDerives.callNameOk i [] _ input rest (embedTree t) rfl hr' rfl hd'
  | ntFail i e input hr hd ih =>
      have hr' : ruleAtM (pegToMacroPeg g).rules i
          = some ({ arity := 0, body := embedExp e } : MRule) := by
        rw [ruleAtM_pegToMacroPeg, hr]; rfl
      have hd' : MDerives (pegToMacroPeg g) .callByName (MExp.subst [] (embedExp e)) input .fail := by
        rw [subst_embedExp]; exact ih
      exact MDerives.callNameFail i [] _ input rfl hr' rfl hd'
  | ntMissing i input hr =>
      have hr' : ruleAtM (pegToMacroPeg g).rules i = none := by
        rw [ruleAtM_pegToMacroPeg, hr]; rfl
      exact MDerives.callMissing i [] input hr'
  | seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ h₁ h₂ ih₁ ih₂ => exact MDerives.seqOk _ _ _ _ _ _ _ ih₁ ih₂
  | seqFail₁ e₁ e₂ input h₁ ih₁ => exact MDerives.seqFail₁ _ _ _ ih₁
  | seqFail₂ e₁ e₂ input rest₁ t₁ h₁ h₂ ih₁ ih₂ => exact MDerives.seqFail₂ _ _ _ _ _ ih₁ ih₂
  | altL e₁ e₂ input rest t h ih => exact MDerives.altL _ _ _ _ _ ih
  | altR e₁ e₂ input rest t h₁ h₂ ih₁ ih₂ => exact MDerives.altR _ _ _ _ _ ih₁ ih₂
  | altFail e₁ e₂ input h₁ h₂ ih₁ ih₂ => exact MDerives.altFail _ _ _ ih₁ ih₂
  | starNil e input h ih => exact MDerives.starNil _ _ ih
  | starCons e input rest rest' t ts h₁ h₂ ih₁ ih₂ => exact MDerives.starCons _ _ _ _ _ _ ih₁ ih₂
  | notOk e input rest t h ih => exact MDerives.notOk _ _ _ _ ih
  | notFail e input h ih => exact MDerives.notFail _ _ ih

/-! ## T1's converse: the embedding is not just success-preserving but
FAITHFUL — an embedded Macro PEG derivation reflects an actual PEG
derivation of the SAME shape (up to `embedTree`/`embedOutcome`). Needed for
T3: to show the aⁿbⁿcⁿ witness's MACRO PEG language is EXACTLY
`abcLanguage` (not just a superset of it), both directions of the
translation are required. -/

/-- Inverts `embedOutcome o = .ok mt mr`: `o` must itself be a success, with
matching tree (via `embedTree`) and rest. -/
theorem embedOutcome_ok_inv {o : Shallot.Outcome} {mt : MTree} {mr : List Char}
    (h : embedOutcome o = MOutcome.ok mt mr) : ∃ t, o = .ok t mr ∧ mt = embedTree t := by
  cases o with
  | fail => exact MOutcome.noConfusion h
  | ok t r =>
      simp only [embedOutcome, MOutcome.ok.injEq] at h
      exact ⟨t, by rw [h.2], h.1.symm⟩

/-- Inverts `embedOutcome o = .fail`: `o` must itself be `.fail`. -/
theorem embedOutcome_fail_inv {o : Shallot.Outcome} (h : embedOutcome o = MOutcome.fail) :
    o = .fail := by
  cases o with
  | fail => rfl
  | ok t r => exact MOutcome.noConfusion h

/-- T1's converse headline: an embedded Macro PEG derivation of `embedExp e`
reflects an actual PEG derivation of `e`, with matching outcome. Proved by
induction on the Macro PEG derivation itself (never on `e`'s structure —
recursion here goes through rule LOOKUP, via `.nt i ↦ .call i []`, not
through `e`'s syntactic subexpressions, so structural induction on `e`
would not be well-founded; induction on the (finite) derivation TREE is).
Each case determines `e`'s own top-level shape by inverting `embedExp`'s
injectivity (`cases e` then discharging the mismatched shapes via
`embedExp`'s definition), never assuming it. -/
theorem peg_embed_sound {g : Shallot.Grammar} {me : MExp} {x : List Char} {o : MOutcome}
    (h : MDerives (pegToMacroPeg g) .callByName me x o) :
    ∀ e : PExp, me = embedExp e → ∃ o', o = embedOutcome o' ∧ Derives g e x o' := by
  induction h using MDerives.rec
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
  case eps input =>
    intro e he
    cases e with
    | eps => exact ⟨.ok (.leaf []) input, rfl, Derives.eps input⟩
    | _ => injection he
  case anyOk c rest =>
    intro e he
    cases e with
    | any => exact ⟨.ok (.leaf [c]) rest, rfl, Derives.anyOk c rest⟩
    | _ => injection he
  case anyFail =>
    intro e he
    cases e with
    | any => exact ⟨.fail, rfl, Derives.anyFail⟩
    | _ => injection he
  case chrOk c d rest hbeq =>
    intro e he
    cases e with
    | chr c' =>
        injection he with hc; subst hc
        exact ⟨.ok (.leaf [d]) rest, rfl, Derives.chrOk c d rest hbeq⟩
    | _ => injection he
  case chrFail c d rest hbeq =>
    intro e he
    cases e with
    | chr c' =>
        injection he with hc; subst hc
        exact ⟨.fail, rfl, Derives.chrFail c d rest hbeq⟩
    | _ => injection he
  case chrEmpty c =>
    intro e he
    cases e with
    | chr c' =>
        injection he with hc; subst hc
        exact ⟨.fail, rfl, Derives.chrEmpty c⟩
    | _ => injection he
  case rangeOk lo hi d rest hle =>
    intro e he
    cases e with
    | range lo' hi' =>
        injection he with hlo hhi; subst hlo; subst hhi
        exact ⟨.ok (.leaf [d]) rest, rfl, Derives.rangeOk lo hi d rest hle⟩
    | _ => injection he
  case rangeFail lo hi d rest hle =>
    intro e he
    cases e with
    | range lo' hi' =>
        injection he with hlo hhi; subst hlo; subst hhi
        exact ⟨.fail, rfl, Derives.rangeFail lo hi d rest hle⟩
    | _ => injection he
  case rangeEmpty lo hi =>
    intro e he
    cases e with
    | range lo' hi' =>
        injection he with hlo hhi; subst hlo; subst hhi
        exact ⟨.fail, rfl, Derives.rangeEmpty lo hi⟩
    | _ => injection he
  case litOk str input rest hstrip =>
    intro e he
    cases e with
    | lit s' =>
        injection he with hstr; subst hstr
        exact ⟨.ok (.leaf str) rest, rfl, Derives.litOk str input rest hstrip⟩
    | _ => injection he
  case litFail str input hstrip =>
    intro e he
    cases e with
    | lit s' =>
        injection he with hstr; subst hstr
        exact ⟨.fail, rfl, Derives.litFail str input hstrip⟩
    | _ => injection he
  case dbg e1 input =>
    intro e he; cases e <;> injection he
  case paramFail k input =>
    intro e he; cases e <;> injection he
  case lam ar bod input =>
    intro e he; cases e <;> injection he
  case callParamFail k args input =>
    intro e he; cases e <;> injection he
  case invokeNameOk ar bod args input rest t hs ha hd ih =>
    intro e he; cases e <;> injection he
  case invokeNameFail ar bod args input hs ha hd ih =>
    intro e he; cases e <;> injection he
  case invokeParOk ar bod args input rest vals t hs ha hargs hd ihargs ih =>
    intro e _he; exact absurd hs (by decide)
  case invokeParFail ar bod args input vals hs ha hargs hd ihargs ih =>
    intro e _he; exact absurd hs (by decide)
  case invokeParArgFail ar bod pre badArg post input preVals hs ha hpre hfail ihpre ih =>
    intro e _he; exact absurd hs (by decide)
  case invokeSeqOk ar bod args input mid rest vals t hs ha hargs hd ihargs ih =>
    intro e _he; exact absurd hs (by decide)
  case invokeSeqFail ar bod args input mid vals hs ha hargs hd ihargs ih =>
    intro e _he; exact absurd hs (by decide)
  case invokeSeqArgFail ar bod pre badArg post input mid preVals hs ha hpre hfail ihpre ih =>
    intro e _he; exact absurd hs (by decide)
  case invokeArity ar bod args input ha =>
    intro e he; cases e <;> injection he
  case callNameOk i args r input rest t hs hr ha hd ih =>
    intro e he
    cases e with
    | nt i' =>
        injection he with hi hargs
        subst hi; subst hargs
        have hlookup : (ruleAt g.rules i).map
            (fun e' => ({ arity := 0, body := embedExp e' } : MRule)) = some r := by
          rw [← ruleAtM_pegToMacroPeg]; exact hr
        cases hlk : ruleAt g.rules i with
        | none => rw [hlk] at hlookup; simp only [Option.map_none] at hlookup; cases hlookup
        | some e' =>
            rw [hlk] at hlookup
            simp only [Option.map_some, Option.some.injEq] at hlookup
            have hrbody : r.body = embedExp e' := by rw [← hlookup]
            rw [hrbody, subst_embedExp] at hd
            obtain ⟨o', hoeq, hde⟩ := ih e' (by rw [hrbody, subst_embedExp])
            obtain ⟨t', hteq, hmteq⟩ := embedOutcome_ok_inv hoeq.symm
            subst hteq
            exact ⟨.ok (.nodeNT i t') rest, by simp [embedOutcome, embedTree, hmteq],
              Derives.ntOk i e' input rest t' hlk hde⟩
    | _ => injection he
  case callNameFail i args r input hs hr ha hd ih =>
    intro e he
    cases e with
    | nt i' =>
        injection he with hi hargs
        subst hi; subst hargs
        have hlookup : (ruleAt g.rules i).map
            (fun e' => ({ arity := 0, body := embedExp e' } : MRule)) = some r := by
          rw [← ruleAtM_pegToMacroPeg]; exact hr
        cases hlk : ruleAt g.rules i with
        | none => rw [hlk] at hlookup; simp only [Option.map_none] at hlookup; cases hlookup
        | some e' =>
            rw [hlk] at hlookup
            simp only [Option.map_some, Option.some.injEq] at hlookup
            have hrbody : r.body = embedExp e' := by rw [← hlookup]
            rw [hrbody, subst_embedExp] at hd
            obtain ⟨o', hoeq, hde⟩ := ih e' (by rw [hrbody, subst_embedExp])
            have hfail : o' = .fail := embedOutcome_fail_inv hoeq.symm
            subst hfail
            exact ⟨.fail, rfl, Derives.ntFail i e' input hlk hde⟩
    | _ => injection he
  case callParOk i args r input rest vals t hs hr ha hargs hd ihargs ih =>
    intro e _he; exact absurd hs (by decide)
  case callParFail i args r input vals hs hr ha hargs hd ihargs ih =>
    intro e _he; exact absurd hs (by decide)
  case callParArgFail i pre badArg post r input preVals hs hr ha hpre hfail ihpre ih =>
    intro e _he; exact absurd hs (by decide)
  case callSeqOk i args r input mid rest vals t hs hr ha hargs hd ihargs ih =>
    intro e _he; exact absurd hs (by decide)
  case callSeqFail i args r input mid vals hs hr ha hargs hd ihargs ih =>
    intro e _he; exact absurd hs (by decide)
  case callSeqArgFail i pre badArg post r input mid preVals hs hr ha hpre hfail ihpre ih =>
    intro e _he; exact absurd hs (by decide)
  case callMissing i args input hr =>
    intro e he
    cases e with
    | nt i' =>
        injection he with hi hargs
        subst hi
        have hlookup : (ruleAt g.rules i).map
            (fun e' => ({ arity := 0, body := embedExp e' } : MRule)) = none := by
          rw [← ruleAtM_pegToMacroPeg]; exact hr
        cases hlk : ruleAt g.rules i with
        | none => exact ⟨.fail, rfl, Derives.ntMissing i input hlk⟩
        | some e' => rw [hlk] at hlookup; simp only [Option.map_some] at hlookup; cases hlookup
    | _ => injection he
  case callArity i args r input hr ha =>
    intro e he
    cases e with
    | nt i' =>
        injection he with hi hargs
        subst hi; subst hargs
        have hlookup : (ruleAt g.rules i).map
            (fun e' => ({ arity := 0, body := embedExp e' } : MRule)) = some r := by
          rw [← ruleAtM_pegToMacroPeg]; exact hr
        cases hlk : ruleAt g.rules i with
        | none => rw [hlk] at hlookup; simp only [Option.map_none] at hlookup; cases hlookup
        | some e' =>
            rw [hlk] at hlookup
            simp only [Option.map_some, Option.some.injEq] at hlookup
            have hr0 : r.arity = 0 := by rw [← hlookup]
            exact absurd hr0 ha
    | _ => injection he
  case seqOk e1 e2 input rest1 rest2 t1 t2 h1 h2 ih1 ih2 =>
    intro e he
    cases e with
    | seq e1' e2' =>
        injection he with he1 he2
        obtain ⟨o1', ho1eq, hd1⟩ := ih1 e1' he1
        obtain ⟨t1', ht1eq, hmt1eq⟩ := embedOutcome_ok_inv ho1eq.symm
        subst ht1eq
        obtain ⟨o2', ho2eq, hd2⟩ := ih2 e2' he2
        obtain ⟨t2', ht2eq, hmt2eq⟩ := embedOutcome_ok_inv ho2eq.symm
        subst ht2eq
        exact ⟨.ok (.seq t1' t2') rest2, by simp [embedOutcome, embedTree, hmt1eq, hmt2eq],
          Derives.seqOk e1' e2' input rest1 rest2 t1' t2' hd1 hd2⟩
    | _ => injection he
  case seqFail₁ e1 e2 input h1 ih1 =>
    intro e he
    cases e with
    | seq e1' e2' =>
        injection he with he1 he2
        obtain ⟨o1', ho1eq, hd1⟩ := ih1 e1' he1
        have hfail1 : o1' = .fail := embedOutcome_fail_inv ho1eq.symm
        subst hfail1
        exact ⟨.fail, rfl, Derives.seqFail₁ e1' e2' input hd1⟩
    | _ => injection he
  case seqFail₂ e1 e2 input rest1 t1 h1 h2 ih1 ih2 =>
    intro e he
    cases e with
    | seq e1' e2' =>
        injection he with he1 he2
        obtain ⟨o1', ho1eq, hd1⟩ := ih1 e1' he1
        obtain ⟨t1', ht1eq, hmt1eq⟩ := embedOutcome_ok_inv ho1eq.symm
        subst ht1eq
        obtain ⟨o2', ho2eq, hd2⟩ := ih2 e2' he2
        have hfail2 : o2' = .fail := embedOutcome_fail_inv ho2eq.symm
        subst hfail2
        exact ⟨.fail, rfl, Derives.seqFail₂ e1' e2' input rest1 t1' hd1 hd2⟩
    | _ => injection he
  case altL e1 e2 input rest t h1 ih1 =>
    intro e he
    cases e with
    | alt e1' e2' =>
        injection he with he1 he2
        obtain ⟨o1', ho1eq, hd1⟩ := ih1 e1' he1
        obtain ⟨t1', ht1eq, hmt1eq⟩ := embedOutcome_ok_inv ho1eq.symm
        subst ht1eq
        exact ⟨.ok (.choiceL t1') rest, by simp [embedOutcome, embedTree, hmt1eq],
          Derives.altL e1' e2' input rest t1' hd1⟩
    | _ => injection he
  case altR e1 e2 input rest t h1 h2 ih1 ih2 =>
    intro e he
    cases e with
    | alt e1' e2' =>
        injection he with he1 he2
        obtain ⟨o1', ho1eq, hd1⟩ := ih1 e1' he1
        have hfail1 : o1' = .fail := embedOutcome_fail_inv ho1eq.symm
        subst hfail1
        obtain ⟨o2', ho2eq, hd2⟩ := ih2 e2' he2
        obtain ⟨t2', ht2eq, hmt2eq⟩ := embedOutcome_ok_inv ho2eq.symm
        subst ht2eq
        exact ⟨.ok (.choiceR t2') rest, by simp [embedOutcome, embedTree, hmt2eq],
          Derives.altR e1' e2' input rest t2' hd1 hd2⟩
    | _ => injection he
  case altFail e1 e2 input h1 h2 ih1 ih2 =>
    intro e he
    cases e with
    | alt e1' e2' =>
        injection he with he1 he2
        obtain ⟨o1', ho1eq, hd1⟩ := ih1 e1' he1
        have hfail1 : o1' = .fail := embedOutcome_fail_inv ho1eq.symm
        subst hfail1
        obtain ⟨o2', ho2eq, hd2⟩ := ih2 e2' he2
        have hfail2 : o2' = .fail := embedOutcome_fail_inv ho2eq.symm
        subst hfail2
        exact ⟨.fail, rfl, Derives.altFail e1' e2' input hd1 hd2⟩
    | _ => injection he
  case starNil e1 input h1 ih1 =>
    intro e he
    cases e with
    | star e1' =>
        injection he with he1
        obtain ⟨o1', ho1eq, hd1⟩ := ih1 e1' he1
        have hfail1 : o1' = .fail := embedOutcome_fail_inv ho1eq.symm
        subst hfail1
        exact ⟨.ok .starNil input, rfl, Derives.starNil e1' input hd1⟩
    | _ => injection he
  case starCons e1 input rest rest' t ts h1 h2 ih1 ih2 =>
    intro e he
    cases e with
    | star e1' =>
        injection he with he1
        obtain ⟨o1', ho1eq, hd1⟩ := ih1 e1' he1
        obtain ⟨t1', ht1eq, hmt1eq⟩ := embedOutcome_ok_inv ho1eq.symm
        subst ht1eq
        obtain ⟨o2', ho2eq, hd2⟩ := ih2 (.star e1') (by simp [embedExp, he1])
        obtain ⟨t2', ht2eq, hmt2eq⟩ := embedOutcome_ok_inv ho2eq.symm
        subst ht2eq
        exact ⟨.ok (.starCons t1' t2') rest', by simp [embedOutcome, embedTree, hmt1eq, hmt2eq],
          Derives.starCons e1' input rest rest' t1' t2' hd1 hd2⟩
    | _ => injection he
  case notOk e1 input rest t h1 ih1 =>
    intro e he
    cases e with
    | notP e1' =>
        injection he with he1
        obtain ⟨o1', ho1eq, hd1⟩ := ih1 e1' he1
        obtain ⟨t1', ht1eq, hmt1eq⟩ := embedOutcome_ok_inv ho1eq.symm
        subst ht1eq
        exact ⟨.fail, rfl, Derives.notOk e1' input rest t1' hd1⟩
    | _ => injection he
  case notFail e1 input h1 ih1 =>
    intro e he
    cases e with
    | notP e1' =>
        injection he with he1
        obtain ⟨o1', ho1eq, hd1⟩ := ih1 e1' he1
        have hfail1 : o1' = .fail := embedOutcome_fail_inv ho1eq.symm
        subst hfail1
        exact ⟨.ok .notT input, rfl, Derives.notFail e1' input hd1⟩
    | _ => injection he
  case nil input => trivial
  case cons a as input p rest t vs h1 hp h2 ih1 ih2 => trivial
  case nil input => trivial
  case cons a as input p rest final t vs h1 hp h2 ih1 => trivial
end Shallot.MacroPeg
