import Shallot.Syntax.Grammar
import Shallot.Syntax.Printer
import Shallot.Syntax.Canon
import Shallot.Syntax.TreeToAst
import Shallot.Peg.Semantics
import Shallot.Peg.Props

/-!
# RT-L1 — the LEXEME layer of the parser roundtrip

Derivation-construction kit for the token level of `shallotGrammar`. Every
lemma CONSTRUCTS a `Derives` derivation (the interpreter is connected later
via completeness T3 + determinism T2). The statements are shaped for RT-L2:
canonical printing puts ONE space after every token, so each lemma consumes
`<token chars> ++ ' ' :: r` and leaves exactly `r`, under the follow-set
side condition `noWsB r = true` ("next char is not whitespace, or EOF").

Contents: numeral kit (`digitsVal_natDigits` and digit-span facts),
character-class bridges (Bool checks of `Canon` ↔ grammar sub-expressions),
`stripPrefix?`/`lit` kit, `Spacing` lemmas, the keyword guard failure
(the `!(Keyword !IdCont)` gate inside `Ident`), and the payoff lemmas
`derives_ident` / `derives_number` / `derives_tok` / `derives_kw` /
`derives_eqTok` / `derives_ltTok`, each carrying the tree-extraction fact
(`identName` / `numberVal`) that RT-L2 needs.
-/

set_option autoImplicit false

namespace Shallot

/-! ## Char/Bool basics -/

theorem beqChar_refl (c : Char) : beqChar c c = true := by
  simp [beqChar]

theorem eq_of_beqChar {a b : Char} (h : beqChar a b = true) : a = b := by
  unfold beqChar at h
  simp only [beq_iff_eq] at h
  exact Char.toNat_inj.mp h

theorem beqChar_symm_true {a b : Char} (h : beqChar a b = true) :
    beqChar b a = true := by
  unfold beqChar at h ⊢
  simp only [beq_iff_eq] at h ⊢
  exact h.symm

theorem beqChar_symm_false {a b : Char} (h : beqChar a b = false) :
    beqChar b a = false := by
  cases hb : beqChar b a with
  | false => rfl
  | true => rw [beqChar_symm_true hb] at h; simp at h

/-! ## stripPrefix? kit -/

theorem stripPrefix?_append (s r : List Char) :
    stripPrefix? s (s ++ r) = some r := by
  induction s with
  | nil => rfl
  | cons c cs ih => simp [stripPrefix?, beqChar_refl, ih]

/-- A literal always consumes itself off the front. -/
theorem derives_lit_append (g : Grammar) (s r : List Char) :
    Derives g (.lit s) (s ++ r) (.ok (.leaf s) r) :=
  Derives.litOk s (s ++ r) r (stripPrefix?_append s r)

/-! ## Character-class kit -/

/-- `[0-9]` as a Bool check (mirrors `isIdStartB`/`isIdContB` in Canon). -/
def isDigitB (c : Char) : Bool := leChar '0' c && leChar c '9'

theorem derives_range_ok (g : Grammar) (lo hi c : Char) (r : List Char)
    (h₁ : leChar lo c = true) (h₂ : leChar c hi = true) :
    Derives g (.range lo hi) (c :: r) (.ok (.leaf [c]) r) :=
  Derives.rangeOk lo hi c r (by rw [h₁, h₂]; rfl)

theorem derives_range_fail (g : Grammar) (lo hi c : Char) (r : List Char)
    (h : (leChar lo c && leChar c hi) = false) :
    Derives g (.range lo hi) (c :: r) .fail :=
  Derives.rangeFail lo hi c r h

theorem derives_digit_ok (g : Grammar) (c : Char) (r : List Char)
    (h : isDigitB c = true) :
    Derives g (.range '0' '9') (c :: r) (.ok (.leaf [c]) r) :=
  Derives.rangeOk '0' '9' c r h

theorem derives_digit_fail (g : Grammar) (c : Char) (r : List Char)
    (h : isDigitB c = false) :
    Derives g (.range '0' '9') (c :: r) .fail :=
  Derives.rangeFail '0' '9' c r h

/-- `isIdStartB` success ⇒ `idStartP` succeeds, consuming exactly `c`. -/
theorem idStartP_ok (g : Grammar) (c : Char) (r : List Char)
    (h : isIdStartB c = true) :
    ∃ t, Derives g idStartP (c :: r) (.ok t r) ∧ PTree.chars t = [c] := by
  unfold isIdStartB at h
  cases h1 : (leChar 'a' c && leChar c 'z') with
  | true =>
    exact ⟨.choiceL (.leaf [c]),
      Derives.altL _ _ _ _ _ (Derives.rangeOk _ _ _ _ h1), rfl⟩
  | false =>
    cases h2 : (leChar 'A' c && leChar c 'Z') with
    | true =>
      exact ⟨.choiceR (.choiceL (.leaf [c])),
        Derives.altR _ _ _ _ _ (Derives.rangeFail _ _ _ _ h1)
          (Derives.altL _ _ _ _ _ (Derives.rangeOk _ _ _ _ h2)), rfl⟩
    | false =>
      have h3 : beqChar c '_' = true := by rw [h1, h2] at h; simpa using h
      exact ⟨.choiceR (.choiceR (.leaf [c])),
        Derives.altR _ _ _ _ _ (Derives.rangeFail _ _ _ _ h1)
          (Derives.altR _ _ _ _ _ (Derives.rangeFail _ _ _ _ h2)
            (Derives.chrOk '_' c r (beqChar_symm_true h3))), rfl⟩

/-- `isIdStartB` failure ⇒ `idStartP` fails. -/
theorem idStartP_fail (g : Grammar) (c : Char) (r : List Char)
    (h : isIdStartB c = false) :
    Derives g idStartP (c :: r) .fail := by
  unfold isIdStartB at h
  simp only [Bool.or_eq_false_iff] at h
  exact Derives.altFail _ _ _ (Derives.rangeFail _ _ _ _ h.1.1)
    (Derives.altFail _ _ _ (Derives.rangeFail _ _ _ _ h.1.2)
      (Derives.chrFail _ _ _ (beqChar_symm_false h.2)))

theorem idStartP_fail_nil (g : Grammar) : Derives g idStartP [] .fail :=
  Derives.altFail _ _ _ (Derives.rangeEmpty _ _)
    (Derives.altFail _ _ _ (Derives.rangeEmpty _ _) (Derives.chrEmpty _))

/-- `isIdContB` success ⇒ `idContP` succeeds, consuming exactly `c`. -/
theorem idContP_ok (g : Grammar) (c : Char) (r : List Char)
    (h : isIdContB c = true) :
    ∃ t, Derives g idContP (c :: r) (.ok t r) ∧ PTree.chars t = [c] := by
  unfold isIdContB at h
  cases hs : isIdStartB c with
  | true =>
    obtain ⟨t, ht, hc⟩ := idStartP_ok g c r hs
    exact ⟨.choiceL t, Derives.altL _ _ _ _ _ ht, by simpa [PTree.chars] using hc⟩
  | false =>
    have hdig : (leChar '0' c && leChar c '9') = true := by
      rw [hs] at h; simpa using h
    exact ⟨.choiceR (.leaf [c]),
      Derives.altR _ _ _ _ _ (idStartP_fail g c r hs)
        (Derives.rangeOk _ _ _ _ hdig), rfl⟩

/-- `isIdContB` failure ⇒ `idContP` fails. -/
theorem idContP_fail (g : Grammar) (c : Char) (r : List Char)
    (h : isIdContB c = false) :
    Derives g idContP (c :: r) .fail := by
  unfold isIdContB at h
  simp only [Bool.or_eq_false_iff] at h
  exact Derives.altFail _ _ _ (idStartP_fail g c r h.1)
    (Derives.rangeFail _ _ _ _ h.2)

theorem idContP_fail_nil (g : Grammar) : Derives g idContP [] .fail :=
  Derives.altFail _ _ _ (idStartP_fail_nil g) (Derives.rangeEmpty _ _)

theorem isIdContB_of_start {c : Char} (h : isIdStartB c = true) :
    isIdContB c = true := by
  unfold isIdContB; rw [h]; rfl

/-! ## Numeral kit -/

theorem digitChar_toNat (m : Nat) (h : m < 10) :
    (Char.ofNat ('0'.toNat + m)).toNat = 48 + m := by
  have h10 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨
      m = 8 ∨ m = 9 := by omega
  rcases h10 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem isDigitB_digitChar (m : Nat) (h : m < 10) :
    isDigitB (Char.ofNat (48 + m)) = true := by
  have h10 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨
      m = 8 ∨ m = 9 := by omega
  rcases h10 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem digitsValGo_append (cs ds : List Char) (acc : Nat) :
    digitsValGo (cs ++ ds) acc = digitsValGo ds (digitsValGo cs acc) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, digitsValGo]
    exact ih _

/-- The digit accumulator only ever appends: `go fuel n acc = go fuel n [] ++ acc`. -/
theorem natDigitsGo_acc : ∀ (fuel n : Nat) (acc : List Char),
    natDigitsGo fuel n acc = natDigitsGo fuel n [] ++ acc := by
  intro fuel
  induction fuel with
  | zero => intro n acc; rfl
  | succ fuel ih =>
    intro n acc
    simp only [natDigitsGo]
    by_cases h10 : n < 10
    · simp [h10]
    · simp only [if_neg h10]
      rw [ih (n / 10) (Char.ofNat ('0'.toNat + n % 10) :: acc),
          ih (n / 10) [Char.ofNat ('0'.toNat + n % 10)]]
      simp

theorem digitsVal_natDigitsGo : ∀ (fuel n : Nat), n < fuel →
    digitsVal (natDigitsGo fuel n []) = n := by
  intro fuel
  induction fuel with
  | zero => intro n h; exact absurd h (Nat.not_lt_zero n)
  | succ fuel ih =>
    intro n h
    have hd := digitChar_toNat (n % 10) (by omega)
    have h0 : '0'.toNat = 48 := rfl
    simp only [natDigitsGo]
    by_cases h10 : n < 10
    · rw [if_pos h10]
      simp only [digitsVal, digitsValGo]
      rw [hd, h0]
      omega
    · rw [if_neg h10]
      rw [natDigitsGo_acc]
      simp only [digitsVal] at ih ⊢
      rw [digitsValGo_append, ih (n / 10) (by omega)]
      simp only [digitsValGo]
      rw [hd, h0]
      omega

/-- RT-L1 numeral roundtrip: `digitsVal` inverts `natDigits`. -/
theorem digitsVal_natDigits (n : Nat) : digitsVal (natDigits n) = n :=
  digitsVal_natDigitsGo (n + 1) n (Nat.lt_succ_self n)

theorem natDigitsGo_all_digits : ∀ (fuel n : Nat) (acc : List Char),
    acc.all isDigitB = true → (natDigitsGo fuel n acc).all isDigitB = true := by
  intro fuel
  induction fuel with
  | zero => intro n acc h; exact h
  | succ fuel ih =>
    intro n acc h
    have hd : isDigitB (Char.ofNat (48 + n % 10)) = true :=
      isDigitB_digitChar (n % 10) (by omega)
    simp only [natDigitsGo]
    by_cases h10 : n < 10
    · rw [if_pos h10]
      simp [List.all_cons, hd, h]
    · rw [if_neg h10]
      exact ih (n / 10) _ (by simp [List.all_cons, hd, h])

/-- Every char printed by `natDigits` is a decimal digit. -/
theorem natDigits_all_digits (n : Nat) : (natDigits n).all isDigitB = true :=
  natDigitsGo_all_digits (n + 1) n [] rfl

theorem natDigitsGo_ne_nil : ∀ (fuel n : Nat) (c : Char) (acc : List Char),
    natDigitsGo fuel n (c :: acc) ≠ [] := by
  intro fuel
  induction fuel with
  | zero => intro n c acc; simp [natDigitsGo]
  | succ fuel ih =>
    intro n c acc
    simp only [natDigitsGo]
    by_cases h10 : n < 10
    · rw [if_pos h10]; simp
    · rw [if_neg h10]; exact ih _ _ _

theorem natDigits_ne_nil (n : Nat) : natDigits n ≠ [] := by
  unfold natDigits
  simp only [natDigitsGo]
  by_cases h10 : n < 10
  · rw [if_pos h10]; simp
  · rw [if_neg h10]; exact natDigitsGo_ne_nil _ _ _ _

/-! ## Spacing -/

/-- One whitespace char, as in rule 0: `' ' / '\n' / '\t' / '\r'`. -/
def wsP : PExp := .alt (.chr ' ') (.alt (.chr '\n') (.alt (.chr '\t') (.chr '\r')))

/-- Bool check matching `wsP` (grammar-side argument order for `chrFail`). -/
def isWsB (c : Char) : Bool :=
  beqChar ' ' c || (beqChar '\n' c || (beqChar '\t' c || beqChar '\r' c))

/-- Follow-set condition: empty input, or the head is not whitespace. -/
def noWsB : List Char → Bool
  | [] => true
  | c :: _ => !isWsB c

/-- Prop form of the follow-set condition. -/
def noWs (r : List Char) : Prop := noWsB r = true

theorem noWs_iff (r : List Char) : noWs r ↔ noWsB r = true := Iff.rfl

theorem spacing_rule : ruleAt shallotGrammar.rules NT.spacing = some (.star wsP) := rfl

/-- `wsP` fails at a non-whitespace boundary. -/
theorem wsP_fail (g : Grammar) (r : List Char) (h : noWsB r = true) :
    Derives g wsP r .fail := by
  cases r with
  | nil =>
    exact Derives.altFail _ _ _ (Derives.chrEmpty _)
      (Derives.altFail _ _ _ (Derives.chrEmpty _)
        (Derives.altFail _ _ _ (Derives.chrEmpty _) (Derives.chrEmpty _)))
  | cons c r' =>
    have h' : isWsB c = false := by
      simp only [noWsB, Bool.not_eq_true'] at h
      exact h
    unfold isWsB at h'
    simp only [Bool.or_eq_false_iff] at h'
    exact Derives.altFail _ _ _ (Derives.chrFail _ _ _ h'.1)
      (Derives.altFail _ _ _ (Derives.chrFail _ _ _ h'.2.1)
        (Derives.altFail _ _ _ (Derives.chrFail _ _ _ h'.2.2.1)
          (Derives.chrFail _ _ _ h'.2.2.2)))

/-- Tree of a zero-width `Spacing`. -/
def spaceTreeNil : PTree := .nodeNT NT.spacing .starNil

/-- Tree of a one-space `Spacing` (the canonical printer's shape). -/
def spaceTree : PTree := .nodeNT NT.spacing (.starCons (.choiceL (.leaf [' '])) .starNil)

/-- `Spacing` matches zero characters at a non-whitespace boundary. -/
theorem derives_spacing_nil (r : List Char) (h : noWsB r = true) :
    Derives shallotGrammar (.nt NT.spacing) r (.ok spaceTreeNil r) :=
  Derives.ntOk _ _ _ _ _ spacing_rule (Derives.starNil _ _ (wsP_fail _ r h))

/-- `Spacing` consumes exactly one space when the next char is not whitespace. -/
theorem derives_spacing_one (r : List Char) (h : noWsB r = true) :
    Derives shallotGrammar (.nt NT.spacing) (' ' :: r) (.ok spaceTree r) :=
  Derives.ntOk _ _ _ _ _ spacing_rule
    (Derives.starCons _ _ _ _ _ _
      (Derives.altL _ _ _ _ _ (Derives.chrOk ' ' ' ' r (beqChar_refl ' ')))
      (Derives.starNil _ _ (wsP_fail _ r h)))

/-! ## Star-of-character-class helper -/

/-- Generic: a star over a one-char matcher consumes exactly a span of
matching chars, stopping where the matcher fails; the tree's span is the
consumed chars. -/
theorem derives_star_chars (g : Grammar) (e : PExp) (p : Char → Bool)
    (hok : ∀ (c : Char) (r' : List Char), p c = true →
      ∃ t, Derives g e (c :: r') (.ok t r') ∧ PTree.chars t = [c]) :
    ∀ (cs r : List Char), cs.all p = true → Derives g e r .fail →
      ∃ t, Derives g (.star e) (cs ++ r) (.ok t r) ∧ PTree.chars t = cs := by
  intro cs
  induction cs with
  | nil =>
    intro r _ hfail
    exact ⟨.starNil, Derives.starNil _ _ hfail, rfl⟩
  | cons c cs ih =>
    intro r hall hfail
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨t1, ht1, hc1⟩ := hok c (cs ++ r) hall.1
    obtain ⟨ts, hts, hcs⟩ := ih r hall.2 hfail
    exact ⟨.starCons t1 ts, Derives.starCons _ _ _ _ _ _ ht1 hts,
      by simp [PTree.chars, hc1, hcs]⟩

theorem derives_star_digits (g : Grammar) (cs r : List Char)
    (hall : cs.all isDigitB = true)
    (hfail : Derives g (.range '0' '9') r .fail) :
    ∃ t, Derives g (.star (.range '0' '9')) (cs ++ r) (.ok t r) ∧
      PTree.chars t = cs :=
  derives_star_chars g _ isDigitB
    (fun c r' hc => ⟨.leaf [c], derives_digit_ok g c r' hc, rfl⟩) cs r hall hfail

theorem derives_star_idCont (g : Grammar) (cs r : List Char)
    (hall : cs.all isIdContB = true)
    (hfail : Derives g idContP r .fail) :
    ∃ t, Derives g (.star idContP) (cs ++ r) (.ok t r) ∧ PTree.chars t = cs :=
  derives_star_chars g _ isIdContB (idContP_ok g) cs r hall hfail

/-! ## Token lemmas -/

/-- Tree of `tok s` on canonical input. -/
def tokTree (s : String) : PTree := .seq (.leaf s.toList) spaceTree

theorem derives_tok (s : String) (r : List Char) (h : noWsB r = true) :
    Derives shallotGrammar (tok s) (s.toList ++ ' ' :: r) (.ok (tokTree s) r) := by
  unfold tok tokTree
  exact Derives.seqOk _ _ _ _ _ _ _ (derives_lit_append _ _ _)
    (derives_spacing_one r h)

/-- Tree of `kw s` on canonical input. -/
def kwTree (s : String) : PTree := .seq (.leaf s.toList) (.seq .notT spaceTree)

theorem derives_kw (s : String) (r : List Char) (h : noWsB r = true) :
    Derives shallotGrammar (kw s) (s.toList ++ ' ' :: r) (.ok (kwTree s) r) := by
  unfold kw kwTree
  exact Derives.seqOk _ _ _ _ _ _ _ (derives_lit_append _ _ _)
    (Derives.seqOk _ _ _ _ _ _ _
      (Derives.notFail _ _ (idContP_fail _ ' ' r (by decide)))
      (derives_spacing_one r h))

/-- Tree of `eqTok`/`ltTok` on canonical input. -/
def chrGuardTree (c : Char) : PTree := .seq (.leaf [c]) (.seq .notT spaceTree)

theorem derives_eqTok (r : List Char) (h : noWsB r = true) :
    Derives shallotGrammar eqTok ('=' :: ' ' :: r) (.ok (chrGuardTree '=') r) := by
  unfold eqTok chrGuardTree
  exact Derives.seqOk _ _ _ _ _ _ _ (Derives.chrOk '=' '=' _ (beqChar_refl '='))
    (Derives.seqOk _ _ _ _ _ _ _
      (Derives.notFail _ _ (Derives.chrFail '=' ' ' r (by decide)))
      (derives_spacing_one r h))

theorem derives_ltTok (r : List Char) (h : noWsB r = true) :
    Derives shallotGrammar ltTok ('<' :: ' ' :: r) (.ok (chrGuardTree '<') r) := by
  unfold ltTok chrGuardTree
  exact Derives.seqOk _ _ _ _ _ _ _ (Derives.chrOk '<' '<' _ (beqChar_refl '<'))
    (Derives.seqOk _ _ _ _ _ _ _
      (Derives.notFail _ _ (Derives.chrFail '=' ' ' r (by decide)))
      (derives_spacing_one r h))

/-! ## The keyword guard (R8)

`Ident` opens with `!(Keyword !IdCont)`. On `x ++ ' ' :: r` with `x` a valid
non-keyword identifier, EVERY `lit kw` alternative either fails outright or
succeeds as a proper prefix of `x` — in which case an idCont char follows,
so the inner `!IdCont` fails. Composed through the prioritized choice, the
whole guard body fails, so the outer `notP` succeeds. -/

/-- `e` is harmless inside `seq e (notP idContP)`: it either fails, or
succeeds with an idCont char following. -/
def KillsAfter (g : Grammar) (e : PExp) (input : List Char) : Prop :=
  Derives g e input .fail ∨
  ∃ t rest, Derives g e input (.ok t rest) ∧
    ∃ t' rest', Derives g idContP rest (.ok t' rest')

theorem KillsAfter.altOf {g : Grammar} {e₁ e₂ : PExp} {input : List Char}
    (h₁ : KillsAfter g e₁ input) (h₂ : KillsAfter g e₂ input) :
    KillsAfter g (.alt e₁ e₂) input := by
  cases h₁ with
  | inl hf =>
    cases h₂ with
    | inl hf₂ => exact Or.inl (Derives.altFail _ _ _ hf hf₂)
    | inr hok =>
      obtain ⟨t, rest, hd, hcont⟩ := hok
      exact Or.inr ⟨.choiceR t, rest, Derives.altR _ _ _ _ _ hf hd, hcont⟩
  | inr hok =>
    obtain ⟨t, rest, hd, hcont⟩ := hok
    exact Or.inr ⟨.choiceL t, rest, Derives.altL _ _ _ _ _ hd, hcont⟩

theorem KillsAfter.guard_fails {g : Grammar} {e : PExp} {input : List Char}
    (h : KillsAfter g e input) :
    Derives g (.seq e (.notP idContP)) input .fail := by
  cases h with
  | inl hf => exact Derives.seqFail₁ _ _ _ hf
  | inr hok =>
    obtain ⟨t, rest, hd, t', rest', hcont⟩ := hok
    exact Derives.seqFail₂ _ _ _ _ _ hd (Derives.notOk _ _ _ _ hcont)

/-- Computational core of `KillsAfter` for a literal: no `Derives` inside,
so the prefix induction needs no inversion. -/
def LitKills (kw input : List Char) : Prop :=
  stripPrefix? kw input = none ∨
  ∃ c cs, stripPrefix? kw input = some (c :: cs) ∧ isIdContB c = true

theorem killsAfter_of_litKills {g : Grammar} {kw input : List Char}
    (h : LitKills kw input) : KillsAfter g (.lit kw) input := by
  cases h with
  | inl hnone => exact Or.inl (Derives.litFail _ _ hnone)
  | inr hsome =>
    obtain ⟨c, cs, heq, hcont⟩ := hsome
    obtain ⟨t', ht', _⟩ := idContP_ok g c cs hcont
    exact Or.inr ⟨.leaf kw, c :: cs, Derives.litOk _ _ _ heq, t', cs, ht'⟩

/-- A space-free literal that is not the whole identifier span either
mismatches, or leaves an idCont char at the front of the remainder. -/
theorem litKills_of_ne : ∀ (kw xs r : List Char),
    kw.all (fun c => !beqChar c ' ') = true →
    xs.all isIdContB = true →
    kw ≠ xs →
    LitKills kw (xs ++ ' ' :: r) := by
  intro kw
  induction kw with
  | nil =>
    intro xs r _ hxs hne
    cases xs with
    | nil => exact absurd rfl hne
    | cons c cs =>
      simp only [List.all_cons, Bool.and_eq_true] at hxs
      exact Or.inr ⟨c, cs ++ ' ' :: r, rfl, hxs.1⟩
  | cons k ks ih =>
    intro xs r hkw hxs hne
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hkw
    cases xs with
    | nil =>
      refine Or.inl ?_
      show stripPrefix? (k :: ks) (' ' :: r) = none
      simp [stripPrefix?, hkw.1]
    | cons c cs =>
      simp only [List.all_cons, Bool.and_eq_true] at hxs
      cases hbc : beqChar k c with
      | false =>
        refine Or.inl ?_
        show stripPrefix? (k :: ks) (c :: (cs ++ ' ' :: r)) = none
        simp [stripPrefix?, hbc]
      | true =>
        have hkc : k = c := eq_of_beqChar hbc
        have hne' : ks ≠ cs := fun he => hne (by rw [hkc, he])
        have hstep : stripPrefix? (k :: ks) ((c :: cs) ++ ' ' :: r) =
            stripPrefix? ks (cs ++ ' ' :: r) := by
          simp [stripPrefix?, hbc]
        cases ih cs r hkw.2 hxs.2 hne' with
        | inl hnone => exact Or.inl (hstep.trans hnone)
        | inr hsome =>
          obtain ⟨c', cs', heq, hcont⟩ := hsome
          exact Or.inr ⟨c', cs', hstep.trans heq, hcont⟩

/-- Unpack `validIdentB` into its three Bool facts. -/
theorem validIdentB_spec (x : String) (hx : validIdentB x = true) :
    ∃ c cs, x.toList = c :: cs ∧ isIdStartB c = true ∧ cs.all isIdContB = true ∧
      keywords.contains x = false := by
  unfold validIdentB at hx
  cases hxl : x.toList with
  | nil => rw [hxl] at hx; simp at hx
  | cons c cs =>
    rw [hxl] at hx
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx
    exact ⟨c, cs, rfl, hx.1.1, hx.1.2, hx.2⟩

/-- The whole identifier span is made of idCont chars. -/
theorem validIdentB_all_idCont (x : String) (hx : validIdentB x = true) :
    x.toList.all isIdContB = true := by
  obtain ⟨c, cs, hxl, hstart, hcont, -⟩ := validIdentB_spec x hx
  rw [hxl]
  simp [List.all_cons, isIdContB_of_start hstart, hcont]

/-- R8: for a valid non-keyword identifier `x`, the guard body
`Keyword !IdCont` fails on `x ++ ' ' :: r` — so `Ident`'s leading `notP`
succeeds. -/
theorem keyword_guard_fails (x : String) (r : List Char)
    (hx : validIdentB x = true) :
    Derives shallotGrammar (.seq keywordP (.notP idContP))
      (x.toList ++ ' ' :: r) .fail := by
  obtain ⟨c, cs, hxl, hstart, hcont, hnk⟩ := validIdentB_spec x hx
  have hallx : x.toList.all isIdContB = true := validIdentB_all_idCont x hx
  simp [keywords] at hnk
  have hd : ∀ kw : String, kw.toList.all (fun c => !beqChar c ' ') = true →
      x ≠ kw → KillsAfter shallotGrammar (.lit kw.toList) (x.toList ++ ' ' :: r) := by
    intro kw hsf hne
    refine killsAfter_of_litKills (litKills_of_ne kw.toList x.toList r hsf hallx ?_)
    intro he
    exact hne (String.toList_inj.mp he.symm)
  exact KillsAfter.guard_fails
    (KillsAfter.altOf (hd "if" (by decide) hnk.1)
      (KillsAfter.altOf (hd "then" (by decide) hnk.2.1)
        (KillsAfter.altOf (hd "else" (by decide) hnk.2.2.1)
          (KillsAfter.altOf (hd "let" (by decide) hnk.2.2.2.1)
            (KillsAfter.altOf (hd "in" (by decide) hnk.2.2.2.2.1)
              (KillsAfter.altOf (hd "def" (by decide) hnk.2.2.2.2.2.1)
                (KillsAfter.altOf (hd "true" (by decide) hnk.2.2.2.2.2.2.1)
                  (KillsAfter.altOf (hd "false" (by decide) hnk.2.2.2.2.2.2.2.1)
                    (KillsAfter.altOf (hd "int" (by decide) hnk.2.2.2.2.2.2.2.2.1)
                      (hd "bool" (by decide) hnk.2.2.2.2.2.2.2.2.2))))))))))

/-! ## Ident and Number -/

theorem ident_rule : ruleAt shallotGrammar.rules NT.ident =
    some (.seq (.notP (.seq keywordP (.notP idContP)))
      (.seq (.seq idStartP (.star idContP)) (.nt NT.spacing))) := rfl

theorem number_rule : ruleAt shallotGrammar.rules NT.number =
    some (.seq (.seq (.range '0' '9') (.star (.range '0' '9'))) (.nt NT.spacing)) := rfl

/-- RT-L1 payoff for identifiers: on canonical input `x ++ ' ' :: r`, the
`Ident` nonterminal derives a node whose inner tree extracts back to `x`. -/
theorem derives_ident (x : String) (r : List Char)
    (hx : validIdentB x = true) (hr : noWsB r = true) :
    ∃ t, Derives shallotGrammar (.nt NT.ident) (x.toList ++ ' ' :: r)
        (.ok (.nodeNT NT.ident t) r) ∧ identName t = .ok x := by
  obtain ⟨c, cs, hxl, hstart, hcont, -⟩ := validIdentB_spec x hx
  have hguard := keyword_guard_fails x r hx
  obtain ⟨t0, ht0, hc0⟩ := idStartP_ok shallotGrammar c (cs ++ ' ' :: r) hstart
  obtain ⟨ts, hts, hcs⟩ := derives_star_idCont shallotGrammar cs (' ' :: r) hcont
    (idContP_fail _ ' ' r (by decide))
  refine ⟨.seq .notT (.seq (.seq t0 ts) spaceTree), ?_, ?_⟩
  · apply Derives.ntOk _ _ _ _ _ ident_rule
    rw [hxl] at hguard ⊢
    exact Derives.seqOk _ _ _ _ _ _ _ (Derives.notFail _ _ hguard)
      (Derives.seqOk _ _ _ _ _ _ _
        (Derives.seqOk _ _ _ _ _ _ _ ht0 hts)
        (derives_spacing_one r hr))
  · simp only [identName, PTree.chars, hc0, hcs, List.cons_append, List.nil_append]
    rw [← hxl, String.ofList_toList]

/-- RT-L1 payoff for numerals: on canonical input `natDigits n ++ ' ' :: r`,
the `Number` nonterminal derives a node whose inner tree evaluates to `n`. -/
theorem derives_number (n : Nat) (r : List Char) (hr : noWsB r = true) :
    ∃ t, Derives shallotGrammar (.nt NT.number) (natDigits n ++ ' ' :: r)
        (.ok (.nodeNT NT.number t) r) ∧ numberVal t = .ok (Int.ofNat n) := by
  have hall : (natDigits n).all isDigitB = true := natDigits_all_digits n
  cases hnd : natDigits n with
  | nil => exact absurd hnd (natDigits_ne_nil n)
  | cons d ds =>
    rw [hnd] at hall
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨ts, hts, hcs⟩ := derives_star_digits shallotGrammar ds (' ' :: r) hall.2
      (derives_digit_fail _ ' ' r (by decide))
    refine ⟨.seq (.seq (.leaf [d]) ts) spaceTree, ?_, ?_⟩
    · apply Derives.ntOk _ _ _ _ _ number_rule
      exact Derives.seqOk _ _ _ _ _ _ _
        (Derives.seqOk _ _ _ _ _ _ _ (derives_digit_ok _ d _ hall.1) hts)
        (derives_spacing_one r hr)
    · simp only [numberVal, PTree.chars, hcs, List.cons_append, List.nil_append]
      rw [← hnd, digitsVal_natDigits]

end Shallot
