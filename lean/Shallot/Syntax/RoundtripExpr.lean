import Shallot.Syntax.Lexemes

/-!
# RT-L2 — the EXPRESSION layer of the parser roundtrip

Constructive derivations for `printExpr`/`printArgs` output: for every
printable-canonical expression `e`, the canonical text `printExpr e` parses
(as a `Derives` derivation) at `NT.expr`, and the extracted tree recovers
`e` exactly (`exprOf`).

Structure: the canonical printer renders every compound expression fully
parenthesized and every atom bare, so EVERY `printExpr e` parses as one
`Primary`. The mutual induction (`derives_print_primary` /
`derives_print_argsOpt` / `derives_print_argsTail`) therefore lives at the
`Primary` level, and a single climb-lemma family (`climb_unary` …
`climb_expr`, bundled as `climb_all`) lifts a Primary item through the
operator tiers with EMPTY star/opt continuations, under the follow-set
condition `exprFollowB` (next char is none of the operator heads and not
`'('` — the `'('` exclusion keeps a bare `Ident` from being extended into
a `Call` by the caller's text).

`printableB` — the roundtrip hypothesis — is `canonExpr` strengthened by
excluding `.binop .eqB` nodes: the printer renders `eqB` and `eqI`
identically (`"== "`), and `treeToAst` decodes `"=="` as `eqI`, so only
`eqI` is printable-canonical. The M11 integrator folds `printableB` into
the final roundtrip statement.
-/

set_option autoImplicit false

namespace Shallot

/-! ## Rule lemmas -/

theorem expr_rule : ruleAt shallotGrammar.rules NT.expr =
    some (.alt (.nt NT.ifExpr) (.alt (.nt NT.letExpr) (.nt NT.orE))) := rfl

theorem ifExpr_rule : ruleAt shallotGrammar.rules NT.ifExpr =
    some (.seq (kw "if") (.seq (.nt NT.expr) (.seq (kw "then")
      (.seq (.nt NT.expr) (.seq (kw "else") (.nt NT.expr)))))) := rfl

theorem letExpr_rule : ruleAt shallotGrammar.rules NT.letExpr =
    some (.seq (kw "let") (.seq (.nt NT.ident) (.seq eqTok
      (.seq (.nt NT.expr) (.seq (kw "in") (.nt NT.expr)))))) := rfl

theorem orE_rule : ruleAt shallotGrammar.rules NT.orE =
    some (.seq (.nt NT.andE) (.star (.seq (tok "||") (.nt NT.andE)))) := rfl

theorem andE_rule : ruleAt shallotGrammar.rules NT.andE =
    some (.seq (.nt NT.cmpE) (.star (.seq (tok "&&") (.nt NT.cmpE)))) := rfl

theorem cmpE_rule : ruleAt shallotGrammar.rules NT.cmpE =
    some (.seq (.nt NT.addE)
      (.alt (.seq (.alt (tok "<=") (.alt ltTok (tok "=="))) (.nt NT.addE)) .eps)) := rfl

theorem addE_rule : ruleAt shallotGrammar.rules NT.addE =
    some (.seq (.nt NT.mulE)
      (.star (.seq (.alt (tok "+") (tok "-")) (.nt NT.mulE)))) := rfl

theorem mulE_rule : ruleAt shallotGrammar.rules NT.mulE =
    some (.seq (.nt NT.unary)
      (.star (.seq (.alt (tok "*") (.alt (tok "/") (tok "%"))) (.nt NT.unary)))) := rfl

theorem unary_rule : ruleAt shallotGrammar.rules NT.unary =
    some (.alt (.seq (tok "-") (.nt NT.unary))
      (.alt (.seq (tok "!") (.nt NT.unary)) (.nt NT.primary))) := rfl

theorem primary_rule : ruleAt shallotGrammar.rules NT.primary =
    some (.alt (.nt NT.number) (.alt (kw "true") (.alt (kw "false")
      (.alt (.nt NT.call) (.alt (.nt NT.ident)
        (.seq (tok "(") (.seq (.nt NT.expr) (tok ")")))))))) := rfl

theorem call_rule : ruleAt shallotGrammar.rules NT.call =
    some (.seq (.nt NT.ident)
      (.seq (tok "(") (.seq (PExp.opt (.nt NT.argList)) (tok ")")))) := rfl

theorem argList_rule : ruleAt shallotGrammar.rules NT.argList =
    some (.seq (.nt NT.expr) (.star (.seq (tok ",") (.nt NT.expr)))) := rfl

/-! ## Follow-set predicates -/

/-- The head of `r` (if any) is not `c`. -/
def headNot (c : Char) : List Char → Bool
  | [] => true
  | d :: _ => !beqChar c d

theorem headNot_cons (c d : Char) (ds : List Char) (h : beqChar c d = false) :
    headNot c (d :: ds) = true := by
  simp [headNot, h]

/-- Follow-set condition of a canonically-printed expression: the next
char (if any) starts no operator token and no call-argument list. In
canonical output the actual follows are `then`/`else`/`in`/`)`/`,`/EOF —
all admissible. -/
def exprFollowB : List Char → Bool
  | [] => true
  | c :: _ => !(beqChar '+' c || beqChar '-' c || beqChar '*' c || beqChar '/' c ||
      beqChar '%' c || beqChar '<' c || beqChar '=' c || beqChar '&' c ||
      beqChar '|' c || beqChar '(' c)

theorem exprFollowB_cons (c : Char) (cs : List Char)
    (h : (beqChar '+' c || beqChar '-' c || beqChar '*' c || beqChar '/' c ||
      beqChar '%' c || beqChar '<' c || beqChar '=' c || beqChar '&' c ||
      beqChar '|' c || beqChar '(' c) = false) : exprFollowB (c :: cs) = true := by
  simp only [exprFollowB, h, Bool.not_false]

theorem exprFollowB_spec (r : List Char) (h : exprFollowB r = true) :
    headNot '+' r = true ∧ headNot '-' r = true ∧ headNot '*' r = true ∧
    headNot '/' r = true ∧ headNot '%' r = true ∧ headNot '<' r = true ∧
    headNot '=' r = true ∧ headNot '&' r = true ∧ headNot '|' r = true ∧
    headNot '(' r = true := by
  cases r with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons c cs =>
    simp only [exprFollowB, Bool.not_eq_true', Bool.or_eq_false_iff] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
    exact ⟨headNot_cons _ _ _ h1, headNot_cons _ _ _ h2, headNot_cons _ _ _ h3,
      headNot_cons _ _ _ h4, headNot_cons _ _ _ h5, headNot_cons _ _ _ h6,
      headNot_cons _ _ _ h7, headNot_cons _ _ _ h8, headNot_cons _ _ _ h9,
      headNot_cons _ _ _ h10⟩

theorem noWsB_cons (c : Char) (cs : List Char) (h : isWsB c = false) :
    noWsB (c :: cs) = true := by
  simp [noWsB, h]

/-! ## Character-class facts (codepoint arithmetic) -/

theorem beqChar_digit_ne (k c : Char) (h : isDigitB c = true)
    (hk : k.toNat < 48 ∨ 57 < k.toNat) : beqChar k c = false := by
  cases hb : beqChar k c with
  | false => rfl
  | true =>
    exfalso
    unfold isDigitB leChar at h
    unfold beqChar at hb
    simp only [Bool.and_eq_true, Nat.ble_eq] at h
    simp only [beq_iff_eq] at hb
    have : '0'.toNat = 48 := rfl
    have : '9'.toNat = 57 := rfl
    omega

theorem beqChar_idStart_ne (k c : Char) (h : isIdStartB c = true)
    (hk : k.toNat < 65 ∨ (90 < k.toNat ∧ k.toNat < 95) ∨
      (95 < k.toNat ∧ k.toNat < 97) ∨ 122 < k.toNat) : beqChar k c = false := by
  cases hb : beqChar k c with
  | false => rfl
  | true =>
    exfalso
    unfold isIdStartB leChar beqChar at h
    unfold beqChar at hb
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at h
    simp only [beq_iff_eq] at hb
    have : 'a'.toNat = 97 := rfl
    have : 'z'.toNat = 122 := rfl
    have : 'A'.toNat = 65 := rfl
    have : 'Z'.toNat = 90 := rfl
    have : '_'.toNat = 95 := rfl
    omega

theorem isWsB_digit (c : Char) (h : isDigitB c = true) : isWsB c = false := by
  cases hb : isWsB c with
  | false => rfl
  | true =>
    exfalso
    unfold isDigitB leChar at h
    unfold isWsB beqChar at hb
    simp only [Bool.and_eq_true, Nat.ble_eq] at h
    simp only [Bool.or_eq_true, beq_iff_eq] at hb
    have : '0'.toNat = 48 := rfl
    have : '9'.toNat = 57 := rfl
    have : ' '.toNat = 32 := rfl
    have : '\n'.toNat = 10 := rfl
    have : '\t'.toNat = 9 := rfl
    have : '\r'.toNat = 13 := rfl
    omega

theorem isWsB_idStart (c : Char) (h : isIdStartB c = true) : isWsB c = false := by
  cases hb : isWsB c with
  | false => rfl
  | true =>
    exfalso
    unfold isIdStartB leChar beqChar at h
    unfold isWsB beqChar at hb
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at h
    simp only [Bool.or_eq_true, beq_iff_eq] at hb
    have : 'a'.toNat = 97 := rfl
    have : 'z'.toNat = 122 := rfl
    have : 'A'.toNat = 65 := rfl
    have : 'Z'.toNat = 90 := rfl
    have : '_'.toNat = 95 := rfl
    have : ' '.toNat = 32 := rfl
    have : '\n'.toNat = 10 := rfl
    have : '\t'.toNat = 9 := rfl
    have : '\r'.toNat = 13 := rfl
    omega

theorem isDigitB_idStart (c : Char) (h : isIdStartB c = true) : isDigitB c = false := by
  cases hd : isDigitB c with
  | false => rfl
  | true =>
    exfalso
    unfold isIdStartB leChar beqChar at h
    unfold isDigitB leChar at hd
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at h hd
    have : 'a'.toNat = 97 := rfl
    have : 'z'.toNat = 122 := rfl
    have : 'A'.toNat = 65 := rfl
    have : 'Z'.toNat = 90 := rfl
    have : '_'.toNat = 95 := rfl
    have : '0'.toNat = 48 := rfl
    have : '9'.toNat = 57 := rfl
    omega

/-! ## Head-based failure kit -/

theorem stripPrefix?_head_none (c : Char) (ks input : List Char)
    (h : headNot c input = true) : stripPrefix? (c :: ks) input = none := by
  cases input with
  | nil => rfl
  | cons d ds =>
    simp only [headNot, Bool.not_eq_true'] at h
    simp [stripPrefix?, h]

theorem lit_head_fail (g : Grammar) (c : Char) (ks input : List Char)
    (h : headNot c input = true) : Derives g (.lit (c :: ks)) input .fail :=
  Derives.litFail _ _ (stripPrefix?_head_none c ks input h)

theorem tok_head_fail (g : Grammar) (s : String) (c : Char) (ks input : List Char)
    (hs : s.toList = c :: ks) (h : headNot c input = true) :
    Derives g (tok s) input .fail := by
  unfold tok
  exact Derives.seqFail₁ _ _ _ (hs ▸ lit_head_fail g c ks input h)

theorem kw_head_fail (g : Grammar) (s : String) (c : Char) (ks input : List Char)
    (hs : s.toList = c :: ks) (h : headNot c input = true) :
    Derives g (kw s) input .fail := by
  unfold kw
  exact Derives.seqFail₁ _ _ _ (hs ▸ lit_head_fail g c ks input h)

theorem chr_head_fail (g : Grammar) (c : Char) (input : List Char)
    (h : headNot c input = true) : Derives g (.chr c) input .fail := by
  cases input with
  | nil => exact Derives.chrEmpty c
  | cons d ds =>
    simp only [headNot, Bool.not_eq_true'] at h
    exact Derives.chrFail c d ds h

theorem ltTok_head_fail (g : Grammar) (input : List Char)
    (h : headNot '<' input = true) : Derives g ltTok input .fail :=
  Derives.seqFail₁ _ _ _ (chr_head_fail g '<' input h)

/-- A keyword token dies on any input where its literal either mismatches
or is followed by an identifier-continuation char (`LitKills`, RT-L1). -/
theorem kw_fail_of_litKills (g : Grammar) (s : String) (input : List Char)
    (h : LitKills s.toList input) : Derives g (kw s) input .fail := by
  unfold kw
  cases h with
  | inl hnone => exact Derives.seqFail₁ _ _ _ (Derives.litFail _ _ hnone)
  | inr hsome =>
    obtain ⟨c, cs, heq, hcont⟩ := hsome
    obtain ⟨t', ht', -⟩ := idContP_ok g c cs hcont
    exact Derives.seqFail₂ _ _ _ _ _ (Derives.litOk _ _ _ heq)
      (Derives.seqFail₁ _ _ _ (Derives.notOk _ _ _ _ ht'))

/-! ## Nonterminal failure cascades -/

theorem keywordP_head_fail (g : Grammar) (c : Char) (rest : List Char)
    (h : (beqChar 'i' c || beqChar 't' c || beqChar 'e' c || beqChar 'l' c ||
          beqChar 'd' c || beqChar 'f' c || beqChar 'b' c) = false) :
    Derives g keywordP (c :: rest) .fail := by
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨hi, ht⟩, he⟩, hl⟩, hd⟩, hf⟩, hb⟩ := h
  unfold keywordP
  exact Derives.altFail _ _ _ (lit_head_fail g 'i' _ _ (headNot_cons _ _ _ hi))
    (Derives.altFail _ _ _ (lit_head_fail g 't' _ _ (headNot_cons _ _ _ ht))
      (Derives.altFail _ _ _ (lit_head_fail g 'e' _ _ (headNot_cons _ _ _ he))
        (Derives.altFail _ _ _ (lit_head_fail g 'l' _ _ (headNot_cons _ _ _ hl))
          (Derives.altFail _ _ _ (lit_head_fail g 'i' _ _ (headNot_cons _ _ _ hi))
            (Derives.altFail _ _ _ (lit_head_fail g 'd' _ _ (headNot_cons _ _ _ hd))
              (Derives.altFail _ _ _ (lit_head_fail g 't' _ _ (headNot_cons _ _ _ ht))
                (Derives.altFail _ _ _ (lit_head_fail g 'f' _ _ (headNot_cons _ _ _ hf))
                  (Derives.altFail _ _ _ (lit_head_fail g 'i' _ _ (headNot_cons _ _ _ hi))
                    (lit_head_fail g 'b' _ _ (headNot_cons _ _ _ hb))))))))))

theorem ident_head_fail (c : Char) (rest : List Char)
    (hkw : (beqChar 'i' c || beqChar 't' c || beqChar 'e' c || beqChar 'l' c ||
          beqChar 'd' c || beqChar 'f' c || beqChar 'b' c) = false)
    (hs : isIdStartB c = false) :
    Derives shallotGrammar (.nt NT.ident) (c :: rest) .fail := by
  apply Derives.ntFail _ _ _ ident_rule
  refine Derives.seqFail₂ _ _ _ _ _
    (Derives.notFail _ _ (Derives.seqFail₁ _ _ _ (keywordP_head_fail _ c rest hkw))) ?_
  exact Derives.seqFail₁ _ _ _ (Derives.seqFail₁ _ _ _ (idStartP_fail _ c rest hs))

theorem number_head_fail (c : Char) (rest : List Char) (h : isDigitB c = false) :
    Derives shallotGrammar (.nt NT.number) (c :: rest) .fail :=
  Derives.ntFail _ _ _ number_rule
    (Derives.seqFail₁ _ _ _ (Derives.seqFail₁ _ _ _ (derives_digit_fail _ c rest h)))

theorem call_fail_of_ident_fail (input : List Char)
    (h : Derives shallotGrammar (.nt NT.ident) input .fail) :
    Derives shallotGrammar (.nt NT.call) input .fail :=
  Derives.ntFail _ _ _ call_rule (Derives.seqFail₁ _ _ _ h)

/-- The whole `Primary` (hence every tier and `Expr`) fails on a `')'`-headed
input — the fail-side of the empty-argument-list `Call`. -/
theorem primary_fail_rparen (rest : List Char) :
    Derives shallotGrammar (.nt NT.primary) (')' :: rest) .fail := by
  apply Derives.ntFail _ _ _ primary_rule
  refine Derives.altFail _ _ _ (number_head_fail ')' rest (by decide)) ?_
  refine Derives.altFail _ _ _ (kw_head_fail _ "true" 't' _ _ rfl (headNot_cons _ _ _ (by decide))) ?_
  refine Derives.altFail _ _ _ (kw_head_fail _ "false" 'f' _ _ rfl (headNot_cons _ _ _ (by decide))) ?_
  have hid : Derives shallotGrammar (.nt NT.ident) (')' :: rest) .fail :=
    ident_head_fail ')' rest (by decide) (by decide)
  refine Derives.altFail _ _ _ (call_fail_of_ident_fail _ hid) ?_
  refine Derives.altFail _ _ _ hid ?_
  exact Derives.seqFail₁ _ _ _ (tok_head_fail _ "(" '(' [] _ rfl (headNot_cons _ _ _ (by decide)))

theorem unary_fail_rparen (rest : List Char) :
    Derives shallotGrammar (.nt NT.unary) (')' :: rest) .fail := by
  apply Derives.ntFail _ _ _ unary_rule
  refine Derives.altFail _ _ _
    (Derives.seqFail₁ _ _ _ (tok_head_fail _ "-" '-' [] _ rfl (headNot_cons _ _ _ (by decide)))) ?_
  exact Derives.altFail _ _ _
    (Derives.seqFail₁ _ _ _ (tok_head_fail _ "!" '!' [] _ rfl (headNot_cons _ _ _ (by decide))))
    (primary_fail_rparen rest)

theorem expr_fails_rparen (rest : List Char) :
    Derives shallotGrammar (.nt NT.expr) (')' :: rest) .fail := by
  have hmul : Derives shallotGrammar (.nt NT.mulE) (')' :: rest) .fail :=
    Derives.ntFail _ _ _ mulE_rule (Derives.seqFail₁ _ _ _ (unary_fail_rparen rest))
  have hadd : Derives shallotGrammar (.nt NT.addE) (')' :: rest) .fail :=
    Derives.ntFail _ _ _ addE_rule (Derives.seqFail₁ _ _ _ hmul)
  have hcmp : Derives shallotGrammar (.nt NT.cmpE) (')' :: rest) .fail :=
    Derives.ntFail _ _ _ cmpE_rule (Derives.seqFail₁ _ _ _ hadd)
  have hand : Derives shallotGrammar (.nt NT.andE) (')' :: rest) .fail :=
    Derives.ntFail _ _ _ andE_rule (Derives.seqFail₁ _ _ _ hcmp)
  have hor : Derives shallotGrammar (.nt NT.orE) (')' :: rest) .fail :=
    Derives.ntFail _ _ _ orE_rule (Derives.seqFail₁ _ _ _ hand)
  apply Derives.ntFail _ _ _ expr_rule
  refine Derives.altFail _ _ _
    (Derives.ntFail _ _ _ ifExpr_rule (Derives.seqFail₁ _ _ _
      (kw_head_fail _ "if" 'i' _ _ rfl (headNot_cons _ _ _ (by decide))))) ?_
  exact Derives.altFail _ _ _
    (Derives.ntFail _ _ _ letExpr_rule (Derives.seqFail₁ _ _ _
      (kw_head_fail _ "let" 'l' _ _ rfl (headNot_cons _ _ _ (by decide))))) hor

/-! ## Printable-canonical ASTs

`canonExpr` strengthened by excluding `.binop .eqB`: the printer renders
`eqB` and `eqI` both as `"== "`, and `cmpOf` decodes `"=="` as `eqI`, so
only `eqI` survives a roundtrip. -/

mutual
  def printableB : Expr → Bool
    | .intLit _ => true
    | .boolLit _ => true
    | .var x => validIdentB x
    | .unop .neg (.intLit _) => false
    | .unop _ e => printableB e
    | .binop .eqB _ _ => false
    | .binop _ l r => printableB l && printableB r
    | .ite c t e => printableB c && printableB t && printableB e
    | .letE x bound body => validIdentB x && printableB bound && printableB body
    | .call f args => validIdentB f && printableArgsB args

  def printableArgsB : Args → Bool
    | .nil => true
    | .cons e rest => printableB e && printableArgsB rest
end

/-! ## What canonical text kills

The first characters of `printExpr e` make the keyword alternatives of
`Expr` (`if`/`let`) and the prefix alternatives of `Unary` (`-`/`!`) fail —
the facts every climb from `Primary` to `Expr` needs about its input. -/

structure Kills (input : List Char) : Prop where
  kwIf : Derives shallotGrammar (kw "if") input .fail
  kwLet : Derives shallotGrammar (kw "let") input .fail
  litNeg : Derives shallotGrammar (.lit ['-']) input .fail
  litNot : Derives shallotGrammar (.lit ['!']) input .fail

theorem kills_of_head (c : Char) (cs : List Char)
    (hi : beqChar 'i' c = false) (hl : beqChar 'l' c = false)
    (hm : beqChar '-' c = false) (hn : beqChar '!' c = false) :
    Kills (c :: cs) :=
  ⟨kw_head_fail _ "if" 'i' _ _ rfl (headNot_cons _ _ _ hi),
   kw_head_fail _ "let" 'l' _ _ rfl (headNot_cons _ _ _ hl),
   lit_head_fail _ '-' [] _ (headNot_cons _ _ _ hm),
   lit_head_fail _ '!' [] _ (headNot_cons _ _ _ hn)⟩

/-- On `x ++ ' ' :: rest` with `x` a valid non-keyword identifier, all four
relevant keyword tokens fail (`if`/`let` for the `Expr` climb, `true`/`false`
for the `Primary` alternative order). -/
theorem ident_kws_fail (x : String) (rest : List Char) (hx : validIdentB x = true) :
    Derives shallotGrammar (kw "if") (x.toList ++ ' ' :: rest) .fail ∧
    Derives shallotGrammar (kw "let") (x.toList ++ ' ' :: rest) .fail ∧
    Derives shallotGrammar (kw "true") (x.toList ++ ' ' :: rest) .fail ∧
    Derives shallotGrammar (kw "false") (x.toList ++ ' ' :: rest) .fail := by
  have hall : x.toList.all isIdContB = true := validIdentB_all_idCont x hx
  obtain ⟨c, cs, hxl, hstart, hcont, hnk⟩ := validIdentB_spec x hx
  simp [keywords] at hnk
  have mk : ∀ (s : String), s.toList.all (fun c => !beqChar c ' ') = true → x ≠ s →
      Derives shallotGrammar (kw s) (x.toList ++ ' ' :: rest) .fail := fun s hsf hne =>
    kw_fail_of_litKills _ _ _ (litKills_of_ne s.toList x.toList rest hsf hall
      (fun he => hne (String.toList_inj.mp he.symm)))
  exact ⟨mk "if" (by decide) hnk.1, mk "let" (by decide) hnk.2.2.2.1,
    mk "true" (by decide) hnk.2.2.2.2.2.2.1, mk "false" (by decide) hnk.2.2.2.2.2.2.2.1⟩

/-- The two facts every climb needs about canonical text: it starts with a
non-whitespace char, and it kills `if`/`let`/`-`/`!`. -/
theorem printExpr_text (e : Expr) (he : printableB e = true) (suffix : List Char) :
    noWsB ((printExpr e).toList ++ suffix) = true ∧
    Kills ((printExpr e).toList ++ suffix) := by
  cases e with
  | intLit n =>
    by_cases hn : n < 0
    · have hEq : (printExpr (Expr.intLit n)).toList ++ suffix =
          '(' :: ' ' :: '-' :: ' ' ::
            (natDigits n.natAbs ++ (' ' :: ')' :: ' ' :: suffix)) := by
        simp [printExpr, hn, printNat, String.toList_append, String.toList_ofList,
          List.append_assoc]
      rw [hEq]
      exact ⟨noWsB_cons _ _ (by decide),
        kills_of_head '(' _ (by decide) (by decide) (by decide) (by decide)⟩
    · cases hnd : natDigits n.natAbs with
      | nil => exact absurd hnd (natDigits_ne_nil n.natAbs)
      | cons d ds =>
        have hall := natDigits_all_digits n.natAbs
        rw [hnd] at hall
        simp only [List.all_cons, Bool.and_eq_true] at hall
        have hEq : (printExpr (Expr.intLit n)).toList ++ suffix =
            d :: (ds ++ ' ' :: suffix) := by
          simp [printExpr, hn, printNat, String.toList_append, String.toList_ofList,
            hnd, List.append_assoc]
        rw [hEq]
        exact ⟨noWsB_cons _ _ (isWsB_digit d hall.1),
          kills_of_head d _ (beqChar_digit_ne 'i' d hall.1 (by decide))
            (beqChar_digit_ne 'l' d hall.1 (by decide))
            (beqChar_digit_ne '-' d hall.1 (by decide))
            (beqChar_digit_ne '!' d hall.1 (by decide))⟩
  | boolLit b =>
    cases b with
    | true =>
      have hEq : (printExpr (Expr.boolLit true)).toList ++ suffix =
          't' :: ('r' :: 'u' :: 'e' :: ' ' :: suffix) := by
        simp [printExpr]
      rw [hEq]
      exact ⟨noWsB_cons _ _ (by decide),
        kills_of_head 't' _ (by decide) (by decide) (by decide) (by decide)⟩
    | false =>
      have hEq : (printExpr (Expr.boolLit false)).toList ++ suffix =
          'f' :: ('a' :: 'l' :: 's' :: 'e' :: ' ' :: suffix) := by
        simp [printExpr]
      rw [hEq]
      exact ⟨noWsB_cons _ _ (by decide),
        kills_of_head 'f' _ (by decide) (by decide) (by decide) (by decide)⟩
  | var x =>
    simp only [printableB] at he
    have hEq : (printExpr (Expr.var x)).toList ++ suffix = x.toList ++ ' ' :: suffix := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    obtain ⟨c, cs, hxl, hstart, -, -⟩ := validIdentB_spec x he
    obtain ⟨hIf, hLet, -, -⟩ := ident_kws_fail x suffix he
    refine ⟨?_, hIf, hLet, ?_, ?_⟩
    · rw [hxl]; exact noWsB_cons _ _ (isWsB_idStart c hstart)
    · rw [hxl]
      exact lit_head_fail _ '-' [] _
        (headNot_cons _ _ _ (beqChar_idStart_ne '-' c hstart (by decide)))
    · rw [hxl]
      exact lit_head_fail _ '!' [] _
        (headNot_cons _ _ _ (beqChar_idStart_ne '!' c hstart (by decide)))
  | unop op e' =>
    have hEq : (printExpr (Expr.unop op e')).toList ++ suffix =
        '(' :: ' ' :: ((printUnOp op).toList ++
          ((printExpr e').toList ++ (')' :: ' ' :: suffix))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    exact ⟨noWsB_cons _ _ (by decide),
      kills_of_head '(' _ (by decide) (by decide) (by decide) (by decide)⟩
  | binop op l r' =>
    have hEq : (printExpr (Expr.binop op l r')).toList ++ suffix =
        '(' :: ' ' :: ((printExpr l).toList ++ ((printBinOp op).toList ++
          ((printExpr r').toList ++ (')' :: ' ' :: suffix)))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    exact ⟨noWsB_cons _ _ (by decide),
      kills_of_head '(' _ (by decide) (by decide) (by decide) (by decide)⟩
  | ite c t e' =>
    have hEq : (printExpr (Expr.ite c t e')).toList ++ suffix =
        '(' :: ' ' :: 'i' :: 'f' :: ' ' :: ((printExpr c).toList ++
          ('t' :: 'h' :: 'e' :: 'n' :: ' ' :: ((printExpr t).toList ++
            ('e' :: 'l' :: 's' :: 'e' :: ' ' :: ((printExpr e').toList ++
              (')' :: ' ' :: suffix)))))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    exact ⟨noWsB_cons _ _ (by decide),
      kills_of_head '(' _ (by decide) (by decide) (by decide) (by decide)⟩
  | letE x bound body =>
    have hEq : (printExpr (Expr.letE x bound body)).toList ++ suffix =
        '(' :: ' ' :: 'l' :: 'e' :: 't' :: ' ' :: (x.toList ++
          (' ' :: '=' :: ' ' :: ((printExpr bound).toList ++
            ('i' :: 'n' :: ' ' :: ((printExpr body).toList ++
              (')' :: ' ' :: suffix)))))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    exact ⟨noWsB_cons _ _ (by decide),
      kills_of_head '(' _ (by decide) (by decide) (by decide) (by decide)⟩
  | call f args =>
    simp only [printableB, Bool.and_eq_true] at he
    have hEq : (printExpr (Expr.call f args)).toList ++ suffix =
        f.toList ++ ' ' :: ('(' :: ' ' ::
          ((printArgs args).toList ++ (')' :: ' ' :: suffix))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    obtain ⟨c, cs, hxl, hstart, -, -⟩ := validIdentB_spec f he.1
    obtain ⟨hIf, hLet, -, -⟩ := ident_kws_fail f _ he.1
    refine ⟨?_, hIf, hLet, ?_, ?_⟩
    · rw [hxl]; exact noWsB_cons _ _ (isWsB_idStart c hstart)
    · rw [hxl]
      exact lit_head_fail _ '-' [] _
        (headNot_cons _ _ _ (beqChar_idStart_ne '-' c hstart (by decide)))
    · rw [hxl]
      exact lit_head_fail _ '!' [] _
        (headNot_cons _ _ _ (beqChar_idStart_ne '!' c hstart (by decide)))

/-! ## The climb: Primary → Unary → MulE → AddE → CmpE → AndE → OrE → Expr

Each step wraps a single lower-tier item with an EMPTY star/opt
continuation; the tier's operator tokens must fail on the follow text. -/

theorem climb_unary (input r : List Char) (t : PTree) (e : Expr)
    (hp : Derives shallotGrammar (.nt NT.primary) input (.ok (.nodeNT NT.primary t) r))
    (hres : primaryOf t = .ok e)
    (hminus : Derives shallotGrammar (.lit ['-']) input .fail)
    (hbang : Derives shallotGrammar (.lit ['!']) input .fail) :
    ∃ t', Derives shallotGrammar (.nt NT.unary) input (.ok (.nodeNT NT.unary t') r) ∧
      unaryOf t' = .ok e := by
  refine ⟨.choiceR (.choiceR (.nodeNT NT.primary t)), ?_, by
    simp only [unaryOf]; exact hres⟩
  apply Derives.ntOk _ _ _ _ _ unary_rule
  exact Derives.altR _ _ _ _ _
    (Derives.seqFail₁ _ _ _ (Derives.seqFail₁ _ _ _ hminus))
    (Derives.altR _ _ _ _ _
      (Derives.seqFail₁ _ _ _ (Derives.seqFail₁ _ _ _ hbang)) hp)

theorem climb_mulE (input r : List Char) (t : PTree) (e : Expr)
    (hu : Derives shallotGrammar (.nt NT.unary) input (.ok (.nodeNT NT.unary t) r))
    (hres : unaryOf t = .ok e)
    (h1 : headNot '*' r = true) (h2 : headNot '/' r = true) (h3 : headNot '%' r = true) :
    ∃ t', Derives shallotGrammar (.nt NT.mulE) input (.ok (.nodeNT NT.mulE t') r) ∧
      mulOf t' = .ok e := by
  refine ⟨.seq (.nodeNT NT.unary t) .starNil, ?_, by
    simp only [mulOf, hres]; rfl⟩
  apply Derives.ntOk _ _ _ _ _ mulE_rule
  refine Derives.seqOk _ _ _ _ _ _ _ hu (Derives.starNil _ _ (Derives.seqFail₁ _ _ _ ?_))
  exact Derives.altFail _ _ _ (tok_head_fail _ "*" '*' [] r rfl h1)
    (Derives.altFail _ _ _ (tok_head_fail _ "/" '/' [] r rfl h2)
      (tok_head_fail _ "%" '%' [] r rfl h3))

theorem climb_addE (input r : List Char) (t : PTree) (e : Expr)
    (hm : Derives shallotGrammar (.nt NT.mulE) input (.ok (.nodeNT NT.mulE t) r))
    (hres : mulOf t = .ok e)
    (h1 : headNot '+' r = true) (h2 : headNot '-' r = true) :
    ∃ t', Derives shallotGrammar (.nt NT.addE) input (.ok (.nodeNT NT.addE t') r) ∧
      addOf t' = .ok e := by
  refine ⟨.seq (.nodeNT NT.mulE t) .starNil, ?_, by
    simp only [addOf, hres]; rfl⟩
  apply Derives.ntOk _ _ _ _ _ addE_rule
  refine Derives.seqOk _ _ _ _ _ _ _ hm (Derives.starNil _ _ (Derives.seqFail₁ _ _ _ ?_))
  exact Derives.altFail _ _ _ (tok_head_fail _ "+" '+' [] r rfl h1)
    (tok_head_fail _ "-" '-' [] r rfl h2)

theorem climb_cmpE (input r : List Char) (t : PTree) (e : Expr)
    (ha : Derives shallotGrammar (.nt NT.addE) input (.ok (.nodeNT NT.addE t) r))
    (hres : addOf t = .ok e)
    (h1 : headNot '<' r = true) (h2 : headNot '=' r = true) :
    ∃ t', Derives shallotGrammar (.nt NT.cmpE) input (.ok (.nodeNT NT.cmpE t') r) ∧
      cmpOf t' = .ok e := by
  refine ⟨.seq (.nodeNT NT.addE t) (.choiceR (.leaf [])), ?_, by
    simp only [cmpOf]; exact hres⟩
  apply Derives.ntOk _ _ _ _ _ cmpE_rule
  refine Derives.seqOk _ _ _ _ _ _ _ ha
    (Derives.altR _ _ _ _ _ (Derives.seqFail₁ _ _ _ ?_) (Derives.eps r))
  exact Derives.altFail _ _ _ (tok_head_fail _ "<=" '<' ['='] r rfl h1)
    (Derives.altFail _ _ _ (ltTok_head_fail _ r h1)
      (tok_head_fail _ "==" '=' ['='] r rfl h2))

theorem climb_andE (input r : List Char) (t : PTree) (e : Expr)
    (hc : Derives shallotGrammar (.nt NT.cmpE) input (.ok (.nodeNT NT.cmpE t) r))
    (hres : cmpOf t = .ok e)
    (h1 : headNot '&' r = true) :
    ∃ t', Derives shallotGrammar (.nt NT.andE) input (.ok (.nodeNT NT.andE t') r) ∧
      andOf t' = .ok e := by
  refine ⟨.seq (.nodeNT NT.cmpE t) .starNil, ?_, by
    simp only [andOf, hres]; rfl⟩
  apply Derives.ntOk _ _ _ _ _ andE_rule
  exact Derives.seqOk _ _ _ _ _ _ _ hc (Derives.starNil _ _ (Derives.seqFail₁ _ _ _
    (tok_head_fail _ "&&" '&' ['&'] r rfl h1)))

theorem climb_orE (input r : List Char) (t : PTree) (e : Expr)
    (hn : Derives shallotGrammar (.nt NT.andE) input (.ok (.nodeNT NT.andE t) r))
    (hres : andOf t = .ok e)
    (h1 : headNot '|' r = true) :
    ∃ t', Derives shallotGrammar (.nt NT.orE) input (.ok (.nodeNT NT.orE t') r) ∧
      orOf t' = .ok e := by
  refine ⟨.seq (.nodeNT NT.andE t) .starNil, ?_, by
    simp only [orOf, hres]; rfl⟩
  apply Derives.ntOk _ _ _ _ _ orE_rule
  exact Derives.seqOk _ _ _ _ _ _ _ hn (Derives.starNil _ _ (Derives.seqFail₁ _ _ _
    (tok_head_fail _ "||" '|' ['|'] r rfl h1)))

theorem climb_expr (input r : List Char) (t : PTree) (e : Expr)
    (ho : Derives shallotGrammar (.nt NT.orE) input (.ok (.nodeNT NT.orE t) r))
    (hres : orOf t = .ok e)
    (hif : Derives shallotGrammar (kw "if") input .fail)
    (hlet : Derives shallotGrammar (kw "let") input .fail) :
    ∃ t', Derives shallotGrammar (.nt NT.expr) input (.ok (.nodeNT NT.expr t') r) ∧
      exprOf t' = .ok e := by
  refine ⟨.choiceR (.choiceR (.nodeNT NT.orE t)), ?_, by
    simp only [exprOf]; exact hres⟩
  apply Derives.ntOk _ _ _ _ _ expr_rule
  exact Derives.altR _ _ _ _ _
    (Derives.ntFail _ _ _ ifExpr_rule (Derives.seqFail₁ _ _ _ hif))
    (Derives.altR _ _ _ _ _
      (Derives.ntFail _ _ _ letExpr_rule (Derives.seqFail₁ _ _ _ hlet)) ho)

/-- The full climb: a canonical `Primary` parse of `printExpr e` lifts to
`Expr` under the follow-set condition. -/
theorem climb_all (e : Expr) (r : List Char) (t : PTree)
    (he : printableB e = true)
    (hp : Derives shallotGrammar (.nt NT.primary) ((printExpr e).toList ++ r)
      (.ok (.nodeNT NT.primary t) r))
    (hres : primaryOf t = .ok e)
    (hf : exprFollowB r = true) :
    ∃ t', Derives shallotGrammar (.nt NT.expr) ((printExpr e).toList ++ r)
      (.ok (.nodeNT NT.expr t') r) ∧ exprOf t' = .ok e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := exprFollowB_spec r hf
  obtain ⟨hkIf, hkLet, hkNeg, hkNot⟩ := (printExpr_text e he r).2
  obtain ⟨tu, hu, hru⟩ := climb_unary _ _ t e hp hres hkNeg hkNot
  obtain ⟨tm, hm, hrm⟩ := climb_mulE _ _ tu e hu hru h3 h4 h5
  obtain ⟨ta, hA, hra⟩ := climb_addE _ _ tm e hm hrm h1 h2
  obtain ⟨tc, hc, hrc⟩ := climb_cmpE _ _ ta e hA hra h6 h7
  obtain ⟨tn, hn, hrn⟩ := climb_andE _ _ tc e hc hrc h8
  obtain ⟨to, ho, hro⟩ := climb_orE _ _ tn e hn hrn h9
  exact climb_expr _ _ to e ho hro hkIf hkLet

/-! ## Climb ladder from intermediate tiers

For text INSIDE the printer's parentheses the operand parses stop below the
operator's tier; these lift the assembled tier back up to `Expr`. -/

theorem climb_from_orE (input r : List Char) (t : PTree) (e : Expr)
    (ho : Derives shallotGrammar (.nt NT.orE) input (.ok (.nodeNT NT.orE t) r))
    (hres : orOf t = .ok e)
    (hif : Derives shallotGrammar (kw "if") input .fail)
    (hlet : Derives shallotGrammar (kw "let") input .fail) :
    ∃ t', Derives shallotGrammar (.nt NT.expr) input (.ok (.nodeNT NT.expr t') r) ∧
      exprOf t' = .ok e :=
  climb_expr input r t e ho hres hif hlet

theorem climb_from_andE (input r : List Char) (t : PTree) (e : Expr)
    (hn : Derives shallotGrammar (.nt NT.andE) input (.ok (.nodeNT NT.andE t) r))
    (hres : andOf t = .ok e) (hf : exprFollowB r = true)
    (hif : Derives shallotGrammar (kw "if") input .fail)
    (hlet : Derives shallotGrammar (kw "let") input .fail) :
    ∃ t', Derives shallotGrammar (.nt NT.expr) input (.ok (.nodeNT NT.expr t') r) ∧
      exprOf t' = .ok e := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := exprFollowB_spec r hf
  obtain ⟨to, ho, hro⟩ := climb_orE _ _ t e hn hres h9
  exact climb_expr _ _ to e ho hro hif hlet

theorem climb_from_cmpE (input r : List Char) (t : PTree) (e : Expr)
    (hc : Derives shallotGrammar (.nt NT.cmpE) input (.ok (.nodeNT NT.cmpE t) r))
    (hres : cmpOf t = .ok e) (hf : exprFollowB r = true)
    (hif : Derives shallotGrammar (kw "if") input .fail)
    (hlet : Derives shallotGrammar (kw "let") input .fail) :
    ∃ t', Derives shallotGrammar (.nt NT.expr) input (.ok (.nodeNT NT.expr t') r) ∧
      exprOf t' = .ok e := by
  obtain ⟨-, -, -, -, -, -, -, h8, -, -⟩ := exprFollowB_spec r hf
  obtain ⟨tn, hn, hrn⟩ := climb_andE _ _ t e hc hres h8
  exact climb_from_andE _ _ tn e hn hrn hf hif hlet

theorem climb_from_addE (input r : List Char) (t : PTree) (e : Expr)
    (ha : Derives shallotGrammar (.nt NT.addE) input (.ok (.nodeNT NT.addE t) r))
    (hres : addOf t = .ok e) (hf : exprFollowB r = true)
    (hif : Derives shallotGrammar (kw "if") input .fail)
    (hlet : Derives shallotGrammar (kw "let") input .fail) :
    ∃ t', Derives shallotGrammar (.nt NT.expr) input (.ok (.nodeNT NT.expr t') r) ∧
      exprOf t' = .ok e := by
  obtain ⟨-, -, -, -, -, h6, h7, -, -, -⟩ := exprFollowB_spec r hf
  obtain ⟨tc, hc, hrc⟩ := climb_cmpE _ _ t e ha hres h6 h7
  exact climb_from_cmpE _ _ tc e hc hrc hf hif hlet

theorem climb_from_mulE (input r : List Char) (t : PTree) (e : Expr)
    (hm : Derives shallotGrammar (.nt NT.mulE) input (.ok (.nodeNT NT.mulE t) r))
    (hres : mulOf t = .ok e) (hf : exprFollowB r = true)
    (hif : Derives shallotGrammar (kw "if") input .fail)
    (hlet : Derives shallotGrammar (kw "let") input .fail) :
    ∃ t', Derives shallotGrammar (.nt NT.expr) input (.ok (.nodeNT NT.expr t') r) ∧
      exprOf t' = .ok e := by
  obtain ⟨h1, h2, -, -, -, -, -, -, -, -⟩ := exprFollowB_spec r hf
  obtain ⟨ta, hA, hra⟩ := climb_addE _ _ t e hm hres h1 h2
  exact climb_from_addE _ _ ta e hA hra hf hif hlet

theorem climb_from_unary (input r : List Char) (t : PTree) (e : Expr)
    (hu : Derives shallotGrammar (.nt NT.unary) input (.ok (.nodeNT NT.unary t) r))
    (hres : unaryOf t = .ok e) (hf : exprFollowB r = true)
    (hif : Derives shallotGrammar (kw "if") input .fail)
    (hlet : Derives shallotGrammar (kw "let") input .fail) :
    ∃ t', Derives shallotGrammar (.nt NT.expr) input (.ok (.nodeNT NT.expr t') r) ∧
      exprOf t' = .ok e := by
  obtain ⟨-, -, h3, h4, h5, -, -, -, -, -⟩ := exprFollowB_spec r hf
  obtain ⟨tm, hm, hrm⟩ := climb_mulE _ _ t e hu hres h3 h4 h5
  exact climb_from_mulE _ _ tm e hm hrm hf hif hlet

/-! ## Paren wrapper and tier assemblies -/

/-- The paren alternative of `Primary`: `'(' ' '` + inner `Expr` + `') '`.
The five preceding alternatives all fail on `'('`. -/
theorem derives_primary_paren (inner r : List Char) (t : PTree) (e : Expr)
    (hin : Derives shallotGrammar (.nt NT.expr) inner
      (.ok (.nodeNT NT.expr t) (')' :: ' ' :: r)))
    (hres : exprOf t = .ok e) (hnw : noWsB inner = true) (hr : noWsB r = true) :
    ∃ tp, Derives shallotGrammar (.nt NT.primary) ('(' :: ' ' :: inner)
      (.ok (.nodeNT NT.primary tp) r) ∧ primaryOf tp = .ok e := by
  refine ⟨.choiceR (.choiceR (.choiceR (.choiceR (.choiceR
    (.seq (tokTree "(") (.seq (.nodeNT NT.expr t) (tokTree ")"))))))), ?_, by
      simp only [primaryOf]; exact hres⟩
  apply Derives.ntOk _ _ _ _ _ primary_rule
  have hid : Derives shallotGrammar (.nt NT.ident) ('(' :: ' ' :: inner) .fail :=
    ident_head_fail '(' _ (by decide) (by decide)
  refine Derives.altR _ _ _ _ _ (number_head_fail '(' _ (by decide)) ?_
  refine Derives.altR _ _ _ _ _
    (kw_head_fail _ "true" 't' _ _ rfl (headNot_cons _ _ _ (by decide))) ?_
  refine Derives.altR _ _ _ _ _
    (kw_head_fail _ "false" 'f' _ _ rfl (headNot_cons _ _ _ (by decide))) ?_
  refine Derives.altR _ _ _ _ _ (call_fail_of_ident_fail _ hid) ?_
  refine Derives.altR _ _ _ _ _ hid ?_
  exact Derives.seqOk _ _ _ _ _ _ _ (derives_tok "(" inner hnw)
    (Derives.seqOk _ _ _ _ _ _ _ hin (derives_tok ")" r hr))

/-- One star iteration at the `MulE` tier: `Unary op Unary`, star ends. -/
theorem assemble_mulE (input mid rest₁ rest : List Char) (tA tB opT : PTree)
    (hA : Derives shallotGrammar (.nt NT.unary) input (.ok (.nodeNT NT.unary tA) mid))
    (hop : Derives shallotGrammar (.alt (tok "*") (.alt (tok "/") (tok "%"))) mid
      (.ok opT rest₁))
    (hB : Derives shallotGrammar (.nt NT.unary) rest₁ (.ok (.nodeNT NT.unary tB) rest))
    (h1 : headNot '*' rest = true) (h2 : headNot '/' rest = true)
    (h3 : headNot '%' rest = true) :
    Derives shallotGrammar (.nt NT.mulE) input (.ok (.nodeNT NT.mulE
      (.seq (.nodeNT NT.unary tA)
        (.starCons (.seq opT (.nodeNT NT.unary tB)) .starNil))) rest) := by
  apply Derives.ntOk _ _ _ _ _ mulE_rule
  refine Derives.seqOk _ _ _ _ _ _ _ hA ?_
  refine Derives.starCons _ _ _ _ _ _ (Derives.seqOk _ _ _ _ _ _ _ hop hB) ?_
  exact Derives.starNil _ _ (Derives.seqFail₁ _ _ _
    (Derives.altFail _ _ _ (tok_head_fail _ "*" '*' [] rest rfl h1)
      (Derives.altFail _ _ _ (tok_head_fail _ "/" '/' [] rest rfl h2)
        (tok_head_fail _ "%" '%' [] rest rfl h3))))

/-- One star iteration at the `AddE` tier: `MulE op MulE`, star ends. -/
theorem assemble_addE (input mid rest₁ rest : List Char) (tA tB opT : PTree)
    (hA : Derives shallotGrammar (.nt NT.mulE) input (.ok (.nodeNT NT.mulE tA) mid))
    (hop : Derives shallotGrammar (.alt (tok "+") (tok "-")) mid (.ok opT rest₁))
    (hB : Derives shallotGrammar (.nt NT.mulE) rest₁ (.ok (.nodeNT NT.mulE tB) rest))
    (h1 : headNot '+' rest = true) (h2 : headNot '-' rest = true) :
    Derives shallotGrammar (.nt NT.addE) input (.ok (.nodeNT NT.addE
      (.seq (.nodeNT NT.mulE tA)
        (.starCons (.seq opT (.nodeNT NT.mulE tB)) .starNil))) rest) := by
  apply Derives.ntOk _ _ _ _ _ addE_rule
  refine Derives.seqOk _ _ _ _ _ _ _ hA ?_
  refine Derives.starCons _ _ _ _ _ _ (Derives.seqOk _ _ _ _ _ _ _ hop hB) ?_
  exact Derives.starNil _ _ (Derives.seqFail₁ _ _ _
    (Derives.altFail _ _ _ (tok_head_fail _ "+" '+' [] rest rfl h1)
      (tok_head_fail _ "-" '-' [] rest rfl h2)))

/-- The filled `opt` at the `CmpE` tier: `AddE op AddE` (no star). -/
theorem assemble_cmpE (input mid rest₁ rest : List Char) (tA tB opT : PTree)
    (hA : Derives shallotGrammar (.nt NT.addE) input (.ok (.nodeNT NT.addE tA) mid))
    (hop : Derives shallotGrammar (.alt (tok "<=") (.alt ltTok (tok "=="))) mid
      (.ok opT rest₁))
    (hB : Derives shallotGrammar (.nt NT.addE) rest₁ (.ok (.nodeNT NT.addE tB) rest)) :
    Derives shallotGrammar (.nt NT.cmpE) input (.ok (.nodeNT NT.cmpE
      (.seq (.nodeNT NT.addE tA)
        (.choiceL (.seq opT (.nodeNT NT.addE tB))))) rest) := by
  apply Derives.ntOk _ _ _ _ _ cmpE_rule
  exact Derives.seqOk _ _ _ _ _ _ _ hA
    (Derives.altL _ _ _ _ _ (Derives.seqOk _ _ _ _ _ _ _ hop hB))

/-- One star iteration at the `AndE` tier: `CmpE "&&" CmpE`, star ends. -/
theorem assemble_andE (input mid rest₁ rest : List Char) (tA tB opT : PTree)
    (hA : Derives shallotGrammar (.nt NT.cmpE) input (.ok (.nodeNT NT.cmpE tA) mid))
    (hop : Derives shallotGrammar (tok "&&") mid (.ok opT rest₁))
    (hB : Derives shallotGrammar (.nt NT.cmpE) rest₁ (.ok (.nodeNT NT.cmpE tB) rest))
    (h1 : headNot '&' rest = true) :
    Derives shallotGrammar (.nt NT.andE) input (.ok (.nodeNT NT.andE
      (.seq (.nodeNT NT.cmpE tA)
        (.starCons (.seq opT (.nodeNT NT.cmpE tB)) .starNil))) rest) := by
  apply Derives.ntOk _ _ _ _ _ andE_rule
  refine Derives.seqOk _ _ _ _ _ _ _ hA ?_
  refine Derives.starCons _ _ _ _ _ _ (Derives.seqOk _ _ _ _ _ _ _ hop hB) ?_
  exact Derives.starNil _ _ (Derives.seqFail₁ _ _ _
    (tok_head_fail _ "&&" '&' ['&'] rest rfl h1))

/-- One star iteration at the `OrE` tier: `AndE "||" AndE`, star ends. -/
theorem assemble_orE (input mid rest₁ rest : List Char) (tA tB opT : PTree)
    (hA : Derives shallotGrammar (.nt NT.andE) input (.ok (.nodeNT NT.andE tA) mid))
    (hop : Derives shallotGrammar (tok "||") mid (.ok opT rest₁))
    (hB : Derives shallotGrammar (.nt NT.andE) rest₁ (.ok (.nodeNT NT.andE tB) rest))
    (h1 : headNot '|' rest = true) :
    Derives shallotGrammar (.nt NT.orE) input (.ok (.nodeNT NT.orE
      (.seq (.nodeNT NT.andE tA)
        (.starCons (.seq opT (.nodeNT NT.andE tB)) .starNil))) rest) := by
  apply Derives.ntOk _ _ _ _ _ orE_rule
  refine Derives.seqOk _ _ _ _ _ _ _ hA ?_
  refine Derives.starCons _ _ _ _ _ _ (Derives.seqOk _ _ _ _ _ _ _ hop hB) ?_
  exact Derives.starNil _ _ (Derives.seqFail₁ _ _ _
    (tok_head_fail _ "||" '|' ['|'] rest rfl h1))

/-! ## Argument-list text -/

/-- The `(", " Expr)*` region of a printed argument list. -/
def argsTailText : Args → List Char
  | .nil => []
  | .cons e rest => ',' :: ' ' :: ((printExpr e).toList ++ argsTailText rest)

theorem printArgs_cons_toList (e : Expr) (rest : Args) :
    (printArgs (.cons e rest)).toList = (printExpr e).toList ++ argsTailText rest := by
  cases rest with
  | nil => simp [printArgs, argsTailText]
  | cons e' rest' =>
    simp [printArgs, argsTailText, String.toList_append,
      printArgs_cons_toList e' rest', List.append_assoc]

/-- Whatever the argument tail is, the text after an argument expression
starts with `','` or `')'` — an admissible expression follow. -/
theorem argsTail_follow (as : Args) (r : List Char) :
    noWsB (argsTailText as ++ (')' :: ' ' :: r)) = true ∧
    exprFollowB (argsTailText as ++ (')' :: ' ' :: r)) = true ∧
    headNot '(' (argsTailText as ++ (')' :: ' ' :: r)) = true := by
  cases as with
  | nil =>
    exact ⟨noWsB_cons _ _ (by decide), exprFollowB_cons _ _ (by decide),
      headNot_cons _ _ _ (by decide)⟩
  | cons e rest =>
    exact ⟨noWsB_cons _ _ (by decide), exprFollowB_cons _ _ (by decide),
      headNot_cons _ _ _ (by decide)⟩

/-- `noWsB` holds at the head of any identifier span. -/
theorem noWs_ident (x : String) (rest : List Char) (hx : validIdentB x = true) :
    noWsB (x.toList ++ rest) = true := by
  obtain ⟨c, cs, hxl, hstart, -, -⟩ := validIdentB_spec x hx
  rw [hxl]
  exact noWsB_cons _ _ (isWsB_idStart c hstart)

/-! ## Operand lifts

A canonically-printed operand (a `Primary` parse of `printExpr x`) lifted
to the tier just below its operator — the star/opt items of the tiers
BELOW must fail on the operator's first char. -/

theorem operand_to_unary (x : Expr) (suffix : List Char) (t : PTree)
    (hx : printableB x = true)
    (hp : Derives shallotGrammar (.nt NT.primary) ((printExpr x).toList ++ suffix)
      (.ok (.nodeNT NT.primary t) suffix))
    (hres : primaryOf t = .ok x) :
    ∃ t', Derives shallotGrammar (.nt NT.unary) ((printExpr x).toList ++ suffix)
      (.ok (.nodeNT NT.unary t') suffix) ∧ unaryOf t' = .ok x := by
  obtain ⟨-, hk⟩ := printExpr_text x hx suffix
  exact climb_unary _ _ t x hp hres hk.litNeg hk.litNot

theorem operand_to_mulE (x : Expr) (suffix : List Char) (t : PTree)
    (hx : printableB x = true)
    (hp : Derives shallotGrammar (.nt NT.primary) ((printExpr x).toList ++ suffix)
      (.ok (.nodeNT NT.primary t) suffix))
    (hres : primaryOf t = .ok x)
    (h1 : headNot '*' suffix = true) (h2 : headNot '/' suffix = true)
    (h3 : headNot '%' suffix = true) :
    ∃ t', Derives shallotGrammar (.nt NT.mulE) ((printExpr x).toList ++ suffix)
      (.ok (.nodeNT NT.mulE t') suffix) ∧ mulOf t' = .ok x := by
  obtain ⟨tu, hu, huv⟩ := operand_to_unary x suffix t hx hp hres
  exact climb_mulE _ _ tu x hu huv h1 h2 h3

theorem operand_to_addE (x : Expr) (suffix : List Char) (t : PTree)
    (hx : printableB x = true)
    (hp : Derives shallotGrammar (.nt NT.primary) ((printExpr x).toList ++ suffix)
      (.ok (.nodeNT NT.primary t) suffix))
    (hres : primaryOf t = .ok x)
    (h1 : headNot '*' suffix = true) (h2 : headNot '/' suffix = true)
    (h3 : headNot '%' suffix = true) (h4 : headNot '+' suffix = true)
    (h5 : headNot '-' suffix = true) :
    ∃ t', Derives shallotGrammar (.nt NT.addE) ((printExpr x).toList ++ suffix)
      (.ok (.nodeNT NT.addE t') suffix) ∧ addOf t' = .ok x := by
  obtain ⟨tm, hm, hmv⟩ := operand_to_mulE x suffix t hx hp hres h1 h2 h3
  exact climb_addE _ _ tm x hm hmv h4 h5

theorem operand_to_cmpE (x : Expr) (suffix : List Char) (t : PTree)
    (hx : printableB x = true)
    (hp : Derives shallotGrammar (.nt NT.primary) ((printExpr x).toList ++ suffix)
      (.ok (.nodeNT NT.primary t) suffix))
    (hres : primaryOf t = .ok x)
    (h1 : headNot '*' suffix = true) (h2 : headNot '/' suffix = true)
    (h3 : headNot '%' suffix = true) (h4 : headNot '+' suffix = true)
    (h5 : headNot '-' suffix = true) (h6 : headNot '<' suffix = true)
    (h7 : headNot '=' suffix = true) :
    ∃ t', Derives shallotGrammar (.nt NT.cmpE) ((printExpr x).toList ++ suffix)
      (.ok (.nodeNT NT.cmpE t') suffix) ∧ cmpOf t' = .ok x := by
  obtain ⟨ta, hA, hav⟩ := operand_to_addE x suffix t hx hp hres h1 h2 h3 h4 h5
  exact climb_cmpE _ _ ta x hA hav h6 h7

theorem operand_to_andE (x : Expr) (suffix : List Char) (t : PTree)
    (hx : printableB x = true)
    (hp : Derives shallotGrammar (.nt NT.primary) ((printExpr x).toList ++ suffix)
      (.ok (.nodeNT NT.primary t) suffix))
    (hres : primaryOf t = .ok x)
    (h1 : headNot '*' suffix = true) (h2 : headNot '/' suffix = true)
    (h3 : headNot '%' suffix = true) (h4 : headNot '+' suffix = true)
    (h5 : headNot '-' suffix = true) (h6 : headNot '<' suffix = true)
    (h7 : headNot '=' suffix = true) (h8 : headNot '&' suffix = true) :
    ∃ t', Derives shallotGrammar (.nt NT.andE) ((printExpr x).toList ++ suffix)
      (.ok (.nodeNT NT.andE t') suffix) ∧ andOf t' = .ok x := by
  obtain ⟨tc, hc, hcv⟩ := operand_to_cmpE x suffix t hx hp hres h1 h2 h3 h4 h5 h6 h7
  exact climb_andE _ _ tc x hc hcv h8

/-! ## Call decode helpers

Stated with the `ArgList?` subtree already in constructor form, so the
matcher inside `callOf` iota-reduces and no rewriting happens under a
dependent match. -/

theorem callOf_decode_nil (ti tf t1 t2 : PTree) (f : String)
    (hiV : identName ti = .ok f) :
    callOf (.seq (.nodeNT NT.ident ti) (.seq t1 (.seq (.choiceR tf) t2))) =
      .ok (.call f .nil) := by
  simp only [callOf]
  rw [hiV]
  rfl

theorem callOf_decode_cons (ti alT t1 t2 : PTree) (f : String) (as : Args)
    (hiV : identName ti = .ok f) (hres : argListOf alT = .ok as) :
    callOf (.seq (.nodeNT NT.ident ti)
      (.seq t1 (.seq (.choiceL (.nodeNT NT.argList alT)) t2))) =
      .ok (.call f as) := by
  simp only [callOf]
  rw [hiV, hres]
  rfl

/-! ## The mutual payoff: canonical text parses as a Primary -/

mutual

/-- RT-L2 core: `printExpr e` parses as ONE `Primary`, and the tree
extracts back to `e`. Follow conditions: next char is not whitespace
(`Spacing` must stop) and not `'('` (a bare `Ident` must not extend into
a `Call`). -/
theorem derives_print_primary (e : Expr) (r : List Char)
    (he : printableB e = true) (hws : noWsB r = true) (hpr : headNot '(' r = true) :
    ∃ t, Derives shallotGrammar (.nt NT.primary) ((printExpr e).toList ++ r)
      (.ok (.nodeNT NT.primary t) r) ∧ primaryOf t = .ok e := by
  cases e with
  | intLit n =>
    by_cases hn : n < 0
    · -- `( - digits ) ` → paren alternative, Unary's "-" branch, Number
      have hdig : noWsB (natDigits n.natAbs ++ ' ' :: (')' :: ' ' :: r)) = true ∧
          Derives shallotGrammar (.lit ['-'])
            (natDigits n.natAbs ++ ' ' :: (')' :: ' ' :: r)) .fail ∧
          Derives shallotGrammar (.lit ['!'])
            (natDigits n.natAbs ++ ' ' :: (')' :: ' ' :: r)) .fail := by
        cases hnd : natDigits n.natAbs with
        | nil => exact absurd hnd (natDigits_ne_nil _)
        | cons d ds =>
          have hall := natDigits_all_digits n.natAbs
          rw [hnd] at hall
          simp only [List.all_cons, Bool.and_eq_true] at hall
          exact ⟨noWsB_cons _ _ (isWsB_digit d hall.1),
            lit_head_fail _ '-' [] _
              (headNot_cons _ _ _ (beqChar_digit_ne '-' d hall.1 (by decide))),
            lit_head_fail _ '!' [] _
              (headNot_cons _ _ _ (beqChar_digit_ne '!' d hall.1 (by decide)))⟩
      obtain ⟨hnwD, hkNeg, hkNot⟩ := hdig
      have hEq : (printExpr (Expr.intLit n)).toList ++ r =
          '(' :: ' ' :: ('-' :: ' ' :: (natDigits n.natAbs ++ ' ' :: (')' :: ' ' :: r))) := by
        simp [printExpr, hn, printNat, String.toList_ofList, String.toList_append,
          List.append_assoc]
      rw [hEq]
      obtain ⟨tn, hnD, hnV⟩ := derives_number n.natAbs (')' :: ' ' :: r)
        (noWsB_cons _ _ (by decide))
      have hprim : Derives shallotGrammar (.nt NT.primary)
          (natDigits n.natAbs ++ ' ' :: (')' :: ' ' :: r))
          (.ok (.nodeNT NT.primary (.choiceL (.nodeNT NT.number tn))) (')' :: ' ' :: r)) :=
        Derives.ntOk _ _ _ _ _ primary_rule (Derives.altL _ _ _ _ _ hnD)
      have hpv : primaryOf (.choiceL (.nodeNT NT.number tn)) =
          .ok (.intLit (Int.ofNat n.natAbs)) := by
        simp only [primaryOf, hnV]; rfl
      obtain ⟨tu, hu, huv⟩ := climb_unary _ _ _ _ hprim hpv hkNeg hkNot
      have hU2 := Derives.ntOk _ _ _ _ _ unary_rule (Derives.altL _ _ _ _ _
        (Derives.seqOk _ _ _ _ _ _ _ (derives_tok "-" _ hnwD) hu))
      have hU2v : unaryOf (.choiceL (.seq (tokTree "-") (.nodeNT NT.unary tu))) =
          .ok (.intLit n) := by
        have h1 : unaryOf (.choiceL (.seq (tokTree "-") (.nodeNT NT.unary tu))) =
            .ok (.intLit (-(Int.ofNat n.natAbs))) := by
          simp only [unaryOf, huv]; rfl
        rw [h1, show -(Int.ofNat n.natAbs) = n from by
          have hc : Int.ofNat n.natAbs = (n.natAbs : Int) := rfl
          rw [hc]; omega]
      obtain ⟨tE, hEd, hEv⟩ := climb_from_unary _ _ _ _ hU2 hU2v
        (exprFollowB_cons _ _ (by decide))
        (kw_head_fail _ "if" 'i' _ _ rfl (headNot_cons _ _ _ (by decide)))
        (kw_head_fail _ "let" 'l' _ _ rfl (headNot_cons _ _ _ (by decide)))
      exact derives_primary_paren _ r tE _ hEd hEv (noWsB_cons _ _ (by decide)) hws
    · -- bare digits → Number alternative
      have hEq : (printExpr (Expr.intLit n)).toList ++ r = natDigits n.natAbs ++ ' ' :: r := by
        simp [printExpr, hn, printNat, String.toList_ofList, String.toList_append,
          List.append_assoc]
      rw [hEq]
      obtain ⟨tn, hnD, hnV⟩ := derives_number n.natAbs r hws
      rw [show Int.ofNat n.natAbs = n from by
        have hc : Int.ofNat n.natAbs = (n.natAbs : Int) := rfl
        rw [hc]; omega] at hnV
      refine ⟨.choiceL (.nodeNT NT.number tn), ?_, ?_⟩
      · exact Derives.ntOk _ _ _ _ _ primary_rule (Derives.altL _ _ _ _ _ hnD)
      · simp only [primaryOf, hnV]; rfl
  | boolLit b =>
    cases b with
    | true =>
      have hEq : (printExpr (Expr.boolLit true)).toList ++ r =
          't' :: 'r' :: 'u' :: 'e' :: ' ' :: r := by
        simp [printExpr]
      rw [hEq]
      refine ⟨.choiceR (.choiceL (kwTree "true")), ?_, by simp [primaryOf]⟩
      apply Derives.ntOk _ _ _ _ _ primary_rule
      exact Derives.altR _ _ _ _ _ (number_head_fail 't' _ (by decide))
        (Derives.altL _ _ _ _ _ (derives_kw "true" r hws))
    | false =>
      have hEq : (printExpr (Expr.boolLit false)).toList ++ r =
          'f' :: 'a' :: 'l' :: 's' :: 'e' :: ' ' :: r := by
        simp [printExpr]
      rw [hEq]
      refine ⟨.choiceR (.choiceR (.choiceL (kwTree "false"))), ?_, by simp [primaryOf]⟩
      apply Derives.ntOk _ _ _ _ _ primary_rule
      refine Derives.altR _ _ _ _ _ (number_head_fail 'f' _ (by decide)) ?_
      refine Derives.altR _ _ _ _ _
        (kw_head_fail _ "true" 't' _ _ rfl (headNot_cons _ _ _ (by decide))) ?_
      exact Derives.altL _ _ _ _ _ (derives_kw "false" r hws)
  | var x =>
    simp only [printableB] at he
    have hEq : (printExpr (Expr.var x)).toList ++ r = x.toList ++ ' ' :: r := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    obtain ⟨c, cs, hxl, hstart, -, -⟩ := validIdentB_spec x he
    obtain ⟨-, -, hTr, hFa⟩ := ident_kws_fail x r he
    obtain ⟨ti, htiD, htiV⟩ := derives_ident x r he hws
    have hnum : Derives shallotGrammar (.nt NT.number) (x.toList ++ ' ' :: r) .fail := by
      rw [hxl]
      exact number_head_fail c _ (isDigitB_idStart c hstart)
    have hcall : Derives shallotGrammar (.nt NT.call) (x.toList ++ ' ' :: r) .fail := by
      apply Derives.ntFail _ _ _ call_rule
      exact Derives.seqFail₂ _ _ _ _ _ htiD
        (Derives.seqFail₁ _ _ _ (tok_head_fail _ "(" '(' [] r rfl hpr))
    refine ⟨.choiceR (.choiceR (.choiceR (.choiceR (.choiceL (.nodeNT NT.ident ti))))),
      ?_, ?_⟩
    · apply Derives.ntOk _ _ _ _ _ primary_rule
      exact Derives.altR _ _ _ _ _ hnum (Derives.altR _ _ _ _ _ hTr
        (Derives.altR _ _ _ _ _ hFa (Derives.altR _ _ _ _ _ hcall
          (Derives.altL _ _ _ _ _ htiD))))
    · simp only [primaryOf, htiV]; rfl
  | unop op e' =>
    cases op with
    | neg =>
      have hne : ∀ m : Int, e' ≠ .intLit m := by
        intro m hm
        subst hm
        simp [printableB] at he
      have he' : printableB e' = true := by
        cases e' <;> simp_all [printableB]
      have hEq : (printExpr (Expr.unop .neg e')).toList ++ r =
          '(' :: ' ' :: ('-' :: ' ' :: ((printExpr e').toList ++ (')' :: ' ' :: r))) := by
        simp [printExpr, printUnOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwS, hkS⟩ := printExpr_text e' he' (')' :: ' ' :: r)
      obtain ⟨tp, hp, hpv⟩ := derives_print_primary e' (')' :: ' ' :: r) he'
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tu, hu, huv⟩ := climb_unary _ _ tp e' hp hpv hkS.litNeg hkS.litNot
      have hU2 := Derives.ntOk _ _ _ _ _ unary_rule (Derives.altL _ _ _ _ _
        (Derives.seqOk _ _ _ _ _ _ _ (derives_tok "-" _ hnwS) hu))
      have hU2v : unaryOf (.choiceL (.seq (tokTree "-") (.nodeNT NT.unary tu))) =
          .ok (.unop .neg e') := by
        simp only [unaryOf, huv]
        cases e' <;> first | (exact absurd rfl (hne _)) | rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_unary _ _ _ _ hU2 hU2v
        (exprFollowB_cons _ _ (by decide))
        (kw_head_fail _ "if" 'i' _ _ rfl (headNot_cons _ _ _ (by decide)))
        (kw_head_fail _ "let" 'l' _ _ rfl (headNot_cons _ _ _ (by decide)))
      exact derives_primary_paren _ r tE _ hEd hEv (noWsB_cons _ _ (by decide)) hws
    | notB =>
      have he' : printableB e' = true := by
        simpa [printableB] using he
      have hEq : (printExpr (Expr.unop .notB e')).toList ++ r =
          '(' :: ' ' :: ('!' :: ' ' :: ((printExpr e').toList ++ (')' :: ' ' :: r))) := by
        simp [printExpr, printUnOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwS, hkS⟩ := printExpr_text e' he' (')' :: ' ' :: r)
      obtain ⟨tp, hp, hpv⟩ := derives_print_primary e' (')' :: ' ' :: r) he'
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tu, hu, huv⟩ := climb_unary _ _ tp e' hp hpv hkS.litNeg hkS.litNot
      have hU2 := Derives.ntOk _ _ _ _ _ unary_rule (Derives.altR _ _ _ _ _
        (Derives.seqFail₁ _ _ _
          (tok_head_fail _ "-" '-' [] _ rfl (headNot_cons _ _ _ (by decide))))
        (Derives.altL _ _ _ _ _
          (Derives.seqOk _ _ _ _ _ _ _ (derives_tok "!" _ hnwS) hu)))
      have hU2v : unaryOf (.choiceR (.choiceL (.seq (tokTree "!") (.nodeNT NT.unary tu)))) =
          .ok (.unop .notB e') := by
        simp only [unaryOf, huv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_unary _ _ _ _ hU2 hU2v
        (exprFollowB_cons _ _ (by decide))
        (kw_head_fail _ "if" 'i' _ _ rfl (headNot_cons _ _ _ (by decide)))
        (kw_head_fail _ "let" 'l' _ _ rfl (headNot_cons _ _ _ (by decide)))
      exact derives_primary_paren _ r tE _ hEd hEv (noWsB_cons _ _ (by decide)) hws
  | binop op l r' =>
    cases op with
    | add =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .add l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('+' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('+' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tmB, hmB, hmBv⟩ := operand_to_mulE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('+' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tmA, hmA, hmAv⟩ := operand_to_mulE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hAdd := assemble_addE _ _ _ _ tmA tmB (.choiceL (tokTree "+")) hmA
        (Derives.altL _ _ _ _ _ (derives_tok "+" _ hnwB)) hmB
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      have hAddV : addOf (.seq (.nodeNT NT.mulE tmA)
          (.starCons (.seq (.choiceL (tokTree "+")) (.nodeNT NT.mulE tmB)) .starNil)) =
          .ok (.binop .add l r') := by
        simp only [addOf, hmAv, goAdd, hmBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_addE _ _ _ _ hAdd hAddV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | sub =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .sub l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('-' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('-' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tmB, hmB, hmBv⟩ := operand_to_mulE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('-' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tmA, hmA, hmAv⟩ := operand_to_mulE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hAdd := assemble_addE _ _ _ _ tmA tmB (.choiceR (tokTree "-")) hmA
        (Derives.altR _ _ _ _ _
          (tok_head_fail _ "+" '+' [] _ rfl (headNot_cons _ _ _ (by decide)))
          (derives_tok "-" _ hnwB)) hmB
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      have hAddV : addOf (.seq (.nodeNT NT.mulE tmA)
          (.starCons (.seq (.choiceR (tokTree "-")) (.nodeNT NT.mulE tmB)) .starNil)) =
          .ok (.binop .sub l r') := by
        simp only [addOf, hmAv, goAdd, hmBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_addE _ _ _ _ hAdd hAddV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | mul =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .mul l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('*' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('*' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tuB, huB, huBv⟩ := operand_to_unary r' _ tpB he.2 hpB hpBv
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('*' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tuA, huA, huAv⟩ := operand_to_unary l _ tpA he.1 hpA hpAv
      have hMul := assemble_mulE _ _ _ _ tuA tuB (.choiceL (tokTree "*")) huA
        (Derives.altL _ _ _ _ _ (derives_tok "*" _ hnwB)) huB
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hMulV : mulOf (.seq (.nodeNT NT.unary tuA)
          (.starCons (.seq (.choiceL (tokTree "*")) (.nodeNT NT.unary tuB)) .starNil)) =
          .ok (.binop .mul l r') := by
        simp only [mulOf, huAv, goMul, huBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_mulE _ _ _ _ hMul hMulV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | div =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .div l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('/' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('/' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tuB, huB, huBv⟩ := operand_to_unary r' _ tpB he.2 hpB hpBv
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('/' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tuA, huA, huAv⟩ := operand_to_unary l _ tpA he.1 hpA hpAv
      have hMul := assemble_mulE _ _ _ _ tuA tuB (.choiceR (.choiceL (tokTree "/"))) huA
        (Derives.altR _ _ _ _ _
          (tok_head_fail _ "*" '*' [] _ rfl (headNot_cons _ _ _ (by decide)))
          (Derives.altL _ _ _ _ _ (derives_tok "/" _ hnwB))) huB
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hMulV : mulOf (.seq (.nodeNT NT.unary tuA)
          (.starCons (.seq (.choiceR (.choiceL (tokTree "/"))) (.nodeNT NT.unary tuB))
            .starNil)) = .ok (.binop .div l r') := by
        simp only [mulOf, huAv, goMul, huBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_mulE _ _ _ _ hMul hMulV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | mod =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .mod l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('%' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('%' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tuB, huB, huBv⟩ := operand_to_unary r' _ tpB he.2 hpB hpBv
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('%' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tuA, huA, huAv⟩ := operand_to_unary l _ tpA he.1 hpA hpAv
      have hMul := assemble_mulE _ _ _ _ tuA tuB
        (.choiceR (.choiceR (tokTree "%"))) huA
        (Derives.altR _ _ _ _ _
          (tok_head_fail _ "*" '*' [] _ rfl (headNot_cons _ _ _ (by decide)))
          (Derives.altR _ _ _ _ _
            (tok_head_fail _ "/" '/' [] _ rfl (headNot_cons _ _ _ (by decide)))
            (derives_tok "%" _ hnwB))) huB
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hMulV : mulOf (.seq (.nodeNT NT.unary tuA)
          (.starCons (.seq (.choiceR (.choiceR (tokTree "%"))) (.nodeNT NT.unary tuB))
            .starNil)) = .ok (.binop .mod l r') := by
        simp only [mulOf, huAv, goMul, huBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_mulE _ _ _ _ hMul hMulV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | lt =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .lt l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('<' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('<' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨taB, haB, haBv⟩ := operand_to_addE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('<' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨taA, haA, haAv⟩ := operand_to_addE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hCmp := assemble_cmpE _ _ _ _ taA taB
        (.choiceR (.choiceL (chrGuardTree '<'))) haA
        (Derives.altR _ _ _ _ _
          (Derives.seqFail₁ _ _ _ (Derives.litFail _ _ rfl))
          (Derives.altL _ _ _ _ _ (derives_ltTok _ hnwB))) haB
      have hCmpV : cmpOf (.seq (.nodeNT NT.addE taA)
          (.choiceL (.seq (.choiceR (.choiceL (chrGuardTree '<')))
            (.nodeNT NT.addE taB)))) = .ok (.binop .lt l r') := by
        simp only [cmpOf, haAv, haBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_cmpE _ _ _ _ hCmp hCmpV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | le =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .le l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('<' :: '=' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('<' :: '=' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨taB, haB, haBv⟩ := operand_to_addE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('<' :: '=' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨taA, haA, haAv⟩ := operand_to_addE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hCmp := assemble_cmpE _ _ _ _ taA taB (.choiceL (tokTree "<=")) haA
        (Derives.altL _ _ _ _ _ (derives_tok "<=" _ hnwB)) haB
      have hCmpV : cmpOf (.seq (.nodeNT NT.addE taA)
          (.choiceL (.seq (.choiceL (tokTree "<=")) (.nodeNT NT.addE taB)))) =
          .ok (.binop .le l r') := by
        simp only [cmpOf, haAv, haBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_cmpE _ _ _ _ hCmp hCmpV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | eqI =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .eqI l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('=' :: '=' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('=' :: '=' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨taB, haB, haBv⟩ := operand_to_addE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('=' :: '=' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨taA, haA, haAv⟩ := operand_to_addE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hCmp := assemble_cmpE _ _ _ _ taA taB
        (.choiceR (.choiceR (tokTree "=="))) haA
        (Derives.altR _ _ _ _ _
          (tok_head_fail _ "<=" '<' ['='] _ rfl (headNot_cons _ _ _ (by decide)))
          (Derives.altR _ _ _ _ _
            (ltTok_head_fail _ _ (headNot_cons _ _ _ (by decide)))
            (derives_tok "==" _ hnwB))) haB
      have hCmpV : cmpOf (.seq (.nodeNT NT.addE taA)
          (.choiceL (.seq (.choiceR (.choiceR (tokTree "=="))) (.nodeNT NT.addE taB)))) =
          .ok (.binop .eqI l r') := by
        simp only [cmpOf, haAv, haBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_cmpE _ _ _ _ hCmp hCmpV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | eqB =>
      simp [printableB] at he
    | andB =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .andB l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('&' :: '&' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('&' :: '&' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tcB, hcB, hcBv⟩ := operand_to_cmpE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('&' :: '&' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tcA, hcA, hcAv⟩ := operand_to_cmpE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hAnd := assemble_andE _ _ _ _ tcA tcB (tokTree "&&") hcA
        (derives_tok "&&" _ hnwB) hcB (headNot_cons _ _ _ (by decide))
      have hAndV : andOf (.seq (.nodeNT NT.cmpE tcA)
          (.starCons (.seq (tokTree "&&") (.nodeNT NT.cmpE tcB)) .starNil)) =
          .ok (.binop .andB l r') := by
        simp only [andOf, hcAv, goAnd, hcBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_andE _ _ _ _ hAnd hAndV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | orB =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .orB l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('|' :: '|' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('|' :: '|' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tnB, hnB, hnBv⟩ := operand_to_andE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('|' :: '|' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tnA, hnA, hnAv⟩ := operand_to_andE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      have hOr := assemble_orE _ _ _ _ tnA tnB (tokTree "||") hnA
        (derives_tok "||" _ hnwB) hnB (headNot_cons _ _ _ (by decide))
      have hOrV : orOf (.seq (.nodeNT NT.andE tnA)
          (.starCons (.seq (tokTree "||") (.nodeNT NT.andE tnB)) .starNil)) =
          .ok (.binop .orB l r') := by
        simp only [orOf, hnAv, goOr, hnBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_expr _ _ _ _ hOr hOrV hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
  | ite c t e' =>
    simp only [printableB, Bool.and_eq_true] at he
    obtain ⟨⟨hc, ht2⟩, he'⟩ := he
    have hEq : (printExpr (Expr.ite c t e')).toList ++ r =
        '(' :: ' ' :: ('i' :: 'f' :: ' ' :: ((printExpr c).toList ++
          ('t' :: 'h' :: 'e' :: 'n' :: ' ' :: ((printExpr t).toList ++
            ('e' :: 'l' :: 's' :: 'e' :: ' ' :: ((printExpr e').toList ++
              (')' :: ' ' :: r))))))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    obtain ⟨tpC, hpC, hpCv⟩ := derives_print_primary c
      ('t' :: 'h' :: 'e' :: 'n' :: ' ' :: ((printExpr t).toList ++
        ('e' :: 'l' :: 's' :: 'e' :: ' ' :: ((printExpr e').toList ++
          (')' :: ' ' :: r))))) hc
      (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
    obtain ⟨tC, hCd, hCv⟩ := climb_all c _ tpC hc hpC hpCv (exprFollowB_cons _ _ (by decide))
    obtain ⟨tpT, hpT, hpTv⟩ := derives_print_primary t
      ('e' :: 'l' :: 's' :: 'e' :: ' ' :: ((printExpr e').toList ++ (')' :: ' ' :: r))) ht2
      (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
    obtain ⟨tT, hTd, hTv⟩ := climb_all t _ tpT ht2 hpT hpTv (exprFollowB_cons _ _ (by decide))
    obtain ⟨tpE, hpE, hpEv⟩ := derives_print_primary e' (')' :: ' ' :: r) he'
      (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
    obtain ⟨tEe, hEd, hEv⟩ := climb_all e' _ tpE he' hpE hpEv (exprFollowB_cons _ _ (by decide))
    have hIf := Derives.ntOk _ _ _ _ _ ifExpr_rule
      (Derives.seqOk _ _ _ _ _ _ _
        (derives_kw "if" _ (printExpr_text c hc
          ('t' :: 'h' :: 'e' :: 'n' :: ' ' :: ((printExpr t).toList ++
            ('e' :: 'l' :: 's' :: 'e' :: ' ' :: ((printExpr e').toList ++
              (')' :: ' ' :: r)))))).1)
        (Derives.seqOk _ _ _ _ _ _ _ hCd
          (Derives.seqOk _ _ _ _ _ _ _
            (derives_kw "then" _ (printExpr_text t ht2
              ('e' :: 'l' :: 's' :: 'e' :: ' ' :: ((printExpr e').toList ++
                (')' :: ' ' :: r)))).1)
            (Derives.seqOk _ _ _ _ _ _ _ hTd
              (Derives.seqOk _ _ _ _ _ _ _
                (derives_kw "else" _ (printExpr_text e' he' (')' :: ' ' :: r)).1)
                hEd)))))
    have hEx := Derives.ntOk _ _ _ _ _ expr_rule (Derives.altL _ _ _ _ _ hIf)
    have hExV : exprOf (.choiceL (.nodeNT NT.ifExpr
        (.seq (kwTree "if") (.seq (.nodeNT NT.expr tC) (.seq (kwTree "then")
          (.seq (.nodeNT NT.expr tT) (.seq (kwTree "else") (.nodeNT NT.expr tEe)))))))) =
        .ok (.ite c t e') := by
      simp only [exprOf, ifOf, hCv, hTv, hEv]; rfl
    exact derives_primary_paren _ r _ _ hEx hExV (noWsB_cons _ _ (by decide)) hws
  | letE x bound body =>
    simp only [printableB, Bool.and_eq_true] at he
    obtain ⟨⟨hx, hb⟩, hbd⟩ := he
    have hEq : (printExpr (Expr.letE x bound body)).toList ++ r =
        '(' :: ' ' :: ('l' :: 'e' :: 't' :: ' ' :: (x.toList ++
          (' ' :: '=' :: ' ' :: ((printExpr bound).toList ++
            ('i' :: 'n' :: ' ' :: ((printExpr body).toList ++ (')' :: ' ' :: r))))))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    obtain ⟨ti, hiD, hiV⟩ := derives_ident x
      ('=' :: ' ' :: ((printExpr bound).toList ++
        ('i' :: 'n' :: ' ' :: ((printExpr body).toList ++ (')' :: ' ' :: r))))) hx
      (noWsB_cons _ _ (by decide))
    obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary bound
      ('i' :: 'n' :: ' ' :: ((printExpr body).toList ++ (')' :: ' ' :: r))) hb
      (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
    obtain ⟨tB, hBd, hBv⟩ := climb_all bound _ tpB hb hpB hpBv
      (exprFollowB_cons _ _ (by decide))
    obtain ⟨tpD, hpD, hpDv⟩ := derives_print_primary body (')' :: ' ' :: r) hbd
      (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
    obtain ⟨tD, hDd, hDv⟩ := climb_all body _ tpD hbd hpD hpDv
      (exprFollowB_cons _ _ (by decide))
    have hLet := Derives.ntOk _ _ _ _ _ letExpr_rule
      (Derives.seqOk _ _ _ _ _ _ _ (derives_kw "let" _ (noWs_ident x _ hx))
        (Derives.seqOk _ _ _ _ _ _ _ hiD
          (Derives.seqOk _ _ _ _ _ _ _
            (derives_eqTok _ (printExpr_text bound hb
              ('i' :: 'n' :: ' ' :: ((printExpr body).toList ++ (')' :: ' ' :: r)))).1)
            (Derives.seqOk _ _ _ _ _ _ _ hBd
              (Derives.seqOk _ _ _ _ _ _ _
                (derives_kw "in" _ (printExpr_text body hbd (')' :: ' ' :: r)).1)
                hDd)))))
    have hEx := Derives.ntOk _ _ _ _ _ expr_rule
      (Derives.altR _ _ _ _ _
        (Derives.ntFail _ _ _ ifExpr_rule (Derives.seqFail₁ _ _ _
          (kw_head_fail _ "if" 'i' _ _ rfl (headNot_cons _ _ _ (by decide)))))
        (Derives.altL _ _ _ _ _ hLet))
    have hExV : exprOf (.choiceR (.choiceL (.nodeNT NT.letExpr
        (.seq (kwTree "let") (.seq (.nodeNT NT.ident ti) (.seq (chrGuardTree '=')
          (.seq (.nodeNT NT.expr tB) (.seq (kwTree "in") (.nodeNT NT.expr tD))))))))) =
        .ok (.letE x bound body) := by
      simp only [exprOf, letOf, hiV, hBv, hDv]; rfl
    exact derives_primary_paren _ r _ _ hEx hExV (noWsB_cons _ _ (by decide)) hws
  | call f args =>
    simp only [printableB, Bool.and_eq_true] at he
    have hEq : (printExpr (Expr.call f args)).toList ++ r =
        f.toList ++ ' ' :: ('(' :: ' ' ::
          ((printArgs args).toList ++ (')' :: ' ' :: r))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    obtain ⟨c0, cs0, hxl, hstart, -, -⟩ := validIdentB_spec f he.1
    obtain ⟨-, -, hTr, hFa⟩ := ident_kws_fail f
      ('(' :: ' ' :: ((printArgs args).toList ++ (')' :: ' ' :: r))) he.1
    obtain ⟨ti, hiD, hiV⟩ := derives_ident f
      ('(' :: ' ' :: ((printArgs args).toList ++ (')' :: ' ' :: r))) he.1
      (noWsB_cons _ _ (by decide))
    have hnum : Derives shallotGrammar (.nt NT.number)
        (f.toList ++ ' ' :: ('(' :: ' ' ::
          ((printArgs args).toList ++ (')' :: ' ' :: r)))) .fail := by
      rw [hxl]
      exact number_head_fail c0 _ (isDigitB_idStart c0 hstart)
    have hnwArgs : noWsB ((printArgs args).toList ++ (')' :: ' ' :: r)) = true := by
      cases args with
      | nil =>
        have h0 : (printArgs Args.nil).toList = ([] : List Char) := by simp [printArgs]
        rw [h0]
        exact noWsB_cons _ _ (by decide)
      | cons e0 rest0 =>
        rw [printArgs_cons_toList, List.append_assoc]
        have ha0 : printableB e0 = true := by
          have h2 := he.2
          simp only [printableArgsB, Bool.and_eq_true] at h2
          exact h2.1
        exact (printExpr_text e0 ha0 _).1
    obtain ⟨taT, haD, haV⟩ := derives_print_argsOpt args r he.2
    refine ⟨.choiceR (.choiceR (.choiceR (.choiceL (.nodeNT NT.call
      (.seq (.nodeNT NT.ident ti) (.seq (tokTree "(") (.seq taT (tokTree ")")))))))),
      ?_, ?_⟩
    · apply Derives.ntOk _ _ _ _ _ primary_rule
      refine Derives.altR _ _ _ _ _ hnum ?_
      refine Derives.altR _ _ _ _ _ hTr ?_
      refine Derives.altR _ _ _ _ _ hFa ?_
      apply Derives.altL
      apply Derives.ntOk _ _ _ _ _ call_rule
      refine Derives.seqOk _ _ _ _ _ _ _ hiD ?_
      refine Derives.seqOk _ _ _ _ _ _ _ (derives_tok "(" _ hnwArgs) ?_
      exact Derives.seqOk _ _ _ _ _ _ _ haD (derives_tok ")" r hws)
    · cases haV with
      | inl h =>
        obtain ⟨tf, h1, h2⟩ := h
        subst h1; subst h2
        simp only [primaryOf]
        exact callOf_decode_nil ti tf _ _ f hiV
      | inr h =>
        obtain ⟨alT, h1, h2⟩ := h
        subst h1
        simp only [primaryOf]
        exact callOf_decode_cons ti alT _ _ f args hiV h2

/-- The `ArgList? ")"`-region content: `printArgs as` parses as the
optional argument list, stopping exactly at the closing `') '`. -/
theorem derives_print_argsOpt (as : Args) (r : List Char) (ha : printableArgsB as = true) :
    ∃ t, Derives shallotGrammar (PExp.opt (.nt NT.argList))
      ((printArgs as).toList ++ (')' :: ' ' :: r)) (.ok t (')' :: ' ' :: r)) ∧
      ((∃ tf, t = .choiceR tf ∧ as = .nil) ∨
       (∃ alT, t = .choiceL (.nodeNT NT.argList alT) ∧ argListOf alT = .ok as)) := by
  cases as with
  | nil =>
    have hEq : (printArgs Args.nil).toList ++ (')' :: ' ' :: r) = ')' :: ' ' :: r := by
      simp [printArgs]
    rw [hEq]
    refine ⟨.choiceR (.leaf []), ?_, Or.inl ⟨.leaf [], rfl, rfl⟩⟩
    exact Derives.altR _ _ _ _ _
      (Derives.ntFail _ _ _ argList_rule
        (Derives.seqFail₁ _ _ _ (expr_fails_rparen _)))
      (Derives.eps _)
  | cons e rest =>
    simp only [printableArgsB, Bool.and_eq_true] at ha
    have hEq : (printArgs (Args.cons e rest)).toList ++ (')' :: ' ' :: r) =
        (printExpr e).toList ++ (argsTailText rest ++ (')' :: ' ' :: r)) := by
      rw [printArgs_cons_toList, List.append_assoc]
    rw [hEq]
    obtain ⟨hnwF, hefF, hprF⟩ := argsTail_follow rest r
    obtain ⟨tp, hp, hpv⟩ := derives_print_primary e
      (argsTailText rest ++ (')' :: ' ' :: r)) ha.1 hnwF hprF
    obtain ⟨tE, hEd, hEv⟩ := climb_all e _ tp ha.1 hp hpv hefF
    obtain ⟨ts, hsD, hsV⟩ := derives_print_argsTail rest r ha.2
    refine ⟨.choiceL (.nodeNT NT.argList (.seq (.nodeNT NT.expr tE) ts)), ?_,
      Or.inr ⟨_, rfl, ?_⟩⟩
    · apply Derives.altL
      apply Derives.ntOk _ _ _ _ _ argList_rule
      exact Derives.seqOk _ _ _ _ _ _ _ hEd hsD
    · simp only [argListOf, hEv, hsV]; rfl

/-- The `(", " Expr)*` region: `argsTailText as` parses as the star,
stopping exactly at the closing `') '`. -/
theorem derives_print_argsTail (as : Args) (r : List Char) (ha : printableArgsB as = true) :
    ∃ t, Derives shallotGrammar (.star (.seq (tok ",") (.nt NT.expr)))
      (argsTailText as ++ (')' :: ' ' :: r)) (.ok t (')' :: ' ' :: r)) ∧
      argItems t = .ok as := by
  cases as with
  | nil =>
    have hEq : argsTailText Args.nil ++ (')' :: ' ' :: r) = ')' :: ' ' :: r := by
      simp [argsTailText]
    rw [hEq]
    refine ⟨.starNil, ?_, rfl⟩
    exact Derives.starNil _ _ (Derives.seqFail₁ _ _ _
      (tok_head_fail _ "," ',' [] _ rfl (headNot_cons _ _ _ (by decide))))
  | cons e rest =>
    simp only [printableArgsB, Bool.and_eq_true] at ha
    have hEq : argsTailText (Args.cons e rest) ++ (')' :: ' ' :: r) =
        ',' :: ' ' :: ((printExpr e).toList ++ (argsTailText rest ++ (')' :: ' ' :: r))) := by
      simp [argsTailText, List.append_assoc]
    rw [hEq]
    obtain ⟨hnwF, hefF, hprF⟩ := argsTail_follow rest r
    obtain ⟨tp, hp, hpv⟩ := derives_print_primary e
      (argsTailText rest ++ (')' :: ' ' :: r)) ha.1 hnwF hprF
    obtain ⟨tE, hEd, hEv⟩ := climb_all e _ tp ha.1 hp hpv hefF
    obtain ⟨ts, hsD, hsV⟩ := derives_print_argsTail rest r ha.2
    have hnwE : noWsB ((printExpr e).toList ++ (argsTailText rest ++ (')' :: ' ' :: r))) =
        true := (printExpr_text e ha.1 _).1
    refine ⟨.starCons (.seq (tokTree ",") (.nodeNT NT.expr tE)) ts, ?_, ?_⟩
    · exact Derives.starCons _ _ _ _ _ _
        (Derives.seqOk _ _ _ _ _ _ _ (derives_tok "," _ hnwE) hEd) hsD
    · simp only [argItems, hEv, hsV]; rfl

end

/-! ## RT-L2 payoff -/

/-- RT-L2, expression layer: for every printable-canonical `e`, the
canonical text `printExpr e` (followed by any admissible `r`) parses at
`NT.expr` consuming exactly the printed text, and the parse tree extracts
back to `e`. -/
theorem derives_printExpr (e : Expr) (r : List Char)
    (he : printableB e = true) (hws : noWsB r = true) (hf : exprFollowB r = true) :
    ∃ t, Derives shallotGrammar (.nt NT.expr) ((printExpr e).toList ++ r)
      (.ok (.nodeNT NT.expr t) r) ∧ exprOf t = .ok e := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10⟩ := exprFollowB_spec r hf
  obtain ⟨t, hp, hres⟩ := derives_print_primary e r he hws h10
  exact climb_all e r t he hp hres hf

/-- Mirror of the `ArgList?` match inside `callOf`. -/
def argsOptOf : PTree → Except ParseErr Args
  | .choiceR _ => .ok .nil
  | .choiceL (.nodeNT _ alT) => argListOf alT
  | _ => .error .shape

/-- RT-L2, argument layer: canonical `printArgs` text in call position —
between `( ` and `) ` — parses as the optional `ArgList` and extracts
back to the argument list. -/
theorem derives_printArgs (as : Args) (r : List Char) (ha : printableArgsB as = true) :
    ∃ t, Derives shallotGrammar (PExp.opt (.nt NT.argList))
      ((printArgs as).toList ++ (')' :: ' ' :: r)) (.ok t (')' :: ' ' :: r)) ∧
      argsOptOf t = .ok as := by
  obtain ⟨t, hd, hv⟩ := derives_print_argsOpt as r ha
  refine ⟨t, hd, ?_⟩
  cases hv with
  | inl h =>
    obtain ⟨tf, h1, h2⟩ := h
    subst h1; subst h2
    rfl
  | inr h =>
    obtain ⟨alT, h1, h2⟩ := h
    subst h1
    simpa [argsOptOf] using h2

#print axioms derives_printExpr

end Shallot
