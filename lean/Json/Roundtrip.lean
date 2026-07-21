import Json.Lexemes
import Shallot.Peg.Completeness

/-!
# J4 — the JSON roundtrip theorem

For every well-formed `JValue` (`wfValue v = true`), the canonical text
`printJson v` parses back to exactly `v`:

- `derives_printJson` — a `Derives` derivation at `JNT.jsonText` consuming
  the WHOLE input, whose tree has exactly the shape `parseJson` unwraps,
  with `valueOf` recovering `v`;
- `parse_print_json` — the interpreter form, via completeness (T3) and
  fuel monotonicity (T0).

Architecture (canonical output has NO whitespace anywhere):
1. whitespace layer — every `nt ws` derivation is `star`-nil;
2. string layer — each code point's `escapeCp` parses as one `char` node
   (four shapes, mirroring `escapeCp_cases` 1:1), `escChars` as the star;
3. number layer — rules 9–12 from the `wf*` digit kit, parameterized by a
   `numFollow` predicate on the text after the number;
4. value layer — mutual recursion over `JValue`/`JArray`/`JMembers`,
   choosing each `value` alternative at exactly the choice depth
   `valueOf` expects;
5. top layer + interpreter connection, mirroring Shallot's `parse_print`.
-/

set_option autoImplicit false

namespace Shallot.Json

/-! ## Rule lemmas (all compute by `rfl`) -/

theorem ws_rule : ruleAt jsonGrammar.rules JNT.ws =
    some (.star (.alt (.chr ' ') (.alt (.chr '\t') (.alt (.chr '\n') (.chr '\r'))))) := rfl

theorem jsonText_rule : ruleAt jsonGrammar.rules JNT.jsonText =
    some (.seq (.nt JNT.ws)
      (.seq (.nt JNT.value) (.seq (.nt JNT.ws) (.notP .any)))) := rfl

theorem value_rule : ruleAt jsonGrammar.rules JNT.value =
    some (.alt (.lit "false".toList)
      (.alt (.lit "null".toList)
        (.alt (.lit "true".toList)
          (.alt (.nt JNT.object)
            (.alt (.nt JNT.array)
              (.alt (.nt JNT.number) (.nt JNT.string))))))) := rfl

theorem object_rule : ruleAt jsonGrammar.rules JNT.object =
    some (.seq beginObjectP
      (.seq (PExp.opt (.seq (.nt JNT.member)
                        (.star (.seq valueSepP (.nt JNT.member)))))
        endObjectP)) := rfl

theorem member_rule : ruleAt jsonGrammar.rules JNT.member =
    some (.seq (.nt JNT.string) (.seq nameSepP (.nt JNT.value))) := rfl

theorem array_rule : ruleAt jsonGrammar.rules JNT.array =
    some (.seq beginArrayP
      (.seq (PExp.opt (.seq (.nt JNT.value)
                        (.star (.seq valueSepP (.nt JNT.value)))))
        endArrayP)) := rfl

theorem string_rule : ruleAt jsonGrammar.rules JNT.string =
    some (.seq (.chr '"') (.seq (.star (.nt JNT.char)) (.chr '"'))) := rfl

theorem char_rule : ruleAt jsonGrammar.rules JNT.char =
    some (.alt unescapedP (.seq (.chr '\\') (.nt JNT.escape))) := rfl

theorem escape_rule : ruleAt jsonGrammar.rules JNT.escape =
    some (.alt (.chr '"')
      (.alt (.chr '\\')
        (.alt (.chr '/')
          (.alt (.chr 'b')
            (.alt (.chr 'f')
              (.alt (.chr 'n')
                (.alt (.chr 'r')
                  (.alt (.chr 't')
                    (.seq (.chr 'u')
                      (.seq (.nt JNT.hex)
                        (.seq (.nt JNT.hex)
                          (.seq (.nt JNT.hex) (.nt JNT.hex))))))))))))) := rfl

theorem number_rule : ruleAt jsonGrammar.rules JNT.number =
    some (.seq (PExp.opt (.chr '-'))
      (.seq (.nt JNT.int)
        (.seq (PExp.opt (.nt JNT.frac)) (PExp.opt (.nt JNT.exp))))) := rfl

theorem int_rule : ruleAt jsonGrammar.rules JNT.int =
    some (.alt (.chr '0') (.seq digit19P (.star digitP))) := rfl

theorem frac_rule : ruleAt jsonGrammar.rules JNT.frac =
    some (.seq (.chr '.') (.seq digitP (.star digitP))) := rfl

theorem exp_rule : ruleAt jsonGrammar.rules JNT.exp =
    some (.seq (.alt (.chr 'e') (.chr 'E'))
      (.seq (PExp.opt (.alt (.chr '-') (.chr '+')))
        (.seq digitP (.star digitP)))) := rfl

theorem hex_rule : ruleAt jsonGrammar.rules JNT.hex =
    some (.alt digitP (.alt (.range 'a' 'f') (.range 'A' 'F'))) := rfl

/-! ## Char/Bool kit -/

theorem toNat_ne_of_beqChar_false {a b : Char} (h : beqChar a b = false) :
    a.toNat ≠ b.toNat := by
  unfold beqChar at h
  simpa using h

theorem beqChar_false_of_toNat_ne {a b : Char} (h : a.toNat ≠ b.toNat) :
    beqChar a b = false := by
  unfold beqChar
  simpa using h

theorem leChar_of_le {a b : Char} (h : a.toNat ≤ b.toNat) : leChar a b = true :=
  (leChar_iff a b).mpr h

theorem leChar_false_of_lt {a b : Char} (h : b.toNat < a.toNat) : leChar a b = false := by
  cases hl : leChar a b with
  | false => rfl
  | true => exact absurd ((leChar_iff a b).mp hl) (by omega)

theorem range_ok_of (lo hi c : Char) (h1 : lo.toNat ≤ c.toNat) (h2 : c.toNat ≤ hi.toNat) :
    (leChar lo c && leChar c hi) = true := by
  rw [leChar_of_le h1, leChar_of_le h2]
  rfl

theorem range_fail_lo (lo hi c : Char) (h : c.toNat < lo.toNat) :
    (leChar lo c && leChar c hi) = false := by
  rw [leChar_false_of_lt h, Bool.false_and]

theorem range_fail_hi (lo hi c : Char) (h : hi.toNat < c.toNat) :
    (leChar lo c && leChar c hi) = false := by
  rw [leChar_false_of_lt h, Bool.and_false]

/-! ## stripPrefix? / lit kit -/

theorem stripPrefix?_cons_ne (c : Char) (cs : List Char) (d : Char) (ds : List Char)
    (h : beqChar c d = false) : stripPrefix? (c :: cs) (d :: ds) = none := by
  simp [stripPrefix?, h]

theorem stripPrefix?_self_append (s x : List Char) : stripPrefix? s (s ++ x) = some x := by
  induction s with
  | nil => rfl
  | cons c cs ih => simp [stripPrefix?, beqChar_refl, ih]

/-- A literal always consumes itself off the front. -/
theorem derives_lit_append (s x : List Char) :
    Derives jsonGrammar (.lit s) (s ++ x) (.ok (.leaf s) x) :=
  Derives.litOk _ _ _ (stripPrefix?_self_append s x)

/-! ## Whitespace layer

Canonical output contains no whitespace, so every `nt ws` derivation is a
zero-width `starNil` — provided the next character is not whitespace. -/

/-- One JSON whitespace char, pattern-first (`beqChar patternChar inputChar`),
matching rule 0's `chr` alternatives in order. -/
def isJWsB (c : Char) : Bool :=
  beqChar ' ' c || (beqChar '\t' c || (beqChar '\n' c || beqChar '\r' c))

/-- Follow condition for `ws`-nil: empty input, or a non-whitespace head. -/
def headNotWs : List Char → Bool
  | [] => true
  | c :: _ => !isJWsB c

theorem headNotWs_cons (c : Char) (t : List Char) (h : isJWsB c = false) :
    headNotWs (c :: t) = true := by
  simp [headNotWs, h]

/-- The `ws` star body (4-way `chr` alt) fails at a no-whitespace boundary. -/
theorem wsBody_fail (x : List Char) (h : headNotWs x = true) :
    Derives jsonGrammar
      (.alt (.chr ' ') (.alt (.chr '\t') (.alt (.chr '\n') (.chr '\r')))) x .fail := by
  cases x with
  | nil =>
    exact Derives.altFail _ _ _ (Derives.chrEmpty _)
      (Derives.altFail _ _ _ (Derives.chrEmpty _)
        (Derives.altFail _ _ _ (Derives.chrEmpty _) (Derives.chrEmpty _)))
  | cons c t =>
    have h' : isJWsB c = false := by simpa [headNotWs] using h
    unfold isJWsB at h'
    simp only [Bool.or_eq_false_iff] at h'
    exact Derives.altFail _ _ _ (Derives.chrFail _ _ _ h'.1)
      (Derives.altFail _ _ _ (Derives.chrFail _ _ _ h'.2.1)
        (Derives.altFail _ _ _ (Derives.chrFail _ _ _ h'.2.2.1)
          (Derives.chrFail _ _ _ h'.2.2.2)))

/-- Tree of a zero-width `ws`. -/
def wsTreeNil : PTree := .nodeNT JNT.ws .starNil

/-- Canonical text: `ws` always matches zero characters. -/
theorem derives_ws_nil (x : List Char) (h : headNotWs x = true) :
    Derives jsonGrammar (.nt JNT.ws) x (.ok wsTreeNil x) :=
  Derives.ntOk _ _ _ _ _ ws_rule (Derives.starNil _ _ (wsBody_fail x h))

/-- Tree of a structural token on canonical input (both `ws` nil). -/
def structTokTree (c : Char) : PTree :=
  .seq wsTreeNil (.seq (.leaf [c]) wsTreeNil)

theorem derives_structTok (c : Char) (x : List Char) (hc : isJWsB c = false)
    (hx : headNotWs x = true) :
    Derives jsonGrammar (structTok c) (c :: x) (.ok (structTokTree c) x) := by
  show Derives jsonGrammar (.seq (.nt JNT.ws) (.seq (.chr c) (.nt JNT.ws))) (c :: x)
    (.ok (.seq wsTreeNil (.seq (.leaf [c]) wsTreeNil)) x)
  exact Derives.seqOk _ _ _ _ _ _ _ (derives_ws_nil _ (headNotWs_cons c x hc))
    (Derives.seqOk _ _ _ _ _ _ _ (Derives.chrOk c c x (beqChar_refl c))
      (derives_ws_nil x hx))

/-- A structural token dies on any other non-whitespace head. -/
theorem structTok_fail (c d : Char) (x : List Char) (hd : isJWsB d = false)
    (hne : beqChar c d = false) :
    Derives jsonGrammar (structTok c) (d :: x) .fail := by
  show Derives jsonGrammar (.seq (.nt JNT.ws) (.seq (.chr c) (.nt JNT.ws))) (d :: x) .fail
  exact Derives.seqFail₂ _ _ _ _ _ (derives_ws_nil _ (headNotWs_cons d x hd))
    (Derives.seqFail₁ _ _ _ (Derives.chrFail _ _ _ hne))

/-! ## Follow predicates

`numFollow` is what a canonical number needs from the text after it (no
digit, `'.'`, `'e'`, `'E'` at the head); `valFollow` adds "no whitespace".
Every call site is `[]`, `','`, `']'` or `'}'`, all of which qualify. -/

def numFollowC (c : Char) : Bool :=
  !((leChar '0' c && leChar c '9') || beqChar '.' c || beqChar 'e' c || beqChar 'E' c)

def numFollow : List Char → Bool
  | [] => true
  | c :: _ => numFollowC c

def valFollowC (c : Char) : Bool := !isJWsB c && numFollowC c

def valFollow : List Char → Bool
  | [] => true
  | c :: _ => valFollowC c

theorem valFollow_cons (c : Char) (t : List Char) (h : valFollowC c = true) :
    valFollow (c :: t) = true := h

theorem numFollow_of_valFollow (x : List Char) (h : valFollow x = true) :
    numFollow x = true := by
  cases x with
  | nil => rfl
  | cons c t =>
    have h' : valFollowC c = true := h
    unfold valFollowC at h'
    rw [Bool.and_eq_true] at h'
    exact h'.2

theorem headNotWs_of_valFollow (x : List Char) (h : valFollow x = true) :
    headNotWs x = true := by
  cases x with
  | nil => rfl
  | cons c t =>
    have h' : valFollowC c = true := h
    unfold valFollowC at h'
    rw [Bool.and_eq_true] at h'
    exact headNotWs_cons c t (by simpa using h'.1)

/-- The three failures a number's follow set guarantees: no more digits,
no `frac`, no `exp` can start there. -/
theorem numFollow_spec (r : List Char) (h : numFollow r = true) :
    Derives jsonGrammar digitP r .fail ∧
    Derives jsonGrammar (.nt JNT.frac) r .fail ∧
    Derives jsonGrammar (.nt JNT.exp) r .fail := by
  cases r with
  | nil =>
    exact ⟨Derives.rangeEmpty _ _,
      Derives.ntFail _ _ _ frac_rule (Derives.seqFail₁ _ _ _ (Derives.chrEmpty _)),
      Derives.ntFail _ _ _ exp_rule (Derives.seqFail₁ _ _ _
        (Derives.altFail _ _ _ (Derives.chrEmpty _) (Derives.chrEmpty _)))⟩
  | cons c t =>
    have hc : numFollowC c = true := h
    simp only [numFollowC, Bool.not_eq_true', Bool.or_eq_false_iff] at hc
    obtain ⟨⟨⟨hdig, hdot⟩, he⟩, hE⟩ := hc
    exact ⟨Derives.rangeFail _ _ _ _ hdig,
      Derives.ntFail _ _ _ frac_rule (Derives.seqFail₁ _ _ _ (Derives.chrFail _ _ _ hdot)),
      Derives.ntFail _ _ _ exp_rule (Derives.seqFail₁ _ _ _
        (Derives.altFail _ _ _ (Derives.chrFail _ _ _ he) (Derives.chrFail _ _ _ hE)))⟩

/-! ## Hex layer -/

/-- A printed hex digit parses as one `HEXDIG` node decoding back to `m`
(rule 13's prioritized choice: digit class first, then lowercase). -/
theorem derives_hex_digitChar (m : Nat) (hm : m < 16) (x : List Char) :
    ∃ t, Derives jsonGrammar (.nt JNT.hex) (hexDigitChar m :: x)
        (.ok (.nodeNT JNT.hex t) x) ∧ hexOf t = .ok m := by
  rcases hexDigitChar_lt16_class m hm with ⟨-, hd⟩ | ⟨-, hd, hl⟩
  · refine ⟨.choiceL (.leaf [hexDigitChar m]), ?_, ?_⟩
    · exact Derives.ntOk _ _ _ _ _ hex_rule
        (Derives.altL _ _ _ _ _ (Derives.rangeOk _ _ _ _ hd))
    · simp only [hexOf, PTree.chars, hexVal_hexDigitChar m hm]
  · refine ⟨.choiceR (.choiceL (.leaf [hexDigitChar m])), ?_, ?_⟩
    · exact Derives.ntOk _ _ _ _ _ hex_rule
        (Derives.altR _ _ _ _ _ (Derives.rangeFail _ _ _ _ hd)
          (Derives.altL _ _ _ _ _ (Derives.rangeOk _ _ _ _ hl)))
    · simp only [hexOf, PTree.chars, hexVal_hexDigitChar m hm]

/-! ## Char layer

`escapeCp c` parses as exactly ONE `char` node whose `charUnitOf` is
`c.toNat`; the four branches of `escapeCp_cases` map 1:1 onto the four
parse shapes (short escape ×2, `\uXXXX`, raw unescaped char). -/

/-- The `unescaped` alternative fails when all three ranges miss. -/
theorem unescaped_fail (c : Char) (x : List Char)
    (h1 : (leChar ' ' c && leChar c '!') = false)
    (h2 : (leChar '#' c && leChar c '[') = false)
    (h3 : (leChar ']' c && leChar c (Char.ofNat 0x10FFFF)) = false) :
    Derives jsonGrammar unescapedP (c :: x) .fail :=
  Derives.altFail _ _ _ (Derives.rangeFail _ _ _ _ h1)
    (Derives.altFail _ _ _ (Derives.rangeFail _ _ _ _ h2)
      (Derives.rangeFail _ _ _ _ h3))

/-- The star of `char` stops at the closing quote: both alternatives of
rule 7 die on `'"'` (the `unescaped` ranges exclude 0x22; the escape
branch needs `'\\'`). -/
theorem char_fail_quote (x : List Char) :
    Derives jsonGrammar (.nt JNT.char) ('"' :: x) .fail :=
  Derives.ntFail _ _ _ char_rule
    (Derives.altFail _ _ _ (unescaped_fail '"' x (by decide) (by decide) (by decide))
      (Derives.seqFail₁ _ _ _ (Derives.chrFail _ _ _ (by decide))))

/-- Per-code-point payoff: `escapeCp c` parses as one `char` node and the
unit extractor recovers `c.toNat`. -/
theorem derives_char_cp (c : Char) (r : List Char) :
    ∃ t, Derives jsonGrammar (.nt JNT.char) (escapeCp c ++ r)
        (.ok (.nodeNT JNT.char t) r) ∧ charUnitOf t = .ok c.toNat := by
  rcases escapeCp_cases c with ⟨hq, hesc⟩ | ⟨hq, hb, hesc⟩ | ⟨hq, hb, hlt, hesc⟩ |
    ⟨hq, hb, hge, hesc⟩
  · -- c = '"' → `\"`, escape alternative 1
    have hc : c = '"' := eq_of_beqChar hq
    subst hc
    rw [hesc]
    refine ⟨.choiceR (.seq (.leaf ['\\'])
      (.nodeNT JNT.escape (.choiceL (.leaf ['"'])))), ?_, by simp only [charUnitOf, escapeOf]⟩
    apply Derives.ntOk _ _ _ _ _ char_rule
    refine Derives.altR _ _ _ _ _
      (unescaped_fail '\\' _ (by decide) (by decide) (by decide)) ?_
    refine Derives.seqOk _ _ _ _ _ _ _ (Derives.chrOk '\\' '\\' _ (beqChar_refl '\\')) ?_
    exact Derives.ntOk _ _ _ _ _ escape_rule
      (Derives.altL _ _ _ _ _ (Derives.chrOk '"' '"' _ (beqChar_refl '"')))
  · -- c = '\\' → `\\`, escape alternative 2
    have hc : c = '\\' := eq_of_beqChar hb
    subst hc
    rw [hesc]
    refine ⟨.choiceR (.seq (.leaf ['\\'])
      (.nodeNT JNT.escape (.choiceR (.choiceL (.leaf ['\\']))))), ?_,
      by simp only [charUnitOf, escapeOf]⟩
    apply Derives.ntOk _ _ _ _ _ char_rule
    refine Derives.altR _ _ _ _ _
      (unescaped_fail '\\' _ (by decide) (by decide) (by decide)) ?_
    refine Derives.seqOk _ _ _ _ _ _ _ (Derives.chrOk '\\' '\\' _ (beqChar_refl '\\')) ?_
    exact Derives.ntOk _ _ _ _ _ escape_rule
      (Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ (by decide))
        (Derives.altL _ _ _ _ _ (Derives.chrOk '\\' '\\' _ (beqChar_refl '\\'))))
  · -- control char → `\uXXXX`, escape alternative 9
    rw [hesc, hex4_shape]
    obtain ⟨t4, h4, hx4⟩ := derives_hex_digitChar (c.toNat % 16)
      (Nat.mod_lt _ (by decide)) r
    obtain ⟨t3, h3, hx3⟩ := derives_hex_digitChar (c.toNat / 16 % 16)
      (Nat.mod_lt _ (by decide)) (hexDigitChar (c.toNat % 16) :: r)
    obtain ⟨t2, h2, hx2⟩ := derives_hex_digitChar (c.toNat / 256 % 16)
      (Nat.mod_lt _ (by decide))
      (hexDigitChar (c.toNat / 16 % 16) :: hexDigitChar (c.toNat % 16) :: r)
    obtain ⟨t1, h1, hx1⟩ := derives_hex_digitChar (c.toNat / 4096 % 16)
      (Nat.mod_lt _ (by decide))
      (hexDigitChar (c.toNat / 256 % 16) :: hexDigitChar (c.toNat / 16 % 16) ::
        hexDigitChar (c.toNat % 16) :: r)
    refine ⟨.choiceR (.seq (.leaf ['\\']) (.nodeNT JNT.escape
      (.choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceR
        (.seq (.leaf ['u'])
          (.seq (.nodeNT JNT.hex t1) (.seq (.nodeNT JNT.hex t2)
            (.seq (.nodeNT JNT.hex t3) (.nodeNT JNT.hex t4))))))))))))))), ?_, ?_⟩
    · apply Derives.ntOk _ _ _ _ _ char_rule
      refine Derives.altR _ _ _ _ _
        (unescaped_fail '\\' _ (by decide) (by decide) (by decide)) ?_
      refine Derives.seqOk _ _ _ _ _ _ _ (Derives.chrOk '\\' '\\' _ (beqChar_refl '\\')) ?_
      apply Derives.ntOk _ _ _ _ _ escape_rule
      refine Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ (by decide)) ?_
      refine Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ (by decide)) ?_
      refine Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ (by decide)) ?_
      refine Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ (by decide)) ?_
      refine Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ (by decide)) ?_
      refine Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ (by decide)) ?_
      refine Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ (by decide)) ?_
      refine Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ (by decide)) ?_
      refine Derives.seqOk _ _ _ _ _ _ _ (Derives.chrOk 'u' 'u' _ (beqChar_refl 'u')) ?_
      exact Derives.seqOk _ _ _ _ _ _ _ h1
        (Derives.seqOk _ _ _ _ _ _ _ h2 (Derives.seqOk _ _ _ _ _ _ _ h3 h4))
    · have harith : ((c.toNat / 4096 % 16 * 16 + c.toNat / 256 % 16) * 16 +
          c.toNat / 16 % 16) * 16 + c.toNat % 16 = c.toNat := by omega
      rw [← harith]
      simp only [charUnitOf, escapeOf, hx1, hx2, hx3, hx4]
      rfl
  · -- plain char (raw output): one `unescaped` char, three range cases
    rw [hesc]
    have hn34 : c.toNat ≠ '"'.toNat := toNat_ne_of_beqChar_false hq
    have hn92 : c.toNat ≠ '\\'.toNat := toNat_ne_of_beqChar_false hb
    have hmax := char_toNat_le_max c
    have h34 : '"'.toNat = 34 := rfl
    have h92 : '\\'.toNat = 92 := rfl
    have h33 : '!'.toNat = 33 := rfl
    have h91 : '['.toNat = 91 := rfl
    rcases show (32 ≤ c.toNat ∧ c.toNat ≤ 33) ∨ (35 ≤ c.toNat ∧ c.toNat ≤ 91) ∨
        (93 ≤ c.toNat ∧ c.toNat ≤ 0x10FFFF) by omega with ⟨ha, hb'⟩ | ⟨ha, hb'⟩ | ⟨ha, hb'⟩
    · refine ⟨.choiceL (.choiceL (.leaf [c])), ?_, by simp only [charUnitOf, PTree.chars]⟩
      exact Derives.ntOk _ _ _ _ _ char_rule (Derives.altL _ _ _ _ _
        (Derives.altL _ _ _ _ _ (Derives.rangeOk _ _ _ _ (range_ok_of ' ' '!' c ha hb'))))
    · refine ⟨.choiceL (.choiceR (.choiceL (.leaf [c]))), ?_,
        by simp only [charUnitOf, PTree.chars]⟩
      refine Derives.ntOk _ _ _ _ _ char_rule (Derives.altL _ _ _ _ _ ?_)
      exact Derives.altR _ _ _ _ _ (Derives.rangeFail _ _ _ _ (range_fail_hi ' ' '!' c (by omega)))
        (Derives.altL _ _ _ _ _ (Derives.rangeOk _ _ _ _ (range_ok_of '#' '[' c ha hb')))
    · refine ⟨.choiceL (.choiceR (.choiceR (.leaf [c]))), ?_,
        by simp only [charUnitOf, PTree.chars]⟩
      refine Derives.ntOk _ _ _ _ _ char_rule (Derives.altL _ _ _ _ _ ?_)
      refine Derives.altR _ _ _ _ _ (Derives.rangeFail _ _ _ _ (range_fail_hi ' ' '!' c (by omega))) ?_
      exact Derives.altR _ _ _ _ _ (Derives.rangeFail _ _ _ _ (range_fail_hi '#' '[' c (by omega)))
        (Derives.rangeOk _ _ _ _ (range_ok_of ']' (Char.ofNat 0x10FFFF) c ha hb'))

/-! ## String layer -/

/-- `escChars s` parses as `star char`, stopping at the closing quote,
with `charUnits` recovering the code units of `s`. -/
theorem derives_charStar (s : List Char) (r : List Char) :
    ∃ t, Derives jsonGrammar (.star (.nt JNT.char)) (escChars s ++ '"' :: r)
        (.ok t ('"' :: r)) ∧ charUnits t = .ok (s.map Char.toNat) := by
  induction s with
  | nil => exact ⟨.starNil, Derives.starNil _ _ (char_fail_quote r), rfl⟩
  | cons c cs ih =>
    obtain ⟨tc, hc, hu⟩ := derives_char_cp c (escChars cs ++ '"' :: r)
    obtain ⟨ts, hts, hus⟩ := ih
    have hEq : escChars (c :: cs) ++ '"' :: r = escapeCp c ++ (escChars cs ++ '"' :: r) := by
      simp [escChars_cons, List.append_assoc]
    rw [hEq]
    refine ⟨.starCons (.nodeNT JNT.char tc) ts,
      Derives.starCons _ _ _ _ _ _ hc hts, ?_⟩
    simp only [charUnits, hu, hus]
    rfl

/-- String payoff: `printString s` (in position `'"' :: escChars s ++ '"' :: r`)
parses as one `string` node with `stringOf` recovering the decoded `s`. -/
theorem derives_string (s : List Char) (r : List Char) :
    ∃ t, Derives jsonGrammar (.nt JNT.string) ('"' :: (escChars s ++ '"' :: r))
        (.ok (.nodeNT JNT.string t) r) ∧ stringOf t = .ok s := by
  obtain ⟨starT, hstar, hunits⟩ := derives_charStar s r
  refine ⟨.seq (.leaf ['"']) (.seq starT (.leaf ['"'])), ?_, ?_⟩
  · apply Derives.ntOk _ _ _ _ _ string_rule
    refine Derives.seqOk _ _ _ _ _ _ _ (Derives.chrOk '"' '"' _ (beqChar_refl '"')) ?_
    exact Derives.seqOk _ _ _ _ _ _ _ hstar (Derives.chrOk '"' '"' _ (beqChar_refl '"'))
  · have h : stringOf (.seq (.leaf ['"']) (.seq starT (.leaf ['"']))) =
        combineUnits (s.map Char.toNat) := by
      simp only [stringOf, hunits]
      rfl
    rw [h, combineUnits_map_toNat]

/-! ## Number layer -/

/-- A digit span parses as `star digitP`, stopping where digits stop;
the tree's span is the consumed characters. -/
theorem derives_digitStar (cs : List Char) (x : List Char)
    (hall : cs.all (fun c => leChar '0' c && leChar c '9') = true)
    (hfail : Derives jsonGrammar digitP x .fail) :
    ∃ t, Derives jsonGrammar (.star digitP) (cs ++ x) (.ok t x) ∧
      PTree.chars t = cs := by
  induction cs with
  | nil => exact ⟨.starNil, Derives.starNil _ _ hfail, rfl⟩
  | cons c cs ih =>
    rw [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨ts, hts, hcs⟩ := ih hall.2
    exact ⟨.starCons (.leaf [c]) ts,
      Derives.starCons _ _ _ _ _ _ (Derives.rangeOk _ _ _ _ hall.1) hts,
      by simp [PTree.chars, hcs]⟩

theorem digitP_fail_dot (y : List Char) : Derives jsonGrammar digitP ('.' :: y) .fail :=
  Derives.rangeFail _ _ _ _ (by decide)

/-- `digitP` dies at the head of a printed exponent (`'e'`/`'E'`). -/
theorem digitP_fail_expSome (e : JExp) (X : List Char) :
    Derives jsonGrammar digitP (printExp (some e) ++ X) .fail := by
  obtain ⟨up, sg, dg⟩ := e
  cases up with
  | false => exact Derives.rangeFail '0' '9' 'e' _ (by decide)
  | true => exact Derives.rangeFail '0' '9' 'E' _ (by decide)

/-- `frac` dies at the head of a printed exponent. -/
theorem frac_fail_expSome (e : JExp) (X : List Char) :
    Derives jsonGrammar (.nt JNT.frac) (printExp (some e) ++ X) .fail := by
  obtain ⟨up, sg, dg⟩ := e
  cases up with
  | false =>
    exact Derives.ntFail _ _ _ frac_rule
      (Derives.seqFail₁ _ _ _ (Derives.chrFail '.' 'e' _ (by decide)))
  | true =>
    exact Derives.ntFail _ _ _ frac_rule
      (Derives.seqFail₁ _ _ _ (Derives.chrFail '.' 'E' _ (by decide)))

/-- Rule 10: a well-formed `int` span parses as one `int` node whose tree
spans exactly the digits (`intOf` reads `t.chars`). -/
theorem derives_int (ip : List Char) (X : List Char) (hwf : wfInt ip = true)
    (hfail : Derives jsonGrammar digitP X .fail) :
    ∃ t, Derives jsonGrammar (.nt JNT.int) (ip ++ X)
        (.ok (.nodeNT JNT.int t) X) ∧ PTree.chars t = ip := by
  rcases wfInt_cases hwf with rfl | ⟨d, ds, rfl, hd, hds⟩
  · refine ⟨.choiceL (.leaf ['0']), ?_, rfl⟩
    exact Derives.ntOk _ _ _ _ _ int_rule
      (Derives.altL _ _ _ _ _ (Derives.chrOk '0' '0' _ (beqChar_refl '0')))
  · obtain ⟨tds, htds, hcds⟩ := derives_digitStar ds X hds hfail
    have hne : beqChar '0' d = false := by
      apply beqChar_false_of_toNat_ne
      rw [Bool.and_eq_true, leChar_iff, leChar_iff] at hd
      have h0 : '0'.toNat = 48 := rfl
      have h1 : '1'.toNat = 49 := rfl
      omega
    refine ⟨.choiceR (.seq (.leaf [d]) tds), ?_, ?_⟩
    · apply Derives.ntOk _ _ _ _ _ int_rule
      refine Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ hne) ?_
      exact Derives.seqOk _ _ _ _ _ _ _ (Derives.rangeOk _ _ _ _ hd) htds
    · simp [PTree.chars, hcds]

/-- Rule 11: a well-formed fraction parses as one `frac` node with
`fracOf` recovering the digits. -/
theorem derives_frac (ds : List Char) (X : List Char) (hwf : wfDigits ds = true)
    (hfail : Derives jsonGrammar digitP X .fail) :
    ∃ t, Derives jsonGrammar (.nt JNT.frac) ('.' :: (ds ++ X))
        (.ok (.nodeNT JNT.frac t) X) ∧ fracOf t = .ok ds := by
  obtain ⟨d, ds', rfl, hd, hds'⟩ := wfDigits_cons hwf
  obtain ⟨tds, htds, hcds⟩ := derives_digitStar ds' X hds' hfail
  refine ⟨.seq (.leaf ['.']) (.seq (.leaf [d]) tds), ?_, ?_⟩
  · apply Derives.ntOk _ _ _ _ _ frac_rule
    refine Derives.seqOk _ _ _ _ _ _ _ (Derives.chrOk '.' '.' _ (beqChar_refl '.')) ?_
    exact Derives.seqOk _ _ _ _ _ _ _ (Derives.rangeOk _ _ _ _ hd) htds
  · simp only [fracOf, PTree.chars, hcds]
    rfl

/-- Rule 12: a well-formed exponent parses as one `exp` node with `expOf`
recovering it exactly (case/sign as written; the sign nests TWO choices). -/
theorem derives_exp (e : JExp) (r : List Char) (hwf : wfDigits e.digits = true)
    (hfail : Derives jsonGrammar digitP r .fail) :
    ∃ t, Derives jsonGrammar (.nt JNT.exp) (printExp (some e) ++ r)
        (.ok (.nodeNT JNT.exp t) r) ∧ expOf t = .ok e := by
  obtain ⟨up, sg, dg⟩ := e
  obtain ⟨d, ds, hdg, hd, hds⟩ := wfDigits_cons hwf
  simp only at hdg
  subst hdg
  obtain ⟨tds, htds, hcds⟩ := derives_digitStar ds r hds hfail
  have hdig : Derives jsonGrammar (.seq digitP (.star digitP)) ((d :: ds) ++ r)
      (.ok (.seq (.leaf [d]) tds) r) :=
    Derives.seqOk _ _ _ _ _ _ _ (Derives.rangeOk _ _ _ _ hd) htds
  have hdnat : 48 ≤ d.toNat ∧ d.toNat ≤ 57 := by
    rw [Bool.and_eq_true, leChar_iff, leChar_iff] at hd
    exact hd
  have hminus : beqChar '-' d = false := beqChar_false_of_toNat_ne (by
    have : '-'.toNat = 45 := rfl
    omega)
  have hplus : beqChar '+' d = false := beqChar_false_of_toNat_ne (by
    have : '+'.toNat = 43 := rfl
    omega)
  have hsignNone : Derives jsonGrammar (PExp.opt (.alt (.chr '-') (.chr '+')))
      ((d :: ds) ++ r) (.ok (.choiceR (.leaf [])) ((d :: ds) ++ r)) :=
    Derives.altR _ _ _ _ _
      (Derives.altFail _ _ _ (Derives.chrFail _ _ _ hminus) (Derives.chrFail _ _ _ hplus))
      (Derives.eps _)
  cases up with
  | false =>
    cases sg with
    | none =>
      refine ⟨.seq (.choiceL (.leaf ['e']))
        (.seq (.choiceR (.leaf [])) (.seq (.leaf [d]) tds)), ?_, ?_⟩
      · apply Derives.ntOk _ _ _ _ _ exp_rule
        refine Derives.seqOk _ _ _ _ _ _ _
          (Derives.altL _ _ _ _ _ (Derives.chrOk 'e' 'e' _ (beqChar_refl 'e'))) ?_
        exact Derives.seqOk _ _ _ _ _ _ _ hsignNone hdig
      · simp only [expOf, PTree.chars, hcds]
        rfl
    | minus =>
      refine ⟨.seq (.choiceL (.leaf ['e']))
        (.seq (.choiceL (.choiceL (.leaf ['-']))) (.seq (.leaf [d]) tds)), ?_, ?_⟩
      · apply Derives.ntOk _ _ _ _ _ exp_rule
        refine Derives.seqOk _ _ _ _ _ _ _
          (Derives.altL _ _ _ _ _ (Derives.chrOk 'e' 'e' _ (beqChar_refl 'e'))) ?_
        refine Derives.seqOk _ _ _ _ _ _ _ ?_ hdig
        exact Derives.altL _ _ _ _ _
          (Derives.altL _ _ _ _ _ (Derives.chrOk '-' '-' _ (beqChar_refl '-')))
      · simp only [expOf, PTree.chars, hcds]
        rfl
    | plus =>
      refine ⟨.seq (.choiceL (.leaf ['e']))
        (.seq (.choiceL (.choiceR (.leaf ['+']))) (.seq (.leaf [d]) tds)), ?_, ?_⟩
      · apply Derives.ntOk _ _ _ _ _ exp_rule
        refine Derives.seqOk _ _ _ _ _ _ _
          (Derives.altL _ _ _ _ _ (Derives.chrOk 'e' 'e' _ (beqChar_refl 'e'))) ?_
        refine Derives.seqOk _ _ _ _ _ _ _ ?_ hdig
        exact Derives.altL _ _ _ _ _
          (Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ (by decide))
            (Derives.chrOk '+' '+' _ (beqChar_refl '+')))
      · simp only [expOf, PTree.chars, hcds]
        rfl
  | true =>
    cases sg with
    | none =>
      refine ⟨.seq (.choiceR (.leaf ['E']))
        (.seq (.choiceR (.leaf [])) (.seq (.leaf [d]) tds)), ?_, ?_⟩
      · apply Derives.ntOk _ _ _ _ _ exp_rule
        refine Derives.seqOk _ _ _ _ _ _ _
          (Derives.altR _ _ _ _ _ (Derives.chrFail 'e' 'E' _ (by decide))
            (Derives.chrOk 'E' 'E' _ (beqChar_refl 'E'))) ?_
        exact Derives.seqOk _ _ _ _ _ _ _ hsignNone hdig
      · simp only [expOf, PTree.chars, hcds]
        rfl
    | minus =>
      refine ⟨.seq (.choiceR (.leaf ['E']))
        (.seq (.choiceL (.choiceL (.leaf ['-']))) (.seq (.leaf [d]) tds)), ?_, ?_⟩
      · apply Derives.ntOk _ _ _ _ _ exp_rule
        refine Derives.seqOk _ _ _ _ _ _ _
          (Derives.altR _ _ _ _ _ (Derives.chrFail 'e' 'E' _ (by decide))
            (Derives.chrOk 'E' 'E' _ (beqChar_refl 'E'))) ?_
        refine Derives.seqOk _ _ _ _ _ _ _ ?_ hdig
        exact Derives.altL _ _ _ _ _
          (Derives.altL _ _ _ _ _ (Derives.chrOk '-' '-' _ (beqChar_refl '-')))
      · simp only [expOf, PTree.chars, hcds]
        rfl
    | plus =>
      refine ⟨.seq (.choiceR (.leaf ['E']))
        (.seq (.choiceL (.choiceR (.leaf ['+']))) (.seq (.leaf [d]) tds)), ?_, ?_⟩
      · apply Derives.ntOk _ _ _ _ _ exp_rule
        refine Derives.seqOk _ _ _ _ _ _ _
          (Derives.altR _ _ _ _ _ (Derives.chrFail 'e' 'E' _ (by decide))
            (Derives.chrOk 'E' 'E' _ (beqChar_refl 'E'))) ?_
        refine Derives.seqOk _ _ _ _ _ _ _ ?_ hdig
        exact Derives.altL _ _ _ _ _
          (Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ (by decide))
            (Derives.chrOk '+' '+' _ (beqChar_refl '+')))
      · simp only [expOf, PTree.chars, hcds]
        rfl

/-- The `[ minus ]` opt takes its ε branch on a well-formed int head. -/
theorem optMinus_none (ip : List Char) (Y : List Char) (hint : wfInt ip = true) :
    Derives jsonGrammar (PExp.opt (.chr '-')) (ip ++ Y)
      (.ok (.choiceR (.leaf [])) (ip ++ Y)) := by
  rcases wfInt_cases hint with rfl | ⟨d, ds, rfl, hd, -⟩
  · exact Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ (by decide)) (Derives.eps _)
  · have hne : beqChar '-' d = false := beqChar_false_of_toNat_ne (by
      rw [Bool.and_eq_true, leChar_iff, leChar_iff] at hd
      have h1 : '1'.toNat = 49 := rfl
      have h9 : '9'.toNat = 57 := rfl
      have hm : '-'.toNat = 45 := rfl
      omega)
    exact Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ hne) (Derives.eps _)

/-- Rule 9 payoff: a well-formed number's canonical text parses as one
`number` node with `numberOf` recovering it exactly. -/
theorem derives_number (n : JNumber) (r : List Char) (hwf : wfNumber n = true)
    (hfr : numFollow r = true) :
    ∃ t, Derives jsonGrammar (.nt JNT.number) (printNumber n ++ r)
        (.ok (.nodeNT JNT.number t) r) ∧ numberOf t = .ok n := by
  obtain ⟨hdigR, hfracR, hexpR⟩ := numFollow_spec r hfr
  obtain ⟨neg, ip, fp, ep⟩ := n
  obtain ⟨hint, hfp, hep⟩ := wfNumber_spec hwf
  simp only at hint hfp hep
  rcases hfp with rfl | hfpwf
  · cases ep with
    | none =>
      -- fp = [], ep = none: tail is bare `r`
      obtain ⟨tI, hI, hIc⟩ := derives_int ip r hint hdigR
      have hTail : Derives jsonGrammar
          (.seq (.nt JNT.int) (.seq (PExp.opt (.nt JNT.frac)) (PExp.opt (.nt JNT.exp))))
          (ip ++ r)
          (.ok (.seq (.nodeNT JNT.int tI)
            (.seq (.choiceR (.leaf [])) (.choiceR (.leaf [])))) r) := by
        refine Derives.seqOk _ _ _ _ _ _ _ hI ?_
        exact Derives.seqOk _ _ _ _ _ _ _
          (Derives.altR _ _ _ _ _ hfracR (Derives.eps _))
          (Derives.altR _ _ _ _ _ hexpR (Derives.eps _))
      cases neg with
      | true =>
        have hEq : printNumber ⟨true, ip, [], Option.none⟩ ++ r = '-' :: (ip ++ r) := by
          simp [printNumber, printExp]
        rw [hEq]
        refine ⟨.seq (.choiceL (.leaf ['-'])) (.seq (.nodeNT JNT.int tI)
          (.seq (.choiceR (.leaf [])) (.choiceR (.leaf [])))), ?_, ?_⟩
        · apply Derives.ntOk _ _ _ _ _ number_rule
          exact Derives.seqOk _ _ _ _ _ _ _
            (Derives.altL _ _ _ _ _ (Derives.chrOk '-' '-' _ (beqChar_refl '-'))) hTail
        · simp only [numberOf, intOf, hIc]
          rfl
      | false =>
        have hEq : printNumber ⟨false, ip, [], Option.none⟩ ++ r = ip ++ r := by
          simp [printNumber, printExp]
        rw [hEq]
        refine ⟨.seq (.choiceR (.leaf [])) (.seq (.nodeNT JNT.int tI)
          (.seq (.choiceR (.leaf [])) (.choiceR (.leaf [])))), ?_, ?_⟩
        · apply Derives.ntOk _ _ _ _ _ number_rule
          exact Derives.seqOk _ _ _ _ _ _ _ (optMinus_none ip r hint) hTail
        · simp only [numberOf, intOf, hIc]
          rfl
    | some e =>
      -- fp = [], ep = some e: tail is `printExp (some e) ++ r`
      obtain ⟨tE, hE, hEv⟩ := derives_exp e r (hep e rfl) hdigR
      obtain ⟨tI, hI, hIc⟩ := derives_int ip (printExp (some e) ++ r) hint
        (digitP_fail_expSome e r)
      have hTail : Derives jsonGrammar
          (.seq (.nt JNT.int) (.seq (PExp.opt (.nt JNT.frac)) (PExp.opt (.nt JNT.exp))))
          (ip ++ (printExp (some e) ++ r))
          (.ok (.seq (.nodeNT JNT.int tI)
            (.seq (.choiceR (.leaf [])) (.choiceL (.nodeNT JNT.exp tE)))) r) := by
        refine Derives.seqOk _ _ _ _ _ _ _ hI ?_
        exact Derives.seqOk _ _ _ _ _ _ _
          (Derives.altR _ _ _ _ _ (frac_fail_expSome e r) (Derives.eps _))
          (Derives.altL _ _ _ _ _ hE)
      cases neg with
      | true =>
        have hEq : printNumber ⟨true, ip, [], some e⟩ ++ r =
            '-' :: (ip ++ (printExp (some e) ++ r)) := by
          simp [printNumber, List.append_assoc]
        rw [hEq]
        refine ⟨.seq (.choiceL (.leaf ['-'])) (.seq (.nodeNT JNT.int tI)
          (.seq (.choiceR (.leaf [])) (.choiceL (.nodeNT JNT.exp tE)))), ?_, ?_⟩
        · apply Derives.ntOk _ _ _ _ _ number_rule
          exact Derives.seqOk _ _ _ _ _ _ _
            (Derives.altL _ _ _ _ _ (Derives.chrOk '-' '-' _ (beqChar_refl '-'))) hTail
        · simp only [numberOf, intOf, hIc, hEv]
          rfl
      | false =>
        have hEq : printNumber ⟨false, ip, [], some e⟩ ++ r =
            ip ++ (printExp (some e) ++ r) := by
          simp [printNumber, List.append_assoc]
        rw [hEq]
        refine ⟨.seq (.choiceR (.leaf [])) (.seq (.nodeNT JNT.int tI)
          (.seq (.choiceR (.leaf [])) (.choiceL (.nodeNT JNT.exp tE)))), ?_, ?_⟩
        · apply Derives.ntOk _ _ _ _ _ number_rule
          exact Derives.seqOk _ _ _ _ _ _ _ (optMinus_none ip _ hint) hTail
        · simp only [numberOf, intOf, hIc, hEv]
          rfl
  · obtain ⟨f0, fs, hfp', -, -⟩ := wfDigits_cons hfpwf
    subst hfp'
    cases ep with
    | none =>
      -- fp = f0 :: fs, ep = none
      obtain ⟨tF, hF, hFv⟩ := derives_frac (f0 :: fs) r hfpwf hdigR
      obtain ⟨tI, hI, hIc⟩ := derives_int ip ('.' :: ((f0 :: fs) ++ r)) hint
        (digitP_fail_dot _)
      have hTail : Derives jsonGrammar
          (.seq (.nt JNT.int) (.seq (PExp.opt (.nt JNT.frac)) (PExp.opt (.nt JNT.exp))))
          (ip ++ ('.' :: ((f0 :: fs) ++ r)))
          (.ok (.seq (.nodeNT JNT.int tI)
            (.seq (.choiceL (.nodeNT JNT.frac tF)) (.choiceR (.leaf [])))) r) := by
        refine Derives.seqOk _ _ _ _ _ _ _ hI ?_
        exact Derives.seqOk _ _ _ _ _ _ _ (Derives.altL _ _ _ _ _ hF)
          (Derives.altR _ _ _ _ _ hexpR (Derives.eps _))
      cases neg with
      | true =>
        have hEq : printNumber ⟨true, ip, f0 :: fs, Option.none⟩ ++ r =
            '-' :: (ip ++ ('.' :: ((f0 :: fs) ++ r))) := by
          simp [printNumber, printExp, List.append_assoc]
        rw [hEq]
        refine ⟨.seq (.choiceL (.leaf ['-'])) (.seq (.nodeNT JNT.int tI)
          (.seq (.choiceL (.nodeNT JNT.frac tF)) (.choiceR (.leaf [])))), ?_, ?_⟩
        · apply Derives.ntOk _ _ _ _ _ number_rule
          exact Derives.seqOk _ _ _ _ _ _ _
            (Derives.altL _ _ _ _ _ (Derives.chrOk '-' '-' _ (beqChar_refl '-'))) hTail
        · simp only [numberOf, intOf, hIc, hFv]
          rfl
      | false =>
        have hEq : printNumber ⟨false, ip, f0 :: fs, Option.none⟩ ++ r =
            ip ++ ('.' :: ((f0 :: fs) ++ r)) := by
          simp [printNumber, printExp, List.append_assoc]
        rw [hEq]
        refine ⟨.seq (.choiceR (.leaf [])) (.seq (.nodeNT JNT.int tI)
          (.seq (.choiceL (.nodeNT JNT.frac tF)) (.choiceR (.leaf [])))), ?_, ?_⟩
        · apply Derives.ntOk _ _ _ _ _ number_rule
          exact Derives.seqOk _ _ _ _ _ _ _ (optMinus_none ip _ hint) hTail
        · simp only [numberOf, intOf, hIc, hFv]
          rfl
    | some e =>
      -- fp = f0 :: fs, ep = some e
      obtain ⟨tE, hE, hEv⟩ := derives_exp e r (hep e rfl) hdigR
      obtain ⟨tF, hF, hFv⟩ := derives_frac (f0 :: fs) (printExp (some e) ++ r) hfpwf
        (digitP_fail_expSome e r)
      obtain ⟨tI, hI, hIc⟩ := derives_int ip
        ('.' :: ((f0 :: fs) ++ (printExp (some e) ++ r))) hint (digitP_fail_dot _)
      have hTail : Derives jsonGrammar
          (.seq (.nt JNT.int) (.seq (PExp.opt (.nt JNT.frac)) (PExp.opt (.nt JNT.exp))))
          (ip ++ ('.' :: ((f0 :: fs) ++ (printExp (some e) ++ r))))
          (.ok (.seq (.nodeNT JNT.int tI)
            (.seq (.choiceL (.nodeNT JNT.frac tF)) (.choiceL (.nodeNT JNT.exp tE)))) r) := by
        refine Derives.seqOk _ _ _ _ _ _ _ hI ?_
        exact Derives.seqOk _ _ _ _ _ _ _ (Derives.altL _ _ _ _ _ hF)
          (Derives.altL _ _ _ _ _ hE)
      cases neg with
      | true =>
        have hEq : printNumber ⟨true, ip, f0 :: fs, some e⟩ ++ r =
            '-' :: (ip ++ ('.' :: ((f0 :: fs) ++ (printExp (some e) ++ r)))) := by
          simp [printNumber, List.append_assoc]
        rw [hEq]
        refine ⟨.seq (.choiceL (.leaf ['-'])) (.seq (.nodeNT JNT.int tI)
          (.seq (.choiceL (.nodeNT JNT.frac tF)) (.choiceL (.nodeNT JNT.exp tE)))), ?_, ?_⟩
        · apply Derives.ntOk _ _ _ _ _ number_rule
          exact Derives.seqOk _ _ _ _ _ _ _
            (Derives.altL _ _ _ _ _ (Derives.chrOk '-' '-' _ (beqChar_refl '-'))) hTail
        · simp only [numberOf, intOf, hIc, hFv, hEv]
          rfl
      | false =>
        have hEq : printNumber ⟨false, ip, f0 :: fs, some e⟩ ++ r =
            ip ++ ('.' :: ((f0 :: fs) ++ (printExp (some e) ++ r))) := by
          simp [printNumber, List.append_assoc]
        rw [hEq]
        refine ⟨.seq (.choiceR (.leaf [])) (.seq (.nodeNT JNT.int tI)
          (.seq (.choiceL (.nodeNT JNT.frac tF)) (.choiceL (.nodeNT JNT.exp tE)))), ?_, ?_⟩
        · apply Derives.ntOk _ _ _ _ _ number_rule
          exact Derives.seqOk _ _ _ _ _ _ _ (optMinus_none ip _ hint) hTail
        · simp only [numberOf, intOf, hIc, hFv, hEv]
          rfl

/-! ## First-character failure kit

Each `value` alternative before the selected one must FAIL; on canonical
text this is always decided by the first character. -/

theorem object_fail_head (c : Char) (x : List Char) (hc : isJWsB c = false)
    (hne : beqChar '{' c = false) :
    Derives jsonGrammar (.nt JNT.object) (c :: x) .fail :=
  Derives.ntFail _ _ _ object_rule (Derives.seqFail₁ _ _ _ (structTok_fail '{' c x hc hne))

theorem array_fail_head (c : Char) (x : List Char) (hc : isJWsB c = false)
    (hne : beqChar '[' c = false) :
    Derives jsonGrammar (.nt JNT.array) (c :: x) .fail :=
  Derives.ntFail _ _ _ array_rule (Derives.seqFail₁ _ _ _ (structTok_fail '[' c x hc hne))

theorem number_fail_head (c : Char) (x : List Char) (h1 : beqChar '-' c = false)
    (h2 : beqChar '0' c = false) (h3 : (leChar '1' c && leChar c '9') = false) :
    Derives jsonGrammar (.nt JNT.number) (c :: x) .fail := by
  apply Derives.ntFail _ _ _ number_rule
  refine Derives.seqFail₂ _ _ _ _ _
    (Derives.altR _ _ _ _ _ (Derives.chrFail _ _ _ h1) (Derives.eps _)) ?_
  refine Derives.seqFail₁ _ _ _ ?_
  exact Derives.ntFail _ _ _ int_rule
    (Derives.altFail _ _ _ (Derives.chrFail _ _ _ h2)
      (Derives.seqFail₁ _ _ _ (Derives.rangeFail _ _ _ _ h3)))

theorem string_fail_head (c : Char) (x : List Char) (h : beqChar '"' c = false) :
    Derives jsonGrammar (.nt JNT.string) (c :: x) .fail :=
  Derives.ntFail _ _ _ string_rule (Derives.seqFail₁ _ _ _ (Derives.chrFail _ _ _ h))

theorem member_fail_head (c : Char) (x : List Char) (h : beqChar '"' c = false) :
    Derives jsonGrammar (.nt JNT.member) (c :: x) .fail :=
  Derives.ntFail _ _ _ member_rule (Derives.seqFail₁ _ _ _ (string_fail_head c x h))

/-- ALL seven `value` alternatives fail (used for the empty array's inner
`opt`, whose head is `']'`). -/
theorem value_fail_head (c : Char) (x : List Char)
    (hf : beqChar 'f' c = false) (hn : beqChar 'n' c = false) (ht : beqChar 't' c = false)
    (hws : isJWsB c = false) (hob : beqChar '{' c = false) (har : beqChar '[' c = false)
    (hmi : beqChar '-' c = false) (hz : beqChar '0' c = false)
    (hd19 : (leChar '1' c && leChar c '9') = false) (hq : beqChar '"' c = false) :
    Derives jsonGrammar (.nt JNT.value) (c :: x) .fail :=
  Derives.ntFail _ _ _ value_rule
    (Derives.altFail _ _ _ (Derives.litFail _ _ (stripPrefix?_cons_ne 'f' _ c _ hf))
      (Derives.altFail _ _ _ (Derives.litFail _ _ (stripPrefix?_cons_ne 'n' _ c _ hn))
        (Derives.altFail _ _ _ (Derives.litFail _ _ (stripPrefix?_cons_ne 't' _ c _ ht))
          (Derives.altFail _ _ _ (object_fail_head c x hws hob)
            (Derives.altFail _ _ _ (array_fail_head c x hws har)
              (Derives.altFail _ _ _ (number_fail_head c x hmi hz hd19)
                (string_fail_head c x hq)))))))

/-- Facts about a number-head character (`'-'` or a digit): not whitespace,
and the five earlier `value` alternatives all die on it. -/
theorem numHead_facts (hd : Char) (t : List Char)
    (hh : hd.toNat = 45 ∨ (48 ≤ hd.toNat ∧ hd.toNat ≤ 57)) :
    headNotWs (hd :: t) = true ∧
    Derives jsonGrammar (.lit "false".toList) (hd :: t) .fail ∧
    Derives jsonGrammar (.lit "null".toList) (hd :: t) .fail ∧
    Derives jsonGrammar (.lit "true".toList) (hd :: t) .fail ∧
    Derives jsonGrammar (.nt JNT.object) (hd :: t) .fail ∧
    Derives jsonGrammar (.nt JNT.array) (hd :: t) .fail := by
  have hsp : ' '.toNat = 32 := rfl
  have htb : '\t'.toNat = 9 := rfl
  have hnl : '\n'.toNat = 10 := rfl
  have hcr : '\r'.toNat = 13 := rfl
  have hws : isJWsB hd = false := by
    unfold isJWsB
    simp only [Bool.or_eq_false_iff]
    exact ⟨beqChar_false_of_toNat_ne (by omega), beqChar_false_of_toNat_ne (by omega),
      beqChar_false_of_toNat_ne (by omega), beqChar_false_of_toNat_ne (by omega)⟩
  have hfc : 'f'.toNat = 102 := rfl
  have hnc : 'n'.toNat = 110 := rfl
  have htc : 't'.toNat = 116 := rfl
  have hoc : '{'.toNat = 123 := rfl
  have hac : '['.toNat = 91 := rfl
  refine ⟨headNotWs_cons _ _ hws, ?_, ?_, ?_, ?_, ?_⟩
  · exact Derives.litFail _ _
      (stripPrefix?_cons_ne 'f' _ hd _ (beqChar_false_of_toNat_ne (by omega)))
  · exact Derives.litFail _ _
      (stripPrefix?_cons_ne 'n' _ hd _ (beqChar_false_of_toNat_ne (by omega)))
  · exact Derives.litFail _ _
      (stripPrefix?_cons_ne 't' _ hd _ (beqChar_false_of_toNat_ne (by omega)))
  · exact object_fail_head hd t hws (beqChar_false_of_toNat_ne (by omega))
  · exact array_fail_head hd t hws (beqChar_false_of_toNat_ne (by omega))

/-- Canonical number text starts with `'-'` or a digit; package the head
facts against arbitrary following text. -/
theorem printNumber_head_facts (n : JNumber) (hwf : wfNumber n = true) (X : List Char) :
    headNotWs (printNumber n ++ X) = true ∧
    Derives jsonGrammar (.lit "false".toList) (printNumber n ++ X) .fail ∧
    Derives jsonGrammar (.lit "null".toList) (printNumber n ++ X) .fail ∧
    Derives jsonGrammar (.lit "true".toList) (printNumber n ++ X) .fail ∧
    Derives jsonGrammar (.nt JNT.object) (printNumber n ++ X) .fail ∧
    Derives jsonGrammar (.nt JNT.array) (printNumber n ++ X) .fail := by
  obtain ⟨neg, ip, fp, ep⟩ := n
  obtain ⟨hint, -, -⟩ := wfNumber_spec hwf
  simp only at hint
  cases neg with
  | true =>
    cases fp with
    | nil =>
      have hEq : printNumber ⟨true, ip, [], ep⟩ ++ X = '-' :: (ip ++ (printExp ep ++ X)) := by
        simp [printNumber, List.append_assoc]
      rw [hEq]
      exact numHead_facts '-' _ (Or.inl (by decide))
    | cons f0 fs =>
      have hEq : printNumber ⟨true, ip, f0 :: fs, ep⟩ ++ X =
          '-' :: (ip ++ ('.' :: ((f0 :: fs) ++ (printExp ep ++ X)))) := by
        simp [printNumber, List.append_assoc]
      rw [hEq]
      exact numHead_facts '-' _ (Or.inl (by decide))
  | false =>
    rcases wfInt_cases hint with rfl | ⟨d, ds, rfl, hd, -⟩
    · cases fp with
      | nil =>
        have hEq : printNumber ⟨false, ['0'], [], ep⟩ ++ X = '0' :: (printExp ep ++ X) := by
          simp [printNumber]
        rw [hEq]
        exact numHead_facts '0' _ (Or.inr (by decide))
      | cons f0 fs =>
        have hEq : printNumber ⟨false, ['0'], f0 :: fs, ep⟩ ++ X =
            '0' :: ('.' :: ((f0 :: fs) ++ (printExp ep ++ X))) := by
          simp [printNumber, List.append_assoc]
        rw [hEq]
        exact numHead_facts '0' _ (Or.inr (by decide))
    · have hdn : 48 ≤ d.toNat ∧ d.toNat ≤ 57 := by
        rw [Bool.and_eq_true, leChar_iff, leChar_iff] at hd
        have h1 : '1'.toNat = 49 := rfl
        have h9 : '9'.toNat = 57 := rfl
        omega
      cases fp with
      | nil =>
        have hEq : printNumber ⟨false, d :: ds, [], ep⟩ ++ X =
            d :: (ds ++ (printExp ep ++ X)) := by
          simp [printNumber, List.append_assoc]
        rw [hEq]
        exact numHead_facts d _ (Or.inr hdn)
      | cons f0 fs =>
        have hEq : printNumber ⟨false, d :: ds, f0 :: fs, ep⟩ ++ X =
            d :: (ds ++ ('.' :: ((f0 :: fs) ++ (printExp ep ++ X)))) := by
          simp [printNumber, List.append_assoc]
        rw [hEq]
        exact numHead_facts d _ (Or.inr hdn)

/-- The head of canonical value text is never whitespace. -/
theorem printValue_head (v : JValue) (hwf : wfValue v = true) (X : List Char) :
    headNotWs (printValue v ++ X) = true := by
  cases v with
  | jnull =>
    simp only [printValue]
    exact headNotWs_cons 'n' _ (by decide)
  | jbool b =>
    cases b with
    | true =>
      simp only [printValue]
      exact headNotWs_cons 't' _ (by decide)
    | false =>
      simp only [printValue]
      exact headNotWs_cons 'f' _ (by decide)
  | jnum m =>
    simp only [printValue]
    exact (printNumber_head_facts m (wfValue_jnum hwf) X).1
  | jstr s =>
    have hEq : printValue (.jstr s) ++ X = '"' :: (escChars s ++ ('"' :: X)) := by
      simp [printValue, printString, List.append_assoc]
    rw [hEq]
    exact headNotWs_cons '"' _ (by decide)
  | jarr vs =>
    have hEq : printValue (.jarr vs) ++ X = '[' :: (printItems vs ++ (']' :: X)) := by
      simp [printValue, List.append_assoc]
    rw [hEq]
    exact headNotWs_cons '[' _ (by decide)
  | jobj ms =>
    have hEq : printValue (.jobj ms) ++ X = '{' :: (printMembers ms ++ ('}' :: X)) := by
      simp [printValue, List.append_assoc]
    rw [hEq]
    exact headNotWs_cons '{' _ (by decide)

/-! ## Item/member segment text

`printItems`/`printMembers` interleave separators; re-express them as
"first element ++ comma-led tail" to match the grammar's `first (sep elem)*`
shape. -/

def itemsTail : JArray → List Char
  | .nil => []
  | .cons v rest => ',' :: (printValue v ++ itemsTail rest)

def memberText (k : List Char) (v : JValue) : List Char :=
  printString k ++ ':' :: printValue v

def membersTail : JMembers → List Char
  | .nil => []
  | .cons k v rest => ',' :: (memberText k v ++ membersTail rest)

theorem printItems_eq (v : JValue) (rest : JArray) :
    printItems (.cons v rest) = printValue v ++ itemsTail rest := by
  cases rest with
  | nil => simp [printItems, itemsTail]
  | cons v1 rest' =>
    simp [printItems, itemsTail, printItems_eq v1 rest']

theorem printMembers_eq (k : List Char) (v : JValue) (rest : JMembers) :
    printMembers (.cons k v rest) = memberText k v ++ membersTail rest := by
  cases rest with
  | nil => simp [printMembers, membersTail, memberText]
  | cons k1 v1 rest' =>
    simp [printMembers, membersTail, memberText, printMembers_eq k1 v1 rest',
      List.append_assoc]

theorem valFollow_itemsTail (rest : JArray) (x : List Char) (hx : valFollow x = true) :
    valFollow (itemsTail rest ++ x) = true := by
  cases rest with
  | nil => simpa [itemsTail] using hx
  | cons v r' =>
    have hEq : itemsTail (.cons v r') ++ x = ',' :: ((printValue v ++ itemsTail r') ++ x) := by
      simp [itemsTail]
    rw [hEq]
    exact valFollow_cons _ _ (by decide)

theorem valFollow_membersTail (rest : JMembers) (x : List Char) (hx : valFollow x = true) :
    valFollow (membersTail rest ++ x) = true := by
  cases rest with
  | nil => simpa [membersTail] using hx
  | cons k v r' =>
    have hEq : membersTail (.cons k v r') ++ x =
        ',' :: ((memberText k v ++ membersTail r') ++ x) := by
      simp [membersTail]
    rw [hEq]
    exact valFollow_cons _ _ (by decide)

theorem memberText_headNotWs (k : List Char) (v : JValue) (x : List Char) :
    headNotWs (memberText k v ++ x) = true := by
  have hEq : memberText k v ++ x = '"' :: (escChars k ++ ('"' :: (':' :: (printValue v ++ x)))) := by
    simp [memberText, printString, List.append_assoc]
  rw [hEq]
  exact headNotWs_cons '"' _ (by decide)

/-- Assemble a `member` node from an already-derived value (keeps the
mutual block's recursion strictly on the AST). -/
theorem derives_member_assemble (k : List Char) (v : JValue) (Z : List Char) (vT : PTree)
    (hv : Derives jsonGrammar (.nt JNT.value) (printValue v ++ Z)
      (.ok (.nodeNT JNT.value vT) Z))
    (hvv : valueOf vT = .ok v) (hwv : wfValue v = true) :
    ∃ mT, Derives jsonGrammar (.nt JNT.member) (memberText k v ++ Z)
        (.ok (.nodeNT JNT.member mT) Z) ∧ memberKeyOf mT = .ok (k, v) := by
  obtain ⟨sT, hS, hSv⟩ := derives_string k (':' :: (printValue v ++ Z))
  have hEq : memberText k v ++ Z =
      '"' :: (escChars k ++ ('"' :: (':' :: (printValue v ++ Z)))) := by
    simp [memberText, printString, List.append_assoc]
  rw [hEq]
  refine ⟨.seq (.nodeNT JNT.string sT) (.seq (structTokTree ':') (.nodeNT JNT.value vT)),
    ?_, ?_⟩
  · apply Derives.ntOk _ _ _ _ _ member_rule
    refine Derives.seqOk _ _ _ _ _ _ _ hS ?_
    exact Derives.seqOk _ _ _ _ _ _ _
      (derives_structTok ':' _ (by decide) (printValue_head v hwv Z)) hv
  · simp only [memberKeyOf, hSv, hvv]
    rfl

/-! ## The value layer (mutual recursion over `JValue`/`JArray`/`JMembers`)

Each constructor maps to its `value` choice depth exactly as `valueOf`
expects: false = L, null = RL, true = RRL, object = RRRL, array = RRRRL,
number = RRRRRL, string = RRRRRR. -/

mutual

/-- Value payoff: canonical text of a well-formed value parses as ONE
`value` node, and `valueOf` recovers the value. -/
theorem derives_value (v : JValue) (r : List Char) (hwf : wfValue v = true)
    (hfollow : valFollow r = true) :
    ∃ t, Derives jsonGrammar (.nt JNT.value) (printValue v ++ r)
        (.ok (.nodeNT JNT.value t) r) ∧ valueOf t = .ok v := by
  cases v with
  | jnull =>
    simp only [printValue]
    refine ⟨.choiceR (.choiceL (.leaf "null".toList)), ?_, by simp only [valueOf]⟩
    apply Derives.ntOk _ _ _ _ _ value_rule
    refine Derives.altR _ _ _ _ _
      (Derives.litFail _ _ (stripPrefix?_cons_ne 'f' _ 'n' _ (by decide))) ?_
    exact Derives.altL _ _ _ _ _ (derives_lit_append _ r)
  | jbool b =>
    cases b with
    | false =>
      simp only [printValue]
      refine ⟨.choiceL (.leaf "false".toList), ?_, by simp only [valueOf]⟩
      exact Derives.ntOk _ _ _ _ _ value_rule
        (Derives.altL _ _ _ _ _ (derives_lit_append _ r))
    | true =>
      simp only [printValue]
      refine ⟨.choiceR (.choiceR (.choiceL (.leaf "true".toList))), ?_,
        by simp only [valueOf]⟩
      apply Derives.ntOk _ _ _ _ _ value_rule
      refine Derives.altR _ _ _ _ _
        (Derives.litFail _ _ (stripPrefix?_cons_ne 'f' _ 't' _ (by decide))) ?_
      refine Derives.altR _ _ _ _ _
        (Derives.litFail _ _ (stripPrefix?_cons_ne 'n' _ 't' _ (by decide))) ?_
      exact Derives.altL _ _ _ _ _ (derives_lit_append _ r)
  | jnum m =>
    simp only [printValue]
    have hwfn := wfValue_jnum hwf
    obtain ⟨-, hLf, hLn, hLt, hOb, hAr⟩ := printNumber_head_facts m hwfn r
    obtain ⟨tN, hN, hNv⟩ := derives_number m r hwfn (numFollow_of_valFollow r hfollow)
    refine ⟨.choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceL
      (.nodeNT JNT.number tN)))))), ?_, ?_⟩
    · apply Derives.ntOk _ _ _ _ _ value_rule
      exact Derives.altR _ _ _ _ _ hLf (Derives.altR _ _ _ _ _ hLn
        (Derives.altR _ _ _ _ _ hLt (Derives.altR _ _ _ _ _ hOb
          (Derives.altR _ _ _ _ _ hAr (Derives.altL _ _ _ _ _ hN)))))
    · simp only [valueOf, hNv]
      rfl
  | jstr s =>
    have hEq : printValue (.jstr s) ++ r = '"' :: (escChars s ++ '"' :: r) := by
      simp [printValue, printString, List.append_assoc]
    rw [hEq]
    obtain ⟨tS, hS, hSv⟩ := derives_string s r
    refine ⟨.choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceR
      (.nodeNT JNT.string tS)))))), ?_, ?_⟩
    · apply Derives.ntOk _ _ _ _ _ value_rule
      refine Derives.altR _ _ _ _ _
        (Derives.litFail _ _ (stripPrefix?_cons_ne 'f' _ '"' _ (by decide))) ?_
      refine Derives.altR _ _ _ _ _
        (Derives.litFail _ _ (stripPrefix?_cons_ne 'n' _ '"' _ (by decide))) ?_
      refine Derives.altR _ _ _ _ _
        (Derives.litFail _ _ (stripPrefix?_cons_ne 't' _ '"' _ (by decide))) ?_
      refine Derives.altR _ _ _ _ _ (object_fail_head '"' _ (by decide) (by decide)) ?_
      refine Derives.altR _ _ _ _ _ (array_fail_head '"' _ (by decide) (by decide)) ?_
      exact Derives.altR _ _ _ _ _
        (number_fail_head '"' _ (by decide) (by decide) (by decide)) hS
    · simp only [valueOf, hSv]
      rfl
  | jarr vs =>
    have hwfa := wfValue_jarr hwf
    have hnwr := headNotWs_of_valFollow r hfollow
    cases vs with
    | nil =>
      have hEq : printValue (.jarr .nil) ++ r = '[' :: (']' :: r) := by
        simp [printValue, printItems]
      rw [hEq]
      refine ⟨.choiceR (.choiceR (.choiceR (.choiceR (.choiceL (.nodeNT JNT.array
        (.seq (structTokTree '[') (.seq (.choiceR (.leaf []))
          (structTokTree ']')))))))), ?_, ?_⟩
      · apply Derives.ntOk _ _ _ _ _ value_rule
        refine Derives.altR _ _ _ _ _
          (Derives.litFail _ _ (stripPrefix?_cons_ne 'f' _ '[' _ (by decide))) ?_
        refine Derives.altR _ _ _ _ _
          (Derives.litFail _ _ (stripPrefix?_cons_ne 'n' _ '[' _ (by decide))) ?_
        refine Derives.altR _ _ _ _ _
          (Derives.litFail _ _ (stripPrefix?_cons_ne 't' _ '[' _ (by decide))) ?_
        refine Derives.altR _ _ _ _ _ (object_fail_head '[' _ (by decide) (by decide)) ?_
        refine Derives.altL _ _ _ _ _ ?_
        apply Derives.ntOk _ _ _ _ _ array_rule
        refine Derives.seqOk _ _ _ _ _ _ _
          (derives_structTok '[' _ (by decide) (headNotWs_cons ']' r (by decide))) ?_
        refine Derives.seqOk _ _ _ _ _ _ _ ?_ (derives_structTok ']' r (by decide) hnwr)
        refine Derives.altR _ _ _ _ _ ?_ (Derives.eps _)
        refine Derives.seqFail₁ _ _ _ ?_
        exact value_fail_head ']' r (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · simp only [valueOf, arrayOf]
    | cons v0 rest =>
      obtain ⟨hwv0, hwrest⟩ := wfArray_cons hwfa
      have hEq : printValue (.jarr (.cons v0 rest)) ++ r =
          '[' :: (printValue v0 ++ (itemsTail rest ++ (']' :: r))) := by
        simp [printValue, printItems_eq, List.append_assoc]
      rw [hEq]
      obtain ⟨v0T, hv0, hv0v⟩ := derives_value v0 (itemsTail rest ++ (']' :: r)) hwv0
        (valFollow_itemsTail rest _ (valFollow_cons ']' r (by decide)))
      obtain ⟨starT, hstar, hitems⟩ := derives_itemsTail rest (']' :: r) hwrest
        (valFollow_cons ']' r (by decide))
        (Derives.seqFail₁ _ _ _ (structTok_fail ',' ']' r (by decide) (by decide)))
      refine ⟨.choiceR (.choiceR (.choiceR (.choiceR (.choiceL (.nodeNT JNT.array
        (.seq (structTokTree '[') (.seq (.choiceL (.seq (.nodeNT JNT.value v0T) starT))
          (structTokTree ']')))))))), ?_, ?_⟩
      · apply Derives.ntOk _ _ _ _ _ value_rule
        refine Derives.altR _ _ _ _ _
          (Derives.litFail _ _ (stripPrefix?_cons_ne 'f' _ '[' _ (by decide))) ?_
        refine Derives.altR _ _ _ _ _
          (Derives.litFail _ _ (stripPrefix?_cons_ne 'n' _ '[' _ (by decide))) ?_
        refine Derives.altR _ _ _ _ _
          (Derives.litFail _ _ (stripPrefix?_cons_ne 't' _ '[' _ (by decide))) ?_
        refine Derives.altR _ _ _ _ _ (object_fail_head '[' _ (by decide) (by decide)) ?_
        refine Derives.altL _ _ _ _ _ ?_
        apply Derives.ntOk _ _ _ _ _ array_rule
        refine Derives.seqOk _ _ _ _ _ _ _
          (derives_structTok '[' _ (by decide) (printValue_head v0 hwv0 _)) ?_
        refine Derives.seqOk _ _ _ _ _ _ _ ?_ (derives_structTok ']' r (by decide) hnwr)
        exact Derives.altL _ _ _ _ _ (Derives.seqOk _ _ _ _ _ _ _ hv0 hstar)
      · simp only [valueOf, arrayOf, hv0v, hitems]
        rfl
  | jobj ms =>
    have hwfm := wfValue_jobj hwf
    have hnwr := headNotWs_of_valFollow r hfollow
    cases ms with
    | nil =>
      have hEq : printValue (.jobj .nil) ++ r = '{' :: ('}' :: r) := by
        simp [printValue, printMembers]
      rw [hEq]
      refine ⟨.choiceR (.choiceR (.choiceR (.choiceL (.nodeNT JNT.object
        (.seq (structTokTree '{') (.seq (.choiceR (.leaf []))
          (structTokTree '}'))))))), ?_, ?_⟩
      · apply Derives.ntOk _ _ _ _ _ value_rule
        refine Derives.altR _ _ _ _ _
          (Derives.litFail _ _ (stripPrefix?_cons_ne 'f' _ '{' _ (by decide))) ?_
        refine Derives.altR _ _ _ _ _
          (Derives.litFail _ _ (stripPrefix?_cons_ne 'n' _ '{' _ (by decide))) ?_
        refine Derives.altR _ _ _ _ _
          (Derives.litFail _ _ (stripPrefix?_cons_ne 't' _ '{' _ (by decide))) ?_
        refine Derives.altL _ _ _ _ _ ?_
        apply Derives.ntOk _ _ _ _ _ object_rule
        refine Derives.seqOk _ _ _ _ _ _ _
          (derives_structTok '{' _ (by decide) (headNotWs_cons '}' r (by decide))) ?_
        refine Derives.seqOk _ _ _ _ _ _ _ ?_ (derives_structTok '}' r (by decide) hnwr)
        refine Derives.altR _ _ _ _ _ ?_ (Derives.eps _)
        exact Derives.seqFail₁ _ _ _ (member_fail_head '}' r (by decide))
      · simp only [valueOf, objectOf]
    | cons k v rest =>
      obtain ⟨hwv, hwrest⟩ := wfMembers_cons hwfm
      have hEq : printValue (.jobj (.cons k v rest)) ++ r =
          '{' :: (memberText k v ++ (membersTail rest ++ ('}' :: r))) := by
        simp [printValue, printMembers_eq, List.append_assoc]
      rw [hEq]
      obtain ⟨vT, hv, hvv⟩ := derives_value v (membersTail rest ++ ('}' :: r)) hwv
        (valFollow_membersTail rest _ (valFollow_cons '}' r (by decide)))
      obtain ⟨mT, hm, hmv⟩ := derives_member_assemble k v _ vT hv hvv hwv
      obtain ⟨starT, hstar, hmembers⟩ := derives_membersTail rest ('}' :: r) hwrest
        (valFollow_cons '}' r (by decide))
        (Derives.seqFail₁ _ _ _ (structTok_fail ',' '}' r (by decide) (by decide)))
      refine ⟨.choiceR (.choiceR (.choiceR (.choiceL (.nodeNT JNT.object
        (.seq (structTokTree '{') (.seq (.choiceL (.seq (.nodeNT JNT.member mT) starT))
          (structTokTree '}'))))))), ?_, ?_⟩
      · apply Derives.ntOk _ _ _ _ _ value_rule
        refine Derives.altR _ _ _ _ _
          (Derives.litFail _ _ (stripPrefix?_cons_ne 'f' _ '{' _ (by decide))) ?_
        refine Derives.altR _ _ _ _ _
          (Derives.litFail _ _ (stripPrefix?_cons_ne 'n' _ '{' _ (by decide))) ?_
        refine Derives.altR _ _ _ _ _
          (Derives.litFail _ _ (stripPrefix?_cons_ne 't' _ '{' _ (by decide))) ?_
        refine Derives.altL _ _ _ _ _ ?_
        apply Derives.ntOk _ _ _ _ _ object_rule
        refine Derives.seqOk _ _ _ _ _ _ _
          (derives_structTok '{' _ (by decide) (memberText_headNotWs k v _)) ?_
        refine Derives.seqOk _ _ _ _ _ _ _ ?_ (derives_structTok '}' r (by decide) hnwr)
        exact Derives.altL _ _ _ _ _ (Derives.seqOk _ _ _ _ _ _ _ hm hstar)
      · simp only [valueOf, objectOf, hmv, hmembers]
        rfl

/-- The `( "," value )*` region of an array body. -/
theorem derives_itemsTail (vs : JArray) (r : List Char) (hwf : wfArray vs = true)
    (hfollow : valFollow r = true)
    (hfail : Derives jsonGrammar (.seq valueSepP (.nt JNT.value)) r .fail) :
    ∃ t, Derives jsonGrammar (.star (.seq valueSepP (.nt JNT.value)))
        (itemsTail vs ++ r) (.ok t r) ∧ arrayItems t = .ok vs := by
  cases vs with
  | nil =>
    refine ⟨.starNil, ?_, by simp only [arrayItems]⟩
    simp only [itemsTail, List.nil_append]
    exact Derives.starNil _ _ hfail
  | cons v rest =>
    obtain ⟨hwv, hwrest⟩ := wfArray_cons hwf
    have hEq : itemsTail (.cons v rest) ++ r =
        ',' :: (printValue v ++ (itemsTail rest ++ r)) := by
      simp [itemsTail, List.append_assoc]
    rw [hEq]
    obtain ⟨vT, hv, hvv⟩ := derives_value v (itemsTail rest ++ r) hwv
      (valFollow_itemsTail rest r hfollow)
    obtain ⟨ts, hts, htsv⟩ := derives_itemsTail rest r hwrest hfollow hfail
    refine ⟨.starCons (.seq (structTokTree ',') (.nodeNT JNT.value vT)) ts, ?_, ?_⟩
    · refine Derives.starCons _ _ _ _ _ _ ?_ hts
      exact Derives.seqOk _ _ _ _ _ _ _
        (derives_structTok ',' _ (by decide) (printValue_head v hwv _)) hv
    · simp only [arrayItems, hvv, htsv]
      rfl

/-- The `( "," member )*` region of an object body. -/
theorem derives_membersTail (ms : JMembers) (r : List Char) (hwf : wfMembers ms = true)
    (hfollow : valFollow r = true)
    (hfail : Derives jsonGrammar (.seq valueSepP (.nt JNT.member)) r .fail) :
    ∃ t, Derives jsonGrammar (.star (.seq valueSepP (.nt JNT.member)))
        (membersTail ms ++ r) (.ok t r) ∧ memberItems t = .ok ms := by
  cases ms with
  | nil =>
    refine ⟨.starNil, ?_, by simp only [memberItems]⟩
    simp only [membersTail, List.nil_append]
    exact Derives.starNil _ _ hfail
  | cons k v rest =>
    obtain ⟨hwv, hwrest⟩ := wfMembers_cons hwf
    have hEq : membersTail (.cons k v rest) ++ r =
        ',' :: (memberText k v ++ (membersTail rest ++ r)) := by
      simp [membersTail, List.append_assoc]
    rw [hEq]
    obtain ⟨vT, hv, hvv⟩ := derives_value v (membersTail rest ++ r) hwv
      (valFollow_membersTail rest r hfollow)
    obtain ⟨mT, hm, hmv⟩ := derives_member_assemble k v _ vT hv hvv hwv
    obtain ⟨ts, hts, htsv⟩ := derives_membersTail rest r hwrest hfollow hfail
    refine ⟨.starCons (.seq (structTokTree ',') (.nodeNT JNT.member mT)) ts, ?_, ?_⟩
    · refine Derives.starCons _ _ _ _ _ _ ?_ hts
      exact Derives.seqOk _ _ _ _ _ _ _
        (derives_structTok ',' _ (by decide) (memberText_headNotWs k v _)) hm
    · simp only [memberItems, hmv, htsv]
      rfl

end

/-! ## Payoffs -/

/-- **J4, derivation form**: the canonical text of a well-formed value
derives at `jsonText` consuming the WHOLE input, with a tree of EXACTLY
the shape `parseJson` unwraps (`nodeNT (seq ws (seq (nodeNT value vT) rest))`),
and `valueOf vT` recovers `v`. -/
theorem derives_printJson (v : JValue) (hwf : wfValue v = true) :
    ∃ wsT vT restT,
      Derives jsonGrammar (.nt JNT.jsonText) (printJson v).toList
        (.ok (.nodeNT JNT.jsonText
          (.seq wsT (.seq (.nodeNT JNT.value vT) restT))) []) ∧
      valueOf vT = .ok v := by
  have htl : (printJson v).toList = printValue v := by
    simp [printJson, String.toList_ofList]
  rw [htl]
  obtain ⟨vT, hvD, hvV⟩ := derives_value v [] hwf rfl
  rw [List.append_nil] at hvD
  have hnw : headNotWs (printValue v) = true := by
    have h := printValue_head v hwf []
    rwa [List.append_nil] at h
  refine ⟨wsTreeNil, vT, .seq wsTreeNil .notT, ?_, hvV⟩
  apply Derives.ntOk _ _ _ _ _ jsonText_rule
  refine Derives.seqOk _ _ _ _ _ _ _ (derives_ws_nil _ hnw) ?_
  refine Derives.seqOk _ _ _ _ _ _ _ hvD ?_
  exact Derives.seqOk _ _ _ _ _ _ _ (derives_ws_nil [] rfl)
    (Derives.notFail _ _ Derives.anyFail)

/-- **J4, interpreter form** — the project's closing JSON result: the
verified PEG interpreter parses `printJson v` back to exactly `v`, for
every sufficiently large fuel (T3 completeness + T0 fuel monotonicity). -/
theorem parse_print_json (v : JValue) (hwf : wfValue v = true) :
    ∃ fuel, ∀ fuel', fuel ≤ fuel' → parseJson fuel' (printJson v) = .ok v := by
  obtain ⟨wsT, vT, restT, hd, hv⟩ := derives_printJson v hwf
  obtain ⟨f, hf⟩ := pegRun_complete hd
  refine ⟨f, fun f' hle => ?_⟩
  have hrun : pegRun jsonGrammar f' (.nt JNT.jsonText) (printJson v).toList =
      some (.ok (.nodeNT JNT.jsonText
        (.seq wsT (.seq (.nodeNT JNT.value vT) restT))) []) :=
    pegRun_mono_le hle hf
  unfold parseJson
  rw [hrun]
  exact hv

#print axioms derives_printJson
#print axioms parse_print_json

end Shallot.Json
