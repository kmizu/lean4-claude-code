import Json.Wf
import Json.ToAst
import Json.Printer

/-!
# J3 — lexical-layer inverse lemmas for the JSON roundtrip

The token-level kit J4's roundtrip proof consumes. Everything here is a
plain equation or Bool fact about the printer's leaf encoders
(`hexDigitChar`/`hex4`/`escapeCp`/`escChars`) and the extractor's leaf
decoders (`hexVal`/`combineUnits`), plus the digit-span bridges out of
`Json/Wf.lean`. Shape mirrors `Shallot/Syntax/Lexemes.lean`: statements
are phrased at the Bool level the grammar side conditions
(`Derives.rangeOk` etc.) want, so J4 can feed them in verbatim.

Contents: hex kit (`hexVal_hexDigitChar`, `hexListVal_hex4`,
`hex4_decode`), scalar-unit kit (`char_toNat_scalar`,
`charOfNat_toNat`, `notSurrogate_toNat`), combineUnits kit
(`combineUnits_scalar_cons` / `combineUnits_of_scalars` /
`combineUnits_map_toNat`), escapeCp kit (`escapeCp_cases` and friends,
`escChars_append`), digit-span kit (`wfDigits_*`, `wfInt_cases`,
`wfNumber_spec`, `wfValue_*`).
-/

set_option autoImplicit false

namespace Shallot.Json

/-! ## Char/Bool basics -/

theorem eq_of_beqChar {a b : Char} (h : beqChar a b = true) : a = b := by
  unfold beqChar at h
  simp only [beq_iff_eq] at h
  exact Char.toNat_inj.mp h

theorem beqChar_refl (c : Char) : beqChar c c = true := by
  simp [beqChar]

/-- `leChar` is `≤` on code points (Bool ↔ Prop bridge). -/
theorem leChar_iff (a b : Char) : leChar a b = true ↔ a.toNat ≤ b.toNat := by
  simp [leChar, Nat.ble_eq]

/-! ## Hex kit -/

/-- `hexDigitChar n` for `n < 10` lands in the grammar's `range '0' '9'`. -/
theorem hexDigitChar_class_digit (n : Nat) (h : n < 10) :
    (leChar '0' (hexDigitChar n) && leChar (hexDigitChar n) '9') = true := by
  have h10 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
      n = 8 ∨ n = 9 := by omega
  rcases h10 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `hexDigitChar n` for `10 ≤ n < 16` lands in `range 'a' 'f'` — and the
digit test is FALSE, which is what rule 13's prioritized choice needs to
take the second alternative. -/
theorem hexDigitChar_class_lower (n : Nat) (h10 : 10 ≤ n) (h : n < 16) :
    (leChar '0' (hexDigitChar n) && leChar (hexDigitChar n) '9') = false ∧
    (leChar 'a' (hexDigitChar n) && leChar (hexDigitChar n) 'f') = true := by
  have h6 : n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- HEXDIG classes for `hexDigitChar`, packaged: below 10 it is a decimal
digit; otherwise the digit test fails and it is in `'a'..'f'`. -/
theorem hexDigitChar_lt16_class (n : Nat) (h : n < 16) :
    (n < 10 ∧ (leChar '0' (hexDigitChar n) && leChar (hexDigitChar n) '9') = true) ∨
    (10 ≤ n ∧ (leChar '0' (hexDigitChar n) && leChar (hexDigitChar n) '9') = false ∧
      (leChar 'a' (hexDigitChar n) && leChar (hexDigitChar n) 'f') = true) := by
  by_cases h10 : n < 10
  · exact Or.inl ⟨h10, hexDigitChar_class_digit n h10⟩
  · have hge : 10 ≤ n := by omega
    exact Or.inr ⟨hge, hexDigitChar_class_lower n hge h⟩

/-- `hexVal` inverts `hexDigitChar` below 16. -/
theorem hexVal_hexDigitChar (n : Nat) (h : n < 16) :
    hexVal (hexDigitChar n) = n := by
  have h16 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
      n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by
    omega
  rcases h16 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Base-16 value of a hex string, most significant digit first (the fold
matches `escapeOf`'s `((a*16 + b)*16 + c)*16 + d`). -/
def hexListVal (cs : List Char) : Nat :=
  cs.foldl (fun acc c => acc * 16 + hexVal c) 0

/-- `hex4` is literally its four digit characters. -/
theorem hex4_shape (u : Nat) :
    hex4 u = [hexDigitChar (u / 4096 % 16), hexDigitChar (u / 256 % 16),
              hexDigitChar (u / 16 % 16), hexDigitChar (u % 16)] := rfl

theorem hex4_length (u : Nat) : (hex4 u).length = 4 := rfl

/-- J3 hex payoff: `hexListVal` inverts `hex4` on UTF-16 code units. -/
theorem hexListVal_hex4 (u : Nat) (h : u ≤ 0xFFFF) : hexListVal (hex4 u) = u := by
  have h1 := hexVal_hexDigitChar (u / 4096 % 16) (Nat.mod_lt _ (by decide))
  have h2 := hexVal_hexDigitChar (u / 256 % 16) (Nat.mod_lt _ (by decide))
  have h3 := hexVal_hexDigitChar (u / 16 % 16) (Nat.mod_lt _ (by decide))
  have h4 := hexVal_hexDigitChar (u % 16) (Nat.mod_lt _ (by decide))
  simp only [hex4, hexListVal, List.foldl, h1, h2, h3, h4]
  omega

/-- The `escapeOf`-shaped decode: whenever `hex4 u = [a, b, c, d]`, the
parser's fold `((hexVal a * 16 + hexVal b) * 16 + hexVal c) * 16 + hexVal d`
recovers `u`. -/
theorem hex4_decode (u : Nat) (h : u ≤ 0xFFFF) (a b c d : Char)
    (heq : hex4 u = [a, b, c, d]) :
    ((hexVal a * 16 + hexVal b) * 16 + hexVal c) * 16 + hexVal d = u := by
  have hv := hexListVal_hex4 u h
  rw [heq] at hv
  simp only [hexListVal, List.foldl] at hv
  omega

/-- Every char `hex4` emits is in a HEXDIG class (digit or lowercase). -/
theorem hex4_all_class (u : Nat) : ∀ c ∈ hex4 u,
    ((leChar '0' c && leChar c '9') || (leChar 'a' c && leChar c 'f')) = true := by
  intro c hc
  have hcase : ∀ m : Nat, m < 16 →
      ((leChar '0' (hexDigitChar m) && leChar (hexDigitChar m) '9') ||
        (leChar 'a' (hexDigitChar m) && leChar (hexDigitChar m) 'f')) = true := by
    intro m hm
    rcases hexDigitChar_lt16_class m hm with ⟨-, hd⟩ | ⟨-, -, hl⟩
    · rw [hd]; rfl
    · rw [hl]; simp
  have hmem : c = hexDigitChar (u / 4096 % 16) ∨ c = hexDigitChar (u / 256 % 16) ∨
      c = hexDigitChar (u / 16 % 16) ∨ c = hexDigitChar (u % 16) := by
    simpa [hex4] using hc
  rcases hmem with rfl | rfl | rfl | rfl <;> exact hcase _ (Nat.mod_lt _ (by decide))

/-! ## Scalar-unit kit -/

/-- Every `Char` is a Unicode scalar value: below the surrogate block, or
past it and within the code-point range (from the `Char.valid` field). -/
theorem char_toNat_scalar (c : Char) :
    c.toNat < 0xD800 ∨ (0xE000 ≤ c.toNat ∧ c.toNat ≤ 0x10FFFF) := by
  have h : Nat.isValidChar c.toNat := c.valid
  unfold Nat.isValidChar at h
  omega

/-- The weakening J4 threads into `combineUnits_scalar_cons`. -/
theorem char_toNat_not_surrogate (c : Char) :
    c.toNat < 0xD800 ∨ 0xE000 ≤ c.toNat := by
  rcases char_toNat_scalar c with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem char_toNat_le_max (c : Char) : c.toNat ≤ 0x10FFFF := by
  rcases char_toNat_scalar c with h | ⟨-, h⟩
  · omega
  · exact h

/-- `Char.ofNat` inverts `Char.toNat` (core `Char.ofNat_toNat`, restated). -/
theorem charOfNat_toNat (c : Char) : Char.ofNat c.toNat = c :=
  Char.ofNat_toNat c

/-- "Not a UTF-16 surrogate", as a Bool. -/
def notSurrogate (n : Nat) : Bool := Nat.blt n 0xD800 || Nat.ble 0xE000 n

theorem notSurrogate_iff (n : Nat) :
    notSurrogate n = true ↔ (n < 0xD800 ∨ 0xE000 ≤ n) := by
  simp [notSurrogate, Nat.blt_eq, Nat.ble_eq]

/-- Every `Char`'s code point is a non-surrogate (Bool form). -/
theorem notSurrogate_toNat (c : Char) : notSurrogate c.toNat = true :=
  (notSurrogate_iff c.toNat).mpr (char_toNat_not_surrogate c)

/-! ## combineUnits kit -/

/-- Both surrogate guards inside `combineUnits` are false on a scalar. -/
theorem surrogate_guards_false {u : Nat} (h : u < 0xD800 ∨ 0xE000 ≤ u) :
    (0xD800 ≤ u && u ≤ 0xDBFF) = false ∧ (0xDC00 ≤ u && u ≤ 0xDFFF) = false := by
  constructor <;>
    (simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)

/-- A scalar unit passes straight through `combineUnits`. -/
theorem combineUnits_scalar_cons (u : Nat) (us : List Nat)
    (h : u < 0xD800 ∨ 0xE000 ≤ u) :
    combineUnits (u :: us) = (combineUnits us).map (Char.ofNat u :: ·) := by
  obtain ⟨h1, h2⟩ := surrogate_guards_false h
  cases hus : combineUnits us with
  | ok cs =>
    rw [combineUnits.eq_def]
    simp only [h1, h2, Bool.false_eq_true, if_false, hus]
    rfl
  | error e =>
    rw [combineUnits.eq_def]
    simp only [h1, h2, Bool.false_eq_true, if_false, hus]
    rfl

/-- An all-scalar unit list decodes to its `Char.ofNat` image. -/
theorem combineUnits_of_scalars (us : List Nat)
    (h : ∀ u ∈ us, u < 0xD800 ∨ 0xE000 ≤ u) :
    combineUnits us = .ok (us.map Char.ofNat) := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    rw [List.map_cons, combineUnits_scalar_cons u us (h u (by simp)),
        ih (fun v hv => h v (by simp [hv]))]
    rfl

/-- J3 combineUnits payoff: re-decoding the code units of an
already-decoded string gives the string back — exactly the shape J4 feeds
it (`s.map Char.toNat` for a decoded `s : List Char`). -/
theorem combineUnits_map_toNat (s : List Char) :
    combineUnits (s.map Char.toNat) = .ok s := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    rw [List.map_cons,
        combineUnits_scalar_cons c.toNat (s.map Char.toNat)
          (char_toNat_not_surrogate c),
        ih]
    show Except.ok (Char.ofNat c.toNat :: s) = Except.ok (c :: s)
    rw [Char.ofNat_toNat]

/-! ## escapeCp kit -/

theorem escapeCp_quote : escapeCp '"' = ['\\', '"'] := by decide

theorem escapeCp_backslash : escapeCp '\\' = ['\\', '\\'] := by decide

/-- Control code points (< 0x20) print as `\uXXXX`. -/
theorem escapeCp_control (c : Char) (h : c.toNat < 0x20) :
    escapeCp c = '\\' :: 'u' :: hex4 c.toNat := by
  have h1 : beqChar c '"' = false := by
    unfold beqChar
    have hq : '"'.toNat = 34 := rfl
    simp only [beq_eq_false_iff_ne]
    omega
  have h2 : beqChar c '\\' = false := by
    unfold beqChar
    have hb : '\\'.toNat = 92 := rfl
    simp only [beq_eq_false_iff_ne]
    omega
  have h3 : Nat.blt c.toNat 0x20 = true := by
    simp only [Nat.blt_eq]
    omega
  simp only [escapeCp, h1, h2, h3, Bool.false_eq_true, if_false, if_true]

/-- Non-quote, non-backslash, non-control code points print as themselves. -/
theorem escapeCp_plain (c : Char) (hq : beqChar c '"' = false)
    (hb : beqChar c '\\' = false) (h : 0x20 ≤ c.toNat) :
    escapeCp c = [c] := by
  have h3 : Nat.blt c.toNat 0x20 = false := by
    cases hlt : Nat.blt c.toNat 0x20
    · rfl
    · exfalso
      have hlt' : c.toNat < 0x20 := by simpa [Nat.blt_eq] using hlt
      omega
  simp only [escapeCp, hq, hb, h3, Bool.false_eq_true, if_false]

/-- Full case characterization of `escapeCp`, with the Bool guard facts J4
needs on each branch (in particular, the plain branch certifies that `c`
is not `'"'`, not `'\\'`, and `≥ 0x20`). -/
theorem escapeCp_cases (c : Char) :
    (beqChar c '"' = true ∧ escapeCp c = ['\\', '"']) ∨
    (beqChar c '"' = false ∧ beqChar c '\\' = true ∧
      escapeCp c = ['\\', '\\']) ∨
    (beqChar c '"' = false ∧ beqChar c '\\' = false ∧ c.toNat < 0x20 ∧
      escapeCp c = '\\' :: 'u' :: hex4 c.toNat) ∨
    (beqChar c '"' = false ∧ beqChar c '\\' = false ∧ 0x20 ≤ c.toNat ∧
      escapeCp c = [c]) := by
  cases hq : beqChar c '"' with
  | true =>
    have hc : c = '"' := eq_of_beqChar hq
    subst hc
    exact Or.inl ⟨rfl, escapeCp_quote⟩
  | false =>
    cases hb : beqChar c '\\' with
    | true =>
      have hc : c = '\\' := eq_of_beqChar hb
      subst hc
      exact Or.inr (Or.inl ⟨hq, rfl, escapeCp_backslash⟩)
    | false =>
      cases hlt : Nat.blt c.toNat 0x20 with
      | true =>
        have hlt' : c.toNat < 0x20 := by simpa [Nat.blt_eq] using hlt
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hlt', escapeCp_control c hlt'⟩))
      | false =>
        have hge : 0x20 ≤ c.toNat := by
          have hnot : ¬ c.toNat < 0x20 := by
            intro hc
            have : Nat.blt c.toNat 0x20 = true := by
              simp only [Nat.blt_eq]; omega
            rw [this] at hlt
            exact Bool.noConfusion hlt
          omega
        exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hge, escapeCp_plain c hq hb hge⟩))

theorem escChars_nil : escChars [] = [] := by simp only [escChars]

theorem escChars_cons (c : Char) (s : List Char) :
    escChars (c :: s) = escapeCp c ++ escChars s := by
  simp only [escChars]

/-- `escChars` is an append homomorphism. -/
theorem escChars_append (a b : List Char) :
    escChars (a ++ b) = escChars a ++ escChars b := by
  induction a with
  | nil => simp only [List.nil_append, escChars]
  | cons c a ih =>
    simp only [List.cons_append, escChars, ih, List.append_assoc]

/-! ## Digit-span kit -/

theorem wfDigits_ne_nil {cs : List Char} (h : wfDigits cs = true) : cs ≠ [] := by
  intro he
  rw [he] at h
  exact absurd h (by decide)

/-- `wfDigits` members are in the `digitP` range (`cs.all` Bool form). -/
theorem wfDigits_all {cs : List Char} (h : wfDigits cs = true) :
    cs.all (fun c => leChar '0' c && leChar c '9') = true := by
  unfold wfDigits at h
  rw [Bool.and_eq_true] at h
  exact h.2

/-- `wfDigits` members are in the `digitP` range (membership form). -/
theorem wfDigits_mem {cs : List Char} (h : wfDigits cs = true) :
    ∀ c ∈ cs, (leChar '0' c && leChar c '9') = true := by
  have hall := wfDigits_all h
  simp only [List.all_eq_true] at hall
  exact hall

/-- The head/tail split of a `wfDigits` span (the `digitP (star digitP)`
shape of rules 11 and 12). -/
theorem wfDigits_cons {cs : List Char} (h : wfDigits cs = true) :
    ∃ d ds, cs = d :: ds ∧ (leChar '0' d && leChar d '9') = true ∧
      ds.all (fun c => leChar '0' c && leChar c '9') = true := by
  cases cs with
  | nil => exact absurd h (by decide)
  | cons d ds =>
    have hall := wfDigits_all h
    rw [List.all_cons, Bool.and_eq_true] at hall
    exact ⟨d, ds, rfl, hall.1, hall.2⟩

theorem wfInt_ne_nil {cs : List Char} (h : wfInt cs = true) : cs ≠ [] := by
  intro he
  rw [he] at h
  exact absurd h (by decide)

/-- The rule-10 split: a well-formed `int` is `['0']` (first alternative)
or a `'1'..'9'` head with a digit tail (second alternative). -/
theorem wfInt_cases {cs : List Char} (h : wfInt cs = true) :
    cs = ['0'] ∨
    ∃ d ds, cs = d :: ds ∧ (leChar '1' d && leChar d '9') = true ∧
      ds.all (fun c => leChar '0' c && leChar c '9') = true := by
  cases cs with
  | nil => exact absurd h (by decide)
  | cons c rest =>
    rw [wfInt, Bool.or_eq_true] at h
    cases h with
    | inl h0 =>
      rw [Bool.and_eq_true] at h0
      obtain ⟨hz, he⟩ := h0
      have hc : c = '0' := eq_of_beqChar hz
      cases rest with
      | nil => exact Or.inl (by rw [hc])
      | cons x xs =>
        rw [List.isEmpty_cons] at he
        exact Bool.noConfusion he
    | inr h1 =>
      rw [Bool.and_eq_true] at h1
      exact Or.inr ⟨c, rest, rfl, h1.1, h1.2⟩

/-- Unpack `wfNumber` into the three per-field facts. -/
theorem wfNumber_spec {n : JNumber} (h : wfNumber n = true) :
    wfInt n.intPart = true ∧
    (n.fracPart = [] ∨ wfDigits n.fracPart = true) ∧
    (∀ e, n.expPart = some e → wfDigits e.digits = true) := by
  unfold wfNumber at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true] at h
  refine ⟨h.1.1, ?_, ?_⟩
  · rcases h.1.2 with hf | hf
    · left
      cases hfr : n.fracPart with
      | nil => rfl
      | cons x xs =>
        rw [hfr, List.isEmpty_cons] at hf
        exact Bool.noConfusion hf
    · right; exact hf
  · intro e he
    have h2 := h.2
    rw [he] at h2
    exact h2

/-! ## wfValue structure bridges -/

theorem wfValue_jnum {n : JNumber} (h : wfValue (.jnum n) = true) :
    wfNumber n = true := by
  rw [wfValue] at h
  exact h

theorem wfValue_jarr {vs : JArray} (h : wfValue (.jarr vs) = true) :
    wfArray vs = true := by
  rw [wfValue] at h
  exact h

theorem wfValue_jobj {ms : JMembers} (h : wfValue (.jobj ms) = true) :
    wfMembers ms = true := by
  rw [wfValue] at h
  exact h

theorem wfArray_cons {v : JValue} {rest : JArray}
    (h : wfArray (.cons v rest) = true) :
    wfValue v = true ∧ wfArray rest = true := by
  rw [wfArray, Bool.and_eq_true] at h
  exact h

theorem wfMembers_cons {k : List Char} {v : JValue} {rest : JMembers}
    (h : wfMembers (.cons k v rest) = true) :
    wfValue v = true ∧ wfMembers rest = true := by
  rw [wfMembers, Bool.and_eq_true] at h
  exact h

end Shallot.Json
