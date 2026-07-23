import MacroPeg.Semantics
import MacroPeg.Interp
import MacroPeg.Render

/-!
# Headline example: the copy language {ww | w ∈ {a,b}*}

`kmizu/macro_peg`'s README claims Macro PEG is strictly more expressive
than ordinary PEG because it can recognize non-context-free languages; the
library's own test suite (`NonTrivialLanguagesSpec.scala`) witnesses this
on a handful of concrete strings for the grammar

    S = Copy("") !.;
    Copy(w) = "a" Copy(w "a") / "b" Copy(w "b") / w;

Here we prove `copy_language_ww`: for EVERY `u : List Char` over `{a, b}`
(not just the witnesses the Scala test suite happens to enumerate),
`Copy([])` matches `u ++ u` exactly. This is the value formal verification
adds over a finite test suite: the same claim, but universally quantified.

## The accumulator is never literally a flat string

The natural induction is on `u`, generalizing the accumulator `w`. The
subtlety: `Copy`'s recursive call passes `w "a"` — in `MExp` terms
`.seq (.param 0) (.chr 'a')` — UNEVALUATED (this project formalizes
call-by-name macro semantics, see `MacroPeg/Semantics.lean`'s module
docstring). So after one recursive step the new activation's `.param 0` is
bound not to a flat `.lit`, but to a `.seq` node; after two steps, a
left-nested chain of `.seq`s; and so on. The induction therefore cannot be
stated over "the accumulator is `.lit w` for some `w`" — it needs an
argument-expression-agnostic invariant, `ExactMatch` below, characterizing
"behaves exactly like `.lit w`" without caring what the expression's syntax
actually is. The base case (`.lit w` itself) and the recursive step
(`.seq wexp (.chr c)` from `wexp`) both preserve this invariant, which is
what lets the induction go through despite the accumulator never
syntactically simplifying.
-/

namespace Shallot.MacroPeg

/-! ## Local Char/`stripPrefix?` kit (kept local rather than importing
`Shallot.Syntax.Lexemes`, which pulls in Shallot's own concrete language
grammar — unrelated to macro_peg; `MacroPeg` only ever depends on the
generic `Shallot.Peg.Syntax` char primitives). -/

theorem mEqOfBeqChar {a b : Char} (h : beqChar a b = true) : a = b := by
  unfold beqChar at h
  simp only [beq_iff_eq] at h
  exact Char.toNat_inj.mp h

theorem mBeqCharRefl (c : Char) : beqChar c c = true := by simp [beqChar]

theorem mBeqCharFalseOfNe {a b : Char} (h : a ≠ b) : beqChar a b = false := by
  cases hb : beqChar a b with
  | false => rfl
  | true => exact absurd (mEqOfBeqChar hb) h

theorem mStripPrefixAppend (s r : List Char) : stripPrefix? s (s ++ r) = some r := by
  induction s with
  | nil => rfl
  | cons c cs ih => simp [stripPrefix?, mBeqCharRefl, ih]

theorem mStripPrefixEqSome {s input rest : List Char} (h : stripPrefix? s input = some rest) :
    input = s ++ rest := by
  induction s generalizing input with
  | nil =>
    simp only [stripPrefix?] at h
    cases h
    rfl
  | cons c cs ih =>
    cases input with
    | nil => simp [stripPrefix?] at h
    | cons d ds =>
      simp only [stripPrefix?] at h
      split at h
      · rename_i hbeq
        have hcd : c = d := mEqOfBeqChar hbeq
        subst hcd
        have hind := ih h
        simp [hind]
      · exact absurd h (by simp)

theorem mStripPrefixNoneOfNotAppend {s input : List Char} (h : ∀ p, input ≠ s ++ p) :
    stripPrefix? s input = none := by
  cases hr : stripPrefix? s input with
  | none => rfl
  | some rest => exact absurd (mStripPrefixEqSome hr) (h rest)

/-! ## The Copy grammar -/

def copyIdx : Nat := 0

/-- `Copy(w) = "a" Copy(w "a") / "b" Copy(w "b") / w`. -/
def copyBody : MExp :=
  .alt (.seq (.chr 'a') (.call copyIdx [.seq (.param 0) (.chr 'a')]))
       (.alt (.seq (.chr 'b') (.call copyIdx [.seq (.param 0) (.chr 'b')]))
             (.param 0))

def copyGrammar : MGrammar := { rules := [{ arity := 1, body := copyBody }] }

theorem copyRule_lookup : ruleAtM copyGrammar.rules copyIdx = some { arity := 1, body := copyBody } :=
  rfl

/-! ## The `ExactMatch` invariant -/

/-- `wexp` behaves exactly like `.lit w`: succeeds on every `w ++ rest`
(consuming exactly `w`), and fails on every input NOT of the form `w ++ _`.
See the module docstring for why this abstraction (rather than "the
accumulator is `.lit w`") is what the induction needs. -/
structure ExactMatch (wexp : MExp) (w : List Char) : Prop where
  succ : ∀ rest, ∃ t, MDerives copyGrammar .callByName wexp (w ++ rest) (.ok t rest)
  fail : ∀ z, (∀ p, z ≠ w ++ p) → MDerives copyGrammar .callByName wexp z .fail

theorem exactMatch_lit (w : List Char) : ExactMatch (.lit w) w where
  succ := fun rest => ⟨.leaf w, MDerives.litOk w (w ++ rest) rest (mStripPrefixAppend w rest)⟩
  fail := fun z hz => MDerives.litFail w z (mStripPrefixNoneOfNotAppend hz)

/-- The step preserving `ExactMatch`: from `wexp` exactly-matching `w`,
`.seq wexp (.chr c)` exactly-matches `w ++ [c]`. This is the fact that lets
`copy_gen`'s induction cross a `Copy` recursive call without the
accumulator ever being flattened to a literal. -/
theorem exactMatch_step {wexp : MExp} {w : List Char} (hm : ExactMatch wexp w) (c : Char) :
    ExactMatch (.seq wexp (.chr c)) (w ++ [c]) where
  succ := fun rest => by
    obtain ⟨t1, h1⟩ := hm.succ (c :: rest)
    refine ⟨.seq t1 (.leaf [c]), ?_⟩
    have heq : w ++ [c] ++ rest = w ++ (c :: rest) := by simp
    rw [heq]
    exact MDerives.seqOk wexp (.chr c) (w ++ (c :: rest)) (c :: rest) rest t1 (.leaf [c])
      h1 (MDerives.chrOk c c rest (mBeqCharRefl c))
  fail := fun z hz => by
    by_cases hw : ∃ p, z = w ++ p
    · obtain ⟨p, hp⟩ := hw
      obtain ⟨t1, h1⟩ := hm.succ p
      rw [← hp] at h1
      cases p with
      | nil =>
        exact MDerives.seqFail₂ wexp (.chr c) z [] t1 h1 (MDerives.chrEmpty c)
      | cons d ps =>
        have hdc : d ≠ c := by
          intro hdc
          subst hdc
          exact hz ps (by simp [hp])
        exact MDerives.seqFail₂ wexp (.chr c) z (d :: ps) t1 h1
          (MDerives.chrFail c d ps (mBeqCharFalseOfNe (Ne.symm hdc)))
    · exact MDerives.seqFail₁ wexp (.chr c) z (hm.fail z (fun p hp => hw ⟨p, hp⟩))

/-- `Copy(wexp)` (for any `wexp` exactly-matching `w`) FAILS on every input
strictly shorter than `w`. Such an input is too short for the third
alternative (`wexp`, which needs all of `w`) and, after consuming a leading
`a`/`b`, still too short for the recursive call on the grown accumulator
(`exactMatch_step`). This is the failure companion `copy_gen`'s base case
needs: to pick the third alternative, the two "grow" alternatives must fail,
and each grow alternative's tail is a `Copy` CALL on a strictly-longer
accumulator applied to an input of length `|w| - 1 < |w ++ [c]|`. -/
theorem copy_fail_short {wexp : MExp} {w : List Char} (hm : ExactMatch wexp w) :
    ∀ z : List Char, z.length < w.length →
      MDerives copyGrammar .callByName (.call copyIdx [wexp]) z .fail := by
  intro z
  induction z generalizing wexp w with
  | nil =>
    intro hlen
    have hne : ∀ p, ([] : List Char) ≠ w ++ p := by
      intro p hp
      have hc := congrArg List.length hp
      simp only [List.length_append, List.length_nil] at hc
      have hwpos : 0 < w.length := hlen
      omega
    have hC : MDerives copyGrammar .callByName wexp [] .fail := hm.fail [] hne
    have hA : MDerives copyGrammar .callByName (.seq (.chr 'a') (.call copyIdx [.seq wexp (.chr 'a')])) [] .fail :=
      MDerives.seqFail₁ (.chr 'a') (.call copyIdx [.seq wexp (.chr 'a')]) [] (MDerives.chrEmpty 'a')
    have hB : MDerives copyGrammar .callByName (.seq (.chr 'b') (.call copyIdx [.seq wexp (.chr 'b')])) [] .fail :=
      MDerives.seqFail₁ (.chr 'b') (.call copyIdx [.seq wexp (.chr 'b')]) [] (MDerives.chrEmpty 'b')
    have hbody : MDerives copyGrammar .callByName (MExp.subst [wexp] copyBody) [] .fail :=
      MDerives.altFail _ _ [] hA (MDerives.altFail _ _ [] hB hC)
    exact MDerives.callNameFail copyIdx [wexp] { arity := 1, body := copyBody } []
      rfl copyRule_lookup rfl hbody
  | cons d z' ih =>
    intro hlen
    have hne : ∀ p, (d :: z') ≠ w ++ p := by
      intro p hp
      have hc := congrArg List.length hp
      simp only [List.length_append, List.length_cons] at hc
      simp only [List.length_cons] at hlen
      omega
    have hC : MDerives copyGrammar .callByName wexp (d :: z') .fail := hm.fail (d :: z') hne
    have hA : MDerives copyGrammar .callByName (.seq (.chr 'a') (.call copyIdx [.seq wexp (.chr 'a')])) (d :: z') .fail := by
      by_cases hda : d = 'a'
      · subst hda
        have hlz : z'.length < (w ++ ['a']).length := by
          simp only [List.length_cons] at hlen
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        have hcall := ih (exactMatch_step hm 'a') hlz
        exact MDerives.seqFail₂ (.chr 'a') (.call copyIdx [.seq wexp (.chr 'a')]) ('a' :: z') z'
          (.leaf ['a']) (MDerives.chrOk 'a' 'a' z' (mBeqCharRefl 'a')) hcall
      · exact MDerives.seqFail₁ (.chr 'a') (.call copyIdx [.seq wexp (.chr 'a')]) (d :: z')
          (MDerives.chrFail 'a' d z' (mBeqCharFalseOfNe (Ne.symm hda)))
    have hB : MDerives copyGrammar .callByName (.seq (.chr 'b') (.call copyIdx [.seq wexp (.chr 'b')])) (d :: z') .fail := by
      by_cases hdb : d = 'b'
      · subst hdb
        have hlz : z'.length < (w ++ ['b']).length := by
          simp only [List.length_cons] at hlen
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        have hcall := ih (exactMatch_step hm 'b') hlz
        exact MDerives.seqFail₂ (.chr 'b') (.call copyIdx [.seq wexp (.chr 'b')]) ('b' :: z') z'
          (.leaf ['b']) (MDerives.chrOk 'b' 'b' z' (mBeqCharRefl 'b')) hcall
      · exact MDerives.seqFail₁ (.chr 'b') (.call copyIdx [.seq wexp (.chr 'b')]) (d :: z')
          (MDerives.chrFail 'b' d z' (mBeqCharFalseOfNe (Ne.symm hdb)))
    have hbody : MDerives copyGrammar .callByName (MExp.subst [wexp] copyBody) (d :: z') .fail :=
      MDerives.altFail _ _ (d :: z') hA (MDerives.altFail _ _ (d :: z') hB hC)
    exact MDerives.callNameFail copyIdx [wexp] { arity := 1, body := copyBody } (d :: z')
      rfl copyRule_lookup rfl hbody

/-! ## The headline theorem -/

/-- `Copy(w)` (via any expression `wexp` exactly-matching `w`) matches
`u ++ w ++ u` for EVERY `u`, generalizing the accumulator via `ExactMatch`.
Induction on `u`: the base case picks the third alternative (`wexp` itself,
via `hm.succ`), after showing the two "grow" alternatives fail because
`.chr 'a'`/`.chr 'b'` followed by a call on a strictly-longer accumulator
can never succeed on an input of exactly `wexp`'s own length (`hm.fail`
applied to the tail, using `exactMatch_step`/`ExactMatch` of the grown
accumulator); the step case consumes one character via `chrOk` and applies
the IH with `w ++ [c]` / `exactMatch_step hm c`. -/
theorem copy_gen {wexp : MExp} {w : List Char} (hm : ExactMatch wexp w) :
    ∀ u : List Char, (∀ c ∈ u, c = 'a' ∨ c = 'b') →
      ∃ t, MDerives copyGrammar .callByName (.call copyIdx [wexp]) (u ++ w ++ u) (.ok t []) := by
  intro u
  induction u generalizing wexp w with
  | nil =>
    intro _hu
    simp only [List.nil_append, List.append_nil]
    have hgrowA : MDerives copyGrammar .callByName (.seq (.chr 'a') (.call copyIdx [.seq wexp (.chr 'a')])) w .fail := by
      by_cases hstarts : ∃ p, w = 'a' :: p
      · obtain ⟨p, hp⟩ := hstarts
        have h1 : MDerives copyGrammar .callByName (.chr 'a') w (.ok (.leaf ['a']) p) := by
          rw [hp]; exact MDerives.chrOk 'a' 'a' p (mBeqCharRefl 'a')
        have hlen : p.length < (w ++ ['a']).length := by
          have hw : w.length = p.length + 1 := by rw [hp]; simp
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        have h2 := copy_fail_short (exactMatch_step hm 'a') p hlen
        exact MDerives.seqFail₂ (.chr 'a') (.call copyIdx [.seq wexp (.chr 'a')]) w p (.leaf ['a']) h1 h2
      · have hstarts' : ∀ p, w ≠ 'a' :: p := fun p hp => hstarts ⟨p, hp⟩
        have hfail : MDerives copyGrammar .callByName (.chr 'a') w .fail := by
          cases w with
          | nil => exact MDerives.chrEmpty 'a'
          | cons d ds =>
            have hda : d ≠ 'a' := fun hda => hstarts' ds (by rw [hda])
            exact MDerives.chrFail 'a' d ds (mBeqCharFalseOfNe (Ne.symm hda))
        exact MDerives.seqFail₁ (.chr 'a') (.call copyIdx [.seq wexp (.chr 'a')]) w hfail
    have hgrowB : MDerives copyGrammar .callByName (.seq (.chr 'b') (.call copyIdx [.seq wexp (.chr 'b')])) w .fail := by
      by_cases hstarts : ∃ p, w = 'b' :: p
      · obtain ⟨p, hp⟩ := hstarts
        have h1 : MDerives copyGrammar .callByName (.chr 'b') w (.ok (.leaf ['b']) p) := by
          rw [hp]; exact MDerives.chrOk 'b' 'b' p (mBeqCharRefl 'b')
        have hlen : p.length < (w ++ ['b']).length := by
          have hw : w.length = p.length + 1 := by rw [hp]; simp
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        have h2 := copy_fail_short (exactMatch_step hm 'b') p hlen
        exact MDerives.seqFail₂ (.chr 'b') (.call copyIdx [.seq wexp (.chr 'b')]) w p (.leaf ['b']) h1 h2
      · have hstarts' : ∀ p, w ≠ 'b' :: p := fun p hp => hstarts ⟨p, hp⟩
        have hfail : MDerives copyGrammar .callByName (.chr 'b') w .fail := by
          cases w with
          | nil => exact MDerives.chrEmpty 'b'
          | cons d ds =>
            have hdb : d ≠ 'b' := fun hdb => hstarts' ds (by rw [hdb])
            exact MDerives.chrFail 'b' d ds (mBeqCharFalseOfNe (Ne.symm hdb))
        exact MDerives.seqFail₁ (.chr 'b') (.call copyIdx [.seq wexp (.chr 'b')]) w hfail
    obtain ⟨t3, h3⟩ := hm.succ []
    simp only [List.append_nil] at h3
    have hbody : MDerives copyGrammar .callByName (MExp.subst [wexp] copyBody) w (.ok (.choiceR (.choiceR t3)) []) :=
      MDerives.altR _ _ w [] _ hgrowA
        (MDerives.altR _ _ w [] _ hgrowB h3)
    exact ⟨.nodeCall copyIdx (.choiceR (.choiceR t3)), MDerives.callNameOk copyIdx [wexp]
      { arity := 1, body := copyBody } w [] _ rfl copyRule_lookup rfl hbody⟩
  | cons c u' ih =>
    intro hu
    have hc : c = 'a' ∨ c = 'b' := hu c (List.mem_cons.mpr (Or.inl rfl))
    have hu' : ∀ x ∈ u', x = 'a' ∨ x = 'b' := fun x hx => hu x (List.mem_cons.mpr (Or.inr hx))
    rcases hc with hca | hcb
    · subst hca
      have hstep := ih (exactMatch_step hm 'a') hu'
      have heq : (u' ++ (w ++ ['a']) ++ u') = u' ++ w ++ ('a' :: u') := by simp
      rw [heq] at hstep
      obtain ⟨t, ht⟩ := hstep
      -- ht : the recursive call matches the remaining input `u' ++ w ++ ('a' :: u')`
      have hbody : MDerives copyGrammar .callByName (MExp.subst [wexp] copyBody)
          (('a' :: u') ++ w ++ ('a' :: u'))
          (.ok (.choiceL (.seq (.leaf ['a']) t)) []) := by
        apply MDerives.altL
        exact MDerives.seqOk (.chr 'a') (.call copyIdx [.seq wexp (.chr 'a')])
          (('a' :: u') ++ w ++ ('a' :: u')) (u' ++ w ++ ('a' :: u')) [] (.leaf ['a']) t
          (MDerives.chrOk 'a' 'a' (u' ++ w ++ ('a' :: u')) (mBeqCharRefl 'a')) ht
      exact ⟨.nodeCall copyIdx (.choiceL (.seq (.leaf ['a']) t)),
        MDerives.callNameOk copyIdx [wexp] { arity := 1, body := copyBody }
          (('a' :: u') ++ w ++ ('a' :: u')) [] _ rfl copyRule_lookup rfl hbody⟩
    · subst hcb
      have hstep := ih (exactMatch_step hm 'b') hu'
      have heq : (u' ++ (w ++ ['b']) ++ u') = u' ++ w ++ ('b' :: u') := by simp
      rw [heq] at hstep
      obtain ⟨t, ht⟩ := hstep
      have hbody : MDerives copyGrammar .callByName (MExp.subst [wexp] copyBody)
          (('b' :: u') ++ w ++ ('b' :: u'))
          (.ok (.choiceR (.choiceL (.seq (.leaf ['b']) t))) []) := by
        apply MDerives.altR
        · -- the "a" alternative fails on an input starting with 'b'
          exact MDerives.seqFail₁ (.chr 'a') (.call copyIdx [.seq wexp (.chr 'a')])
            (('b' :: u') ++ w ++ ('b' :: u'))
            (MDerives.chrFail 'a' 'b' (u' ++ w ++ ('b' :: u'))
              (mBeqCharFalseOfNe (by decide : ('a' : Char) ≠ 'b')))
        · apply MDerives.altL
          exact MDerives.seqOk (.chr 'b') (.call copyIdx [.seq wexp (.chr 'b')])
            (('b' :: u') ++ w ++ ('b' :: u')) (u' ++ w ++ ('b' :: u')) [] (.leaf ['b']) t
            (MDerives.chrOk 'b' 'b' (u' ++ w ++ ('b' :: u')) (mBeqCharRefl 'b')) ht
      exact ⟨.nodeCall copyIdx (.choiceR (.choiceL (.seq (.leaf ['b']) t))),
        MDerives.callNameOk copyIdx [wexp] { arity := 1, body := copyBody }
          (('b' :: u') ++ w ++ ('b' :: u')) [] _ rfl copyRule_lookup rfl hbody⟩

/-- **Headline theorem**: `Copy("")` matches `u ++ u` for EVERY `u ∈ {a,b}*`
— the copy language `{ww}`, a textbook non-context-free language, matched
by a Macro PEG grammar. A finite Scala test suite
(`NonTrivialLanguagesSpec.scala`) can only ever check finitely many `u`;
this is the same claim for all of them at once. -/
theorem copy_language_ww (u : List Char) (hu : ∀ c ∈ u, c = 'a' ∨ c = 'b') :
    ∃ t, MDerives copyGrammar .callByName (.call copyIdx [.lit []]) (u ++ u) (.ok t []) := by
  have := copy_gen (exactMatch_lit []) u hu
  simpa using this

/-! ## `CallByValuePar` smoke tests

Not a headline theorem (out of scope for this milestone, per
`docs/roadmap.md`) — just computed confirmation, via the `#guard`
convention already used elsewhere in this project (e.g. `Json/Grammar.lean`),
that the `.callByValuePar` semantics added in `MacroPeg/Semantics.lean`/
`Interp.lean` actually behave as `MacroPegCallByValueParSpec.scala`
describes: `F(A) = A A A` applied to `"a"`, evaluated under
`.callByValuePar`, extracts `A`'s VALUE (the substring `"a"` consumed by
matching `.lit ['a']` against the ORIGINAL, unadvanced input) and splices
it in three times, matching `"aaa"` in full. -/

def parFIdx : Nat := 0

/-- `F(A) = A A A`. -/
def parFBody : MExp := .seq (.param 0) (.seq (.param 0) (.param 0))

def parFGrammar : MGrammar := { rules := [{ arity := 1, body := parFBody }] }

#guard renderMPeg (mpegRun parFGrammar .callByValuePar 200 (.call parFIdx [.lit ['a']]) "aaa".toList) == "ok+0"

#guard renderMPeg (mpegRun parFGrammar .callByValuePar 200 (.call parFIdx [.lit ['a']]) "aab".toList) == "fail"

/-! Too short: evaluating the argument against `"aa"` still only extracts a
single `"a"` (the argument itself doesn't see or care about the rest of the
body), so the body's three-fold repetition of that same value needs `"aaa"`
— `"aa"` alone is insufficient. -/
#guard renderMPeg (mpegRun parFGrammar .callByValuePar 200 (.call parFIdx [.lit ['a']]) "aa".toList) == "fail"

/-! ## `CallByValueSeq` smoke tests

Same discipline as the `CallByValuePar` block above — computed confirmation
via `#guard`, not a headline theorem. Mirrors
`MacroPegCallByValueSeqSpec.scala`'s `"simple"` example: `F(A, B, C) =
"abc"; S = F("a", "b", "c");` on `"abcabc"`. Under `.callByValueSeq` the
three actual parameters are evaluated IN SEQUENCE, each against whatever
input the previous one left off at — `"a"` against `"abcabc"` (leaving
`"bcabc"`), `"b"` against `"bcabc"` (leaving `"cabc"`), `"c"` against
`"cabc"` (leaving `"abc"`) — and only THEN is the body `A B C` (= `"abc"`
once substituted) derived, starting from that final threaded position
`"abc"`, matching it exactly. Contrast with `CallByValuePar`'s `parFGrammar`
above, where the body always starts back at the ORIGINAL input. -/

def seqFIdx : Nat := 0

/-- `F(A, B, C) = A B C`. -/
def seqFBody : MExp := .seq (.param 0) (.seq (.param 1) (.param 2))

def seqFGrammar : MGrammar := { rules := [{ arity := 3, body := seqFBody }] }

#guard renderMPeg
  (mpegRun seqFGrammar .callByValueSeq 200
    (.call seqFIdx [.lit ['a'], .lit ['b'], .lit ['c']]) "abcabc".toList) == "ok+0"

/-! Wrong last character: the first two arguments still thread through `"a"`
then `"b"` exactly as above, leaving `"cabx"`; the THIRD argument `"c"` is
evaluated against that (still matches, `"c"` is a prefix of `"cabx"`,
leaving `"abx"`) — so argument evaluation itself does not notice the flaw at
all, it only surfaces once the body `"abc"` is matched against the final
threaded position `"abx"` and fails on the last character. -/
#guard renderMPeg
  (mpegRun seqFGrammar .callByValueSeq 200
    (.call seqFIdx [.lit ['a'], .lit ['b'], .lit ['c']]) "abcabx".toList) == "fail"

/-! Too short: after threading through all three arguments (leaving `""`),
the body `"abc"` has nothing left to match. -/
#guard renderMPeg
  (mpegRun seqFGrammar .callByValueSeq 200
    (.call seqFIdx [.lit ['a'], .lit ['b'], .lit ['c']]) "abc".toList) == "fail"

/-! ## Higher-order (M-PEG-4) smoke tests

Same discipline as the Par/Seq blocks above — computed confirmation via
`#guard`, not a headline theorem (the closure-return-and-apply-elsewhere
case remains out of scope; see `MacroPeg/Syntax.lean`'s module docstring).
There is no surface `.peg` parser in this project, so "pass a named rule as
a callable value" and "pass a lambda literal" both elaborate to the exact
same `.lam arity body` shape — a caller wanting to reference a named rule
`R` as a value just writes `.lam R.arity R.body` directly, exactly as a
lambda literal would. The two examples below exercise that unification from
both ends. -/

/-- Mirrors `HigherOrderEvalSpec.scala`'s "evaluates nested macro
application": `S = Double(Plus1, "aa") !.; Plus1(s: ?) = s s; Double(f: ?,
s: ?) = f(f(s));`. `Plus1` is passed as a value — here written directly as
the `.lam` wrapping its (arity, body) rather than through a name, since
there is no separate name resolution step in this project's AST. `Double`'s
body applies its callable parameter `f` to `f(s)` — TWO nested `.callParam`
uses, exercising `.invoke` invoking an argument that is itself an
unevaluated `.invoke` (call-by-name: nothing forces the inner one before
the outer one needs it). -/
def plus1Body : MExp := .seq (.param 0) (.param 0)

def doubleHofIdx : Nat := 0

/-- `Double(f: ?, s: ?) = f(f(s))`, i.e. `callParam 0 [callParam 0 [param 1]]`. -/
def doubleHofBody : MExp := .callParam 0 [.callParam 0 [.param 1]]

def doubleHofGrammar : MGrammar := { rules := [{ arity := 2, body := doubleHofBody }] }

/-! `Double(Plus1, "aa")` — doubling twice, "aa" -> "aaaa" -> "aaaaaaaa". -/
#guard renderMPeg
  (mpegRun doubleHofGrammar .callByName 200
    (.call doubleHofIdx [.lam 1 plus1Body, .lit ['a', 'a']]) "aaaaaaaa".toList) == "ok+0"

/-! Only one doubling's worth of input: the SECOND `f` application has
nothing left after the first consumes all four characters. -/
#guard renderMPeg
  (mpegRun doubleHofGrammar .callByName 200
    (.call doubleHofIdx [.lam 1 plus1Body, .lit ['a', 'a']]) "aaaa".toList) == "fail"

/-- Mirrors `HigherOrderAdvancedSpec.scala`'s "uses higher-order functions
with multiple parameters": `Map2(f: ?, x: ?, y: ?) = f(x, y); S =
Map2((x, y -> x y x), "a", "b") !.;`. Exercises a LAMBDA LITERAL (not a
named-rule reference) of arity 2 — checks `.invoke`'s multi-argument
substitution, not just the single-argument shape `plus1Body` above uses. -/
def xyxBody : MExp := .seq (.param 0) (.seq (.param 1) (.param 0))

def map2Idx : Nat := 0

/-- `Map2(f: ?, x: ?, y: ?) = f(x, y)`, i.e. `callParam 0 [param 1, param 2]`. -/
def map2Body : MExp := .callParam 0 [.param 1, .param 2]

def map2Grammar : MGrammar := { rules := [{ arity := 3, body := map2Body }] }

/-! `Map2((x,y -> x y x), "a", "b")` matches `"a" ++ "b" ++ "a"` = `"aba"`. -/
#guard renderMPeg
  (mpegRun map2Grammar .callByName 200
    (.call map2Idx [.lam 2 xyxBody, .lit ['a'], .lit ['b']]) "aba".toList) == "ok+0"

/-! Wrong last character. -/
#guard renderMPeg
  (mpegRun map2Grammar .callByName 200
    (.call map2Idx [.lam 2 xyxBody, .lit ['a'], .lit ['b']]) "abx".toList) == "fail"

/-! Too short. -/
#guard renderMPeg
  (mpegRun map2Grammar .callByName 200
    (.call map2Idx [.lam 2 xyxBody, .lit ['a'], .lit ['b']]) "ab".toList) == "fail"

end Shallot.MacroPeg
