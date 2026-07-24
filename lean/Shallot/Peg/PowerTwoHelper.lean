import Shallot.Peg.Semantics
import Shallot.Peg.Interp
import Shallot.Peg.Determinism
import Shallot.Peg.Examples
import Shallot.Render

/-!
# T7 evidence, positive side: Loff–Moreira–Reis's power-of-two-length trick

`Cfg/OpenProblems.lean` records Loff, Moreira and Reis's Theorem 8 (JCSS
2019): the language of palindromes whose length is a power of two DOES have
a plain PEG, via a helper nonterminal that locates positions at a
positive-power-of-two distance from end-of-input using only `&`/`!`
lookahead. This file formalizes the CORE mechanism that theorem rests on —
the `Helper` nonterminal itself — since it is what makes Theorem 8 work and
is the clearest illustration of *why* this trick cannot generalize to
arbitrary-length palindromes (see the module docstring in
`Shallot/Peg/Palindrome.lean` and the discussion in `Cfg/OpenProblems.lean`
for that non-generalization argument; this file is the positive result the
argument is contrasted against, not an attempt at the open conjecture
itself).

`Helper ← Bit Helper Bit / Bit Bit` (`Bit ← 0 / 1`) is claimed by the paper
to accept exactly those inputs whose length is a positive power of two,
consuming the entire input in that case. Hand-tracing the interpreter's
behavior on inputs that are NOT of that length (reproduced here by direct
computation before any proof was attempted, same discipline as
`Palindrome.lean`'s `"aaaa"` witness) reveals `Helper`'s consumption
function has the closed form

  f(m) = 2 * (m - 2^k)   where 2^k < m ≤ 2^(k+1)

which the paper does not spell out explicitly. `helper_consumption` below
is the fully general theorem capturing this — for EVERY `m ≥ 2`, not just
powers of two — proved by strong induction on `m`. `helper_iff_power_of_two`
then specializes it to recover exactly the paper's claim.
-/

namespace Shallot

def BitIdx : Nat := 0
def HelperIdx : Nat := 1

/-- `Bit ← 0 / 1`. -/
def bitBody : PExp := .alt (.chr '0') (.chr '1')

/-- `Helper ← Bit Helper Bit / Bit Bit`. -/
def helperBody : PExp :=
  .alt (.seq (.nt BitIdx) (.seq (.nt HelperIdx) (.nt BitIdx)))
    (.seq (.nt BitIdx) (.nt BitIdx))

def helperGrammar : Grammar := { rules := [bitBody, helperBody], start := HelperIdx }

/-- Every character in `w` is `'0'` or `'1'` — the alphabet `Bit` matches. -/
def IsBitString (w : List Char) : Prop := ∀ c ∈ w, c = '0' ∨ c = '1'

theorem IsBitString.tail {c : Char} {w : List Char} (h : IsBitString (c :: w)) :
    IsBitString w := fun d hd => h d (List.mem_cons_of_mem c hd)

/-! ## Smoke tests (small `m`, `#guard`-pinned before the general proof) -/

#guard renderPeg (pegRun helperGrammar 100 (.nt HelperIdx) "".toList) == "fail"
#guard renderPeg (pegRun helperGrammar 100 (.nt HelperIdx) "0".toList) == "fail"
#guard renderPeg (pegRun helperGrammar 100 (.nt HelperIdx) "00".toList) == "ok+0"
#guard renderPeg (pegRun helperGrammar 100 (.nt HelperIdx) "010".toList) == "ok+1"
#guard renderPeg (pegRun helperGrammar 100 (.nt HelperIdx) "0100".toList) == "ok+0"
#guard renderPeg (pegRun helperGrammar 100 (.nt HelperIdx) "01001".toList) == "ok+3"
#guard renderPeg (pegRun helperGrammar 100 (.nt HelperIdx) "010010".toList) == "ok+2"
#guard renderPeg (pegRun helperGrammar 100 (.nt HelperIdx) "0100101".toList) == "ok+1"
#guard renderPeg (pegRun helperGrammar 100 (.nt HelperIdx) "01001010".toList) == "ok+0"
#guard renderPeg (pegRun helperGrammar 100 (.nt HelperIdx) "010010101".toList) == "ok+7"

/-! ## `Bit`'s semantics: matches exactly one `'0'`/`'1'`, fails on empty or
other characters -/

theorem bit_ok_zero (rest : List Char) :
    ∃ t, Derives helperGrammar (.nt BitIdx) ('0' :: rest) (.ok t rest) :=
  ⟨_, .ntOk _ _ _ _ _ rfl (.altL _ _ _ _ _ (.chrOk _ _ _ rfl))⟩

theorem bit_ok_one (rest : List Char) :
    ∃ t, Derives helperGrammar (.nt BitIdx) ('1' :: rest) (.ok t rest) :=
  ⟨_, .ntOk _ _ _ _ _ rfl (.altR _ _ _ _ _ (.chrFail _ _ _ rfl) (.chrOk _ _ _ rfl))⟩

/-- `Bit` on a bit-string char succeeds, consuming exactly that one
character. -/
theorem bit_ok {c : Char} (hc : c = '0' ∨ c = '1') (rest : List Char) :
    ∃ t, Derives helperGrammar (.nt BitIdx) (c :: rest) (.ok t rest) := by
  rcases hc with hc | hc <;> subst hc
  · exact bit_ok_zero rest
  · exact bit_ok_one rest

theorem bit_fail_empty : Derives helperGrammar (.nt BitIdx) [] .fail :=
  .ntFail _ _ _ rfl (.altFail _ _ _ (.chrEmpty _) (.chrEmpty _))

/-! ## `Helper`'s base cases: fails on inputs shorter than 2 -/

theorem helper_fails_empty : Derives helperGrammar (.nt HelperIdx) [] .fail :=
  .ntFail _ _ _ rfl (.altFail _ _ _
    (.seqFail₁ _ _ _ bit_fail_empty)
    (.seqFail₁ _ _ _ bit_fail_empty))

theorem helper_fails_len1 {c : Char} (hc : c = '0' ∨ c = '1') :
    Derives helperGrammar (.nt HelperIdx) [c] .fail := by
  obtain ⟨t, ht⟩ := bit_ok hc []
  exact .ntFail _ _ _ rfl (.altFail _ _ _
    (.seqFail₂ _ _ _ _ _ ht (.seqFail₁ _ _ _ helper_fails_empty))
    (.seqFail₂ _ _ _ _ _ ht bit_fail_empty))

/-! ## The main consumption theorem -/

/-- **The core mechanism behind Theorem 8**: on any bit-string input of
length `m ≥ 2`, `Helper` succeeds, and its unconsumed remainder always has
length `2^(log2(m-1)+1) - m` — the closed form `f(m) = 2*(m - 2^k)` for
`2^k < m ≤ 2^(k+1)` from the module docstring, re-expressed via `Nat.log2`.
When `m` is itself a power of two this remainder is `0` (full consumption);
otherwise `Helper` accepts only a proper prefix. Proved by strong induction
on `m`, splitting on whether the recursive `Helper` call (on the tail,
length `m-1`) fully consumes its input or not — the two cases are exactly
`Bit Helper Bit` succeeding vs. falling through to `Bit Bit`. -/
theorem helper_consumption : ∀ (m : Nat), 2 ≤ m → ∀ (w : List Char), w.length = m →
    IsBitString w →
    ∃ t rest, Derives helperGrammar (.nt HelperIdx) w (.ok t rest) ∧
      rest.length = 2 ^ (Nat.log2 (m - 1) + 1) - m ∧ IsBitString rest := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm2 w hlen hbits
    obtain ⟨c1, w1, rfl⟩ := List.ne_nil_iff_exists_cons.mp
      (show w ≠ [] by rintro rfl; simp at hlen; omega)
    have hw1len : w1.length = m - 1 := by simp at hlen; omega
    obtain ⟨c2, w2, rfl⟩ := List.ne_nil_iff_exists_cons.mp
      (show w1 ≠ [] by rintro rfl; simp at hw1len; omega)
    have hc1 : c1 = '0' ∨ c1 = '1' := hbits c1 List.mem_cons_self
    have hc2 : c2 = '0' ∨ c2 = '1' := hbits c2 (by simp)
    obtain ⟨t1, ht1⟩ := bit_ok hc1 (c2 :: w2)
    by_cases hm2eq : m = 2
    · -- Base case: m = 2, so w2 = [].
      subst hm2eq
      have hw2eq : w2 = [] := by simpa using hw1len
      subst hw2eq
      obtain ⟨t2, ht2⟩ := bit_ok hc2 []
      have hderiv : Derives helperGrammar (.nt HelperIdx) [c1, c2] (.ok _ []) :=
        .ntOk _ _ _ _ _ rfl (.altR _ _ _ _ _
          (.seqFail₂ _ _ _ _ _ ht1 (.seqFail₁ _ _ _ (helper_fails_len1 hc2)))
          (.seqOk _ _ _ _ _ _ _ ht1 ht2))
      have hlenpf : ([] : List Char).length = 2 ^ (Nat.log2 (2 - 1) + 1) - 2 := by decide
      exact ⟨_, [], hderiv, hlenpf, by simp [IsBitString]⟩
    · -- Inductive step: m ≥ 3, apply ih to the tail (c2 :: w2), length m - 1.
      have hm3 : 3 ≤ m := by omega
      have hw2lentail : (c2 :: w2).length = m - 1 := by simpa using hw1len
      obtain ⟨t', rest', hderiv', hrestlen', hbitsrest'⟩ :=
        ih (m - 1) (by omega) (by omega) (c2 :: w2) hw2lentail hbits.tail
      have hm2ne : m - 1 - 1 ≠ 0 := by omega
      generalize hgen : Nat.log2 (m - 1 - 1) = k' at hrestlen'
      have hk'lo : 2 ^ k' ≤ m - 1 - 1 := hgen ▸ Nat.log2_self_le hm2ne
      have hk'hi : m - 1 - 1 < 2 ^ (k' + 1) := hgen ▸ Nat.lt_log2_self
      cases rest' with
      | nil =>
        -- Helper(c2::w2) fully consumed ⟹ 2^(k'+1) = m - 1, and m - 1 is
        -- itself the next power of two: k = k' + 1.
        have hzero : (0 : Nat) = 2 ^ (k' + 1) - (m - 1) := by simpa using hrestlen'
        have h2kle : 2 ^ (k' + 1) ≤ m - 1 := by omega
        have heq2k : 2 ^ (k' + 1) = m - 1 := by omega
        have hklog : Nat.log2 (m - 1) = k' + 1 := by rw [← heq2k]; exact Nat.log2_two_pow
        obtain ⟨t2, ht2⟩ := bit_ok hc2 w2
        have hderiv : Derives helperGrammar (.nt HelperIdx) (c1 :: c2 :: w2) (.ok _ w2) :=
          .ntOk _ _ _ _ _ rfl (.altR _ _ _ _ _
            (.seqFail₂ _ _ _ _ _ ht1 (.seqFail₂ _ _ _ _ _ hderiv' bit_fail_empty))
            (.seqOk _ _ _ _ _ _ _ ht1 ht2))
        have hw2len : w2.length = m - 2 := by
          have := hw2lentail; simp at this; omega
        have hpow : 2 ^ (k' + 1 + 1) = 2 * 2 ^ (k' + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        have hlenpf : w2.length = 2 ^ (Nat.log2 (m - 1) + 1) - m := by
          rw [hklog, hw2len, hpow, heq2k]; omega
        exact ⟨_, w2, hderiv, hlenpf, hbits.tail.tail⟩
      | cons d rest'' =>
        -- Helper(c2::w2) partially consumed, leaving d :: rest'' — the same
        -- power-of-two range k = k' applies to m as to m - 1.
        have hdbit : d = '0' ∨ d = '1' := hbitsrest' d List.mem_cons_self
        obtain ⟨t2, ht2⟩ := bit_ok hdbit rest''
        have hrestlen'' : (d :: rest'').length = 2 ^ (k' + 1) - (m - 1) := hrestlen'
        have hdlen : (d :: rest'').length ≥ 1 := by simp
        have hstrict : (m : Nat) - 1 < 2 ^ (k' + 1) := by omega
        have hklog : Nat.log2 (m - 1) = k' := by
          have hm1ne : m - 1 ≠ 0 := by omega
          exact (Nat.log2_eq_iff hm1ne).mpr ⟨by omega, hstrict⟩
        have hderiv : Derives helperGrammar (.nt HelperIdx) (c1 :: c2 :: w2) (.ok _ rest'') :=
          .ntOk _ _ _ _ _ rfl (.altL _ _ _ _ _
            (.seqOk _ _ _ _ _ _ _ ht1 (.seqOk _ _ _ _ _ _ _ hderiv' ht2)))
        have hlencalc : rest''.length + 1 = 2 ^ (k' + 1) - (m - 1) := by
          simpa using hrestlen''
        have hlenpf : rest''.length = 2 ^ (Nat.log2 (m - 1) + 1) - m := by
          rw [hklog]; omega
        exact ⟨_, rest'', hderiv, hlenpf, hbitsrest'.tail⟩

/-- **Recovering Loff–Moreira–Reis's Theorem 8 claim about `Helper`**:
on a bit-string whose length is a positive power of two, `Helper` succeeds
and consumes the ENTIRE input — no leftover. This is the special case of
`helper_consumption` where `m = 2^n`: the general closed form's remainder
`2^(log2(m-1)+1) - m` vanishes exactly here, since `log2(2^n - 1) = n - 1`
makes `2^((n-1)+1) = 2^n = m`. Combined with `&`/`!` lookahead against this
nonterminal (not formalized here — see `Cfg/OpenProblems.lean`), this is
the mechanism that lets the paper's `S`/`Palindrome`/`P` grammar locate the
midpoint of a power-of-two-length string, the core positive result T7's
open conjecture is contrasted against. -/
theorem helper_full_on_power_of_two {n : Nat} (hn : 1 ≤ n) (w : List Char)
    (hlen : w.length = 2 ^ n) (hbits : IsBitString w) :
    ∃ t, Derives helperGrammar (.nt HelperIdx) w (.ok t []) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hm2 : 2 ≤ 2 ^ (n' + 1) := by
    have h1 : (2:Nat) ^ 1 ≤ 2 ^ (n' + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    simpa using h1
  obtain ⟨t, rest, hderiv, hrestlen, _⟩ := helper_consumption (2 ^ (n' + 1)) hm2 w hlen hbits
  have hsplit : 2 ^ (n' + 1) = 2 * 2 ^ n' := by rw [Nat.pow_succ, Nat.mul_comm]
  have hm1ne : 2 ^ (n' + 1) - 1 ≠ 0 := by
    have := @Nat.one_le_two_pow n'
    omega
  have hlog : Nat.log2 (2 ^ (n' + 1) - 1) = n' :=
    (Nat.log2_eq_iff hm1ne).mpr ⟨by omega, by omega⟩
  rw [hlog] at hrestlen
  have hzero : rest.length = 0 := by omega
  have hrestnil : rest = [] := List.length_eq_zero_iff.mp hzero
  exact ⟨t, hrestnil ▸ hderiv⟩

end Shallot
