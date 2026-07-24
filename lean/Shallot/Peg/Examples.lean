import Shallot.Peg.Semantics
import Shallot.Peg.Interp
import Shallot.Peg.Determinism
import Shallot.Render

/-!
# `aⁿbⁿcⁿ` — a non-context-free language recognized by plain PEG

Transcribes the 2016 SWoPP draft's Fig. 6 verbatim (`S <- &(A !"b") "a"+ B
!.; A <- "a" A? "b"; B <- "b" B? "c"`), the paper's own example of a
language PEG recognizes despite it not being context-free — this is T3's
witness (`CFL ⊊ MPEL^CBN_1`, via T1 + this example).

Rule indices: `Sidx := 0`, `Aidx := 1`, `Bidx := 2`.

`A`'s `A? = .nt A / eps` always tries recursing FIRST (Ford's prioritized
choice), so it greedily consumes as many leading `'a'`s as the input has —
but COMMITS to that recursion once it succeeds, even if the immediately
following characters then can't supply enough matching `'b'`s (the classic
"can't backtrack out of an already-successful choice" PEG behavior). This
means `A` on `y` either fails outright (not enough `'b'`s follow the full
leading `'a'`-run) or succeeds consuming EXACTLY `leadRunA y` `'a'`s
followed by that many `'b'`s — never a shorter prefix. `S`'s outer `!"b"`
check (after the separate, non-consuming `&(A !"b")` lookahead) is what
rules out the OTHER mismatch direction (more `'b'`s than `'a'`s: `A` would
still succeed, just leaving a stray `'b'` as `rest`, which `!"b"` then
catches).
-/

namespace Shallot

def Sidx : Nat := 0
def Aidx : Nat := 1
def Bidx : Nat := 2

def abcABody : PExp := .seq (.chr 'a') (.seq (PExp.opt (.nt Aidx)) (.chr 'b'))
def abcBBody : PExp := .seq (.chr 'b') (.seq (PExp.opt (.nt Bidx)) (.chr 'c'))
def abcSBody : PExp :=
  .seq (PExp.andP (.seq (.nt Aidx) (.notP (.lit ['b']))))
    (.seq (PExp.plus (.chr 'a')) (.seq (.nt Bidx) (.notP .any)))

def abcGrammar : Grammar := { rules := [abcSBody, abcABody, abcBBody], start := Sidx }

/-! ## Smoke tests (small `n`, `#guard`-pinned before the general proof) -/

#guard renderPeg (pegRun abcGrammar 200 (.nt Sidx) "".toList) == "fail"
#guard renderPeg (pegRun abcGrammar 200 (.nt Sidx) "abc".toList) == "ok+0"
#guard renderPeg (pegRun abcGrammar 200 (.nt Sidx) "aabbcc".toList) == "ok+0"
#guard renderPeg (pegRun abcGrammar 200 (.nt Sidx) "aaabbbccc".toList) == "ok+0"
#guard renderPeg (pegRun abcGrammar 200 (.nt Sidx) "aabbccc".toList) == "fail"
#guard renderPeg (pegRun abcGrammar 200 (.nt Sidx) "aaabbccc".toList) == "fail"
#guard renderPeg (pegRun abcGrammar 200 (.nt Sidx) "ab".toList) == "fail"

/-! ## `A`'s full characterization

`A` on `y` succeeds iff `y`'s ENTIRE leading run of `'a'`s (length
`leadRunA y`) is followed immediately by that many `'b'`s — never a
shorter prefix (Ford's "can't backtrack out of an already-successful
choice": `A?` always tries recursing deeper first and commits once it
does). -/

def leadRunA : List Char → Nat
  | [] => 0
  | c :: cs => if beqChar c 'a' then 1 + leadRunA cs else 0

def leadRunB : List Char → Nat
  | [] => 0
  | c :: cs => if beqChar c 'b' then 1 + leadRunB cs else 0

theorem leadRunA_replicate_cons {c : Char} (hc : beqChar c 'a' = false) :
    ∀ (m : Nat) (cs : List Char),
      leadRunA (List.replicate m 'a' ++ c :: cs) = m
  | 0, _cs => by simp [leadRunA, hc]
  | m + 1, cs => by
      rw [List.replicate_succ, List.cons_append]
      show (if beqChar 'a' 'a' then 1 + leadRunA (List.replicate m 'a' ++ c :: cs) else 0) = m + 1
      rw [if_pos (by decide), leadRunA_replicate_cons hc m cs]
      omega

theorem leadRunB_replicate_cons {c : Char} (hc : beqChar c 'b' = false) :
    ∀ (m : Nat) (cs : List Char),
      leadRunB (List.replicate m 'b' ++ c :: cs) = m
  | 0, _cs => by simp [leadRunB, hc]
  | m + 1, cs => by
      rw [List.replicate_succ, List.cons_append]
      show (if beqChar 'b' 'b' then 1 + leadRunB (List.replicate m 'b' ++ c :: cs) else 0) = m + 1
      rw [if_pos (by decide), leadRunB_replicate_cons hc m cs]
      omega

/-- Reassociating a trailing `c` right before `rest` into a leading `c`,
across an intervening run of the same character — needed to align a
`replicate`-with-trailing-extra shape (from an inner recursive match) with
a `replicate_succ`-unfolded (leading-cons) target shape. -/
theorem replicate_append_cons {α : Type _} (c : α) (m : Nat) (rest : List α) :
    List.replicate m c ++ (c :: rest) = c :: (List.replicate m c ++ rest) := by
  rw [show c :: rest = [c] ++ rest from rfl, ← List.append_assoc, ← List.replicate_succ',
    List.replicate_succ, List.cons_append]

/-- `beqChar c d = true` forces `c = d` (`Char.toNat` is injective). -/
theorem beqChar_eq {c d : Char} (h : beqChar c d = true) : c = d := by
  simp only [beqChar, beq_iff_eq] at h
  exact Char.toNat_inj.mp h

/-- Completeness half of `A`'s characterization, as its own helper (plain
induction on `m`, no need for the `y.length` strong induction the full
`A_char` iff needs): for ANY `m ≥ 1` and ANY `rest`, `A` matches
`aᵐbᵐ ++ rest` — no side-condition on `rest` is needed (in particular no
"`m` is the true leading run" hypothesis), since `replicate m 'a' ++
replicate m 'b' ++ rest` with `m ≥ 1` automatically has leading-`'a'`-run
EXACTLY `m` regardless of `rest`'s own content (the next character after
the `'a'`-run is forced to be `'b'`, from `replicate m 'b'`'s own head). -/
theorem A_complete : ∀ (n : Nat) (rest : List Char),
    ∃ t, Derives abcGrammar (.nt Aidx)
      (List.replicate (n + 1) 'a' ++ List.replicate (n + 1) 'b' ++ rest) (.ok t rest)
  | 0, rest => by
      have hAfail : Derives abcGrammar (.nt Aidx) ('b' :: rest) .fail :=
        Derives.ntFail Aidx abcABody ('b' :: rest) rfl
          (by simp only [abcABody]; exact Derives.seqFail₁ _ _ _ (Derives.chrFail 'a' 'b' rest (by decide)))
      have hEps : Derives abcGrammar .eps ('b' :: rest) (.ok (.leaf []) ('b' :: rest)) :=
        Derives.eps _
      have hOpt : Derives abcGrammar (PExp.opt (.nt Aidx)) ('b' :: rest)
          (.ok (.choiceR (.leaf [])) ('b' :: rest)) :=
        Derives.altR (.nt Aidx) .eps ('b' :: rest) ('b' :: rest) (.leaf []) hAfail hEps
      have hChrB : Derives abcGrammar (.chr 'b') ('b' :: rest) (.ok (.leaf ['b']) rest) :=
        Derives.chrOk 'b' 'b' rest (by decide)
      have hTail : Derives abcGrammar (.seq (PExp.opt (.nt Aidx)) (.chr 'b')) ('b' :: rest)
          (.ok (.seq (.choiceR (.leaf [])) (.leaf ['b'])) rest) :=
        Derives.seqOk _ _ _ _ _ _ _ hOpt hChrB
      have hChrA : Derives abcGrammar (.chr 'a') ('a' :: 'b' :: rest) (.ok (.leaf ['a']) ('b' :: rest)) :=
        Derives.chrOk 'a' 'a' ('b' :: rest) (by decide)
      have hBody : Derives abcGrammar abcABody ('a' :: 'b' :: rest)
          (.ok (.seq (.leaf ['a']) (.seq (.choiceR (.leaf [])) (.leaf ['b']))) rest) := by
        simp only [abcABody]
        exact Derives.seqOk _ _ _ _ _ _ _ hChrA hTail
      exact ⟨_, Derives.ntOk Aidx abcABody ('a' :: 'b' :: rest) rest _ rfl hBody⟩
  | n + 1, rest => by
      have hcons : List.replicate (n + 2) 'b' ++ rest = List.replicate (n + 1) 'b' ++ ('b' :: rest) := by
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]
      obtain ⟨t', hrec0⟩ := A_complete n ('b' :: rest)
      have hrec : Derives abcGrammar (.nt Aidx)
          (List.replicate (n + 1) 'a' ++ (List.replicate (n + 2) 'b' ++ rest)) (.ok t' ('b' :: rest)) := by
        simp only [List.append_assoc] at hrec0
        rwa [← hcons] at hrec0
      have hOpt : Derives abcGrammar (PExp.opt (.nt Aidx))
          (List.replicate (n + 1) 'a' ++ (List.replicate (n + 2) 'b' ++ rest))
          (.ok (.choiceL t') ('b' :: rest)) :=
        Derives.altL (.nt Aidx) .eps _ _ _ hrec
      have hChrB : Derives abcGrammar (.chr 'b') ('b' :: rest) (.ok (.leaf ['b']) rest) :=
        Derives.chrOk 'b' 'b' rest (by decide)
      have hTail : Derives abcGrammar (.seq (PExp.opt (.nt Aidx)) (.chr 'b'))
          (List.replicate (n + 1) 'a' ++ (List.replicate (n + 2) 'b' ++ rest))
          (.ok (.seq (.choiceL t') (.leaf ['b'])) rest) :=
        Derives.seqOk _ _ _ _ _ _ _ hOpt hChrB
      have hChrA : Derives abcGrammar (.chr 'a')
          ('a' :: (List.replicate (n + 1) 'a' ++ (List.replicate (n + 2) 'b' ++ rest)))
          (.ok (.leaf ['a']) (List.replicate (n + 1) 'a' ++ (List.replicate (n + 2) 'b' ++ rest))) :=
        Derives.chrOk 'a' 'a' _ (by decide)
      have hBody : Derives abcGrammar abcABody
          ('a' :: (List.replicate (n + 1) 'a' ++ (List.replicate (n + 2) 'b' ++ rest)))
          (.ok (.seq (.leaf ['a']) (.seq (.choiceL t') (.leaf ['b']))) rest) := by
        simp only [abcABody]
        exact Derives.seqOk _ _ _ _ _ _ _ hChrA hTail
      have hnt := Derives.ntOk Aidx abcABody
        ('a' :: (List.replicate (n + 1) 'a' ++ (List.replicate (n + 2) 'b' ++ rest))) rest _ rfl hBody
      have heq : List.replicate (n + 1 + 1) 'a' ++ List.replicate (n + 1 + 1) 'b' ++ rest
          = 'a' :: (List.replicate (n + 1) 'a' ++ (List.replicate (n + 2) 'b' ++ rest)) := by
        simp only [List.append_assoc]
        rw [List.replicate_succ]
        rfl
      exact ⟨_, heq ▸ hnt⟩

/-- `A`'s success: consumes exactly `leadRunA y` `'a'`s then that many
`'b'`s — proved by strong induction on `y.length`, since the recursive
`A?` case examines a STRICTLY shorter tail. -/
theorem A_char : ∀ (len : Nat) (y : List Char), y.length = len → ∀ (rest : List Char),
    (∃ t, Derives abcGrammar (.nt Aidx) y (.ok t rest)) ↔
      leadRunA y ≥ 1 ∧ y = List.replicate (leadRunA y) 'a' ++ List.replicate (leadRunA y) 'b' ++ rest := by
  intro len
  induction len using Nat.strongRecOn with
  | ind len ih =>
    intro y hlen rest
    constructor
    · rintro ⟨t, hderiv⟩
      cases hderiv with
      | ntOk _ _ _ _ _ hr hd =>
          simp only [abcGrammar, ruleAt, Aidx] at hr
          injection hr with hr
          subst hr
          simp only [abcABody] at hd
          cases hd with
          | seqOk _ _ _ rest1 _ _ _ h1 h2 =>
              cases h1 with
              | chrOk _ d _ hbeq =>
                  have hdEq : d = 'a' := (beqChar_eq hbeq).symm
                  subst hdEq
                  cases h2 with
                  | seqOk _ _ _ rest2 _ _ _ hopt hchrb =>
                      cases hopt with
                      | altL _ _ _ _ _ hA =>
                          have hlend : ('a' :: rest1).length = len := hlen
                          simp only [List.length_cons] at hlend
                          have hlt : rest1.length < len := by omega
                          obtain ⟨hmrec1, hmrec2⟩ :=
                            (ih rest1.length hlt rest1 rfl rest2).mp ⟨_, hA⟩
                          cases hchrb with
                          | chrOk _ d' _ hbeq' =>
                              have hdEq' : d' = 'b' := (beqChar_eq hbeq').symm
                              subst hdEq'
                              have hleadEq : leadRunA ('a' :: rest1) = leadRunA rest1 + 1 := by
                                show (if beqChar 'a' 'a' then 1 + leadRunA rest1 else 0)
                                  = leadRunA rest1 + 1
                                rw [if_pos (by decide)]
                                omega
                              rw [hleadEq]
                              refine ⟨by omega, ?_⟩
                              show 'a' :: rest1 = List.replicate (leadRunA rest1 + 1) 'a'
                                ++ List.replicate (leadRunA rest1 + 1) 'b' ++ rest
                              generalize hk : leadRunA rest1 = k at hmrec2 ⊢
                              simp only [hmrec2, List.replicate_succ, List.append_assoc,
                                replicate_append_cons, List.cons_append]
                      | altR _ _ _ _ _ _ hEps =>
                          cases hEps with
                          | eps _ =>
                              cases hchrb with
                              | chrOk _ d' _ hbeq' =>
                                  have hdEq' : d' = 'b' := (beqChar_eq hbeq').symm
                                  subst hdEq'
                                  have hleadEq : leadRunA ('a' :: 'b' :: rest) = 1 := by
                                    show (if beqChar 'a' 'a' then 1 + leadRunA ('b' :: rest) else 0) = 1
                                    rw [if_pos (by decide)]
                                    show 1 + (if beqChar 'b' 'a' then 1 + leadRunA rest else 0) = 1
                                    rw [if_neg (by decide)]
                                  rw [hleadEq]
                                  exact ⟨by omega, rfl⟩
    · rintro ⟨hge, heq⟩
      obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hge
      obtain ⟨t, ht⟩ := A_complete n rest
      refine ⟨t, ?_⟩
      rw [heq, hn]
      simpa [Nat.add_comm] using ht

/-- Completeness half of `B`'s characterization, as its own helper (plain
induction on `m`, no need for the `y.length` strong induction the full
`B_char` iff needs): for ANY `m ≥ 1` and ANY `rest`, `B` matches
`aᵐbᵐ ++ rest` — no side-condition on `rest` is needed (in particular no
"`m` is the true leading run" hypothesis), since `replicate m 'b' ++
replicate m 'c' ++ rest` with `m ≥ 1` automatically has leading-`'b'`-run
EXACTLY `m` regardless of `rest`'s own content (the next character after
the `'b'`-run is forced to be `'c'`, from `replicate m 'c'`'s own head). -/
theorem B_complete : ∀ (n : Nat) (rest : List Char),
    ∃ t, Derives abcGrammar (.nt Bidx)
      (List.replicate (n + 1) 'b' ++ List.replicate (n + 1) 'c' ++ rest) (.ok t rest)
  | 0, rest => by
      have hAfail : Derives abcGrammar (.nt Bidx) ('c' :: rest) .fail :=
        Derives.ntFail Bidx abcBBody ('c' :: rest) rfl
          (by simp only [abcBBody]; exact Derives.seqFail₁ _ _ _ (Derives.chrFail 'b' 'c' rest (by decide)))
      have hEps : Derives abcGrammar .eps ('c' :: rest) (.ok (.leaf []) ('c' :: rest)) :=
        Derives.eps _
      have hOpt : Derives abcGrammar (PExp.opt (.nt Bidx)) ('c' :: rest)
          (.ok (.choiceR (.leaf [])) ('c' :: rest)) :=
        Derives.altR (.nt Bidx) .eps ('c' :: rest) ('c' :: rest) (.leaf []) hAfail hEps
      have hChrB : Derives abcGrammar (.chr 'c') ('c' :: rest) (.ok (.leaf ['c']) rest) :=
        Derives.chrOk 'c' 'c' rest (by decide)
      have hTail : Derives abcGrammar (.seq (PExp.opt (.nt Bidx)) (.chr 'c')) ('c' :: rest)
          (.ok (.seq (.choiceR (.leaf [])) (.leaf ['c'])) rest) :=
        Derives.seqOk _ _ _ _ _ _ _ hOpt hChrB
      have hChrA : Derives abcGrammar (.chr 'b') ('b' :: 'c' :: rest) (.ok (.leaf ['b']) ('c' :: rest)) :=
        Derives.chrOk 'b' 'b' ('c' :: rest) (by decide)
      have hBody : Derives abcGrammar abcBBody ('b' :: 'c' :: rest)
          (.ok (.seq (.leaf ['b']) (.seq (.choiceR (.leaf [])) (.leaf ['c']))) rest) := by
        simp only [abcBBody]
        exact Derives.seqOk _ _ _ _ _ _ _ hChrA hTail
      exact ⟨_, Derives.ntOk Bidx abcBBody ('b' :: 'c' :: rest) rest _ rfl hBody⟩
  | n + 1, rest => by
      have hcons : List.replicate (n + 2) 'c' ++ rest = List.replicate (n + 1) 'c' ++ ('c' :: rest) := by
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]
      obtain ⟨t', hrec0⟩ := B_complete n ('c' :: rest)
      have hrec : Derives abcGrammar (.nt Bidx)
          (List.replicate (n + 1) 'b' ++ (List.replicate (n + 2) 'c' ++ rest)) (.ok t' ('c' :: rest)) := by
        simp only [List.append_assoc] at hrec0
        rwa [← hcons] at hrec0
      have hOpt : Derives abcGrammar (PExp.opt (.nt Bidx))
          (List.replicate (n + 1) 'b' ++ (List.replicate (n + 2) 'c' ++ rest))
          (.ok (.choiceL t') ('c' :: rest)) :=
        Derives.altL (.nt Bidx) .eps _ _ _ hrec
      have hChrB : Derives abcGrammar (.chr 'c') ('c' :: rest) (.ok (.leaf ['c']) rest) :=
        Derives.chrOk 'c' 'c' rest (by decide)
      have hTail : Derives abcGrammar (.seq (PExp.opt (.nt Bidx)) (.chr 'c'))
          (List.replicate (n + 1) 'b' ++ (List.replicate (n + 2) 'c' ++ rest))
          (.ok (.seq (.choiceL t') (.leaf ['c'])) rest) :=
        Derives.seqOk _ _ _ _ _ _ _ hOpt hChrB
      have hChrA : Derives abcGrammar (.chr 'b')
          ('b' :: (List.replicate (n + 1) 'b' ++ (List.replicate (n + 2) 'c' ++ rest)))
          (.ok (.leaf ['b']) (List.replicate (n + 1) 'b' ++ (List.replicate (n + 2) 'c' ++ rest))) :=
        Derives.chrOk 'b' 'b' _ (by decide)
      have hBody : Derives abcGrammar abcBBody
          ('b' :: (List.replicate (n + 1) 'b' ++ (List.replicate (n + 2) 'c' ++ rest)))
          (.ok (.seq (.leaf ['b']) (.seq (.choiceL t') (.leaf ['c']))) rest) := by
        simp only [abcBBody]
        exact Derives.seqOk _ _ _ _ _ _ _ hChrA hTail
      have hnt := Derives.ntOk Bidx abcBBody
        ('b' :: (List.replicate (n + 1) 'b' ++ (List.replicate (n + 2) 'c' ++ rest))) rest _ rfl hBody
      have heq : List.replicate (n + 1 + 1) 'b' ++ List.replicate (n + 1 + 1) 'c' ++ rest
          = 'b' :: (List.replicate (n + 1) 'b' ++ (List.replicate (n + 2) 'c' ++ rest)) := by
        simp only [List.append_assoc]
        rw [List.replicate_succ]
        rfl
      exact ⟨_, heq ▸ hnt⟩

/-- `B`'s success: consumes exactly `leadRunB y` `'b'`s then that many
`'c'`s — proved by strong induction on `y.length`, since the recursive
`B?` case examines a STRICTLY shorter tail. -/
theorem B_char : ∀ (len : Nat) (y : List Char), y.length = len → ∀ (rest : List Char),
    (∃ t, Derives abcGrammar (.nt Bidx) y (.ok t rest)) ↔
      leadRunB y ≥ 1 ∧ y = List.replicate (leadRunB y) 'b' ++ List.replicate (leadRunB y) 'c' ++ rest := by
  intro len
  induction len using Nat.strongRecOn with
  | ind len ih =>
    intro y hlen rest
    constructor
    · rintro ⟨t, hderiv⟩
      cases hderiv with
      | ntOk _ _ _ _ _ hr hd =>
          simp only [abcGrammar, ruleAt, Bidx] at hr
          injection hr with hr
          subst hr
          simp only [abcBBody] at hd
          cases hd with
          | seqOk _ _ _ rest1 _ _ _ h1 h2 =>
              cases h1 with
              | chrOk _ d _ hbeq =>
                  have hdEq : d = 'b' := (beqChar_eq hbeq).symm
                  subst hdEq
                  cases h2 with
                  | seqOk _ _ _ rest2 _ _ _ hopt hchrb =>
                      cases hopt with
                      | altL _ _ _ _ _ hA =>
                          have hlend : ('b' :: rest1).length = len := hlen
                          simp only [List.length_cons] at hlend
                          have hlt : rest1.length < len := by omega
                          obtain ⟨hmrec1, hmrec2⟩ :=
                            (ih rest1.length hlt rest1 rfl rest2).mp ⟨_, hA⟩
                          cases hchrb with
                          | chrOk _ d' _ hbeq' =>
                              have hdEq' : d' = 'c' := (beqChar_eq hbeq').symm
                              subst hdEq'
                              have hleadEq : leadRunB ('b' :: rest1) = leadRunB rest1 + 1 := by
                                show (if beqChar 'b' 'b' then 1 + leadRunB rest1 else 0)
                                  = leadRunB rest1 + 1
                                rw [if_pos (by decide)]
                                omega
                              rw [hleadEq]
                              refine ⟨by omega, ?_⟩
                              show 'b' :: rest1 = List.replicate (leadRunB rest1 + 1) 'b'
                                ++ List.replicate (leadRunB rest1 + 1) 'c' ++ rest
                              generalize hk : leadRunB rest1 = k at hmrec2 ⊢
                              simp only [hmrec2, List.replicate_succ, List.append_assoc,
                                replicate_append_cons, List.cons_append]
                      | altR _ _ _ _ _ _ hEps =>
                          cases hEps with
                          | eps _ =>
                              cases hchrb with
                              | chrOk _ d' _ hbeq' =>
                                  have hdEq' : d' = 'c' := (beqChar_eq hbeq').symm
                                  subst hdEq'
                                  have hleadEq : leadRunB ('b' :: 'c' :: rest) = 1 := by
                                    show (if beqChar 'b' 'b' then 1 + leadRunB ('c' :: rest) else 0) = 1
                                    rw [if_pos (by decide)]
                                    show 1 + (if beqChar 'c' 'b' then 1 + leadRunB rest else 0) = 1
                                    rw [if_neg (by decide)]
                                  rw [hleadEq]
                                  exact ⟨by omega, rfl⟩
    · rintro ⟨hge, heq⟩
      obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hge
      obtain ⟨t, ht⟩ := B_complete n rest
      refine ⟨t, ?_⟩
      rw [heq, hn]
      simpa [Nat.add_comm] using ht

/-- `.star (.chr 'a')` is unconditional (never fails) and always consumes
EXACTLY the leading run of `'a'`s — no ambiguity/commitment risk the way
`A`'s macro-recursive `A?` has, since `star`'s `starNil` fallback needs no
separate suffix to also succeed. Plain structural induction on `y`. -/
theorem beqChar_comm (a b : Char) : beqChar a b = beqChar b a := by
  simp only [beqChar]
  exact Bool.beq_comm

theorem star_chrA_char : ∀ (y : List Char),
    ∃ t, Derives abcGrammar (.star (.chr 'a')) y (.ok t (y.drop (leadRunA y)))
  | [] => ⟨.starNil, Derives.starNil (.chr 'a') [] (Derives.chrEmpty 'a')⟩
  | c :: cs => by
      by_cases hc : beqChar c 'a' = true
      · have hdc : c = 'a' := beqChar_eq hc
        subst hdc
        obtain ⟨t', ht'⟩ := star_chrA_char cs
        have hlead : leadRunA ('a' :: cs) = leadRunA cs + 1 := by
          show (if beqChar 'a' 'a' then 1 + leadRunA cs else 0) = leadRunA cs + 1
          rw [if_pos (by decide)]
          omega
        refine ⟨.starCons (.leaf ['a']) t', ?_⟩
        show Derives abcGrammar (.star (.chr 'a')) ('a' :: cs)
          (.ok (.starCons (.leaf ['a']) t') (('a' :: cs).drop (leadRunA ('a' :: cs))))
        rw [hlead, List.drop_succ_cons]
        exact Derives.starCons (.chr 'a') ('a' :: cs) cs (cs.drop (leadRunA cs))
          (.leaf ['a']) t' (Derives.chrOk 'a' 'a' cs (by decide)) ht'
      · have hbeq : beqChar c 'a' = false := by
          simp only [Bool.not_eq_true] at hc
          exact hc
        have hbeq' : beqChar 'a' c = false := by rw [beqChar_comm]; exact hbeq
        have hlead : leadRunA (c :: cs) = 0 := by
          show (if beqChar c 'a' then 1 + leadRunA cs else 0) = 0
          rw [if_neg (by rw [hbeq]; decide)]
        refine ⟨.starNil, ?_⟩
        rw [hlead]
        exact Derives.starNil (.chr 'a') (c :: cs) (Derives.chrFail 'a' c cs hbeq')

/-- `plus (.chr 'a') = .seq (.chr 'a') (.star (.chr 'a'))` consumes exactly
`m` `'a'`s given `m ≥ 1` and the input's leading `'a'`-run is EXACTLY `m`
(i.e. it's `replicate m 'a' ++ rest` with `rest` not `'a'`-headed). -/
theorem leadRunA_replicate_succ_append (k : Nat) (rest : List Char) :
    leadRunA (List.replicate (k + 1) 'a' ++ rest) = 1 + leadRunA (List.replicate k 'a' ++ rest) := by
  rw [List.replicate_succ, List.cons_append]
  show (if beqChar 'a' 'a' then 1 + leadRunA (List.replicate k 'a' ++ rest) else 0)
    = 1 + leadRunA (List.replicate k 'a' ++ rest)
  rw [if_pos (by decide)]

theorem plus_chrA_char (m : Nat) (hm : 1 ≤ m) (rest : List Char)
    (hnotA : leadRunA (List.replicate m 'a' ++ rest) = m) :
    ∃ t, Derives abcGrammar (PExp.plus (.chr 'a')) (List.replicate m 'a' ++ rest) (.ok t rest) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
  have hk' : m = k + 1 := by omega
  subst hk'
  have hlead : leadRunA (List.replicate k 'a' ++ rest) = k := by
    have := leadRunA_replicate_succ_append k rest
    omega
  rw [List.replicate_succ]
  have hchr : Derives abcGrammar (.chr 'a') ('a' :: (List.replicate k 'a' ++ rest))
      (.ok (.leaf ['a']) (List.replicate k 'a' ++ rest)) := Derives.chrOk 'a' 'a' _ (by decide)
  obtain ⟨t', ht'⟩ := star_chrA_char (List.replicate k 'a' ++ rest)
  rw [hlead, List.drop_left' List.length_replicate] at ht'
  exact ⟨.seq (.leaf ['a']) t', Derives.seqOk _ _ _ _ _ _ _ hchr ht'⟩

theorem leadRunB_replicate_self : ∀ (m : Nat), leadRunB (List.replicate m 'b') = m
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ]
      show (if beqChar 'b' 'b' then 1 + leadRunB (List.replicate n 'b') else 0) = n + 1
      rw [if_pos (by decide), leadRunB_replicate_self n]
      omega

/-- If `.lit ['b']` fails on `restA`, `restA` either is empty or doesn't
start with `'b'` — inverts `stripPrefix?`'s own case split. -/
theorem lit_b_fail_inv {restA : List Char} (h : Derives abcGrammar (.lit ['b']) restA .fail) :
    restA = [] ∨ ∃ d rest', restA = d :: rest' ∧ beqChar d 'b' = false := by
  cases h with
  | litFail _ _ hstrip =>
      cases restA with
      | nil => exact Or.inl rfl
      | cons d rest' =>
          refine Or.inr ⟨d, rest', rfl, ?_⟩
          simp only [stripPrefix?] at hstrip
          by_cases hbd : beqChar 'b' d = true
          · rw [if_pos hbd] at hstrip; cases hstrip
          · rw [beqChar_comm]
            simpa only [Bool.not_eq_true] using hbd

/-- Plain inversion of `.seqOk`, packaged as a flat existential — destructuring
`Derives g (.seq e₁ e₂) input (.ok tOut rest₂)` inline via `cases ... with`
inside a chain of already-nested `cases` is unreliable (the intermediate
`rest₁` binder silently lands on a stale auto-generated name once the tree
output `tOut` itself is an opaque variable needing generalization); proving
this inversion in isolation, then `obtain`-ing the flat witness, sidesteps
that entirely. -/
theorem seq_inv {g : Grammar} {e₁ e₂ : PExp} {input rest₂ : List Char} {tOut : PTree}
    (h : Derives g (.seq e₁ e₂) input (.ok tOut rest₂)) :
    ∃ rest₁ t₁ t₂, tOut = .seq t₁ t₂ ∧
      Derives g e₁ input (.ok t₁ rest₁) ∧ Derives g e₂ rest₁ (.ok t₂ rest₂) := by
  cases h with
  | seqOk _ _ _ rest₁ _ t₁ t₂ h₁ h₂ => exact ⟨rest₁, t₁, t₂, rfl, h₁, h₂⟩

/-- `S`'s headline: `S` recognizes exactly `{aⁿbⁿcⁿ | n ≥ 1}` — T3's witness,
a non-context-free language a plain (macro-free) PEG recognizes. -/
theorem S_char (w : List Char) :
    (∃ t, Derives abcGrammar (.nt Sidx) w (.ok t [])) ↔
      ∃ n, 1 ≤ n ∧ w = List.replicate n 'a' ++ List.replicate n 'b' ++ List.replicate n 'c' := by
  constructor
  · rintro ⟨t, hderiv⟩
    cases hderiv with
    | ntOk _ _ _ _ _ hr hd =>
        simp only [abcGrammar, ruleAt, Sidx] at hr
        injection hr with hr
        subst hr
        simp only [abcSBody] at hd
        cases hd with
        | seqOk _ _ _ rest1 _ _ _ hAndPart hSecondPart =>
            cases hAndPart with
            | notFail _ _ hNotFail =>
                cases hNotFail with
                | notOk _ _ _ _ hSeqAB =>
                    obtain ⟨restA, t1A, t2A, htEq, hA, hNotLitB⟩ := seq_inv hSeqAB
                    subst htEq
                    obtain ⟨hge, heqA⟩ := (A_char w.length w rfl restA).mp ⟨_, hA⟩
                    cases hNotLitB with
                        | notFail _ _ hLitFail =>
                            rename_i restA
                            have hrestAshape := lit_b_fail_inv hLitFail
                            cases hSecondPart with
                            | seqOk _ _ _ restP _ _ _ hPlus hRest =>
                                obtain ⟨k, hk'⟩ := Nat.exists_eq_add_of_le hge
                                have hk : leadRunA w = k + 1 := by omega
                                have hwCons : w = 'a' :: (List.replicate k 'a'
                                    ++ List.replicate (leadRunA w) 'b' ++ restA) := by
                                  conv => lhs; rw [heqA]
                                  simp only [hk, List.replicate_succ, List.cons_append]
                                have hw_reshape : w = List.replicate (leadRunA w) 'a'
                                    ++ (List.replicate (leadRunA w) 'b' ++ restA) := by
                                  conv => lhs; rw [heqA]
                                  rw [List.append_assoc]
                                obtain ⟨t', ht'⟩ := plus_chrA_char (leadRunA w) hge
                                  (List.replicate (leadRunA w) 'b' ++ restA) (by rw [← hw_reshape])
                                rw [← hw_reshape] at ht'
                                have hEqOut := derives_det hPlus ht'
                                injection hEqOut with _ hRestPEq
                                obtain ⟨restB, tB, tNotAny, htEq2, hB, hNotAny⟩ := seq_inv hRest
                                cases hNotAny with
                                | notFail _ _ hAnyFail =>
                                    obtain ⟨hBge, hBeq⟩ :=
                                      (B_char restP.length restP rfl []).mp ⟨tB, hB⟩
                                    have hLeadEq : leadRunB restP = leadRunA w := by
                                      rcases hrestAshape with hEmpty | ⟨d, rest', hEq, hbeq⟩
                                      · rw [hRestPEq, hEmpty, List.append_nil,
                                          leadRunB_replicate_self]
                                      · rw [hRestPEq, hEq, leadRunB_replicate_cons hbeq]
                                    rw [hLeadEq] at hBeq
                                    simp only [List.append_nil] at hBeq
                                    have hFinal : List.replicate (leadRunA w) 'b' ++ restA
                                        = List.replicate (leadRunA w) 'b'
                                          ++ List.replicate (leadRunA w) 'c' :=
                                      hRestPEq.symm.trans hBeq
                                    have hRestAeq : restA = List.replicate (leadRunA w) 'c' :=
                                      List.append_cancel_left hFinal
                                    refine ⟨leadRunA w, hge, ?_⟩
                                    conv => lhs; rw [hwCons, hRestAeq]
                                    simp only [hk, List.replicate_succ, List.cons_append]
  · rintro ⟨n, hn, hw⟩
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
    have hk' : n = k + 1 := by omega
    subst hw
    -- Part 1: the and-predicate `&(A !"b")`.
    obtain ⟨tA, hA⟩ := A_complete k (List.replicate n 'c')
    rw [← hk'] at hA
    have hNotB : Derives abcGrammar (.lit ['b']) (List.replicate n 'c') .fail := by
      apply Derives.litFail
      cases n with
      | zero => omega
      | succ n' => rfl
    have hNotPLitB : Derives abcGrammar (.notP (.lit ['b'])) (List.replicate n 'c')
        (.ok .notT (List.replicate n 'c')) :=
      Derives.notFail (.lit ['b']) (List.replicate n 'c') hNotB
    have hSeqAB : Derives abcGrammar (.seq (.nt Aidx) (.notP (.lit ['b'])))
        (List.replicate n 'a' ++ List.replicate n 'b' ++ List.replicate n 'c')
        (.ok (.seq tA .notT) (List.replicate n 'c')) :=
      Derives.seqOk _ _ _ _ _ _ _ hA hNotPLitB
    have hAndP : Derives abcGrammar (PExp.andP (.seq (.nt Aidx) (.notP (.lit ['b']))))
        (List.replicate n 'a' ++ List.replicate n 'b' ++ List.replicate n 'c')
        (.ok .notT (List.replicate n 'a' ++ List.replicate n 'b' ++ List.replicate n 'c')) :=
      Derives.notFail _ _ (Derives.notOk _ _ _ _ hSeqAB)
    -- Part 2: `"a"+ B !.`.
    have hnotA : leadRunA (List.replicate n 'a' ++ (List.replicate n 'b' ++ List.replicate n 'c'))
        = n := by
      subst hk'
      rw [show List.replicate (k + 1) 'b' ++ List.replicate (k + 1) 'c'
        = 'b' :: (List.replicate k 'b' ++ List.replicate (k + 1) 'c') from by
          rw [List.replicate_succ, List.cons_append]]
      exact leadRunA_replicate_cons (c := 'b') (by decide) (k + 1) _
    obtain ⟨tP, hPlus0⟩ := plus_chrA_char n hn (List.replicate n 'b' ++ List.replicate n 'c') hnotA
    have hPlus : Derives abcGrammar (PExp.plus (.chr 'a'))
        (List.replicate n 'a' ++ List.replicate n 'b' ++ List.replicate n 'c')
        (.ok tP (List.replicate n 'b' ++ List.replicate n 'c')) := by
      rw [List.append_assoc]; exact hPlus0
    obtain ⟨tB, hB0⟩ := B_complete k []
    have hB : Derives abcGrammar (.nt Bidx) (List.replicate n 'b' ++ List.replicate n 'c') (.ok tB []) := by
      rw [← hk'] at hB0
      simpa using hB0
    have hNotAny : Derives abcGrammar (.notP .any) [] (.ok .notT []) :=
      Derives.notFail .any [] Derives.anyFail
    have hSeqBAny : Derives abcGrammar (.seq (.nt Bidx) (.notP .any))
        (List.replicate n 'b' ++ List.replicate n 'c') (.ok (.seq tB .notT) []) :=
      Derives.seqOk _ _ _ _ _ _ _ hB hNotAny
    have hSecond : Derives abcGrammar (.seq (PExp.plus (.chr 'a')) (.seq (.nt Bidx) (.notP .any)))
        (List.replicate n 'a' ++ List.replicate n 'b' ++ List.replicate n 'c') (.ok (.seq tP (.seq tB .notT)) []) :=
      Derives.seqOk _ _ _ _ _ _ _ hPlus hSeqBAny
    have hBody : Derives abcGrammar abcSBody
        (List.replicate n 'a' ++ List.replicate n 'b' ++ List.replicate n 'c')
        (.ok (.seq .notT (.seq tP (.seq tB .notT))) []) := by
      simp only [abcSBody]
      exact Derives.seqOk _ _ _ _ _ _ _ hAndP hSecond
    exact ⟨_, Derives.ntOk Sidx abcSBody _ [] _ rfl hBody⟩


end Shallot
