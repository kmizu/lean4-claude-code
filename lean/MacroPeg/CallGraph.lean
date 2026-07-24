import MacroPeg.Syntax

/-!
# Macro-call graph and acyclicity (M-PEG-5)

Formalizes the "which rules does this rule statically call" graph that the reference
`MacroExpander.expandGrammar` (`kmizu/macro_peg`) implicitly assumes is acyclic — its
naive syntactic inlining diverges whenever a parameterized rule's call-expansion graph
has a cycle (verified this session: `Rec(n: ?) = "a" Rec(n)`, an entirely ordinary,
non-left-recursive rule, hangs the real Scala `expandGrammar` for 60+ seconds).

Design decisions (see `docs/roadmap.md`'s M-PEG-5 entry for the full rationale):
- Only `.call i (a :: as)` (a NON-EMPTY actual-parameter list) is a graph edge / an
  expansion target, mirroring the reference `Evaluator`'s real `Call(name, params)` vs.
  bare `Identifier` split — this project's uniform `.call i args` constructor otherwise
  erases that distinction (`args = []` ⟺ "was written as a bare reference"). `.call i []`
  is left alone by the graph and by `MExp.expand` (`MacroPeg/Expand.lean`).
- Unlike `MExp.subst` (which treats `.lam` as an opaque leaf for capture-safety during
  ONE substitution event), the call graph — and `MExp.expand` — DOES recurse into `.lam`
  bodies: a `.call` node can sit inside a `.lam` literal (exactly the closure-return
  shape in `closureReturnGrammar`, `Examples.lean`), and expansion has no caller
  environment to protect (it's a whole-grammar rewrite, not a single substitution).

This module is Lean-only infrastructure (not part of the Lens-extracted subset — only
`MExp.expand`/`MGrammar.expandGrammar` in `Expand.lean` need extraction), but the
membership check below is still hand-rolled (`natElem`, mirroring `argAt`/`ruleAtM`'s
own-recursion style) rather than `List.contains`, purely because its `if`-shaped
equation is far more `simp`/`split`-friendly in the monotonicity proofs below than the
stdlib's `Bool.or`-shaped one.
-/

namespace Shallot.MacroPeg

/-- Own-recursion membership check on `Nat` lists (mirrors `argAt`'s style), used for
`rankGo`'s on-stack `visiting` check. -/
def natElem : Nat → List Nat → Bool
  | _, [] => false
  | n, m :: ms => if n == m then true else natElem n ms

/-! Direct call targets (rule indices) that `e` may statically invoke via a
non-empty-arg `.call` node, recursing into `.lam`/`.invoke` bodies (see module
docstring) and ordinary structural subterms. `.callParam` has no static target (`k` is
only resolved once `subst` fires) — only its `args` are scanned. -/
mutual
  def MExp.staticCalls : MExp → List Nat
    | .call i (a :: as) => i :: MExp.staticCallsArgs (a :: as)
    | .call _ [] => []
    | .seq e₁ e₂ => MExp.staticCalls e₁ ++ MExp.staticCalls e₂
    | .alt e₁ e₂ => MExp.staticCalls e₁ ++ MExp.staticCalls e₂
    | .star e => MExp.staticCalls e
    | .notP e => MExp.staticCalls e
    | .dbg e => MExp.staticCalls e
    | .lam _ bod => MExp.staticCalls bod
    | .callParam _ args => MExp.staticCallsArgs args
    | .invoke _ bod args => MExp.staticCalls bod ++ MExp.staticCallsArgs args
    | .eps => []
    | .any => []
    | .chr _ => []
    | .range _ _ => []
    | .lit _ => []
    | .param _ => []

  def MExp.staticCallsArgs : List MExp → List Nat
    | [] => []
    | e :: es => MExp.staticCalls e ++ MExp.staticCallsArgs es
end

/-- The set of rules that rule `i`'s body statically calls (`[]` if `i` is out of
range — same zero-well-formedness-assumptions discipline as `ruleAtM`). -/
def MGrammar.calls (g : MGrammar) (i : Nat) : List Nat :=
  match ruleAtM g.rules i with
  | none => []
  | some r => MExp.staticCalls r.body

/-! Rank/height of node `i` in the graph `adj`, computed by a fuel-and-`visiting`-
guarded DFS: `visiting` tracks nodes currently on the recursion stack, and revisiting
one of them (`none`) is exactly a genuine cycle. Mutual with `rankSuccs`, which folds
over a node's successors, threading the SAME `visiting`/`fuel` to each — mirrors
`Interp.lean`'s `evalArgsPar` idiom of a fixed fuel/context shared across a
sibling list, decremented once per "layer" (here: once per node visited). -/
mutual
  def rankGo (adj : Nat → List Nat) (visiting : List Nat) : Nat → Nat → Option Nat
    | 0, _ => none
    | fuel + 1, i =>
      if natElem i visiting then none
      else (rankSuccs adj (i :: visiting) fuel (adj i)).map (fun rs => 1 + rs.foldr max 0)

  def rankSuccs (adj : Nat → List Nat) (visiting : List Nat) (fuel : Nat) :
      List Nat → Option (List Nat)
    | [] => some []
    | j :: js =>
      match rankGo adj visiting fuel j with
      | none => none
      | some r =>
        match rankSuccs adj visiting fuel js with
        | none => none
        | some rs => some (r :: rs)
end

/-- Top-level rank of rule `i` in grammar `g`: a fresh DFS (`visiting = []`), fuel
bounded by the number of rules (any genuinely acyclic graph on `n` nodes has no simple
path longer than `n` edges, so this is always enough fuel when `g` is acyclic). -/
def rank (g : MGrammar) (i : Nat) : Nat :=
  (rankGo g.calls [] g.rules.length i).getD 0

/-- Decidable acyclicity of `g`'s macro-call graph: every rule's DFS (fresh
`visiting`, fuel = `g.rules.length`) succeeds. Plain computable `Bool`, `#guard`/
`decide`-able directly — no `Decidable` instance machinery needed. -/
def acyclicB (g : MGrammar) : Bool :=
  (List.range g.rules.length).all (fun i => (rankGo g.calls [] g.rules.length i).isSome)

/-! ## Termination theorem: `acyclicB g = true` implies a strict rank drop across
every edge. Two supporting monotonicity lemmas, mirroring `Fuel.lean`'s `mpegRun_mono`
/ `evalArgsPar_mono_of_mpegRun_mono` composition pattern: prove the list-processing
helper's version first (parameterized by a hypothesis about the single-node version at
the SAME fuel/visiting), then close the single-node version by induction on `fuel`. -/

/-- More fuel, same `visiting`, never changes an already-`some` result — same shape as
`Fuel.lean`'s `mpegRun_mono` (T0). -/
theorem rankSuccs_mono_of_rankGo_mono {adj : Nat → List Nat} {visiting : List Nat}
    {fuel : Nat}
    (hM : ∀ {j r}, rankGo adj visiting fuel j = some r →
                    rankGo adj visiting (fuel + 1) j = some r) :
    ∀ {js rs}, rankSuccs adj visiting fuel js = some rs →
               rankSuccs adj visiting (fuel + 1) js = some rs
  | [], rs, h => by simp only [rankSuccs] at h ⊢; exact h
  | j :: js, rs, h => by
    simp only [rankSuccs] at h
    cases hj : rankGo adj visiting fuel j with
    | none => rw [hj] at h; simp at h
    | some r =>
      rw [hj] at h
      cases hjs : rankSuccs adj visiting fuel js with
      | none => rw [hjs] at h; simp at h
      | some rs' =>
        rw [hjs] at h
        simp only [Option.some.injEq] at h
        simp only [rankSuccs, hM hj, rankSuccs_mono_of_rankGo_mono hM hjs]
        rw [← h]

theorem rankGo_mono {adj : Nat → List Nat} {visiting : List Nat} {fuel : Nat} {i r : Nat}
    (h : rankGo adj visiting fuel i = some r) :
    rankGo adj visiting (fuel + 1) i = some r := by
  induction fuel generalizing visiting i r with
  | zero => simp [rankGo] at h
  | succ fuel ih =>
    simp only [rankGo] at h ⊢
    split at h
    · simp at h
    · rename_i hvisit
      simp only [hvisit] at h ⊢
      cases hrs : rankSuccs adj (i :: visiting) fuel (adj i) with
      | none => rw [hrs] at h; simp at h
      | some rs =>
        rw [hrs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have hM : ∀ {j r'}, rankGo adj (i :: visiting) fuel j = some r' →
            rankGo adj (i :: visiting) (fuel + 1) j = some r' := fun {j r'} hj => ih hj
        rw [rankSuccs_mono_of_rankGo_mono hM hrs]
        simp [← h]

/-- `rankGo_mono` iterated: any `fuel' ≥ fuel` preserves an already-`some` result,
same shape as `Fuel.lean`'s `mpegRun_mono_le`. -/
theorem rankGo_mono_le {adj : Nat → List Nat} {visiting : List Nat} {fuel fuel' : Nat}
    {i r : Nat} (hle : fuel ≤ fuel') (h : rankGo adj visiting fuel i = some r) :
    rankGo adj visiting fuel' i = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact rankGo_mono ih

/-- Shrinking `visiting` (same `fuel`) can only help: if the DFS succeeds with a
bigger `visiting`, it succeeds with a smaller one too, at a rank no larger. This is
the genuinely novel piece of this milestone — the "gray/white/black" DFS cycle-check
intuition made precise: `visiting` only ever PREVENTS success (via the on-stack
check), so removing entries from it can only turn a `none` into a `some`, never the
reverse, and the value can only shrink (or stay equal). Holds unconditionally
(regardless of whether the underlying graph is acyclic) — acyclicity is only needed
later, to know the TOP-LEVEL `visiting = []` computation succeeds at all. -/
theorem rankSuccs_shrink_of_rankGo_shrink {adj : Nat → List Nat}
    {visiting visiting' : List Nat}
    (hsub : ∀ x, natElem x visiting' = true → natElem x visiting = true)
    {fuel : Nat}
    (hM : ∀ {j r}, rankGo adj visiting fuel j = some r →
                    ∃ r', r' ≤ r ∧ rankGo adj visiting' fuel j = some r') :
    ∀ {js rs}, rankSuccs adj visiting fuel js = some rs →
               ∃ rs', rankSuccs adj visiting' fuel js = some rs' ∧
                      rs'.foldr max 0 ≤ rs.foldr max 0
  | [], rs, h => by
    simp only [rankSuccs, Option.some.injEq] at h
    exact ⟨[], by simp [rankSuccs, ← h]⟩
  | j :: js, rs, h => by
    simp only [rankSuccs] at h
    cases hj : rankGo adj visiting fuel j with
    | none => rw [hj] at h; simp at h
    | some r =>
      rw [hj] at h
      cases hjs : rankSuccs adj visiting fuel js with
      | none => rw [hjs] at h; simp at h
      | some rs0 =>
        rw [hjs] at h
        simp only [Option.some.injEq] at h
        obtain ⟨r', hr'le, hr'⟩ := hM hj
        obtain ⟨rs0', hrs0', hrs0'le⟩ := rankSuccs_shrink_of_rankGo_shrink hsub hM hjs
        refine ⟨r' :: rs0', by simp only [rankSuccs, hr', hrs0'], ?_⟩
        rw [← h, List.foldr_cons, List.foldr_cons]
        omega

/-- `hsub` extends to both lists gaining the same head element. -/
theorem natElem_cons_hsub {visiting visiting' : List Nat}
    (hsub : ∀ x, natElem x visiting' = true → natElem x visiting = true) (i : Nat) :
    ∀ x, natElem x (i :: visiting') = true → natElem x (i :: visiting) = true := by
  intro x hx
  simp only [natElem] at hx ⊢
  split at hx <;> split <;> simp_all [hsub x]

theorem rankGo_shrink {adj : Nat → List Nat} {visiting visiting' : List Nat}
    (hsub : ∀ x, natElem x visiting' = true → natElem x visiting = true)
    {fuel : Nat} {i r : Nat} (h : rankGo adj visiting fuel i = some r) :
    ∃ r', r' ≤ r ∧ rankGo adj visiting' fuel i = some r' := by
  induction fuel generalizing visiting visiting' i r with
  | zero => simp [rankGo] at h
  | succ fuel ih =>
    simp only [rankGo] at h ⊢
    split at h
    · simp at h
    · rename_i hvisit
      have hvisit' : natElem i visiting' = false := by
        cases hc : natElem i visiting' with
        | false => rfl
        | true => exact absurd (hsub i hc) (by simp [hvisit])
      simp only [hvisit']
      cases hrs : rankSuccs adj (i :: visiting) fuel (adj i) with
      | none => rw [hrs] at h; simp at h
      | some rs =>
        rw [hrs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have hM : ∀ {j r'}, rankGo adj (i :: visiting) fuel j = some r' →
            ∃ r'', r'' ≤ r' ∧ rankGo adj (i :: visiting') fuel j = some r'' :=
          fun {j r'} hj => ih (natElem_cons_hsub hsub i) hj
        obtain ⟨rs', hrs', hrs'le⟩ :=
          rankSuccs_shrink_of_rankGo_shrink (natElem_cons_hsub hsub i) hM hrs
        refine ⟨1 + rs'.foldr max 0, ?_, ?_⟩
        · rw [← h]; exact Nat.add_le_add_left hrs'le 1
        · simp [hrs']

/-! ## Closing the argument: `acyclicB g = true` gives a strict rank drop across
every edge (`rank_lt_of_acyclic`). Composes `rankGo_mono_le` (L1) with `rankGo_shrink`
(L2) to relate the INNER `rankGo` call made while unfolding `i` (`visiting = [i]`,
`fuel = N - 1`) to the FRESH top-level call defining `rank g j` (`visiting = []`,
`fuel = N`). -/

theorem ruleAtM_some_lt {rs : List MRule} {i : Nat} {r : MRule} (h : ruleAtM rs i = some r) :
    i < rs.length := by
  induction rs generalizing i with
  | nil => simp [ruleAtM] at h
  | cons r' rs' ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [ruleAtM] at h
      exact Nat.succ_lt_succ (ih h)

/-- If `rankSuccs` succeeds over a list containing `j`, then `j` itself succeeds via
`rankGo`, with a value bounded by the whole list's folded max. -/
theorem rankSuccs_mem {adj : Nat → List Nat} {visiting : List Nat} {fuel : Nat} :
    ∀ {js : List Nat} {rs : List Nat}, rankSuccs adj visiting fuel js = some rs →
    ∀ {j : Nat}, j ∈ js → ∃ r, rankGo adj visiting fuel j = some r ∧ r ≤ rs.foldr max 0
  | j' :: js', rs, h, j, hj => by
    simp only [rankSuccs] at h
    cases hj' : rankGo adj visiting fuel j' with
    | none => rw [hj'] at h; simp at h
    | some r' =>
      rw [hj'] at h
      cases hjs' : rankSuccs adj visiting fuel js' with
      | none => rw [hjs'] at h; simp at h
      | some rs' =>
        rw [hjs'] at h
        simp only [Option.some.injEq] at h
        cases hj with
        | head =>
          refine ⟨r', hj', ?_⟩
          rw [← h, List.foldr_cons]
          exact Nat.le_max_left _ _
        | tail _ hmem =>
          obtain ⟨r, hr, hrle⟩ := rankSuccs_mem hjs' hmem
          refine ⟨r, hr, ?_⟩
          rw [← h, List.foldr_cons]
          exact Nat.le_trans hrle (Nat.le_max_right _ _)

/-- `acyclicB g = true` implies every rule index `< g.rules.length` has a
successful top-level `rankGo` — i.e. `rank g i'` is genuinely its computed rank, not
the `getD 0` fallback. -/
theorem rankGo_top_some_of_acyclic {g : MGrammar} (hacyc : acyclicB g = true)
    {i' : Nat} (hlt : i' < g.rules.length) :
    ∃ r, rankGo g.calls [] g.rules.length i' = some r := by
  simp only [acyclicB, List.all_eq_true] at hacyc
  have := hacyc i' (by simpa using hlt)
  simpa [Option.isSome_iff_exists] using this

theorem rank_lt_of_acyclic {g : MGrammar} (hacyc : acyclicB g = true) {i j : Nat}
    (hij : j ∈ g.calls i) : rank g j < rank g i := by
  have hisome : ∃ r, ruleAtM g.rules i = some r := by
    cases hc : ruleAtM g.rules i with
    | some r => exact ⟨r, rfl⟩
    | none =>
      exfalso
      have hempty : g.calls i = [] := by simp [MGrammar.calls, hc]
      rw [hempty] at hij
      exact absurd hij (by simp)
  obtain ⟨r, hr⟩ := hisome
  have hilt : i < g.rules.length := ruleAtM_some_lt hr
  obtain ⟨ri, hrankI⟩ := rankGo_top_some_of_acyclic hacyc hilt
  obtain ⟨fuel, hfuel⟩ : ∃ fuel, g.rules.length = fuel + 1 := ⟨g.rules.length - 1, by omega⟩
  have hrankI' := hrankI
  rw [hfuel] at hrankI'
  simp only [rankGo] at hrankI'
  split at hrankI'
  · simp at hrankI'
  · rename_i hvi
    cases hrs : rankSuccs g.calls [i] fuel (g.calls i) with
    | none => rw [hrs] at hrankI'; simp at hrankI'
    | some rs =>
      rw [hrs] at hrankI'
      simp only [Option.map_some, Option.some.injEq] at hrankI'
      obtain ⟨rj', hrj', hrj'le⟩ := rankSuccs_mem hrs hij
      have hstep1 : rankGo g.calls [i] (fuel + 1) j = some rj' := rankGo_mono hrj'
      have hstep1' : rankGo g.calls [i] g.rules.length j = some rj' := by
        rw [hfuel]; exact hstep1
      have hsub : ∀ x, natElem x ([] : List Nat) = true → natElem x [i] = true := by
        intro x hx; simp [natElem] at hx
      obtain ⟨rj, hrjle, hrankJ⟩ := rankGo_shrink hsub hstep1'
      have heqI : rank g i = ri := by simp [rank, hrankI]
      have heqJ : rank g j = rj := by simp [rank, hrankJ]
      rw [heqI, heqJ]
      omega

end Shallot.MacroPeg
