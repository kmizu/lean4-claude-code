import MacroPeg.CallGraph

/-!
# Macro expansion (M-PEG-5)

Formalizes the reference `MacroExpander.expandGrammar` (`kmizu/macro_peg`) — an eager,
syntactic, whole-grammar call-inliner — as a total Lean function, PROVEN terminating
under the `acyclicB` well-formedness precondition (`CallGraph.lean`) via
`rank_lt_of_acyclic` used directly as the `termination_by` measure.

Order of operations differs slightly from the Scala reference for termination-proof
convenience: the Scala `expand` substitutes a callee's actual parameters into its RAW
body first, then re-expands the substituted result (so any call embedded in an
argument that itself lands inside the callee's body only gets expanded on that later
pass). This module instead expands the callee's body and the actual arguments
INDEPENDENTLY (each strictly decreases in `rank`/`size` on its own) and only then
substitutes — the two orders agree on the final "no calls remain" fixpoint (T-fix
below) because `expand` never introduces new calls that substitution could later
expose, it only ever inlines/removes them; substituting two independently
call-expansion-complete pieces cannot resurrect a call. Documented here since it is a
deliberate divergence from the reference's literal algorithm, not an oversight.
-/

namespace Shallot.MacroPeg

/-! Structural size (own recursion, mirrors `staticCalls`'s style) — the SIZE half of
`expand`'s lexicographic termination measure, breaking ties where `rankExpr` doesn't
strictly decrease (ordinary structural descent that doesn't cross a call boundary). -/
mutual
  def MExp.size : MExp → Nat
    | .call _ args => 1 + MExp.sizeArgs args
    | .seq e₁ e₂ => 1 + MExp.size e₁ + MExp.size e₂
    | .alt e₁ e₂ => 1 + MExp.size e₁ + MExp.size e₂
    | .star e => 1 + MExp.size e
    | .notP e => 1 + MExp.size e
    | .dbg e => 1 + MExp.size e
    | .lam _ bod => 1 + MExp.size bod
    | .callParam _ args => 1 + MExp.sizeArgs args
    | .invoke _ bod args => 1 + MExp.size bod + MExp.sizeArgs args
    | .eps => 1
    | .any => 1
    | .chr _ => 1
    | .range _ _ => 1
    | .lit _ => 1
    | .param _ => 1

  def MExp.sizeArgs : List MExp → Nat
    | [] => 0
    | e :: es => 1 + MExp.size e + MExp.sizeArgs es
end

/-- The largest rank among `e`'s direct call targets, `0` if it calls nothing — the
RANK half of `expand`'s termination measure. Crossing into a callee's body (the
`.call`/`.invoke` cases below) strictly decreases this component, via
`rank_lt_of_acyclic`; every other case is non-increasing (a subterm's call targets are
a subset of the whole's), so ties are broken by `MExp.size`. -/
def rankExpr (g : MGrammar) (e : MExp) : Nat :=
  (MExp.staticCalls e).foldr (fun i acc => max (rank g i) acc) 0

/-- `rankExpr` over a list of actual parameters (mirrors `staticCallsArgs`). -/
def rankExprArgs (g : MGrammar) (es : List MExp) : Nat :=
  (MExp.staticCallsArgs es).foldr (fun i acc => max (rank g i) acc) 0

/-- `foldr max` over a list of ranks distributes over `++` — the algebraic fact
behind every "a subterm's `rankExpr` is `≤` the whole's" inequality below (`rankExpr`/
`rankExprArgs` are always `(staticCalls[Args] ...).foldr max`, and `staticCalls[Args]`
is always built from `++`/single-recursion over the `MExp` structure). -/
theorem foldrMaxRank_append (g : MGrammar) (l1 l2 : List Nat) :
    (l1 ++ l2).foldr (fun i acc => max (rank g i) acc) 0 =
      max (l1.foldr (fun i acc => max (rank g i) acc) 0)
          (l2.foldr (fun i acc => max (rank g i) acc) 0) := by
  induction l1 with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.max_assoc]

/-- `rankExpr`/`rankExprArgs` of a direct subterm never exceeds the whole's — the
non-strict half of every structural `decreasing_by` obligation below (paired with a
strict `size` decrease to break ties). -/
theorem rankExpr_le_seq_left (g : MGrammar) (e₁ e₂ : MExp) :
    rankExpr g e₁ ≤ rankExpr g (.seq e₁ e₂) := by
  simp only [rankExpr, MExp.staticCalls, foldrMaxRank_append]; exact Nat.le_max_left _ _

theorem rankExpr_le_seq_right (g : MGrammar) (e₁ e₂ : MExp) :
    rankExpr g e₂ ≤ rankExpr g (.seq e₁ e₂) := by
  simp only [rankExpr, MExp.staticCalls, foldrMaxRank_append]; exact Nat.le_max_right _ _

theorem rankExpr_le_alt_left (g : MGrammar) (e₁ e₂ : MExp) :
    rankExpr g e₁ ≤ rankExpr g (.alt e₁ e₂) := by
  simp only [rankExpr, MExp.staticCalls, foldrMaxRank_append]; exact Nat.le_max_left _ _

theorem rankExpr_le_alt_right (g : MGrammar) (e₁ e₂ : MExp) :
    rankExpr g e₂ ≤ rankExpr g (.alt e₁ e₂) := by
  simp only [rankExpr, MExp.staticCalls, foldrMaxRank_append]; exact Nat.le_max_right _ _

theorem rankExpr_le_star (g : MGrammar) (e : MExp) : rankExpr g e ≤ rankExpr g (.star e) := by
  simp only [rankExpr, MExp.staticCalls]; exact Nat.le_refl _

theorem rankExpr_le_notP (g : MGrammar) (e : MExp) : rankExpr g e ≤ rankExpr g (.notP e) := by
  simp only [rankExpr, MExp.staticCalls]; exact Nat.le_refl _

theorem rankExpr_le_dbg (g : MGrammar) (e : MExp) : rankExpr g e ≤ rankExpr g (.dbg e) := by
  simp only [rankExpr, MExp.staticCalls]; exact Nat.le_refl _

theorem rankExpr_le_lam (g : MGrammar) (ar : Nat) (bod : MExp) :
    rankExpr g bod ≤ rankExpr g (.lam ar bod) := by
  simp only [rankExpr, MExp.staticCalls]; exact Nat.le_refl _

theorem rankExpr_le_invoke_bod (g : MGrammar) (ar : Nat) (bod : MExp) (args : List MExp) :
    rankExpr g bod ≤ rankExpr g (.invoke ar bod args) := by
  simp only [rankExpr, MExp.staticCalls, foldrMaxRank_append]; exact Nat.le_max_left _ _

theorem rankExprArgs_le_invoke_args (g : MGrammar) (ar : Nat) (bod : MExp) (args : List MExp) :
    rankExprArgs g args ≤ rankExpr g (.invoke ar bod args) := by
  simp only [rankExpr, rankExprArgs, MExp.staticCalls, foldrMaxRank_append]
  exact Nat.le_max_right _ _

theorem rankExprArgs_le_callParam (g : MGrammar) (k : Nat) (args : List MExp) :
    rankExprArgs g args ≤ rankExpr g (.callParam k args) := by
  simp only [rankExpr, rankExprArgs, MExp.staticCalls]; exact Nat.le_refl _

theorem rankExprArgs_le_call (g : MGrammar) (i : Nat) (args : List MExp) :
    rankExprArgs g args ≤ rankExpr g (.call i args) := by
  cases args with
  | nil => simp [rankExprArgs, MExp.staticCallsArgs]
  | cons a as =>
    simp only [rankExpr, rankExprArgs, MExp.staticCalls]
    exact Nat.le_max_right _ _

/-- `rankExpr`/`rankExprArgs` of the head/tail of an actual-parameter list never
exceeds the whole list's. -/
theorem rankExpr_le_args_head (g : MGrammar) (e : MExp) (es : List MExp) :
    rankExpr g e ≤ rankExprArgs g (e :: es) := by
  simp only [rankExprArgs, MExp.staticCallsArgs, foldrMaxRank_append]; exact Nat.le_max_left _ _

theorem rankExprArgs_le_args_tail (g : MGrammar) (e : MExp) (es : List MExp) :
    rankExprArgs g es ≤ rankExprArgs g (e :: es) := by
  simp only [rankExprArgs, MExp.staticCallsArgs, foldrMaxRank_append]; exact Nat.le_max_right _ _

/-- The callee rule's own rank never exceeds a non-empty-arg call site's — the fact
that lets `MExp.expand`'s `.call i (a::as)` case cross into `MExp.expandRule g h i`. -/
theorem rank_le_call (g : MGrammar) (i : Nat) (a : MExp) (as : List MExp) :
    rank g i ≤ rankExpr g (.call i (a :: as)) := by
  simp only [rankExpr, MExp.staticCalls]
  exact Nat.le_max_left _ _

/-- `rank g i` is always positive (`rankGo`'s only `some`-producing branch is
`1 + ...`) — needed as the base case for `rankExpr_lt_of_acyclic` below. -/
theorem rank_pos_of_acyclic {g : MGrammar} (hacyc : acyclicB g = true) {i : Nat} {r : MRule}
    (hr : ruleAtM g.rules i = some r) : 0 < rank g i := by
  have hilt : i < g.rules.length := ruleAtM_some_lt hr
  obtain ⟨ri, hrankI⟩ := rankGo_top_some_of_acyclic hacyc hilt
  have heqI : rank g i = ri := by simp [rank, hrankI]
  rw [heqI]
  obtain ⟨fuel, hfuel⟩ : ∃ fuel, g.rules.length = fuel + 1 := ⟨g.rules.length - 1, by omega⟩
  rw [hfuel] at hrankI
  simp only [rankGo] at hrankI
  split at hrankI
  · simp at hrankI
  · cases hrs : rankSuccs g.calls [i] fuel (g.calls i) with
    | none => rw [hrs] at hrankI; simp at hrankI
    | some rs =>
      rw [hrs] at hrankI
      simp only [Option.map_some, Option.some.injEq] at hrankI
      omega

/-- `foldr max` over a list where every element's rank is `< bound` never reaches
`bound` — the list-level companion to `rank_lt_of_acyclic`'s single-edge inequality,
used to bound `rankExpr g r.body` (the max over ALL of `r`'s direct callees) at once. -/
theorem foldrMaxRank_lt_of_forall_lt (g : MGrammar) {bound : Nat} (hpos : 0 < bound) :
    ∀ (l : List Nat), (∀ x ∈ l, rank g x < bound) →
      l.foldr (fun j acc => max (rank g j) acc) 0 < bound
  | [], _ => hpos
  | x :: xs, hall => by
    simp only [List.foldr_cons]
    have hx : rank g x < bound := hall x List.mem_cons_self
    have hxs := foldrMaxRank_lt_of_forall_lt g hpos xs
      (fun y hy => hall y (List.mem_cons_of_mem _ hy))
    omega

/-- The strict decrease `MExp.expandRule` needs to cross into a callee's body: the
MAX rank among ALL of `r`'s direct callees is strictly below `i`'s own rank, given
acyclicity. Composes `rank_lt_of_acyclic` (per-edge) with `foldrMaxRank_lt_of_forall_lt`
(lifting "every edge" to "the max over all edges"). -/
theorem rankExpr_lt_of_acyclic {g : MGrammar} (hacyc : acyclicB g = true) {i : Nat} {r : MRule}
    (hr : ruleAtM g.rules i = some r) : rankExpr g r.body < rank g i := by
  have hpos := rank_pos_of_acyclic hacyc hr
  have hcalls : g.calls i = MExp.staticCalls r.body := by simp [MGrammar.calls, hr]
  have hall : ∀ x ∈ MExp.staticCalls r.body, rank g x < rank g i := by
    intro x hx
    rw [← hcalls] at hx
    exact rank_lt_of_acyclic hacyc hx
  simpa [rankExpr] using foldrMaxRank_lt_of_forall_lt g hpos (MExp.staticCalls r.body) hall

/-- Every `decreasing_by` obligation below has this exact shape: the `rankExpr`/
`rankExprArgs` component only ever weakly decreases across a structural step, but
`MExp.size`/`MExp.sizeArgs` always strictly does — so together they give a genuine
`Prod.lexLt` decrease regardless of whether the rank half ties or drops. -/
theorem lex_of_le_of_lt {a b c d : Nat} (hle : a ≤ b) (hlt : c < d) :
    a < b ∨ (a = b ∧ c < d) := by
  rcases Nat.lt_or_eq_of_le hle with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hlt⟩

mutual
  /-- Eager, syntactic macro expansion — inlines every non-empty-arg `.call` node,
  recursively, until none remain (`T_fix` below). Terminates (via `termination_by`
  below, using `rank_lt_of_acyclic`) whenever `h : acyclicB g = true`. -/
  def MExp.expand (g : MGrammar) (h : acyclicB g = true) : MExp → MExp
    | .call i [] => .call i []
    | .call i (a :: as) =>
      MExp.subst (MExp.expandArgs g h (a :: as)) (MExp.expandRule g h i)
    | .seq e₁ e₂ => .seq (MExp.expand g h e₁) (MExp.expand g h e₂)
    | .alt e₁ e₂ => .alt (MExp.expand g h e₁) (MExp.expand g h e₂)
    | .star e => .star (MExp.expand g h e)
    | .notP e => .notP (MExp.expand g h e)
    | .dbg e => .dbg (MExp.expand g h e)
    | .lam ar bod => .lam ar (MExp.expand g h bod)
    | .callParam k args => .callParam k (MExp.expandArgs g h args)
    | .invoke ar bod args => .invoke ar (MExp.expand g h bod) (MExp.expandArgs g h args)
    | .eps => .eps
    | .any => .any
    | .chr c => .chr c
    | .range lo hi => .range lo hi
    | .lit s => .lit s
    | .param k => .param k
  termination_by e => (rankExpr g e, MExp.size e)
  decreasing_by
    all_goals show Prod.Lex Nat.lt Nat.lt _ _
    all_goals apply Prod.Lex.right'
    all_goals
      first
        | exact rankExprArgs_le_call g _ _
        | exact rank_le_call g _ _ _
        | exact rankExpr_le_seq_left g _ _
        | exact rankExpr_le_seq_right g _ _
        | exact rankExpr_le_alt_left g _ _
        | exact rankExpr_le_alt_right g _ _
        | exact rankExpr_le_star g _
        | exact rankExpr_le_notP g _
        | exact rankExpr_le_dbg g _
        | exact rankExpr_le_lam g _ _
        | exact rankExprArgs_le_callParam g _ _
        | exact rankExpr_le_invoke_bod g _ _ _
        | exact rankExprArgs_le_invoke_args g _ _ _
        | (simp [MExp.size, MExp.sizeArgs]; omega)
        | simp [MExp.size, MExp.sizeArgs]

  /-- `expand` mapped over an actual-parameter list (own recursion, matching
  `MExp.substArgs`'s style). -/
  def MExp.expandArgs (g : MGrammar) (h : acyclicB g = true) : List MExp → List MExp
    | [] => []
    | e :: es => MExp.expand g h e :: MExp.expandArgs g h es
  termination_by es => (rankExprArgs g es, MExp.sizeArgs es)
  decreasing_by
    all_goals show Prod.Lex Nat.lt Nat.lt _ _
    all_goals apply Prod.Lex.right'
    all_goals
      first
        | exact rankExpr_le_args_head g _ _
        | exact rankExprArgs_le_args_tail g _ _
        | (simp [MExp.size, MExp.sizeArgs]; omega)
        | simp [MExp.size, MExp.sizeArgs]

  /-- Rule `i`'s body, fully expanded — a missing index falls back to
  `MExp.failAlways`, continuing the zero-well-formedness-assumptions discipline (same
  as `MExp.subst`'s out-of-range `.param`). -/
  def MExp.expandRule (g : MGrammar) (h : acyclicB g = true) (i : Nat) : MExp :=
    match hr : ruleAtM g.rules i with
    | none => MExp.failAlways
    | some r => MExp.expand g h r.body
  termination_by (rank g i, 0)
  decreasing_by
    show Prod.Lex Nat.lt Nat.lt _ _
    apply Prod.Lex.left
    exact rankExpr_lt_of_acyclic h hr
end

/-- The reference `MacroExpander.expandGrammar`: every rule's body, fully expanded. -/
def MGrammar.expandGrammar (g : MGrammar) (h : acyclicB g = true) : MGrammar :=
  { rules := g.rules.map (fun r => { arity := r.arity, body := MExp.expand g h r.body }) }

/-! ## T-fix: `expand` reaches the reference's stated fixpoint ("no remaining calls")

Mirrors the Scala `MacroExpander.expandGrammar`'s documented goal directly: after
expansion, no non-empty-arg `.call` node remains anywhere in the result. -/

/-! Does `e` contain a non-empty-arg `.call` node anywhere (the thing `expand` is
supposed to eliminate)? Mirrors `MExp.staticCalls`'s traversal shape exactly (same
cases recurse the same way), but yields a `Bool` verdict rather than collecting
indices. -/
mutual
  def MExp.hasCall : MExp → Bool
    | .call _ (_ :: _) => true
    | .call _ [] => false
    | .seq e₁ e₂ => e₁.hasCall || e₂.hasCall
    | .alt e₁ e₂ => e₁.hasCall || e₂.hasCall
    | .star e => e.hasCall
    | .notP e => e.hasCall
    | .dbg e => e.hasCall
    | .lam _ bod => bod.hasCall
    | .callParam _ args => MExp.hasCallArgs args
    | .invoke _ bod args => bod.hasCall || MExp.hasCallArgs args
    | .eps => false
    | .any => false
    | .chr _ => false
    | .range _ _ => false
    | .lit _ => false
    | .param _ => false

  def MExp.hasCallArgs : List MExp → Bool
    | [] => false
    | e :: es => e.hasCall || MExp.hasCallArgs es
end

/-- Every element reachable via `argAt` from a call-free actual-parameter list is
itself call-free. -/
theorem hasCallArgs_mem : ∀ {args : List MExp} {k : Nat} {a : MExp},
    MExp.hasCallArgs args = false → argAt args k = some a → a.hasCall = false
  | _ :: _, 0, _, hargs, h => by
    simp only [argAt] at h
    cases h
    simp only [MExp.hasCallArgs, Bool.or_eq_false_iff] at hargs
    exact hargs.1
  | _ :: _, _ + 1, _, hargs, h => by
    simp only [argAt] at h
    simp only [MExp.hasCallArgs, Bool.or_eq_false_iff] at hargs
    exact hasCallArgs_mem hargs.2 h

/-! **Substitution preserves call-freeness.** Needed for T-fix's `.call i (a::as)`
case, which joins an already-expanded (hence call-free) body with already-expanded
(hence call-free) actual parameters via `MExp.subst` — this is exactly what lets that
join stay call-free. Structural (not well-founded) mutual induction directly
mirroring `MExp.subst`/`MExp.substArgs`'s own recursion shape (`Syntax.lean`). -/
mutual
  theorem subst_hasCall_eq_false {args : List MExp} (hargs : MExp.hasCallArgs args = false) :
      ∀ {body : MExp}, body.hasCall = false → (MExp.subst args body).hasCall = false
    | .eps, _ => by simp [MExp.subst, MExp.hasCall]
    | .any, _ => by simp [MExp.subst, MExp.hasCall]
    | .chr _, _ => by simp [MExp.subst, MExp.hasCall]
    | .range _ _, _ => by simp [MExp.subst, MExp.hasCall]
    | .lit _, _ => by simp [MExp.subst, MExp.hasCall]
    | .param k, _ => by
      simp only [MExp.subst]
      cases h : argAt args k with
      | none => simp [MExp.failAlways, MExp.hasCall]
      | some a => exact hasCallArgs_mem hargs h
    | .call i margs, hbody => by
      cases margs with
      | nil =>
        simp only [MExp.subst, MExp.substArgs, MExp.hasCall]
      | cons a as => simp [MExp.hasCall] at hbody
    | .seq e₁ e₂, hbody => by
      simp only [MExp.hasCall, Bool.or_eq_false_iff] at hbody
      simp only [MExp.subst, MExp.hasCall, Bool.or_eq_false_iff]
      exact ⟨subst_hasCall_eq_false hargs hbody.1, subst_hasCall_eq_false hargs hbody.2⟩
    | .alt e₁ e₂, hbody => by
      simp only [MExp.hasCall, Bool.or_eq_false_iff] at hbody
      simp only [MExp.subst, MExp.hasCall, Bool.or_eq_false_iff]
      exact ⟨subst_hasCall_eq_false hargs hbody.1, subst_hasCall_eq_false hargs hbody.2⟩
    | .star e, hbody => by
      simp only [MExp.hasCall] at hbody
      simp only [MExp.subst, MExp.hasCall]
      exact subst_hasCall_eq_false hargs hbody
    | .notP e, hbody => by
      simp only [MExp.hasCall] at hbody
      simp only [MExp.subst, MExp.hasCall]
      exact subst_hasCall_eq_false hargs hbody
    | .dbg e, hbody => by
      simp only [MExp.hasCall] at hbody
      simp only [MExp.subst, MExp.hasCall]
      exact subst_hasCall_eq_false hargs hbody
    | .lam _ar _bod, hbody => by simp only [MExp.subst]; exact hbody
    | .callParam k margs, hbody => by
      simp only [MExp.hasCall] at hbody
      simp only [MExp.subst]
      cases h : argAt args k with
      | none => simp [MExp.failAlways, MExp.hasCall]
      | some av =>
        cases av with
        | lam ar bod =>
          have hbodfree : MExp.hasCall bod = false := by
            have := hasCallArgs_mem hargs h
            simpa [MExp.hasCall] using this
          simp only [MExp.hasCall, Bool.or_eq_false_iff]
          exact ⟨hbodfree, substArgs_hasCall_eq_false hargs hbody⟩
        | _ => simp [MExp.failAlways, MExp.hasCall]
    | .invoke _ar bod margs, hbody => by
      simp only [MExp.hasCall, Bool.or_eq_false_iff] at hbody
      simp only [MExp.subst, MExp.hasCall, Bool.or_eq_false_iff]
      exact ⟨hbody.1, substArgs_hasCall_eq_false hargs hbody.2⟩

  theorem substArgs_hasCall_eq_false {args : List MExp} (hargs : MExp.hasCallArgs args = false) :
      ∀ {margs : List MExp}, MExp.hasCallArgs margs = false →
        MExp.hasCallArgs (MExp.substArgs args margs) = false
    | [], _ => by simp [MExp.substArgs, MExp.hasCallArgs]
    | e :: es, hmargs => by
      simp only [MExp.hasCallArgs, Bool.or_eq_false_iff] at hmargs
      simp only [MExp.substArgs, MExp.hasCallArgs, Bool.or_eq_false_iff]
      exact ⟨subst_hasCall_eq_false hargs hmargs.1, substArgs_hasCall_eq_false hargs hmargs.2⟩
end

/-- **T-fix.** `expand`'s output never contains a non-empty-arg `.call` node — the
pass genuinely reaches the "no remaining calls" fixpoint the reference
`MacroExpander.expandGrammar` is documented to compute. Proved by the auto-generated
mutual induction principle for the `expand`/`expandArgs`/`expandRule` well-founded
group (`MExp.expand.induct`), whose case hypotheses (`ih1`/`ih2`/`ih3` below) supply
exactly the three motives simultaneously. -/
theorem expand_hasCall_eq_false (g : MGrammar) (h : acyclicB g = true) (e : MExp) :
    (MExp.expand g h e).hasCall = false :=
  MExp.expand.induct g h
    (motive1 := fun e => (MExp.expand g h e).hasCall = false)
    (motive2 := fun i => (MExp.expandRule g h i).hasCall = false)
    (motive3 := fun es => MExp.hasCallArgs (MExp.expandArgs g h es) = false)
    (fun _i => by simp [MExp.expand, MExp.hasCall])
    (fun _i _a _as ih3 ih2 => by
      simp only [MExp.expand]
      exact subst_hasCall_eq_false ih3 ih2)
    (fun _e₁ _e₂ ih1 ih2 => by simp [MExp.expand, MExp.hasCall, ih1, ih2])
    (fun _e₁ _e₂ ih1 ih2 => by simp [MExp.expand, MExp.hasCall, ih1, ih2])
    (fun _e ih => by simp [MExp.expand, MExp.hasCall, ih])
    (fun _e ih => by simp [MExp.expand, MExp.hasCall, ih])
    (fun _e ih => by simp [MExp.expand, MExp.hasCall, ih])
    (fun _ar _bod ih => by simp [MExp.expand, MExp.hasCall, ih])
    (fun _k _args ih3 => by simp [MExp.expand, MExp.hasCall, ih3])
    (fun _ar _bod _args ih1 ih3 => by simp [MExp.expand, MExp.hasCall, ih1, ih3])
    (by simp [MExp.expand, MExp.hasCall])
    (by simp [MExp.expand, MExp.hasCall])
    (fun _c => by simp [MExp.expand, MExp.hasCall])
    (fun _lo _hi => by simp [MExp.expand, MExp.hasCall])
    (fun _s => by simp [MExp.expand, MExp.hasCall])
    (fun _k => by simp [MExp.expand, MExp.hasCall])
    (fun _i hnone => by
      unfold MExp.expandRule
      split
      · simp [MExp.failAlways, MExp.hasCall]
      · next heq => rw [heq] at hnone; simp at hnone)
    (fun _i _r hr ih1 => by
      unfold MExp.expandRule
      split
      · next heq => rw [heq] at hr; simp at hr
      · next heq => rw [heq] at hr; cases hr; exact ih1)
    (by simp [MExp.expandArgs, MExp.hasCallArgs])
    (fun _e _es ih1 ih3 => by simp [MExp.expandArgs, MExp.hasCallArgs, ih1, ih3])
    e

/-- Companion fact for `MExp.expandArgs` — every element of the expanded list is
call-free (mechanical corollary of `expand_hasCall_eq_false`, by ordinary structural
induction on the list; no well-founded machinery needed here). -/
theorem expandArgs_hasCallArgs_eq_false (g : MGrammar) (h : acyclicB g = true) :
    ∀ es : List MExp, MExp.hasCallArgs (MExp.expandArgs g h es) = false
  | [] => by simp [MExp.expandArgs, MExp.hasCallArgs]
  | e :: es => by
    simp [MExp.expandArgs, MExp.hasCallArgs, expand_hasCall_eq_false g h e,
      expandArgs_hasCallArgs_eq_false g h es]

/-- The headline, stated for the whole grammar: no rule's expanded body has a
remaining call, after `MGrammar.expandGrammar`. -/
theorem expandGrammar_hasCall_eq_false (g : MGrammar) (h : acyclicB g = true) (r : MRule)
    (hr : r ∈ (MGrammar.expandGrammar g h).rules) : r.body.hasCall = false := by
  simp only [MGrammar.expandGrammar, List.mem_map] at hr
  obtain ⟨r0, _, heq⟩ := hr
  rw [← heq]
  exact expand_hasCall_eq_false g h r0.body

end Shallot.MacroPeg
