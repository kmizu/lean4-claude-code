import Shallot.Lang.TypeCheck

/-!
# Typechecker verification (M6)

L1: `typecheck`/`typecheckArgs` are SOUND w.r.t. `HasType`/`HasTypeArgs`.
L2: they are COMPLETE (note completeness of `typecheckArgs` holds for any
    `f` — the name is only an error payload).
L3: `checkProgram` decides `WTProg`, both directions.

No unproven holes; only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace Shallot

/-- Boolean type equality agrees with propositional equality. -/
theorem Ty.beq_iff : ∀ a b : Ty, Ty.beq a b = true ↔ a = b := by
  intro a b
  cases a <;> cases b <;> simp [Ty.beq]

theorem Ty.beq_refl (a : Ty) : Ty.beq a a = true :=
  (Ty.beq_iff a a).mpr rfl

/-! ## L1 — soundness -/

mutual

theorem typecheck_sound (S : Sig) (Γ : TyCtx) (e : Expr) (τ : Ty)
    (h : typecheck S Γ e = .ok τ) : HasType S Γ e τ := by
  cases e with
  | intLit n =>
    simp only [typecheck] at h
    injection h with h'
    subst h'
    exact HasType.intLit Γ n
  | boolLit b =>
    simp only [typecheck] at h
    injection h with h'
    subst h'
    exact HasType.boolLit Γ b
  | var x =>
    simp only [typecheck] at h
    split at h
    · rename_i τ' heq
      injection h with h'
      subst h'
      exact HasType.var Γ x τ' heq
    · exact nomatch h
  | unop op e =>
    simp only [typecheck] at h
    split at h
    · exact nomatch h
    · rename_i τ' heq
      split at h
      · rename_i hb
        injection h with h'
        subst h'
        rw [(Ty.beq_iff τ' (unOpSig op).1).mp hb] at heq
        exact HasType.unop Γ op e (typecheck_sound S Γ e (unOpSig op).1 heq)
      · exact nomatch h
  | binop op l r =>
    simp only [typecheck] at h
    split at h
    · exact nomatch h
    · rename_i τl heql
      split at h
      · exact nomatch h
      · rename_i τr heqr
        split at h
        · rename_i hbl
          split at h
          · rename_i hbr
            injection h with h'
            subst h'
            rw [(Ty.beq_iff τl (binOpSig op).1).mp hbl] at heql
            rw [(Ty.beq_iff τr (binOpSig op).2.1).mp hbr] at heqr
            exact HasType.binop Γ op l r
              (typecheck_sound S Γ l (binOpSig op).1 heql)
              (typecheck_sound S Γ r (binOpSig op).2.1 heqr)
          · exact nomatch h
        · exact nomatch h
  | ite c t e =>
    simp only [typecheck] at h
    split at h
    · exact nomatch h
    · rename_i τc heqc
      split at h
      · rename_i hbc
        split at h
        · exact nomatch h
        · rename_i τt heqt
          split at h
          · exact nomatch h
          · rename_i τe heqe
            split at h
            · rename_i hbte
              injection h with h'
              subst h'
              rw [(Ty.beq_iff τc Ty.bool).mp hbc] at heqc
              have he' := typecheck_sound S Γ e τe heqe
              rw [← (Ty.beq_iff τt τe).mp hbte] at he'
              exact HasType.ite Γ c t e τt
                (typecheck_sound S Γ c Ty.bool heqc)
                (typecheck_sound S Γ t τt heqt)
                he'
            · exact nomatch h
      · exact nomatch h
  | letE x bound body =>
    simp only [typecheck] at h
    split at h
    · exact nomatch h
    · rename_i τ₁ heq
      exact HasType.letE Γ x bound body τ₁ τ
        (typecheck_sound S Γ bound τ₁ heq)
        (typecheck_sound S ((x, τ₁) :: Γ) body τ h)
  | call f args =>
    simp only [typecheck] at h
    split at h
    · exact nomatch h
    · rename_i tys ret heq
      split at h
      · exact nomatch h
      · rename_i u hargs
        injection h with h'
        subst h'
        exact HasType.call Γ f args tys ret heq
          (typecheckArgs_sound S Γ f args tys u hargs)

theorem typecheckArgs_sound (S : Sig) (Γ : TyCtx) (f : String) (as : Args)
    (tys : List Ty) (u : Unit)
    (h : typecheckArgs S Γ f as tys = .ok u) : HasTypeArgs S Γ as tys := by
  cases as with
  | nil =>
    cases tys with
    | nil => exact HasTypeArgs.nil Γ
    | cons τ tys =>
      simp only [typecheckArgs] at h
      exact nomatch h
  | cons e rest =>
    cases tys with
    | nil =>
      simp only [typecheckArgs] at h
      exact nomatch h
    | cons τ tys =>
      simp only [typecheckArgs] at h
      split at h
      · exact nomatch h
      · rename_i τe heq
        split at h
        · rename_i hb
          rw [(Ty.beq_iff τe τ).mp hb] at heq
          exact HasTypeArgs.cons Γ e rest τ tys
            (typecheck_sound S Γ e τ heq)
            (typecheckArgs_sound S Γ f rest tys u h)
        · exact nomatch h

end

/-! ## L2 — completeness -/

mutual

theorem typecheck_complete (S : Sig) (Γ : TyCtx) (e : Expr) (τ : Ty)
    (h : HasType S Γ e τ) : typecheck S Γ e = .ok τ :=
  match Γ, e, τ, h with
  | _, _, _, .intLit Γ n => by simp [typecheck]
  | _, _, _, .boolLit Γ b => by simp [typecheck]
  | _, _, _, .var Γ x τ hx => by simp [typecheck, hx]
  | _, _, _, .unop Γ op e he => by
    simp [typecheck, typecheck_complete S Γ e (unOpSig op).1 he, Ty.beq_refl]
  | _, _, _, .binop Γ op l r hl hr => by
    simp [typecheck, typecheck_complete S Γ l (binOpSig op).1 hl,
      typecheck_complete S Γ r (binOpSig op).2.1 hr, Ty.beq_refl]
  | _, _, _, .ite Γ c t e τ hc ht he => by
    simp [typecheck, typecheck_complete S Γ c .bool hc,
      typecheck_complete S Γ t τ ht, typecheck_complete S Γ e τ he,
      Ty.beq_refl]
  | _, _, _, .letE Γ x bound body τ₁ τ₂ h₁ h₂ => by
    simp [typecheck, typecheck_complete S Γ bound τ₁ h₁,
      typecheck_complete S ((x, τ₁) :: Γ) body τ₂ h₂]
  | _, _, _, .call Γ f args tys ret hf hargs => by
    simp [typecheck, hf, typecheckArgs_complete S Γ f args tys hargs]

theorem typecheckArgs_complete (S : Sig) (Γ : TyCtx) (f : String) (as : Args)
    (tys : List Ty) (h : HasTypeArgs S Γ as tys) :
    typecheckArgs S Γ f as tys = .ok () :=
  match Γ, as, tys, h with
  | _, _, _, .nil Γ => by simp [typecheckArgs]
  | _, _, _, .cons Γ e rest τ tys he hr => by
    simp [typecheckArgs, typecheck_complete S Γ e τ he,
      typecheckArgs_complete S Γ f rest tys hr, Ty.beq_refl]

end

/-! ## L3 — program level -/

theorem checkFuns_sound (S : Sig) :
    ∀ (ds : List FunDef) (u : Unit), checkFuns S ds = .ok u →
      ∀ d, d ∈ ds → HasType S d.params d.body d.retTy := by
  intro ds
  induction ds with
  | nil =>
    intro u h d hd
    simp at hd
  | cons d0 rest ih =>
    intro u h d hd
    simp only [checkFuns] at h
    split at h
    · exact nomatch h
    · rename_i τ heq
      split at h
      · rename_i hb
        obtain rfl | hmem := List.mem_cons.mp hd
        · rw [(Ty.beq_iff _ _).mp hb] at heq
          exact typecheck_sound S _ _ _ heq
        · exact ih u h d hmem
      · exact nomatch h

theorem checkFuns_complete (S : Sig) :
    ∀ (ds : List FunDef),
      (∀ d, d ∈ ds → HasType S d.params d.body d.retTy) →
      checkFuns S ds = .ok () := by
  intro ds
  induction ds with
  | nil => intro _; simp [checkFuns]
  | cons d0 rest ih =>
    intro hall
    have h0 := typecheck_complete S d0.params d0.body d0.retTy
      (hall d0 (List.mem_cons.mpr (Or.inl rfl)))
    have hr := ih (fun d hd => hall d (List.mem_cons.mpr (Or.inr hd)))
    simp [checkFuns, h0, Ty.beq_refl, hr]

theorem checkProgram_sound (p : Program) (τ : Ty)
    (h : checkProgram p = .ok τ) : WTProg p := by
  simp only [checkProgram] at h
  split at h
  · exact nomatch h
  · rename_i u heq
    exact ⟨checkFuns_sound _ p.funs u heq, τ, typecheck_sound _ [] p.main τ h⟩

theorem checkProgram_complete (p : Program) (h : WTProg p) :
    ∃ τ, checkProgram p = .ok τ := by
  obtain ⟨τ, hmain⟩ := h.main
  refine ⟨τ, ?_⟩
  have hf := checkFuns_complete (p.funs.map FunDef.sig) p.funs h.bodies
  have hm := typecheck_complete (p.funs.map FunDef.sig) [] p.main τ hmain
  simp [checkProgram, hf, hm]

end Shallot
