import Shallot.Vm.Compile
import Shallot.Lang.EvalLemmas
import Shallot.Data.RBVerify

/-!
# M10 — compiler correctness (V0–V2)

Simulation of the interpreter by the compiled stack-VM code, for SUCCESS
outcomes (the plan's V1 scoping: errors/divergence are corpus-checked
empirically, not proved here).

* **V0** — machine infrastructure: one-step characterizations of `vmRun`,
  fuel monotonicity (`vmRun_mono`/`_le`), sequencing (`vmRun_append_error`,
  `vmRun_append_ok`), and the code-table bridge
  (`find?_codeTable_of_funTable`, via R6).

  A statement-shape note on sequencing: the naive
  `run c₁ st lo = ok st' → run c₂ st' lo = ok st'' → run (c₁++c₂) st lo = ok st''`
  is FALSE — `bind`/`unbind` inside `c₁` change the locals, and `vmRun`
  returns only the stack, so the second run must start from the FINAL
  locals of the first, which the hypothesis cannot name. `vmRun_append_ok`
  therefore existentially quantifies those final locals. For compiled
  (bind/unbind-balanced) code the final locals are the initial ones, but
  that is not observable from `vmRun`'s result — which is why V1 below is
  stated in continuation-passing form: the continuation runs at the SAME
  locals, and the letE case discharges the balance obligation locally.

* **V1** — `compile_sim_cont` (mutual with the `compileArgs` version, one
  fuel induction): if `eval` succeeds with `v` and `EnvMatch env σ locals`
  holds, then for ANY continuation code `rest` that runs successfully from
  the stack with `v` pushed, some fuel runs `compileExpr σ e ++ rest` from
  the original stack to the same outcome. `EnvMatch` is the STRUCTURAL
  lockstep relation (env = zip of σ with locals). The non-CPS corollary
  `compile_sim` instantiates `rest := []`.

* **V2** — `compile_correct`: `runProgram` success transfers to
  `vmRunProgram` success with the same value.

Proof discipline as in `Peg/Fuel.lean` / `Lang/EvalLemmas.lean`:
`rw [vmRun.eq_def]` / `rw [eval.eq_def]` unfolds exactly one layer, then
`dsimp only`; never `simp only [vmRun]` near successor-fuel IH targets;
`cases hx : <fuel-independent scrutinee>` substitutes the goal, so only
hypotheses need `rw [hx] at h`.
-/

namespace Shallot

/-! ## V0.0 — one-step characterizations of `vmRun` -/

theorem vmRun_zero (ct : RBNode (List Instr)) (code : List Instr)
    (stack locals : List Value) : vmRun ct 0 code stack locals = none := rfl

theorem vmRun_nil (ct : RBNode (List Instr)) (f : Nat) (stack locals : List Value) :
    vmRun ct (f + 1) [] stack locals = some (.ok stack) := rfl

theorem vmRun_pushI {ct : RBNode (List Instr)} {f : Nat} {n : Int}
    {rest : List Instr} {stack locals : List Value} :
    vmRun ct (f + 1) (.pushI n :: rest) stack locals =
      vmRun ct f rest (.vint n :: stack) locals := rfl

theorem vmRun_pushB {ct : RBNode (List Instr)} {f : Nat} {b : Bool}
    {rest : List Instr} {stack locals : List Value} :
    vmRun ct (f + 1) (.pushB b :: rest) stack locals =
      vmRun ct f rest (.vbool b :: stack) locals := rfl

theorem vmRun_load {ct : RBNode (List Instr)} {f i : Nat} {rest : List Instr}
    {stack locals : List Value} {v : Value} (h : valAt locals i = some v) :
    vmRun ct (f + 1) (.load i :: rest) stack locals =
      vmRun ct f rest (v :: stack) locals := by
  rw [vmRun.eq_def]
  dsimp only
  rw [h]

theorem vmRun_bind {ct : RBNode (List Instr)} {f : Nat} {rest : List Instr}
    {v : Value} {stack locals : List Value} :
    vmRun ct (f + 1) (.bind :: rest) (v :: stack) locals =
      vmRun ct f rest stack (v :: locals) := rfl

theorem vmRun_unbind {ct : RBNode (List Instr)} {f : Nat} {rest : List Instr}
    {v : Value} {stack locals : List Value} :
    vmRun ct (f + 1) (.unbind :: rest) stack (v :: locals) =
      vmRun ct f rest stack locals := rfl

theorem vmRun_unop {ct : RBNode (List Instr)} {f : Nat} {op : UnOp}
    {rest : List Instr} {v v' : Value} {stack locals : List Value}
    (h : evalUnOp op v = .ok v') :
    vmRun ct (f + 1) (.unop op :: rest) (v :: stack) locals =
      vmRun ct f rest (v' :: stack) locals := by
  rw [vmRun.eq_def]
  dsimp only
  rw [h]

theorem vmRun_binop {ct : RBNode (List Instr)} {f : Nat} {op : BinOp}
    {rest : List Instr} {a b v' : Value} {stack locals : List Value}
    (h : evalBinOp op a b = .ok v') :
    vmRun ct (f + 1) (.binop op :: rest) (b :: a :: stack) locals =
      vmRun ct f rest (v' :: stack) locals := by
  rw [vmRun.eq_def]
  dsimp only
  rw [h]

theorem vmRun_branch {ct : RBNode (List Instr)} {f : Nat} {tC eC rest : List Instr}
    {b : Bool} {stack locals : List Value} :
    vmRun ct (f + 1) (.branch tC eC :: rest) (.vbool b :: stack) locals =
      vmRun ct f ((if b = true then tC else eC) ++ rest) stack locals := rfl

theorem vmRun_call {ct : RBNode (List Instr)} {f : Nat} {fn : String} {ar : Nat}
    {code rest : List Instr} {stack locals args st : List Value} {v : Value}
    (hf : RBNode.find? ct fn = some code)
    (hp : popN ar stack [] = some (args, st))
    (hb : vmRun ct f code [] args = some (.ok [v])) :
    vmRun ct (f + 1) (.call fn ar :: rest) stack locals =
      vmRun ct f rest (v :: st) locals := by
  rw [vmRun.eq_def]
  dsimp only
  rw [hf]
  dsimp only
  rw [hp]
  dsimp only
  rw [hb]

/-! ## V0.1 — fuel monotonicity -/

theorem vmRun_mono {ct : RBNode (List Instr)} {f : Nat} {code : List Instr}
    {stack locals : List Value} {r : Except RtErr (List Value)}
    (h : vmRun ct f code stack locals = some r) :
    vmRun ct (f + 1) code stack locals = some r := by
  induction f generalizing code stack locals r with
  | zero => simp [vmRun] at h
  | succ f ih =>
    cases code with
    | nil =>
      rw [vmRun.eq_def] at h ⊢
      exact h
    | cons i rest =>
      rw [vmRun.eq_def] at h ⊢
      dsimp only at h ⊢
      cases i with
      | pushI n => exact ih h
      | pushB b => exact ih h
      | load idx =>
        dsimp only at h ⊢
        cases hv : valAt locals idx with
        | none => rw [hv] at h; exact h
        | some v => rw [hv] at h; exact ih h
      | bind =>
        cases stack with
        | nil => exact h
        | cons v st => exact ih h
      | unbind =>
        cases locals with
        | nil => exact h
        | cons v ls => exact ih h
      | unop op =>
        cases stack with
        | nil => exact h
        | cons v st =>
          dsimp only at h ⊢
          cases hop : evalUnOp op v with
          | error er => rw [hop] at h; exact h
          | ok v' => rw [hop] at h; exact ih h
      | binop op =>
        cases stack with
        | nil => exact h
        | cons b st1 =>
          cases st1 with
          | nil => exact h
          | cons a st =>
            dsimp only at h ⊢
            cases hop : evalBinOp op a b with
            | error er => rw [hop] at h; exact h
            | ok v' => rw [hop] at h; exact ih h
      | branch tC eC =>
        cases stack with
        | nil => exact h
        | cons v st =>
          cases v with
          | vint n => exact h
          | vbool b => exact ih h
      | crash => exact h
      | call fn ar =>
        dsimp only at h ⊢
        cases hf : RBNode.find? ct fn with
        | none => rw [hf] at h; exact h
        | some code' =>
          rw [hf] at h
          dsimp only at h ⊢
          cases hp : popN ar stack [] with
          | none => rw [hp] at h; exact h
          | some pr =>
            rw [hp] at h
            obtain ⟨args, st⟩ := pr
            dsimp only at h ⊢
            cases hr : vmRun ct f code' [] args with
            | none => rw [hr] at h; simp at h
            | some res =>
              rw [hr] at h
              rw [ih hr]
              cases res with
              | error er => exact h
              | ok vs =>
                cases vs with
                | nil => exact h
                | cons v vs' =>
                  cases vs' with
                  | nil => exact ih h
                  | cons w ws => exact h

/-- Fuel monotonicity lifted along `≤`. -/
theorem vmRun_mono_le {ct : RBNode (List Instr)} {f f' : Nat} {code : List Instr}
    {stack locals : List Value} {r : Except RtErr (List Value)}
    (hle : f ≤ f') (h : vmRun ct f code stack locals = some r) :
    vmRun ct f' code stack locals = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact vmRun_mono ih

/-! ## V0.2 — sequencing / decomposition -/

/-- Errors are terminal: appending a continuation does not disturb them
(same fuel — an erroring `c₁` never reaches `c₂`). -/
theorem vmRun_append_error {ct : RBNode (List Instr)} {f : Nat} {c₁ c₂ : List Instr}
    {st lo : List Value} {er : RtErr}
    (h : vmRun ct f c₁ st lo = some (.error er)) :
    vmRun ct f (c₁ ++ c₂) st lo = some (.error er) := by
  induction f generalizing c₁ st lo with
  | zero => simp [vmRun] at h
  | succ f ih =>
    cases c₁ with
    | nil =>
      rw [vmRun.eq_def] at h
      simp at h
    | cons i rest =>
      rw [List.cons_append]
      rw [vmRun.eq_def] at h ⊢
      dsimp only at h ⊢
      cases i with
      | pushI n => exact ih h
      | pushB b => exact ih h
      | load idx =>
        dsimp only at h ⊢
        cases hv : valAt lo idx with
        | none => rw [hv] at h; exact h
        | some v => rw [hv] at h; exact ih h
      | bind =>
        cases st with
        | nil => exact h
        | cons v s => exact ih h
      | unbind =>
        cases lo with
        | nil => exact h
        | cons v ls => exact ih h
      | unop op =>
        cases st with
        | nil => exact h
        | cons v s =>
          dsimp only at h ⊢
          cases hop : evalUnOp op v with
          | error er' => rw [hop] at h; exact h
          | ok v' => rw [hop] at h; exact ih h
      | binop op =>
        cases st with
        | nil => exact h
        | cons b s1 =>
          cases s1 with
          | nil => exact h
          | cons a s =>
            dsimp only at h ⊢
            cases hop : evalBinOp op a b with
            | error er' => rw [hop] at h; exact h
            | ok v' => rw [hop] at h; exact ih h
      | branch tC eC =>
        cases st with
        | nil => exact h
        | cons v s =>
          cases v with
          | vint n => exact h
          | vbool b =>
            have h' := ih (c₁ := (if b = true then tC else eC) ++ rest) h
            rw [List.append_assoc] at h'
            exact h'
      | crash => exact h
      | call fn ar =>
        dsimp only at h ⊢
        cases hf : RBNode.find? ct fn with
        | none => rw [hf] at h; exact h
        | some code' =>
          rw [hf] at h
          dsimp only at h ⊢
          cases hp : popN ar st [] with
          | none => rw [hp] at h; exact h
          | some pr =>
            rw [hp] at h
            obtain ⟨args, s⟩ := pr
            dsimp only at h ⊢
            cases hr : vmRun ct f code' [] args with
            | none => rw [hr] at h; simp at h
            | some res =>
              rw [hr] at h
              cases res with
              | error er' => exact h
              | ok vs =>
                cases vs with
                | nil => exact h
                | cons v vs' =>
                  cases vs' with
                  | nil => exact ih h
                  | cons w ws => exact h

/-- Successful runs compose with a continuation. The final locals of the
`c₁` run are not part of `vmRun`'s result (only the stack is returned), so
they are existentially quantified: SOME locals `lo'` exist such that any
successful continuation from stack `st'` and locals `lo'` extends the run.
(The naive statement reusing `lo` for the continuation is false — `bind`
inside `c₁` changes the locals.) -/
theorem vmRun_append_ok {ct : RBNode (List Instr)} {f₁ : Nat} {c₁ : List Instr}
    {st st' lo : List Value} (h : vmRun ct f₁ c₁ st lo = some (.ok st')) :
    ∃ lo', ∀ (f₂ : Nat) (c₂ : List Instr) (st'' : List Value),
      vmRun ct f₂ c₂ st' lo' = some (.ok st'') →
      vmRun ct (f₁ + f₂) (c₁ ++ c₂) st lo = some (.ok st'') := by
  induction f₁ generalizing c₁ st st' lo with
  | zero => simp [vmRun] at h
  | succ f₁ ih =>
    cases c₁ with
    | nil =>
      rw [vmRun.eq_def] at h
      dsimp only at h
      simp only [Option.some.injEq, Except.ok.injEq] at h
      subst h
      refine ⟨lo, ?_⟩
      intro f₂ c₂ st'' h₂
      rw [List.nil_append]
      exact vmRun_mono_le (by omega) h₂
    | cons i rest =>
      rw [vmRun.eq_def] at h
      dsimp only at h
      cases i with
      | pushI n =>
        obtain ⟨lo', hp⟩ := ih h
        refine ⟨lo', ?_⟩
        intro f₂ c₂ st'' h₂
        rw [List.cons_append, Nat.add_right_comm, vmRun_pushI]
        exact hp f₂ c₂ st'' h₂
      | pushB b =>
        obtain ⟨lo', hp⟩ := ih h
        refine ⟨lo', ?_⟩
        intro f₂ c₂ st'' h₂
        rw [List.cons_append, Nat.add_right_comm, vmRun_pushB]
        exact hp f₂ c₂ st'' h₂
      | load idx =>
        dsimp only at h
        cases hv : valAt lo idx with
        | none => rw [hv] at h; simp at h
        | some v =>
          rw [hv] at h
          obtain ⟨lo', hp⟩ := ih h
          refine ⟨lo', ?_⟩
          intro f₂ c₂ st'' h₂
          rw [List.cons_append, Nat.add_right_comm, vmRun_load hv]
          exact hp f₂ c₂ st'' h₂
      | bind =>
        cases st with
        | nil => simp at h
        | cons v s =>
          obtain ⟨lo', hp⟩ := ih h
          refine ⟨lo', ?_⟩
          intro f₂ c₂ st'' h₂
          rw [List.cons_append, Nat.add_right_comm, vmRun_bind]
          exact hp f₂ c₂ st'' h₂
      | unbind =>
        cases lo with
        | nil => simp at h
        | cons v ls =>
          obtain ⟨lo', hp⟩ := ih h
          refine ⟨lo', ?_⟩
          intro f₂ c₂ st'' h₂
          rw [List.cons_append, Nat.add_right_comm, vmRun_unbind]
          exact hp f₂ c₂ st'' h₂
      | unop op =>
        cases st with
        | nil => simp at h
        | cons v s =>
          dsimp only at h
          cases hop : evalUnOp op v with
          | error er => rw [hop] at h; simp at h
          | ok v' =>
            rw [hop] at h
            obtain ⟨lo', hp⟩ := ih h
            refine ⟨lo', ?_⟩
            intro f₂ c₂ st'' h₂
            rw [List.cons_append, Nat.add_right_comm, vmRun_unop hop]
            exact hp f₂ c₂ st'' h₂
      | binop op =>
        cases st with
        | nil => simp at h
        | cons b s1 =>
          cases s1 with
          | nil => simp at h
          | cons a s =>
            dsimp only at h
            cases hop : evalBinOp op a b with
            | error er => rw [hop] at h; simp at h
            | ok v' =>
              rw [hop] at h
              obtain ⟨lo', hp⟩ := ih h
              refine ⟨lo', ?_⟩
              intro f₂ c₂ st'' h₂
              rw [List.cons_append, Nat.add_right_comm, vmRun_binop hop]
              exact hp f₂ c₂ st'' h₂
      | branch tC eC =>
        cases st with
        | nil => simp at h
        | cons v s =>
          cases v with
          | vint n => simp at h
          | vbool b =>
            obtain ⟨lo', hp⟩ := ih (c₁ := (if b = true then tC else eC) ++ rest) h
            refine ⟨lo', ?_⟩
            intro f₂ c₂ st'' h₂
            rw [List.cons_append, Nat.add_right_comm, vmRun_branch]
            have h' := hp f₂ c₂ st'' h₂
            rw [List.append_assoc] at h'
            exact h'
      | crash => simp at h
      | call fn ar =>
        dsimp only at h
        cases hf : RBNode.find? ct fn with
        | none => rw [hf] at h; simp at h
        | some code' =>
          rw [hf] at h
          dsimp only at h
          cases hpn : popN ar st [] with
          | none => rw [hpn] at h; simp at h
          | some pr =>
            rw [hpn] at h
            obtain ⟨args, s⟩ := pr
            dsimp only at h
            cases hr : vmRun ct f₁ code' [] args with
            | none => rw [hr] at h; simp at h
            | some res =>
              rw [hr] at h
              cases res with
              | error er => simp at h
              | ok vs =>
                cases vs with
                | nil => simp at h
                | cons v vs' =>
                  cases vs' with
                  | cons w ws => simp at h
                  | nil =>
                    obtain ⟨lo', hp⟩ := ih h
                    refine ⟨lo', ?_⟩
                    intro f₂ c₂ st'' h₂
                    rw [List.cons_append, Nat.add_right_comm,
                      vmRun_call hf hpn (vmRun_mono_le (Nat.le_add_right f₁ f₂) hr)]
                    exact hp f₂ c₂ st'' h₂

/-! ## V0.3 — code-table bridge (via R6) -/

/-- First-match association over the compiled entries agrees with the
function-definition entries: same names, compiled payloads. -/
theorem assocLookup_compileFun : ∀ (funs : List FunDef) (g : String) (d : FunDef),
    assocLookup (funs.map fun d => (d.name, d)) g = some d →
    assocLookup (funs.map compileFun) g =
      some (compileExpr (d.params.map (·.1)) d.body) := by
  intro funs
  induction funs with
  | nil =>
    intro g d h
    simp [assocLookup] at h
  | cons fd rest ih =>
    intro g d h
    simp only [List.map_cons] at h ⊢
    simp only [compileFun]
    simp only [assocLookup] at h ⊢
    cases hc : cmpStr g fd.name with
    | eq =>
      rw [hc] at h
      have h2 : some fd = some d := h
      injection h2 with h2
      subst h2
      rfl
    | lt => rw [hc] at h; exact ih g d h
    | gt => rw [hc] at h; exact ih g d h

/-- Table bridge: a hit in the interpreter's function table forces the
corresponding hit (compiled body under the parameter names) in the VM's
code table. Both tables are `fromList` over the same name list, so R6
reduces this to first-match association lookup. -/
theorem find?_codeTable_of_funTable {funs : List FunDef} {g : String} {d : FunDef}
    (h : RBNode.find? (mkFunTable funs) g = some d) :
    RBNode.find? (mkCodeTable funs) g =
      some (compileExpr (d.params.map (·.1)) d.body) := by
  rw [mkFunTable, RBNode.find_fromList] at h
  rw [mkCodeTable, RBNode.find_fromList]
  exact assocLookup_compileFun funs g d h

/-! ## V1.0 — the lockstep environment relation and glue lemmas -/

/-- Structural positional correspondence between the interpreter's
environment, the compile-time name list, and the VM's locals: `env` is
exactly the zip of `σ` with `locals`. `letE` and `call` build all three in
lockstep — this is the whole simulation invariant. -/
inductive EnvMatch : Env → List String → List Value → Prop where
  | nil : EnvMatch [] [] []
  | cons : (x : String) → (v : Value) → (env : Env) → (σ : List String) →
      (locals : List Value) → EnvMatch env σ locals →
      EnvMatch ((x, v) :: env) (x :: σ) (v :: locals)

/-- A successful interpreter lookup forces a compile-time index and the
matching runtime slot (the direction the `var` case needs). -/
theorem EnvMatch.lookup {env : Env} {σ : List String} {locals : List Value}
    (hm : EnvMatch env σ locals) :
    ∀ {x : String} {v : Value}, lookupVal env x = some v →
      ∃ i, idxOf σ x = some i ∧ valAt locals i = some v := by
  induction hm with
  | nil =>
    intro x v h
    simp [lookupVal] at h
  | cons y w env σ locals hm ih =>
    intro x v h
    simp only [lookupVal] at h
    by_cases hb : beqStr x y = true
    · rw [if_pos hb] at h
      injection h with h
      subst h
      refine ⟨0, ?_, rfl⟩
      simp [idxOf, hb]
    · rw [if_neg hb] at h
      obtain ⟨i, hi, hv⟩ := ih h
      refine ⟨i + 1, ?_, hv⟩
      simp [idxOf, hb, hi]

/-- `bindParams` builds exactly the lockstep zip of the parameter names
with the argument values (which are the callee's locals, as `popN`
delivers them in parameter order). -/
theorem bindParams_envMatch : ∀ (params : List (String × Ty)) (vs : List Value)
    (env' : Env), bindParams params vs = some env' →
    EnvMatch env' (params.map (·.1)) vs := by
  intro params
  induction params with
  | nil =>
    intro vs env' h
    cases vs with
    | nil =>
      have h2 : some ([] : Env) = some env' := h
      injection h2 with h2
      subst h2
      exact EnvMatch.nil
    | cons v vs' => simp [bindParams] at h
  | cons p ps ih =>
    intro vs env' h
    obtain ⟨x, ty⟩ := p
    cases vs with
    | nil => simp [bindParams] at h
    | cons v vs' =>
      rw [bindParams.eq_def] at h
      dsimp only at h
      cases hb : bindParams ps vs' with
      | none => rw [hb] at h; simp at h
      | some env'' =>
        rw [hb] at h
        have h2 : some ((x, v) :: env'') = some env' := h
        injection h2 with h2
        subst h2
        exact EnvMatch.cons x v _ _ _ (ih vs' env'' hb)

/-- `popN` over a pushed block: popping `ws.length` values from
`ws ++ stack` reverses `ws` onto the accumulator and leaves `stack`. -/
theorem popN_append : ∀ (ws stack acc : List Value),
    popN ws.length (ws ++ stack) acc = some (ws.reverse ++ acc, stack) := by
  intro ws
  induction ws with
  | nil =>
    intro stack acc
    simp [popN]
  | cons w ws ih =>
    intro stack acc
    have step : popN (ws.length + 1) (w :: (ws ++ stack)) acc
        = popN ws.length (ws ++ stack) (w :: acc) := rfl
    rw [List.cons_append, List.length_cons, step, ih]
    simp [List.reverse_cons, List.append_assoc]

/-- The call-site instance: the args were pushed left-to-right (so the
stack holds `vs.reverse ++ stack`), and `popN` returns them in PUSH
order — parameter order — with the caller's stack underneath. -/
theorem popN_reverse (vs stack : List Value) :
    popN vs.length (vs.reverse ++ stack) [] = some (vs, stack) := by
  have h := popN_append vs.reverse stack []
  rw [List.length_reverse, List.reverse_reverse, List.append_nil] at h
  exact h

/-- A successful `evalArgs` yields one value per syntactic argument, so
the compiled `call`'s static arity matches the number of pushed values. -/
theorem evalArgs_length {ft : RBNode FunDef} : ∀ (f : Nat) (as : Args) (env : Env)
    (vs : List Value), evalArgs ft f env as = some (.ok vs) →
    countArgs as = vs.length := by
  intro f
  induction f with
  | zero =>
    intro as env vs h
    simp [evalArgs] at h
  | succ f ih =>
    intro as env vs h
    cases as with
    | nil =>
      rw [evalArgs.eq_def] at h
      dsimp only at h
      have h2 : some (Except.ok ([] : List Value)) = some (.ok vs) := h
      injection h2 with h2
      injection h2 with h2
      subst h2
      rfl
    | cons e rest =>
      rw [evalArgs.eq_def] at h
      dsimp only at h
      cases h1 : eval ft f env e with
      | none => rw [h1] at h; simp at h
      | some r1 =>
        rw [h1] at h
        cases r1 with
        | error er => simp at h
        | ok v =>
          dsimp only at h
          cases h2 : evalArgs ft f env rest with
          | none => rw [h2] at h; simp at h
          | some r2 =>
            rw [h2] at h
            cases r2 with
            | error er => simp at h
            | ok vs' =>
              have h3 : some (Except.ok (v :: vs')) = some (.ok vs) := h
              injection h3 with h3
              injection h3 with h3
              subst h3
              simp only [countArgs, List.length_cons, ih rest env vs' h2]
              omega

/-! ## V1 — expression simulation (continuation-passing form) -/

/-- **V1 engine** (mutual with the argument-list version, one fuel
induction). If the interpreter succeeds with `v` under a lockstep
environment, then for ANY continuation `rest` that runs successfully from
the stack with `v` pushed — at the SAME locals, which is sound because
compiled code is bind/unbind-balanced and the letE case discharges exactly
that obligation — some fuel runs `compileExpr σ e ++ rest` from the
original stack to the same final outcome. Instantiating `rest := []`
recovers the plain simulation statement (`compile_sim` below). -/
theorem compile_sim_cont (funs : List FunDef) (f : Nat) :
    (∀ (env : Env) (e : Expr) (v : Value) (σ : List String)
        (locals stack : List Value) (rest : List Instr) (fr : Nat)
        (out : List Value),
        eval (mkFunTable funs) f env e = some (.ok v) →
        EnvMatch env σ locals →
        vmRun (mkCodeTable funs) fr rest (v :: stack) locals = some (.ok out) →
        ∃ f', vmRun (mkCodeTable funs) f' (compileExpr σ e ++ rest) stack locals
          = some (.ok out)) ∧
    (∀ (env : Env) (as : Args) (vs : List Value) (σ : List String)
        (locals stack : List Value) (rest : List Instr) (fr : Nat)
        (out : List Value),
        evalArgs (mkFunTable funs) f env as = some (.ok vs) →
        EnvMatch env σ locals →
        vmRun (mkCodeTable funs) fr rest (vs.reverse ++ stack) locals
          = some (.ok out) →
        ∃ f', vmRun (mkCodeTable funs) f' (compileArgs σ as ++ rest) stack locals
          = some (.ok out)) := by
  induction f with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro env e v σ locals stack rest fr out h hm hk
      simp [eval] at h
    · intro env as vs σ locals stack rest fr out h hm hk
      simp [evalArgs] at h
  | succ f ih =>
    obtain ⟨ihe, iha⟩ := ih
    refine ⟨?_, ?_⟩
    · intro env e v σ locals stack rest fr out h hm hk
      cases e with
      | intLit n =>
        rw [eval.eq_def] at h
        dsimp only at h
        have h2 : some (Except.ok (Value.vint n)) = some (.ok v) := h
        injection h2 with h2
        injection h2 with h2
        subst h2
        refine ⟨fr + 1, ?_⟩
        simp only [compileExpr, List.cons_append, List.nil_append]
        rw [vmRun_pushI]
        exact hk
      | boolLit b =>
        rw [eval.eq_def] at h
        dsimp only at h
        have h2 : some (Except.ok (Value.vbool b)) = some (.ok v) := h
        injection h2 with h2
        injection h2 with h2
        subst h2
        refine ⟨fr + 1, ?_⟩
        simp only [compileExpr, List.cons_append, List.nil_append]
        rw [vmRun_pushB]
        exact hk
      | var x =>
        rw [eval.eq_def] at h
        dsimp only at h
        cases hl : lookupVal env x with
        | none => rw [hl] at h; simp at h
        | some w =>
          rw [hl] at h
          have h2 : some (Except.ok w) = some (.ok v) := h
          injection h2 with h2
          injection h2 with h2
          subst h2
          obtain ⟨i, hi, hv⟩ := hm.lookup hl
          refine ⟨fr + 1, ?_⟩
          simp only [compileExpr]
          rw [hi]
          simp only [List.cons_append, List.nil_append]
          rw [vmRun_load hv]
          exact hk
      | unop op e1 =>
        rw [eval.eq_def] at h
        dsimp only at h
        cases h1 : eval (mkFunTable funs) f env e1 with
        | none => rw [h1] at h; simp at h
        | some r1 =>
          rw [h1] at h
          cases r1 with
          | error er => simp at h
          | ok v1 =>
            dsimp only at h
            have hop : evalUnOp op v1 = .ok v := by
              have h2 : some (evalUnOp op v1) = some (.ok v) := h
              exact Option.some.inj h2
            have hcont : vmRun (mkCodeTable funs) (fr + 1) (.unop op :: rest)
                (v1 :: stack) locals = some (.ok out) := by
              rw [vmRun_unop hop]
              exact hk
            obtain ⟨f', h'⟩ := ihe env e1 v1 σ locals stack (.unop op :: rest)
              (fr + 1) out h1 hm hcont
            refine ⟨f', ?_⟩
            simp only [compileExpr, List.append_assoc, List.singleton_append]
            exact h'
      | binop op l r =>
        rw [eval.eq_def] at h
        dsimp only at h
        cases h1 : eval (mkFunTable funs) f env l with
        | none => rw [h1] at h; simp at h
        | some r1 =>
          rw [h1] at h
          cases r1 with
          | error er => simp at h
          | ok vl =>
            dsimp only at h
            cases h2 : eval (mkFunTable funs) f env r with
            | none => rw [h2] at h; simp at h
            | some r2 =>
              rw [h2] at h
              cases r2 with
              | error er => simp at h
              | ok vr =>
                dsimp only at h
                have hop : evalBinOp op vl vr = .ok v := by
                  have h3 : some (evalBinOp op vl vr) = some (.ok v) := h
                  exact Option.some.inj h3
                have hc2 : vmRun (mkCodeTable funs) (fr + 1) (.binop op :: rest)
                    (vr :: vl :: stack) locals = some (.ok out) := by
                  rw [vmRun_binop hop]
                  exact hk
                obtain ⟨f₂, hR⟩ := ihe env r vr σ locals (vl :: stack)
                  (.binop op :: rest) (fr + 1) out h2 hm hc2
                obtain ⟨f₁, hL⟩ := ihe env l vl σ locals stack
                  (compileExpr σ r ++ .binop op :: rest) f₂ out h1 hm hR
                refine ⟨f₁, ?_⟩
                simp only [compileExpr, List.append_assoc, List.singleton_append]
                exact hL
      | ite c t e1 =>
        rw [eval.eq_def] at h
        dsimp only at h
        cases hc : eval (mkFunTable funs) f env c with
        | none => rw [hc] at h; simp at h
        | some rc =>
          rw [hc] at h
          cases rc with
          | error er => simp at h
          | ok vc =>
            cases vc with
            | vint n => simp at h
            | vbool b =>
              dsimp only at h
              cases b with
              | true =>
                simp at h
                obtain ⟨fT, hT⟩ := ihe env t v σ locals stack rest fr out h hm hk
                have hcont : vmRun (mkCodeTable funs) (fT + 1)
                    (.branch (compileExpr σ t) (compileExpr σ e1) :: rest)
                    (.vbool true :: stack) locals = some (.ok out) := by
                  rw [vmRun_branch]
                  simpa using hT
                obtain ⟨f₁, hC⟩ := ihe env c (.vbool true) σ locals stack
                  (.branch (compileExpr σ t) (compileExpr σ e1) :: rest) (fT + 1)
                  out hc hm hcont
                refine ⟨f₁, ?_⟩
                simp only [compileExpr, List.append_assoc, List.singleton_append]
                exact hC
              | false =>
                simp at h
                obtain ⟨fE, hE⟩ := ihe env e1 v σ locals stack rest fr out h hm hk
                have hcont : vmRun (mkCodeTable funs) (fE + 1)
                    (.branch (compileExpr σ t) (compileExpr σ e1) :: rest)
                    (.vbool false :: stack) locals = some (.ok out) := by
                  rw [vmRun_branch]
                  simpa using hE
                obtain ⟨f₁, hC⟩ := ihe env c (.vbool false) σ locals stack
                  (.branch (compileExpr σ t) (compileExpr σ e1) :: rest) (fE + 1)
                  out hc hm hcont
                refine ⟨f₁, ?_⟩
                simp only [compileExpr, List.append_assoc, List.singleton_append]
                exact hC
      | letE x bound body =>
        rw [eval.eq_def] at h
        dsimp only at h
        cases hb : eval (mkFunTable funs) f env bound with
        | none => rw [hb] at h; simp at h
        | some rb =>
          rw [hb] at h
          cases rb with
          | error er => simp at h
          | ok vb =>
            dsimp only at h
            have hun : vmRun (mkCodeTable funs) (fr + 1) (.unbind :: rest)
                (v :: stack) (vb :: locals) = some (.ok out) := by
              rw [vmRun_unbind]
              exact hk
            obtain ⟨fB, hB⟩ := ihe ((x, vb) :: env) body v (x :: σ) (vb :: locals)
              stack (.unbind :: rest) (fr + 1) out h
              (EnvMatch.cons x vb env σ locals hm) hun
            have hbind : vmRun (mkCodeTable funs) (fB + 1)
                (.bind :: (compileExpr (x :: σ) body ++ .unbind :: rest))
                (vb :: stack) locals = some (.ok out) := by
              rw [vmRun_bind]
              exact hB
            obtain ⟨f₁, hL⟩ := ihe env bound vb σ locals stack
              (.bind :: (compileExpr (x :: σ) body ++ .unbind :: rest)) (fB + 1)
              out hb hm hbind
            refine ⟨f₁, ?_⟩
            simp only [compileExpr, List.append_assoc, List.cons_append]
            exact hL
      | call fn args =>
        rw [eval.eq_def] at h
        dsimp only at h
        cases hf : RBNode.find? (mkFunTable funs) fn with
        | none => rw [hf] at h; simp at h
        | some d =>
          rw [hf] at h
          dsimp only at h
          cases ha : evalArgs (mkFunTable funs) f env args with
          | none => rw [ha] at h; simp at h
          | some ra =>
            rw [ha] at h
            cases ra with
            | error er => simp at h
            | ok vs =>
              dsimp only at h
              cases hbp : bindParams d.params vs with
              | none => rw [hbp] at h; simp at h
              | some env' =>
                rw [hbp] at h
                have hcode := find?_codeTable_of_funTable (funs := funs) hf
                have hmatch := bindParams_envMatch d.params vs env' hbp
                obtain ⟨fB, hB⟩ := ihe env' d.body v (d.params.map (·.1)) vs []
                  [] 1 [v] h hmatch (vmRun_nil _ 0 [v] vs)
                rw [List.append_nil] at hB
                have hlen := evalArgs_length (ft := mkFunTable funs) f args env vs ha
                have hB' : vmRun (mkCodeTable funs) (max fB fr)
                    (compileExpr (d.params.map (·.1)) d.body) [] vs
                    = some (.ok [v]) := vmRun_mono_le (Nat.le_max_left _ _) hB
                have hk' : vmRun (mkCodeTable funs) (max fB fr) rest (v :: stack)
                    locals = some (.ok out) :=
                  vmRun_mono_le (Nat.le_max_right _ _) hk
                have hpop : popN (countArgs args) (vs.reverse ++ stack) []
                    = some (vs, stack) := by
                  rw [hlen]
                  exact popN_reverse vs stack
                have hcall : vmRun (mkCodeTable funs) (max fB fr + 1)
                    (.call fn (countArgs args) :: rest) (vs.reverse ++ stack)
                    locals = some (.ok out) := by
                  rw [vmRun_call hcode hpop hB']
                  exact hk'
                obtain ⟨f₁, hA⟩ := iha env args vs σ locals stack
                  (.call fn (countArgs args) :: rest) (max fB fr + 1) out ha hm
                  hcall
                refine ⟨f₁, ?_⟩
                simp only [compileExpr, List.append_assoc, List.singleton_append]
                exact hA
    · intro env as vs σ locals stack rest fr out h hm hk
      cases as with
      | nil =>
        rw [evalArgs.eq_def] at h
        dsimp only at h
        have h2 : some (Except.ok ([] : List Value)) = some (.ok vs) := h
        injection h2 with h2
        injection h2 with h2
        subst h2
        refine ⟨fr, ?_⟩
        simp only [compileArgs, List.nil_append]
        simpa using hk
      | cons e1 rest' =>
        rw [evalArgs.eq_def] at h
        dsimp only at h
        cases h1 : eval (mkFunTable funs) f env e1 with
        | none => rw [h1] at h; simp at h
        | some r1 =>
          rw [h1] at h
          cases r1 with
          | error er => simp at h
          | ok v1 =>
            dsimp only at h
            cases h2 : evalArgs (mkFunTable funs) f env rest' with
            | none => rw [h2] at h; simp at h
            | some r2 =>
              rw [h2] at h
              cases r2 with
              | error er => simp at h
              | ok vs' =>
                have h3 : some (Except.ok (v1 :: vs')) = some (.ok vs) := h
                injection h3 with h3
                injection h3 with h3
                subst h3
                have hk' : vmRun (mkCodeTable funs) fr rest
                    (vs'.reverse ++ (v1 :: stack)) locals = some (.ok out) := by
                  simpa [List.reverse_cons, List.append_assoc] using hk
                obtain ⟨f₂, hR⟩ := iha env rest' vs' σ locals (v1 :: stack) rest
                  fr out h2 hm hk'
                obtain ⟨f₁, hE⟩ := ihe env e1 v1 σ locals stack
                  (compileArgs σ rest' ++ rest) f₂ out h1 hm hR
                refine ⟨f₁, ?_⟩
                simp only [compileArgs, List.append_assoc]
                exact hE

/-- **V1** — expression simulation, plain form: an interpreter success at
value `v` is reproduced by the compiled code, which pushes exactly `v`
onto any starting stack. -/
theorem compile_sim {funs : List FunDef} {f : Nat} {env : Env} {e : Expr}
    {v : Value} {σ : List String} {locals : List Value}
    (h : eval (mkFunTable funs) f env e = some (.ok v))
    (hm : EnvMatch env σ locals) (stack : List Value) :
    ∃ f', vmRun (mkCodeTable funs) f' (compileExpr σ e) stack locals
      = some (.ok (v :: stack)) := by
  obtain ⟨f', h'⟩ := (compile_sim_cont funs f).1 env e v σ locals stack [] 1
    (v :: stack) h hm (vmRun_nil _ 0 (v :: stack) locals)
  rw [List.append_nil] at h'
  exact ⟨f', h'⟩

/-- V1, argument-list companion: the compiled argument block pushes the
values left-to-right (so the last argument ends on top — `vs.reverse`
prepended to the stack). -/
theorem compileArgs_sim {funs : List FunDef} {f : Nat} {env : Env} {as : Args}
    {vs : List Value} {σ : List String} {locals : List Value}
    (h : evalArgs (mkFunTable funs) f env as = some (.ok vs))
    (hm : EnvMatch env σ locals) (stack : List Value) :
    ∃ f', vmRun (mkCodeTable funs) f' (compileArgs σ as) stack locals
      = some (.ok (vs.reverse ++ stack)) := by
  obtain ⟨f', h'⟩ := (compile_sim_cont funs f).2 env as vs σ locals stack [] 1
    (vs.reverse ++ stack) h hm (vmRun_nil _ 0 (vs.reverse ++ stack) locals)
  rw [List.append_nil] at h'
  exact ⟨f', h'⟩

/-! ## V2 — program-level compiler correctness -/

/-- **V2** — whole-program compiler correctness: if the interpreter runs
the program to a value, the compiled program runs to the SAME value with
some fuel. `main` is compiled under `σ = []` with empty locals and stack
(`EnvMatch.nil`), and the VM leaves exactly the singleton result stack. -/
theorem compile_correct {p : Program} {fuel : Nat} {v : Value}
    (h : runProgram p fuel = some (.ok v)) :
    ∃ fuel', vmRunProgram p fuel' = some (.ok v) := by
  rw [runProgram] at h
  obtain ⟨f', h'⟩ := compile_sim h EnvMatch.nil []
  refine ⟨f', ?_⟩
  rw [vmRunProgram, h']

#print axioms vmRun_mono
#print axioms compile_sim_cont
#print axioms compile_sim
#print axioms compile_correct

end Shallot
