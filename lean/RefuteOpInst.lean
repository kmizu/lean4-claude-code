import Lens.Pipeline

/-! Adversarial probe: does the builtin-op dispatch ignore a custom
non-core instance on a builtin-kind type? -/

instance myDiv : Div Int := ⟨Int.tdiv⟩

def cap3 : Int := (-7) / 2

-- Ground truth in Lean: which instance did elaboration pick?
#eval cap3            -- tdiv → -3 ; ediv → -4
#eval Int.tdiv (-7) 2 -- expect -3
#eval Int.ediv (-7) 2 -- expect -4

-- Show the elaborated value of cap3 so we can see the instance argument.
open Lean Meta in
#eval show MetaM Unit from do
  let some (.defnInfo dv) := (← getEnv).find? `cap3 | throwError "no cap3"
  IO.println s!"cap3 value: {← ppExpr dv.value}"
  IO.println s!"raw: {dv.value}"

-- Now extract cap3 and print whatever comes out (or the errors).
#eval show Lean.MetaM Unit from do
  let res ← Lens.extractModule [`cap3] { pkg := "probe" }
  match res with
  | .ok m => IO.println (Lens.Printer.renderModule m)
  | .error errs => for e in errs do IO.println e.render

-- Same hole claimed for BEq: custom BEq Nat extracts as `==`?
instance weirdBeq : BEq Nat := ⟨fun a b => a ≤ b⟩

def cmp2 : Bool := (3 == 5)

#eval cmp2  -- with weirdBeq: 3 ≤ 5 = true ; core beq → false

#eval show Lean.MetaM Unit from do
  let res ← Lens.extractModule [`cmp2] { pkg := "probe" }
  match res with
  | .ok m => IO.println (Lens.Printer.renderModule m)
  | .error errs => for e in errs do IO.println e.render
