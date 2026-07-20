import Shallot.Vm.Machine

/-!
# Compiler: Shallot AST → VM code

Positional compilation: the compile-time environment `σ : List String`
mirrors the runtime locals list index-for-index — `var x` becomes
`load (indexOf σ x)`, `let` brackets its body with `bind`/`unbind`, and a
function body is compiled with `σ = parameter names`. This lockstep is the
whole simulation invariant of V1 (M10).
-/

namespace Shallot

def idxOf : List String → String → Option Nat
  | [], _ => none
  | y :: rest, x =>
    if beqStr x y then some 0
    else
      match idxOf rest x with
      | some i => some (i + 1)
      | none => none

def countArgs : Args → Nat
  | .nil => 0
  | .cons _ rest => 1 + countArgs rest

mutual
  def compileExpr (σ : List String) : Expr → List Instr
    | .intLit n => [.pushI n]
    | .boolLit b => [.pushB b]
    | .var x =>
      match idxOf σ x with
      | some i => [.load i]
      | none => [.crash] -- unreachable on typechecked input (V1 hypothesis)
    | .unop op e => compileExpr σ e ++ [.unop op]
    | .binop op l r => compileExpr σ l ++ compileExpr σ r ++ [.binop op]
    | .ite c t e =>
      compileExpr σ c ++ [.branch (compileExpr σ t) (compileExpr σ e)]
    | .letE x bound body =>
      compileExpr σ bound ++ [.bind] ++ compileExpr (x :: σ) body ++ [.unbind]
    | .call f args => compileArgs σ args ++ [.call f (countArgs args)]

  def compileArgs (σ : List String) : Args → List Instr
    | .nil => []
    | .cons e rest => compileExpr σ e ++ compileArgs σ rest
end

def compileFun (d : FunDef) : String × List Instr :=
  (d.name, compileExpr (d.params.map (·.1)) d.body)

def mkCodeTable (funs : List FunDef) : RBNode (List Instr) :=
  RBNode.fromList (funs.map compileFun)

/-- Compile and run a whole program; the result is `main`'s value. -/
def vmRunProgram (p : Program) (fuel : Nat) : Option (Except RtErr Value) :=
  match vmRun (mkCodeTable p.funs) fuel (compileExpr [] p.main) [] [] with
  | none => none
  | some (.error er) => some (.error er)
  | some (.ok [v]) => some (.ok v)
  | some (.ok _) => some (.error .stuckVM)

end Shallot
