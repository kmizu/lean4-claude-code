import Shallot.Lang.Eval

/-!
# Stack VM — structured control

A genuine stack machine (operand stack, positional locals, call-by-name
code table) with STRUCTURED control: `branch` carries its arm code and
sequencing is list-append, `call` runs the callee on a fresh operand stack
and expects a singleton result. No program counters, no jump targets — the
plan's pre-approved R1 design that keeps the M10 simulation proof at L
difficulty instead of XL, while remaining a faithful compilation target
(the JVM itself is a structured-control stack machine at the bytecode
verifier's level of abstraction).

Fuel conventions as everywhere: `none` = fuel only; `stuckVM` errors are
excluded on compiled well-typed code by V1/V2 (M10).
-/

namespace Shallot

inductive Instr where
  | pushI (n : Int)
  | pushB (b : Bool)
  /-- Push the value of local slot `i` (0 = innermost binding). -/
  | load (i : Nat)
  /-- Pop the stack top and cons it onto the locals. -/
  | bind
  /-- Drop the innermost local. -/
  | unbind
  | unop (op : UnOp)
  /-- Pops right operand first (it is on top), then left. -/
  | binop (op : BinOp)
  /-- Pop a Bool; run the corresponding arm, then continue. -/
  | branch (thenC elseC : List Instr)
  /-- Pop `arity` argument values, run `f`'s code on an empty stack with
  the arguments as locals, push its singleton result. -/
  | call (f : String) (arity : Nat)
  /-- Compiler-emitted for unreachable paths (unbound variables on
  untypechecked input); always faults with `stuckVM`. -/
  | crash

def valAt : List Value → Nat → Option Value
  | [], _ => none
  | v :: _, 0 => some v
  | _ :: rest, i + 1 => valAt rest i

/-- Pop `n` values; returns them in PUSH order (first-pushed first — exactly
parameter order for calls) together with the remaining stack. -/
def popN : Nat → List Value → List Value → Option (List Value × List Value)
  | 0, stack, acc => some (acc, stack)
  | _ + 1, [], _ => none
  | n + 1, v :: stack, acc => popN n stack (v :: acc)

/-- Run `code` to completion. Result: the final operand stack. -/
def vmRun (ct : RBNode (List Instr)) :
    Nat → List Instr → List Value → List Value → Option (Except RtErr (List Value))
  | 0, _, _, _ => none
  | _ + 1, [], stack, _ => some (.ok stack)
  | fuel + 1, i :: rest, stack, locals =>
    match i with
    | .pushI n => vmRun ct fuel rest (.vint n :: stack) locals
    | .pushB b => vmRun ct fuel rest (.vbool b :: stack) locals
    | .load idx =>
      match valAt locals idx with
      | some v => vmRun ct fuel rest (v :: stack) locals
      | none => some (.error .stuckVM)
    | .bind =>
      match stack with
      | v :: st => vmRun ct fuel rest st (v :: locals)
      | [] => some (.error .stuckVM)
    | .unbind =>
      match locals with
      | _ :: ls => vmRun ct fuel rest stack ls
      | [] => some (.error .stuckVM)
    | .unop op =>
      match stack with
      | v :: st =>
        match evalUnOp op v with
        | .ok v' => vmRun ct fuel rest (v' :: st) locals
        | .error er => some (.error er)
      | [] => some (.error .stuckVM)
    | .binop op =>
      match stack with
      | b :: a :: st =>
        match evalBinOp op a b with
        | .ok v' => vmRun ct fuel rest (v' :: st) locals
        | .error er => some (.error er)
      | _ => some (.error .stuckVM)
    | .branch thenC elseC =>
      match stack with
      | .vbool b :: st =>
        vmRun ct fuel ((if b = true then thenC else elseC) ++ rest) st locals
      | _ => some (.error .stuckVM)
    | .crash => some (.error .stuckVM)
    | .call f arity =>
      match RBNode.find? ct f with
      | none => some (.error (.stuckFun f))
      | some code =>
        match popN arity stack [] with
        | none => some (.error .stuckVM)
        | some (args, st) =>
          match vmRun ct fuel code [] args with
          | none => none
          | some (.error er) => some (.error er)
          | some (.ok [v]) => vmRun ct fuel rest (v :: st) locals
          | some (.ok _) => some (.error .stuckVM)

end Shallot
