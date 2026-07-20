import Lean
import Lens.Core

/-!
# Builtin mapping tables (the hand-audited part of the TCB)

Maps a *minimal* whitelist of Lean core constants onto Scala equivalents.
Everything else our code touches is either extracted as an ordinary decl or
rejected fail-loud. Semantics pinned empirically in M1 (`Shallot/Tests/Guards.lean`):

- `Nat` subtraction truncates; `Nat`/`Int` division/modulo by zero = 0 / identity
- `Int` default `/`, `%` are **Euclidean** (`ediv`/`emod`) — remainder ≥ 0.
  Scala `BigInt` `/`/`%` are T-division, so these go through `RT.intDiv`/`RT.intMod`.
-/

namespace Lens.Builtins

open Lean

/-- Coarse type discriminator for dispatching heterogeneous ops. -/
inductive Kind where
  | nat | int | str | bool | char | other
  deriving Inhabited, BEq

def kindOf (t : Expr) : Kind :=
  match t.getAppFn with
  | .const ``Nat _ => .nat
  | .const ``Int _ => .int
  | .const ``String _ => .str
  | .const ``Bool _ => .bool
  | .const ``Char _ => .char
  | _ => .other

/-- Heterogeneous-operator entry: `arity` counts ALL elaborated args
(type + instance + value); `typeArgIdx` is dispatched on; `valueArgs` are the
argument positions that become Scala operands. -/
structure OpEntry where
  arity : Nat
  typeArgIdx : Nat
  valueArgs : List Nat
  key : Kind → Option String

/-- `HAdd.hAdd : {α β γ} → [inst] → α → β → γ` and friends. -/
def hetBinOp (key : Kind → Option String) : OpEntry :=
  { arity := 6, typeArgIdx := 0, valueArgs := [4, 5], key }

/-- Plain `Nat.add : Nat → Nat → Nat`-style entry. -/
def monoBinOp (k : String) : OpEntry :=
  { arity := 2, typeArgIdx := 0, valueArgs := [0, 1], key := fun _ => some k }

def opTable : List (Name × OpEntry) :=
  [ (``HAdd.hAdd, hetBinOp fun | .nat | .int => some "add" | _ => none),
    (``HSub.hSub, hetBinOp fun | .nat => some "natSub" | .int => some "sub" | _ => none),
    (``HMul.hMul, hetBinOp fun | .nat | .int => some "mul" | _ => none),
    (``HDiv.hDiv, hetBinOp fun | .nat => some "natDiv" | .int => some "intDiv" | _ => none),
    (``HMod.hMod, hetBinOp fun | .nat => some "natMod" | .int => some "intMod" | _ => none),
    (``HAppend.hAppend, hetBinOp fun | .str => some "strAppend" | _ => none),
    (``Neg.neg, { arity := 3, typeArgIdx := 0, valueArgs := [2],
                  key := fun | .int => some "neg" | _ => none }),
    (``Nat.add, monoBinOp "add"), (``Nat.mul, monoBinOp "mul"),
    (``Nat.sub, monoBinOp "natSub"), (``Nat.div, monoBinOp "natDiv"),
    (``Nat.mod, monoBinOp "natMod"),
    (``Int.add, monoBinOp "add"), (``Int.mul, monoBinOp "mul"),
    (``Int.sub, monoBinOp "sub"),
    (``Int.ediv, monoBinOp "intDiv"), (``Int.emod, monoBinOp "intMod"),
    (``String.append, monoBinOp "strAppend") ]

def findOp (n : Name) : Option OpEntry :=
  (opTable.find? (·.1 == n)).map (·.2)

/-- Builtin TYPE heads: Lean type constant → (Scala id, expected #args). -/
def typeTable : List (Name × (MS.QualId × Nat)) :=
  [ (``List, (["List"], 1)),
    (``Option, (["Option"], 1)),
    (``Except, (["Either"], 2)) ]

def findType (n : Name) : Option (MS.QualId × Nat) :=
  (typeTable.find? (·.1 == n)).map (·.2)

/-- Builtin CONSTRUCTORS: Lean ctor → printer key.
`numParams` type params are dropped; remaining args become operands. -/
structure CtorEntry where
  numParams : Nat
  numFields : Nat
  key : String

def ctorTable : List (Name × CtorEntry) :=
  [ (``List.nil, ⟨1, 0, "nil"⟩),
    (``List.cons, ⟨1, 2, "cons"⟩),
    (``Option.none, ⟨1, 0, "none"⟩),
    (``Option.some, ⟨1, 1, "some"⟩),
    (``Except.error, ⟨2, 1, "left"⟩),
    (``Except.ok, ⟨2, 1, "right"⟩),
    (``Prod.mk, ⟨2, 2, "tuple2"⟩) ]

def findCtor (n : Name) : Option CtorEntry :=
  (ctorTable.find? (·.1 == n)).map (·.2)

end Lens.Builtins
