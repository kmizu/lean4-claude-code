import Lean
import Lens.Core
import Lens.Builtins

/-!
# Translation: Lean declarations → MiniScala IR (extractor v0)

v0 scope: inductives/structures (non-indexed, non-mutual) and non-recursive,
monomorphic definitions — applications, lambdas, lets, literals, constructor
applications, structure projections, whitelisted arithmetic/string primitives.

Recursion (equation route), polymorphic defs and nested `match` land in
v1/v2; until then they are rejected fail-loud with a milestone pointer.

This file will split into `Types/Inductive/Term/Closure` once the equation
route lands (M2+) and the content justifies it.
-/

namespace Lens

open Lean Meta

def tparamName (i : Nat) : String :=
  if i < 26 then String.singleton (Char.ofNat ('A'.toNat + i)) else s!"T{i}"

/-! ## Types -/

/-- Translate a Lean type into an `SType`. `tvars` maps universe-of-types
binders (from the enclosing telescope) to Scala type-parameter names. -/
partial def transType (tvars : List (FVarId × String)) (e : Expr) : ExtractM MS.SType := do
  let e := e.consumeMData
  match e with
  | .fvar id =>
    match tvars.find? (·.1 == id) with
    | some (_, n) => return .tvar n
    | none => err "type" "unbound type variable"
  | .forallE .. =>
    forallTelescopeReducing e fun xs body => do
      let mut doms : List MS.SType := []
      for x in xs do
        let ld ← x.fvarId!.getDecl
        if ld.type.isSort then
          err "type" "polymorphic function type (not supported in v0)"
        if ← Meta.isProp ld.type then
          err "type" "Prop argument in extracted function type"
        doms := doms ++ [← transType tvars ld.type]
      return .func doms (← transType tvars body)
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const c _ =>
      match c with
      | ``Nat | ``Int => expectNoArgs c args MS.SType.bigint
      | ``String => expectNoArgs c args .string
      | ``Char => expectNoArgs c args .char
      | ``Bool => expectNoArgs c args .boolean
      | ``Unit | ``PUnit => expectNoArgs c args .unit
      | ``Prod =>
        if h : args.size = 2 then
          return .tuple [← transType tvars args[0], ← transType tvars args[1]]
        else err "type" "Prod arity"
      | _ =>
        match Builtins.findType c with
        | some (qid, arity) =>
          if args.size == arity then
            return .named qid (← args.toList.mapM (transType tvars))
          else err "type" s!"builtin type {c} applied to {args.size} args (expected {arity})"
        | none =>
          match (← getEnv).find? c with
          | some (.inductInfo _) =>
            require c
            return .named [← mangled c] (← args.toList.mapM (transType tvars))
          | _ => err "type" s!"unsupported type head '{c}'"
    | _ => err "type" s!"unsupported type expression"
where
  expectNoArgs (c : Name) (args : Array Expr) (t : MS.SType) : ExtractM MS.SType :=
    if args.isEmpty then pure t
    else err "type" s!"type constant {c} unexpectedly applied"

/-! ## Inductives / structures -/

def isPropFormer (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ body => return body.isProp

def transInductive (iv : InductiveVal) : ExtractM Unit := do
  if iv.numIndices > 0 then err "inductive" "indexed inductives are not extractable"
  if iv.all.length > 1 then err "inductive" "mutual inductives land in v3"
  if iv.isUnsafe then err "inductive" "unsafe inductive"
  let sName ← mangled iv.name
  let tparams := (List.range iv.numParams).map tparamName
  let mut ctors : List (String × List (String × MS.SType)) := []
  for cn in iv.ctors do
    let cv ← getConstInfoCtor cn
    let fields ← forallTelescopeReducing cv.type fun xs _ => do
      let tvars := (List.range cv.numParams).map fun i => (xs[i]!.fvarId!, tparamName i)
      let mut fs : List (String × MS.SType) := []
      for i in [cv.numParams : xs.size] do
        let ld ← xs[i]!.fvarId!.getDecl
        if ← Meta.isProp ld.type then
          err "inductive" s!"Prop field in constructor {cn} — proof-carrying data is not extractable"
        fs := fs ++ [(Mangle.binderName ld.userName (i - cv.numParams), ← transType tvars ld.type)]
      pure fs
    ctors := ctors ++ [(Mangle.mangleLast cn, fields)]
  if isStructure (← getEnv) iv.name && ctors.length == 1 then
    emit (.caseClass sName tparams ctors.head!.2)
  else
    emit (.adt sName tparams ctors)

/-! ## Terms -/

structure TCtx where
  tvars : List (FVarId × String) := []
  vars : List (FVarId × String) := []

/-- Scala reference for a constructor: structures apply the case class
directly (`Point(...)`), ADT ctors live in the companion (`Color.red(...)`). -/
def ctorQualId (cv : ConstructorVal) : ExtractM MS.QualId := do
  let tyName ← mangled cv.induct
  if isStructure (← getEnv) cv.induct then
    return [tyName]
  else
    return [tyName, Mangle.mangleLast cv.name]

mutual

partial def transTerm (ctx : TCtx) (e : Expr) : ExtractM MS.SExpr := do
  match e.consumeMData with
  | .lit (.natVal n) => return .lit (.int n)
  | .lit (.strVal s) => return .lit (.str s)
  | .fvar id =>
    match ctx.vars.find? (·.1 == id) with
    | some (_, n) => return .var n
    | none => err "term" "unbound variable in term position"
  | .lam .. =>
    lambdaTelescope (e.consumeMData) fun xs body => do
      let mut ctx := ctx
      let mut params : List (String × MS.SType) := []
      for x in xs do
        let ld ← x.fvarId!.getDecl
        if ld.type.isSort then err "term" "type-lambda (polymorphism lands in v1)"
        if ← Meta.isProp ld.type then err "term" "proof-lambda in executable code"
        let n := Mangle.binderName ld.userName (← freshName)
        ctx := { ctx with vars := (x.fvarId!, n) :: ctx.vars }
        params := params ++ [(n, ← transType ctx.tvars ld.type)]
      return .lam params (← transTerm ctx body)
  | .letE nm t v b _ =>
    let v' ← transTerm ctx v
    let t' ← transType ctx.tvars t
    withLetDecl nm t v fun fv => do
      let n := Mangle.binderName nm (← freshName)
      let ctx := { ctx with vars := (fv.fvarId!, n) :: ctx.vars }
      return .letE n (some t') v' (← transTerm ctx (b.instantiate1 fv))
  | .proj tyName idx s =>
    let some si := getStructureInfo? (← getEnv) tyName
      | err "term" s!"primitive projection on non-structure {tyName}"
    let some fname := si.fieldNames[idx]?
      | err "term" "projection index out of range"
    return .proj (Mangle.sanitizeSegment fname.toString) (← transTerm ctx s)
  | .app .. => transApp ctx (e.consumeMData)
  | .const .. => transApp ctx (e.consumeMData)
  | _ => err "term" "unsupported term shape"

partial def transApp (ctx : TCtx) (e : Expr) : ExtractM MS.SExpr := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .fvar _ => return mkApp' (← transTerm ctx fn) (← args.toList.mapM (transTerm ctx))
  | .lam .. => transTerm ctx e.headBeta
  | .const c _ =>
    -- 1. literal folding
    if c == ``OfNat.ofNat then
      if h : args.size = 3 then
        match args[1].consumeMData with
        | .lit (.natVal n) =>
          match Builtins.kindOf args[0] with
          | .nat | .int => return .lit (.int n)
          | _ => err "term" "OfNat on unsupported type"
        | _ => err "term" "non-literal OfNat application"
      else err "term" "partially applied OfNat"
    else if c == ``Bool.true && args.isEmpty then return .lit (.bool true)
    else if c == ``Bool.false && args.isEmpty then return .lit (.bool false)
    else if c == ``Unit.unit && args.isEmpty then return .lit .unit
    else if c == ``ite then
      if h : args.size = 5 then
        return .ite (← transDecInst ctx args[2]) (← transTerm ctx args[3]) (← transTerm ctx args[4])
      else err "term" "unsupported ite arity"
    else
    -- 2. whitelisted operators
    match Builtins.findOp c with
    | some entry =>
      if args.size < entry.arity then
        err "term" s!"partially applied builtin operator {c}"
      else
        let some key := entry.key (Builtins.kindOf args[entry.typeArgIdx]!)
          | err "term" s!"operator {c} at unsupported operand type"
        let operands ← entry.valueArgs.mapM fun i => transTerm ctx args[i]!
        return mkApp' (.builtin key operands) (← (args.toList.drop entry.arity).mapM (transTerm ctx))
    | none =>
    -- 3. builtin container constructors
    match Builtins.findCtor c with
    | some ce =>
      if args.size == ce.numParams + ce.numFields then
        let operands ← (args.toList.drop ce.numParams).mapM (transTerm ctx)
        return .builtin ce.key operands
      else err "term" s!"partially applied builtin constructor {c}"
    | none =>
    -- 4. environment dispatch
    match (← getEnv).find? c with
    | some (.ctorInfo cv) =>
      if args.size < cv.numParams + cv.numFields then
        err "term" s!"partially applied constructor {c} (eta-expansion lands in v1)"
      else
        require cv.induct
        let targs ← (args.toList.take cv.numParams).mapM (transType ctx.tvars)
        let fields ← ((args.toList.drop cv.numParams).take cv.numFields).mapM (transTerm ctx)
        let extra ← (args.toList.drop (cv.numParams + cv.numFields)).mapM (transTerm ctx)
        let qid ← ctorQualId cv
        return mkApp' (.ctorApp qid targs fields) extra
    | some (.defnInfo dv) => do
      match ← getProjectionFnInfo? c with
      | some pinfo =>
        if pinfo.fromClass then
          err "term" s!"typeclass projection '{c}' is not whitelisted"
        else if args.size ≤ pinfo.numParams then
          err "term" s!"partially applied projection {c}"
        else
          let struct ← transTerm ctx args[pinfo.numParams]!
          let extra ← (args.toList.drop (pinfo.numParams + 1)).mapM (transTerm ctx)
          return mkApp' (.proj (Mangle.mangleLast c) struct) extra
      | none =>
        if ← Meta.isProp dv.type then
          err "term" s!"proof constant '{c}' in executable code"
        else if ← hasTypeParams dv.type then
          err "term" s!"polymorphic definition '{c}' (lands in v1)"
        else
          require c
          return mkApp' (.global [← mangled c] []) (← args.toList.mapM (transTerm ctx))
    | some (.thmInfo _) => err "term" s!"theorem '{c}' leaked into executable code"
    | some _ => err "term" s!"unsupported constant '{c}'"
    | none => err "term" s!"unknown constant '{c}'"
  | _ => err "term" "unsupported application head"
where
  mkApp' (base : MS.SExpr) (extra : List MS.SExpr) : MS.SExpr :=
    if extra.isEmpty then base else .app base extra
  hasTypeParams (ty : Expr) : ExtractM Bool :=
    forallTelescopeReducing ty fun xs _ => do
      for x in xs do
        if (← x.fvarId!.getDecl).type.isSort then return true
      return false

/-- Translate a `Decidable` instance term (the instance argument of `ite`)
into the Boolean expression it decides. Whitelisted instances only. -/
partial def transDecInst (ctx : TCtx) (inst : Expr) : ExtractM MS.SExpr := do
  let inst := inst.consumeMData
  let fn := inst.getAppFn
  let args := inst.getAppArgs
  match fn with
  | .const c _ =>
    match Builtins.findDecInst c with
    | some key =>
      if h : args.size = 2 then
        return .builtin key [← transTerm ctx args[0], ← transTerm ctx args[1]]
      else err "term" s!"Decidable instance '{c}' applied to {args.size} args (expected 2)"
    | none => err "term" s!"Decidable instance '{c}' is not whitelisted — use a hand-written beq"
  | _ => err "term" "unsupported Decidable instance shape"

end

/-! ## Definitions -/

def recursionMarkers (e : Expr) : List Name :=
  e.getUsedConstants.toList.filter fun n =>
    n == ``WellFounded.fix ||
    (match n with
     | .str _ s => s == "brecOn" || s == "rec"
     | _ => false)

def transDef (dv : DefinitionVal) : ExtractM Unit := do
  let markers := recursionMarkers dv.value
  if !markers.isEmpty then
    err "def" s!"recursive definition (via {markers}) — the equation route lands in v1"
  forallTelescopeReducing dv.type fun xs ret => do
    let mut ctx : TCtx := {}
    let mut params : List (String × MS.SType) := []
    for x in xs do
      let ld ← x.fvarId!.getDecl
      if ld.type.isSort then
        err "def" "polymorphic definition (lands in v1)"
      if ← Meta.isProp ld.type then
        err "def" "Prop parameter in extracted definition"
      let n := Mangle.binderName ld.userName (← freshName)
      ctx := { ctx with vars := (x.fvarId!, n) :: ctx.vars }
      params := params ++ [(n, ← transType ctx.tvars ld.type)]
    let retTy ← transType ctx.tvars ret
    let body := (mkAppN dv.value xs).headBeta
    emit (.defn (← mangled dv.name) [] params retTy (← transTerm ctx body) false)

end Lens
