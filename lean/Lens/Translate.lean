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
          | some (.defnInfo _) =>
            -- type abbreviation (e.g. `abbrev Sig := List …`): unfold
            match ← unfoldDefinition? e with
            | some e' => transType tvars e'
            | none => err "type" s!"unsupported type head '{c}' (non-unfoldable definition)"
          | _ => err "type" s!"unsupported type head '{c}'"
    | _ => err "type" s!"unsupported type expression"
where
  expectNoArgs (c : Name) (args : Array Expr) (t : MS.SType) : ExtractM MS.SType :=
    if args.isEmpty then pure t
    else err "type" s!"type constant {c} unexpectedly applied"

/-! ## Inductives / structures -/

def isPropFormer (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ body => return body.isProp

/-- Translate ONE inductive (possibly a member of a mutual block). -/
def transInductiveOne (iv : InductiveVal) : ExtractM Unit := do
  if iv.numIndices > 0 then err "inductive" "indexed inductives are not extractable"
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

/-- Translate a whole (possibly mutual) inductive block. Each member is
emitted once; siblings are marked seen so their queue entries no-op. -/
def transInductive (iv : InductiveVal) : ExtractM Unit := do
  for n in iv.all do
    let already := (← get).seen.find? n == some .emitted
    if !already then
      markSeen n .emitted
      transInductiveOne (← getConstInfoInduct n)

/-! ## Terms -/

structure TCtx where
  tvars : List (FVarId × String) := []
  vars : List (FVarId × String) := []
  /-- Names that locals must not collide with (e.g. signature parameter
  names when translating equation RHSs). -/
  reserved : List String := []

def TCtx.hasName (ctx : TCtx) (s : String) : Bool :=
  ctx.reserved.contains s || ctx.vars.any (·.2 == s) || ctx.tvars.any (·.2 == s)

/-- Pick a name not already bound in scope (capture avoidance, review
finding #1: distinct Lean binders must never conflate to one Scala name). -/
partial def pickName (ctx : TCtx) (base : String) : String :=
  if !ctx.hasName base then base else go 1
where
  go (i : Nat) : String :=
    let cand := s!"{base}_{i}"
    if ctx.hasName cand then go (i + 1) else cand

/-- Bind a local variable with a collision-free name. -/
def pushVar (ctx : TCtx) (id : FVarId) (userName : Name) : ExtractM (String × TCtx) := do
  let base := Mangle.binderName userName (← freshName)
  let n := pickName ctx base
  return (n, { ctx with vars := (id, n) :: ctx.vars })

/-- Scala reference for a constructor: structures apply the case class
directly (`Point(...)`), ADT ctors live in the companion (`Color.red(...)`). -/
def ctorQualId (cv : ConstructorVal) : ExtractM MS.QualId := do
  let tyName ← mangled cv.induct
  if isStructure (← getEnv) cv.induct then
    return [tyName]
  else
    return [tyName, Mangle.mangleLast cv.name]

/-! ## Patterns (shared by the equation route and matcher decomposition) -/

/-- Builtin-container constructor patterns use reserved `$`-ids; the printer
renders them as native Scala patterns (`::`/`Nil`/`Some`/`None`/…). -/
def builtinPatId (c : Name) : Option (MS.QualId × Nat) :=
  if c == ``List.cons then some (["$cons"], 1)
  else if c == ``List.nil then some (["$nil"], 1)
  else if c == ``Option.some then some (["$some"], 1)
  else if c == ``Option.none then some (["$none"], 1)
  else if c == ``Except.error then some (["$left"], 2)
  else if c == ``Except.ok then some (["$right"], 2)
  else none

/-- Flatten a `Nat.succ`-chain pattern. Returns `none` if `e` isn't one. -/
partial def flattenNatPat (ctx : TCtx) (k : Nat) (e : Expr) :
    ExtractM (Option (MS.Pat × TCtx)) := do
  let e := e.consumeMData
  match e with
  | .fvar id =>
    if k == 0 then return none -- plain variable, handled by the caller
    let ld ← id.getDecl
    let (n, ctx') ← pushVar ctx id ld.userName
    return some (.natGE k (some n), ctx')
  | .lit (.natVal n) => return some (.lit (.int (n + k)), ctx)
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const ``Nat.succ _ =>
      if h : args.size = 1 then flattenNatPat ctx (k + 1) args[0]
      else return none
    | .const ``Nat.zero _ =>
      if args.isEmpty then return some (.lit (.int k), ctx) else return none
    | .const ``OfNat.ofNat _ =>
      if h : args.size = 3 then
        match args[1].consumeMData with
        | .lit (.natVal n) => return some (.lit (.int (n + k)), ctx)
        | _ => return none
      else return none
    | _ => return none

/-- Parse one constructor-pattern expression into a pattern, binding its
variables capture-free. -/
partial def parsePat (ctx : TCtx) (e : Expr) : ExtractM (MS.Pat × TCtx) := do
  let e := e.consumeMData
  if let some r ← flattenNatPat ctx 0 e then return r
  match e with
  | .fvar id =>
    let ld ← id.getDecl
    let (n, ctx') ← pushVar ctx id ld.userName
    return (.var n, ctx')
  | .lit (.natVal n) => return (.lit (.int n), ctx)
  | .lit (.strVal s) => return (.lit (.str s), ctx)
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const c _ =>
      if c == ``Bool.true && args.isEmpty then return (.lit (.bool true), ctx)
      if c == ``Bool.false && args.isEmpty then return (.lit (.bool false), ctx)
      let subPats (ctx : TCtx) (numParams : Nat) : ExtractM (List MS.Pat × TCtx) := do
        let mut ctx := ctx
        let mut pats : List MS.Pat := []
        for i in [numParams : args.size] do
          let (p, ctx') ← parsePat ctx args[i]!
          ctx := ctx'
          pats := pats ++ [p]
        return (pats, ctx)
      if c == ``Prod.mk && args.size == 4 then
        let (pats, ctx) ← subPats ctx 2
        return (.tuple pats, ctx)
      match builtinPatId c with
      | some (qid, numParams) =>
        let (pats, ctx) ← subPats ctx numParams
        return (.ctor qid pats, ctx)
      | none =>
      match (← getEnv).find? c with
      | some (.ctorInfo cv) =>
        require cv.induct
        let (pats, ctx) ← subPats ctx cv.numParams
        return (.ctor (← ctorQualId cv) pats, ctx)
      | _ => err "pattern" s!"unsupported pattern head '{c}'"
    | _ => err "pattern" "unsupported pattern shape"

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
        let (n, ctx') ← pushVar ctx x.fvarId! ld.userName
        ctx := ctx'
        params := params ++ [(n, ← transType ctx.tvars ld.type)]
      return .lam params (← transTerm ctx body)
  | .letE nm t v b _ =>
    let v' ← transTerm ctx v
    let t' ← transType ctx.tvars t
    withLetDecl nm t v fun fv => do
      let (n, ctx) ← pushVar ctx fv.fvarId! nm
      return .letE n (some t') v' (← transTerm ctx (b.instantiate1 fv))
  | .proj tyName idx s =>
    if tyName == ``Prod then
      return .builtin (if idx == 0 then "fst" else "snd") [← transTerm ctx s]
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
        if !Builtins.isCanonicalInst (← getEnv) args[2] then
          err "term" s!"non-canonical OfNat instance — custom numeral semantics are not extractable"
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
    else if c == ``Char.ofNat then
      if h : args.size = 1 then
        match args[0].consumeMData with
        | .lit (.natVal n) => return .lit (.char n)
        | _ => err "term" "non-literal Char.ofNat (dynamic Char construction is not extractable)"
      else err "term" "Char.ofNat arity"
    else if c == ``ite then
      if h : args.size = 5 then
        return .ite (← transDecInst ctx args[2]) (← transTerm ctx args[3]) (← transTerm ctx args[4])
      else err "term" "unsupported ite arity"
    else if c == ``Decidable.decide then
      if h : args.size = 2 then
        transDecInst ctx args[1]
      else err "term" "unsupported decide arity"
    else
    -- 2. whitelisted operators
    match Builtins.findOp c with
    | some entry =>
      if args.size < entry.arity then
        err "term" s!"partially applied builtin operator {c}"
      else
        let some key := entry.key (Builtins.kindOf args[entry.typeArgIdx]!)
          | err "term" s!"operator {c} at unsupported operand type"
        if let some ii := entry.instArgIdx then
          if !Builtins.isCanonicalInst (← getEnv) args[ii]! then
            err "term" s!"non-canonical instance for operator {c} — only core instances get builtin semantics"
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
    -- 4. nested `match` (compiler-generated matcher functions)
    if (← getMatcherInfo? c).isSome then
      transMatcher ctx e
    else
    -- 5. environment dispatch
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
          -- Prod projections map to Scala tuple accessors, not field names.
          if pinfo.ctorName == ``Prod.mk then
            let key := if pinfo.i == 0 then "fst" else "snd"
            return mkApp' (.builtin key [struct]) extra
          else
            return mkApp' (.proj (Mangle.mangleLast c) struct) extra
      | none =>
        if ← Meta.isProp dv.type then
          err "term" s!"proof constant '{c}' in executable code"
        else
          let nT ← countLeadingTypeParams dv.type
          if args.size < nT then
            err "term" s!"partially applied polymorphic definition '{c}'"
          require c
          let targs ← (args.toList.take nT).mapM (transType ctx.tvars)
          let rest ← (args.toList.drop nT).mapM (transTerm ctx)
          return mkApp' (.global [← mangled c] targs) rest
    | some (.thmInfo _) => err "term" s!"theorem '{c}' leaked into executable code"
    | some _ => err "term" s!"unsupported constant '{c}'"
    | none => err "term" s!"unknown constant '{c}'"
  | _ => err "term" "unsupported application head"
where
  mkApp' (base : MS.SExpr) (extra : List MS.SExpr) : MS.SExpr :=
    if extra.isEmpty then base else .app base extra
  /-- Count PREFIX type binders; non-prefix polymorphism is fail-loud. -/
  countLeadingTypeParams (ty : Expr) : ExtractM Nat :=
    forallTelescopeReducing ty fun xs _ => do
      let mut n := 0
      let mut valueSeen := false
      for x in xs do
        if (← x.fvarId!.getDecl).type.isSort then
          if valueSeen then err "term" "type parameter after a value parameter"
          n := n + 1
        else
          valueSeen := true
      return n

/-- Decompose a matcher application (`f.match_N params motive discrs alts`)
into a Scala `match` (extractor v2, the review-flagged risk item).

Constructor identity per alternative comes from the matcher's own
match-equations (`Match.getEquationsFor`): equation `i`'s LHS carries the
constructor patterns in discriminant positions, and its RHS `altᵢ v₁ … v_k`
fixes the order in which pattern variables feed the alternative — we bind
OUR alt-lambda's binders to those pattern-variable names positionally. -/
partial def transMatcher (ctx : TCtx) (e : Expr) : ExtractM MS.SExpr := do
  let some mApp ← matchMatcherApp? e
    | err "match" "matcher application failed to decompose"
  let discrs ← mApp.discrs.toList.mapM (transTerm ctx)
  let scrut : MS.SExpr := match discrs with
    | [d] => d
    | ds => .builtin "mkTuple" ds
  let eqns ← Lean.Meta.Match.getEquationsFor mApp.matcherName
  if eqns.eqnNames.size != mApp.alts.size then
    err "match" s!"match-equation count {eqns.eqnNames.size} ≠ alt count {mApp.alts.size} (overlapping patterns land in v3)"
  let mut cases : List (MS.Pat × MS.SExpr) := []
  for i in [0 : mApp.alts.size] do
    let eqnStmt := (← getConstInfo eqns.eqnNames[i]!).type
    let (pat, argNames) ← forallTelescopeReducing eqnStmt fun _ys core => do
      let some (_, lhs, rhs) := core.consumeMData.eq?
        | err "match" "match equation is not an equality"
      let lhsArgs := lhs.getAppArgs
      if lhsArgs.size < mApp.discrs.size + mApp.alts.size then
        err "match" "match equation LHS arity too small"
      let discrStart := lhsArgs.size - mApp.alts.size - mApp.discrs.size
      let mut pctx : TCtx := ctx
      let mut pats : List MS.Pat := []
      for j in [0 : mApp.discrs.size] do
        let (p, pctx') ← parsePat pctx lhsArgs[discrStart + j]!
        pctx := pctx'
        pats := pats ++ [p]
      let pat : MS.Pat := match pats with
        | [p] => p
        | ps => .tuple ps
      -- RHS args: pattern variables, or `Unit.unit` for field-less
      -- alternatives (the compiler gives those a unit-thunk parameter).
      let names ← rhs.consumeMData.getAppArgs.toList.mapM fun a => do
        match a.consumeMData with
        | .fvar id =>
          match pctx.vars.find? (·.1 == id) with
          | some (_, n) => pure (some n)
          | none => err "match" "match-equation RHS variable not bound by any pattern"
        | .const c _ =>
          if c == ``Unit.unit || c == ``PUnit.unit then pure none
          else err "match" s!"unexpected constant '{c}' in match-equation RHS (overlap hypotheses land in v3)"
        | _ => err "match" "non-variable in match-equation RHS (overlap hypotheses land in v3)"
      pure (pat, names)
    let altBody ← lambdaBoundedTelescope mApp.alts[i]! argNames.length fun xs body => do
      if xs.size != argNames.length then
        err "match" s!"alt {i} binder count {xs.size} ≠ pattern variable count {argNames.length}"
      let mut actx := ctx
      for (x, n?) in xs.toList.zip argNames do
        match n? with
        | some n => actx := { actx with vars := (x.fvarId!, n) :: actx.vars }
        | none =>
          -- unit-thunk binder: never referenced by the body, bind a dummy
          let (_, actx') ← pushVar actx x.fvarId! Name.anonymous
          actx := actx'
      transTerm actx body
    cases := cases ++ [(pat, altBody)]
  let base := MS.SExpr.matchE scrut cases
  let extra ← mApp.remaining.toList.mapM (transTerm ctx)
  return if extra.isEmpty then base else .app base extra

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

/-- Split a definition's telescope into leading type parameters (Sort
binders → Scala tparams) and value parameters. Sort binders after a value
binder are rejected (non-prefix polymorphism). -/
def sigParams (xs : Array Expr) : ExtractM (List String × TCtx × List (String × MS.SType)) := do
  let mut ctx : TCtx := {}
  let mut tparams : List String := []
  let mut params : List (String × MS.SType) := []
  for x in xs do
    let ld ← x.fvarId!.getDecl
    if ld.type.isSort then
      if !params.isEmpty then
        err "def" "type parameter after a value parameter (non-prefix polymorphism)"
      let tn := tparamName tparams.length
      tparams := tparams ++ [tn]
      ctx := { ctx with tvars := (x.fvarId!, tn) :: ctx.tvars }
    else if ← Meta.isProp ld.type then
      err "def" "Prop parameter in extracted definition"
    else
      let (n, ctx') ← pushVar ctx x.fvarId! ld.userName
      ctx := ctx'
      params := params ++ [(n, ← transType ctx.tvars ld.type)]
  return (tparams, ctx, params)

def transDef (dv : DefinitionVal) : ExtractM Unit := do
  let markers := recursionMarkers dv.value
  if !markers.isEmpty then
    err "def" s!"recursive definition (via {markers}) — the equation route lands in v1"
  forallTelescopeReducing dv.type fun xs ret => do
    let (tparams, ctx, params) ← sigParams xs
    let retTy ← transType ctx.tvars ret
    let body := (mkAppN dv.value xs).headBeta
    emit (.defn (← mangled dv.name) tparams params retTy (← transTerm ctx body) false)

end Lens
