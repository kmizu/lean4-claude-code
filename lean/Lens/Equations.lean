import Lens.Translate

/-!
# Body extraction, primary route: equation lemmas (extractor v1)

`Lean.Meta.getEqnsFor?` returns, for structural/well-founded recursion AND
top-level pattern-matching definitions, one theorem per source alternative of
the form `∀ vars, f p₁ … pₙ = rhs` — crucially with **direct** recursive
calls in the RHS (no `brecOn`/`WellFounded.fix` decompilation needed).

We reconstruct a Scala `match`:
- argument positions where every equation has a plain variable stay ordinary
  parameters; positions with a real pattern in ANY equation become the
  (tupled) scrutinee
- `Nat.succ`-chains flatten to `Pat.natGE` (rendered as a guard case)
- equations are emitted in index order = source order = Scala's first-match
  order, so overlap hypotheses can simply be dropped
-/

namespace Lens

open Lean Meta

/-! ## Tail-recursion detection (conservative, syntactic) -/

mutual

partial def containsSelf (self : String) (e : MS.SExpr) : Bool :=
  match e with
  | .global [s] _ => s == self
  | .var _ | .lit _ | .panic _ => false
  | .global _ _ => false
  | .app f as => containsSelf self f || as.any (containsSelf self)
  | .ctorApp _ _ as | .builtin _ as => as.any (containsSelf self)
  | .lam _ b => containsSelf self b
  | .letE _ _ v b => containsSelf self v || containsSelf self b
  | .matchE s cs => containsSelf self s || cs.any (fun (_, b) => containsSelf self b)
  | .ite c t e => containsSelf self c || containsSelf self t || containsSelf self e
  | .proj _ t | .ascribe t _ => containsSelf self t

partial def tailPosOk (self : String) (e : MS.SExpr) : Bool :=
  match e with
  | .app (.global [s] _) as =>
    if s == self then as.all (fun a => !containsSelf self a)
    else !(as.any (containsSelf self))
  | .matchE s cs => !containsSelf self s && cs.all (fun (_, b) => tailPosOk self b)
  | .ite c t e => !containsSelf self c && tailPosOk self t && tailPosOk self e
  | .letE _ _ v b => !containsSelf self v && tailPosOk self b
  | .ascribe t _ => tailPosOk self t
  | e => !containsSelf self e

end

def isSelfTailRec (self : String) (body : MS.SExpr) : Bool :=
  containsSelf self body && tailPosOk self body

/-! ## The equation route -/

/-- Peel `∀`-binders structurally and return the LHS argument "shape" of one
equation: `true` = plain bound variable at that position. -/
partial def eqnShape (stmt : Expr) : ExtractM (Array Bool) := do
  let mut core := stmt
  while core.isForall do
    core := core.bindingBody!
  let some (_, lhs, _) := core.consumeMData.eq?
    | err "eqns" "equation statement is not an equality"
  return lhs.getAppArgs.map (·.isBVar)

def transDefViaEqns (dv : DefinitionVal) (eqns : Array Name) : ExtractM Unit := do
  -- Pass 1: which argument positions are pattern positions?
  let mut arity : Option Nat := none
  let mut isVar : Array Bool := #[]
  for eqn in eqns do
    let shape ← eqnShape (← getConstInfo eqn).type
    match arity with
    | none => arity := some shape.size; isVar := shape
    | some a =>
      if shape.size != a then err "eqns" "equations with inconsistent arities"
      isVar := (isVar.zip shape).map fun (x, y) => x && y
  let some nArgs := arity | err "eqns" "definition has no equations"
  let patPos := (List.range nArgs).filter fun i => !(isVar[i]!)
  if patPos.isEmpty && eqns.size != 1 then
    err "eqns" "multiple equations but no pattern positions (unexpected)"

  -- Signature from the def's own type (stable parameter names).
  forallTelescopeReducing dv.type fun xs ret => do
    if xs.size != nArgs then
      err "eqns" s!"equation arity {nArgs} ≠ signature arity {xs.size} (packed args land in v3)"
    let (tparams, sigCtx, params) ← sigParams xs
    let nT := tparams.length
    if patPos.any (· < nT) then
      err "eqns" "pattern in a type-parameter position"
    let sigNames : Array String := (params.map (·.1)).toArray
    let retTy ← transType sigCtx.tvars ret
    let name ← mangled dv.name

    -- No pattern positions: a single unfold equation (`f x y = rhs`) —
    -- covers non-recursive defs and `if`-style recursion (e.g. gcd), whose
    -- RHS carries DIRECT recursive calls (the whole point of this route).
    if patPos.isEmpty then
      let body ← forallTelescopeReducing (← getConstInfo eqns[0]!).type fun _ys core => do
        let some (_, lhs, rhs) := core.consumeMData.eq?
          | err "eqns" "equation statement is not an equality"
        let lhsArgs := lhs.getAppArgs
        if lhsArgs.size != nArgs then err "eqns" "equation LHS arity mismatch"
        let mut ctx : TCtx := {}
        for i in [0 : nArgs] do
          match lhsArgs[i]!.consumeMData with
          | .fvar id =>
            if i < nT then
              ctx := { ctx with tvars := (id, tparams[i]!) :: ctx.tvars }
            else
              ctx := { ctx with vars := (id, sigNames[i - nT]!) :: ctx.vars }
          | _ => err "eqns" "non-variable in pattern-free equation LHS"
        transTerm ctx rhs
      emit (.defn name tparams params retTy body (isSelfTailRec name body))
      return

    -- Pass 2: one Scala case per equation.
    let mut cases : List (MS.Pat × MS.SExpr) := []
    for eqn in eqns do
      let stmt := (← getConstInfo eqn).type
      let (pat, body) ← forallTelescopeReducing stmt fun _ys core => do
        let some (_, lhs, rhs) := core.consumeMData.eq?
          | err "eqns" "equation statement is not an equality"
        let lhsArgs := lhs.getAppArgs
        if lhsArgs.size != nArgs then err "eqns" "equation LHS arity mismatch"
        -- Pattern variables must not collide with pass-through signature names.
        let mut ctx : TCtx := { reserved := sigNames.toList }
        let mut pats : List MS.Pat := []
        for i in [0 : nArgs] do
          let a := lhsArgs[i]!.consumeMData
          if patPos.contains i then
            let (p, ctx') ← parsePat ctx a
            ctx := ctx'
            pats := pats ++ [p]
          else
            match a with
            | .fvar id =>
              if i < nT then
                ctx := { ctx with tvars := (id, tparams[i]!) :: ctx.tvars }
              else
                ctx := { ctx with vars := (id, sigNames[i - nT]!) :: ctx.vars }
            | _ => err "eqns" "non-variable at pass-through position"
        let pat : MS.Pat := match pats with
          | [p] => p
          | ps => .tuple ps
        pure (pat, ← transTerm ctx rhs)
      cases := cases ++ [(pat, body)]

    let scrut : MS.SExpr := match patPos with
      | [i] => .var sigNames[i - nT]!
      | is => .builtin "mkTuple" (is.map fun i => .var sigNames[i - nT]!)
    let body := MS.SExpr.matchE scrut cases
    emit (.defn name tparams params retTy body (isSelfTailRec name body))

end Lens
