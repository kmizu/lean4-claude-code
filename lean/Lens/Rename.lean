import Lens.MiniScala
import Lens.Mangle

/-!
# Capture-protection rename pass (review findings #2/#3/#5)

Runs on the assembled `SModule` before printing, when the full set of
top-level names is known. Renames any LOCAL binder (def param, lambda param,
`val`, pattern variable, `natGE` bind) whose name would capture:
- a top-level generated definition (`.global` refs are printed bare),
- the runtime alias `RT` or a Scala/Java built-in from `Mangle.denyList`,
- a printer guard name (`_g<digits>`, allocated later during rendering).

`.var` occurrences are rewritten through a scoped environment; `.global`
references are untouched. Local–local conflation is prevented earlier, at
translate time (`pushVar`) — this pass is the local-vs-global half plus a
defensive re-check.
-/

namespace Lens.Rename

open Lens.MS

def isGuardName (s : String) : Bool :=
  s.length > 2 && s.startsWith "_g" && (s.toList.drop 2).all (·.isDigit)

def bad (forbidden scope : List String) (s : String) : Bool :=
  forbidden.contains s || isGuardName s || scope.contains s

partial def pick (forbidden scope : List String) (base : String) : String :=
  if !bad forbidden scope base then base else go 1
where
  go (i : Nat) : String :=
    let cand := s!"{base}_{i}"
    if bad forbidden scope cand then go (i + 1) else cand

/-- Scoped renaming environment: `(old, new)` pairs, innermost first. -/
abbrev Env := List (String × String)

mutual

partial def rnExpr (fb : List String) (env : Env) (scope : List String) :
    SExpr → SExpr
  | .var n => .var ((env.find? (·.1 == n)).map (·.2) |>.getD n)
  | .global i t => .global i t
  | .lit l => .lit l
  | .app f as => .app (rnExpr fb env scope f) (as.map (rnExpr fb env scope))
  | .ctorApp i t as => .ctorApp i t (as.map (rnExpr fb env scope))
  | .lam ps b =>
    let (ps', env', scope') := rnParams fb env scope ps
    .lam ps' (rnExpr fb env' scope' b)
  | .letE n ty v b =>
    let v' := rnExpr fb env scope v
    let n' := pick fb scope n
    .letE n' ty v' (rnExpr fb ((n, n') :: env) (n' :: scope) b)
  | .matchE s cs =>
    .matchE (rnExpr fb env scope s) (cs.map fun (p, b) =>
      let (p', env', scope') := rnPat fb env scope p
      (p', rnExpr fb env' scope' b))
  | .ite c t e => .ite (rnExpr fb env scope c) (rnExpr fb env scope t) (rnExpr fb env scope e)
  | .proj f t => .proj f (rnExpr fb env scope t)
  | .ascribe e ty => .ascribe (rnExpr fb env scope e) ty
  | .panic m => .panic m
  | .builtin k as => .builtin k (as.map (rnExpr fb env scope))

partial def rnParams (fb : List String) (env : Env) (scope : List String) :
    List (String × SType) → (List (String × SType) × Env × List String)
  | [] => ([], env, scope)
  | (n, t) :: rest =>
    let n' := pick fb scope n
    let (rest', env', scope') := rnParams fb ((n, n') :: env) (n' :: scope) rest
    ((n', t) :: rest', env', scope')

partial def rnPat (fb : List String) (env : Env) (scope : List String) :
    Pat → (Pat × Env × List String)
  | .var n =>
    let n' := pick fb scope n
    (.var n', (n, n') :: env, n' :: scope)
  | .natGE k (some n) =>
    let n' := pick fb scope n
    (.natGE k (some n'), (n, n') :: env, n' :: scope)
  | .ctor id args =>
    let (args', env', scope') := rnPatList fb env scope args
    (.ctor id args', env', scope')
  | .tuple args =>
    let (args', env', scope') := rnPatList fb env scope args
    (.tuple args', env', scope')
  | p => (p, env, scope)

partial def rnPatList (fb : List String) (env : Env) (scope : List String) :
    List Pat → (List Pat × Env × List String)
  | [] => ([], env, scope)
  | p :: rest =>
    let (p', env', scope') := rnPat fb env scope p
    let (rest', env'', scope'') := rnPatList fb env' scope' rest
    (p' :: rest', env'', scope'')

end

def rnDecl (fb : List String) : SDecl → SDecl
  | .defn name tps params ret body tr =>
    let (params', env, scope) := rnParams fb [] [] params
    .defn name tps params' ret (rnExpr fb env scope body) tr
  | d => d

/-- Entry point: protect all module-level names from local capture. -/
def protect (m : SModule) : SModule :=
  let fb := m.decls.map (·.name) ++ "RT" :: Mangle.denyList
  { m with decls := m.decls.map (rnDecl fb) }

end Lens.Rename
