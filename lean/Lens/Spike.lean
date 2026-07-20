import Lean
import Lean.Compiler.LCNF

/-!
# Lens M0 API spike

Compilation of this file *is* the verification that every compiler-internal
API Lens depends on exists with the expected shape in the pinned toolchain
(v4.32.0). Version-sensitive code stays confined to `Lens/Equations.lean`,
`Lens/Matcher.lean`, `Lens/Lcnf.lean` — this spike is their early-warning
system. If a future (never mid-project) toolchain bump breaks anything, it
breaks *here* first.
-/

open Lean Meta

/-! ## Environment loading & dependency closure -/

#check @Lean.importModules
#check @Lean.initSearchPath
#check @Lean.findSysroot
example (env : Environment) (n : Name) : Option ConstantInfo := env.find? n
example (ci : ConstantInfo) : Option Expr := ci.value?
example (ci : ConstantInfo) : Expr := ci.type
example (ci : ConstantInfo) : NameSet := ci.getUsedConstantsAsSet
example (e : Expr) : Array Name := e.getUsedConstants

/-! ## Inductives & structures → Scala ADTs / case classes -/

example (iv : InductiveVal) : List Name := iv.ctors
example (iv : InductiveVal) : List Name := iv.all
example (iv : InductiveVal) : Nat := iv.numParams
example (iv : InductiveVal) : Nat := iv.numIndices
example (iv : InductiveVal) : Bool := iv.isRec
example (cv : ConstructorVal) : Name := cv.induct
example (cv : ConstructorVal) : Nat := cv.numParams
example (cv : ConstructorVal) : Nat := cv.numFields
example (cv : ConstructorVal) : Nat := cv.cidx
#check @Lean.isStructure
#check @Lean.getStructureInfo?
#check @Lean.getStructureFields
#check @Lean.getProjFnInfoForField?

/-! ## Body extraction, primary route: equation lemmas -/

#check @Lean.Meta.getEqnsFor?
#check @Lean.Meta.getUnfoldEqnFor?

/-! ## Nested matches: matcher decomposition -/

#check @Lean.Meta.matchMatcherApp?
example (m : MatcherApp) : Array Expr := m.discrs
example (m : MatcherApp) : Array Expr := m.alts
example (m : MatcherApp) : Array Expr := m.params
example (m : MatcherApp) : Expr := m.motive
example (m : MatcherApp) : Array Nat := m.altNumParams
#check @Lean.Meta.getMatcherInfo?
#check @Lean.Meta.Match.getEquationsFor
example (eqns : Lean.Meta.Match.MatchEqns) : Array Name := eqns.eqnNames

/-! ## Fallback route: LCNF (base phase) -/

#check @Lean.Compiler.LCNF.getBaseDecl?
#check @Lean.Compiler.LCNF.getMonoDecl?
#check Lean.Compiler.LCNF.Code
#check Lean.Compiler.LCNF.LetValue
#check Lean.Compiler.LCNF.LitValue
#check @Lean.Compiler.LCNF.Alt.alt

/-! ## Term-level helpers -/

#check @Lean.Meta.forallTelescopeReducing
#check @Lean.Meta.lambdaTelescope
#check @Lean.Meta.whnf
#check @Lean.Meta.isProp
#check @Lean.Meta.constructorApp?
#check @Lean.getProjectionFnInfo?
#check @Lean.Expr.isAppOf
example (env : Environment) (n : Name) : Bool := (env.find? n).any (· matches .ctorInfo _)
example (e : Expr) : Option Nat := e.nat?
