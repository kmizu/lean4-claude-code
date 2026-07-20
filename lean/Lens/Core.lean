import Lean
import Lens.MiniScala
import Lens.Mangle

/-!
# Extraction monad, error accumulation, work queue

Fail-loud policy: every unsupported construct produces a `LensError` naming
the declaration, phase and offender. Errors are accumulated per declaration
(translation of one decl aborts on its first error; the driver continues with
the other decls) and the driver refuses to write ANY output if the error list
is nonempty.
-/

namespace Lens

open Lean

structure LensError where
  declName : Name
  phase : String
  msg : String
  deriving Inhabited

def LensError.render (e : LensError) : String :=
  s!"lens: [{e.phase}] {e.declName}: {e.msg}"

structure Config where
  pkg : String := "shallot.gen"
  stripPrefix : Name := `Shallot
  deriving Inhabited

inductive DeclResult where
  /-- Translation in progress (cycle breaker) or produced a decl. -/
  | pending
  | emitted
  | builtinRef
  | skipped
  deriving Inhabited, BEq

structure ExtractState where
  cfg : Config
  /-- Classification of every name seen so far (cycle breaker included). -/
  seen : NameMap DeclResult := {}
  /-- Work queue (BFS, deterministic). -/
  queue : Array Name := #[]
  /-- Successfully translated decls, in completion order. -/
  out : Array MS.SDecl := #[]
  errors : Array LensError := #[]
  /-- Fresh-name counter for anonymous binders (per-decl, reset by driver). -/
  fresh : Nat := 0
  /-- Decl currently being translated (for error attribution). -/
  current : Name := .anonymous
  deriving Inhabited

abbrev ExtractM := StateT ExtractState MetaM

/-- Abort translation of the current decl with a fail-loud error. -/
def err {α} (phase msg : String) : ExtractM α := do
  let cur := (← get).current
  throwError "lens-decl-error: [{phase}] {cur}: {msg}"

def recordError (declName : Name) (phase msg : String) : ExtractM Unit :=
  modify fun s => { s with errors := s.errors.push ⟨declName, phase, msg⟩ }

/-- Enqueue a name for translation unless already processed/queued. -/
def require (n : Name) : ExtractM Unit := do
  let s ← get
  if s.seen.contains n then return ()
  modify fun s => { s with seen := s.seen.insert n .pending, queue := s.queue.push n }

def markSeen (n : Name) (r : DeclResult) : ExtractM Unit :=
  modify fun s => { s with seen := s.seen.insert n r }

def emit (d : MS.SDecl) : ExtractM Unit :=
  modify fun s => { s with out := s.out.push d }

def freshName : ExtractM Nat := do
  let s ← get
  set { s with fresh := s.fresh + 1 }
  return s.fresh

def mangled (n : Name) : ExtractM String := do
  return Mangle.mangle (← get).cfg.stripPrefix n

end Lens
