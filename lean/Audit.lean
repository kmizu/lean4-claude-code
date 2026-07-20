import Shallot.Basic
import Shallot.Data.RBVerify
import Shallot.Data.RBBalance
import Shallot.Lang.TypeCheckVerify
import Shallot.Lang.EvalLemmas
import Shallot.Opt.ConstFoldVerify
import Shallot.Peg.Props
import Shallot.Peg.Fuel
import Shallot.Peg.Soundness
import Shallot.Peg.Determinism
import Shallot.Peg.Completeness

/-!
# Axiom audit

Every flagship theorem must depend on nothing beyond the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — ideally fewer. `#guard_msgs`
turns any drift (a stray axiom or unproven hole) into a **build failure**,
so `lake build` itself is the audit.

Add one `#guard_msgs in #print axioms <theorem>` block per flagship theorem.
-/

/-- info: 'Shallot.hello_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.hello_length

/-! ## PEG framework (M4): T0–T3 + P1 -/

/-- info: 'Shallot.pegRun_mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.pegRun_mono

/-- info: 'Shallot.derives_suffix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.derives_suffix

/-- info: 'Shallot.pegRun_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.pegRun_sound

/-- info: 'Shallot.derives_det' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.derives_det

/-- info: 'Shallot.pegRun_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.pegRun_complete

/-! ## RBMap (M6): order theory, BST invariant, model refinement, balance -/

/-- info: 'Shallot.cmpStr_lt_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.cmpStr_lt_trans

/-- info: 'Shallot.RBNode.ordered_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.RBNode.ordered_insert

/-- info: 'Shallot.RBNode.find_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.RBNode.find_insert

/-- info: 'Shallot.RBNode.find_fromList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.RBNode.find_fromList

/-- info: 'Shallot.RBBalance.rb_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.RBBalance.rb_insert

/-! ## Typechecker (M6): soundness and completeness -/

/-- info: 'Shallot.typecheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.typecheck_sound

/-- info: 'Shallot.typecheck_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.typecheck_complete

/-- info: 'Shallot.checkProgram_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.checkProgram_sound

/-- info: 'Shallot.checkProgram_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.checkProgram_complete

/-! ## Interpreter + optimizer (M8, part 1): L4, O1, O2 -/

/-- info: 'Shallot.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.eval_mono

/-- info: 'Shallot.optExpr_hasType' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.optExpr_hasType

/-- info: 'Shallot.optExpr_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.optExpr_eval
