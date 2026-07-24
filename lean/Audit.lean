import Shallot.Basic
import Shallot.Data.RBVerify
import Shallot.Data.RBBalance
import Shallot.Lang.TypeCheckVerify
import Shallot.Lang.EvalLemmas
import Shallot.Opt.ConstFoldVerify
import Shallot.Lang.TypeSound
import Shallot.Vm.Correct
import Shallot.Syntax.Roundtrip
import Json.Roundtrip
import Shallot.Peg.Props
import Shallot.Peg.Fuel
import Shallot.Peg.Soundness
import Shallot.Peg.Determinism
import Shallot.Peg.Completeness
import Shallot.Peg.Examples
import Shallot.Peg.Palindrome
import Shallot.Peg.PowerTwoHelper
import Shallot.Peg.PalindromeEpsFirst
import Shallot.Peg.PalindromeEpsMiddle
import Shallot.Peg.PalindromeAllOrders
import Shallot.Peg.MidPoint
import Shallot.Peg.MidPointGeneral
import MacroPeg
import Cfg

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

/-! ## Type soundness + program-level optimizer preservation (M8, part 2) -/

/-- info: 'Shallot.eval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.eval_sound

/-- info: 'Shallot.runProgram_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.runProgram_sound

/-- info: 'Shallot.optProgram_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.optProgram_run

/-! ## Compiler correctness (M10) — the flagship -/

/-- info: 'Shallot.vmRun_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.vmRun_mono

/-- info: 'Shallot.compile_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.compile_sim

/-- info: 'Shallot.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.compile_correct

/-! ## Parser roundtrip + pipeline composition (M11) — the closing theorems -/

/-- info: 'Shallot.derives_printExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.derives_printExpr

/-- info: 'Shallot.derives_printProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.derives_printProgram

/-- info: 'Shallot.parse_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.parse_print

/-- info: 'Shallot.pipeline_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.pipeline_correct

/-! ## Verified JSON parser (J-series) — RFC 8259 roundtrip -/

/-- info: 'Shallot.Json.derives_printJson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Json.derives_printJson

/-- info: 'Shallot.Json.parse_print_json' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Json.parse_print_json

/-! ## Macro PEG (M-PEG / M-PEG-2): call-by-name + call-by-value-par — T0–T3 -/

/-- info: 'Shallot.MacroPeg.mpegRun_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.mpegRun_mono

/-- info: 'Shallot.MacroPeg.mderives_suffix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.mderives_suffix

/-- info: 'Shallot.MacroPeg.mpegRun_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.mpegRun_sound

/-- info: 'Shallot.MacroPeg.mderives_det' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.mderives_det

/-- info: 'Shallot.MacroPeg.mpegRun_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.mpegRun_complete

/-- info: 'Shallot.MacroPeg.copy_language_ww' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.copy_language_ww

/-! ## T1: plain PEG embeds into arity-0 Macro PEG (both directions) -/

/-- info: 'Shallot.MacroPeg.peg_embed_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.peg_embed_complete

/-- info: 'Shallot.MacroPeg.peg_embed_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.peg_embed_sound

/-! ## `aⁿbⁿcⁿ` — a non-context-free language a plain PEG recognizes -/

/-- info: 'Shallot.S_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.S_char

/-! ## T2: GNF CFG embeds into arity-1 Macro PEG (both directions) -/

/-- info: 'Shallot.Cfg.cfg_cps_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.cfg_cps_complete

/-- info: 'Shallot.Cfg.cfg_cps_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.cfg_cps_sound

/-! ## T3: `CFL ⊊ MPEL^CBN_1` — the language-hierarchy theorem -/

/-- info: 'Shallot.Cfg.cfl_proper_subset_mpel1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.cfl_proper_subset_mpel1

/-! ## T7: `CFL ⊆ PEL` — the settled half (`PEL ⊄ CFL`); the other
direction is an open problem, documented not proved (`Cfg/OpenProblems.lean`) -/

/-- info: 'Shallot.Cfg.abc_isPEL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.abc_isPEL

/-- info: 'Shallot.Cfg.pel_not_subset_cfl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.pel_not_subset_cfl

/-! ## T7 evidence: the textbook palindrome CFG, read literally as a plain
PEG, is sound but incomplete (`Shallot/Peg/Palindrome.lean`) -/

/-- info: 'Shallot.exists_palindrome_palGrammar_rejects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.exists_palindrome_palGrammar_rejects

/-- info: 'Shallot.palGrammar_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.palGrammar_sound

/-- info: 'Shallot.palGrammar_accepts_only_palindromes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.palGrammar_accepts_only_palindromes

/-! ## T7 evidence, positive side: Loff–Moreira–Reis's Theorem 8 mechanism
(`Shallot/Peg/PowerTwoHelper.lean`) -/

/-- info: 'Shallot.helper_consumption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.helper_consumption

/-- info: 'Shallot.helper_full_on_power_of_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.helper_full_on_power_of_two

/-! ## T7 evidence, another natural construction tried: eps-first priority
order rejects every non-empty input (`Shallot/Peg/PalindromeEpsFirst.lean`) -/

/-- info: 'Shallot.palEpsFirst_rejects_nonempty' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.palEpsFirst_rejects_nonempty

/-! ## T7 evidence, a third priority order tried: eps-middle makes an
alternative structurally unreachable (`Shallot/Peg/PalindromeEpsMiddle.lean`) -/

/-- info: 'Shallot.palEpsMiddle_rejects_bb' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.palEpsMiddle_rejects_bb

/-! ## T7 evidence: complete classification of all 6 priority orders of the
peel-both-ends family (`Shallot/Peg/PalindromeAllOrders.lean`) -/

/-- info: 'Shallot.all_six_peel_orders_incomplete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.all_six_peel_orders_incomplete

/-! ## T7 evidence: even a midpoint-only requirement (no end-matching)
already breaks this construction style (`Shallot/Peg/MidPoint.lean`) -/

/-- info: 'Shallot.midGrammar_rejects_bab' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.midGrammar_rejects_bab

/-! ## T7 theorem: PEG cannot locate the midpoint, quantified over every
2-letter alphabet (`Shallot/Peg/MidPointGeneral.lean`) -/

/-- info: 'Shallot.genMid_rejects_c1c0c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.genMid_rejects_c1c0c1

/-! ## Counterexample corpus (CE-001, CE-002 — Lean side; CE-003 is Scala-only,
see `MacroPeg/Counterexamples.lean`'s module docstring) -/

/-- info: 'Shallot.MacroPeg.ce001_callByName' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce001_callByName

/-- info: 'Shallot.MacroPeg.ce001_callByValueSeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce001_callByValueSeq

/-- info: 'Shallot.MacroPeg.ce001_callByValuePar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce001_callByValuePar

/-- info: 'Shallot.MacroPeg.ce001_strategies_disagree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce001_strategies_disagree

/-- info: 'Shallot.MacroPeg.selfCall_loop_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.selfCall_loop_none

/-- info: 'Shallot.MacroPeg.selfCallDiverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.selfCallDiverges
