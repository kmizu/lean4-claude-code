import Cfg.Semantics
import MacroPeg.Semantics
import MacroPeg.Determinism

/-!
# CPS embedding of a GNF context-free grammar into first-order call-by-name Macro PEG

For a GNF production `A → a A₁ A₂ ⋯ Aₘ`, builds the Macro PEG alternative
`A(K) ← "a" A₁(A₂(⋯Aₘ(K)⋯))`, threading a continuation parameter `K` through
every alternative so prioritized choice can backtrack to the next CFG
production when a local match succeeds but the remainder (continuation)
fails. Continuations here are ORDINARY first-order `MExp` values built from
`.call`/`.seq` — never `.lam`/`.callParam`/`.invoke` — since under
`.callByName`, `MExp.subst`'s plain substitution already re-threads a
nested, unevaluated continuation expression into every alternative branch it
reaches; no closures are needed.
-/

namespace Shallot.Cfg

open Shallot.MacroPeg

/-- `A₁(A₂(⋯Aₘ(K)⋯))`, right-to-left: innermost is `Aₘ(K)`. -/
def buildCallSeq : List Nat → MExp → MExp
  | [], k => k
  | j :: js, k => .call j [buildCallSeq js k]

/-- One alternative's CPS body: `ε ↦ K`; `c A₁…Aₘ ↦ "c" A₁(A₂(⋯Aₘ(K)⋯))`. -/
def altExpr (rhs : Rhs) (k : MExp) : MExp :=
  match gnfHead rhs with
  | none => k
  | some (c, js) => .seq (.chr c) (buildCallSeq js k)

/-- All of a nonterminal's alternatives, right-associated `.alt` chain;
`[]` alternatives (no productions) never derive anything. -/
def altsExpr : List Rhs → MExp → MExp
  | [], _ => MExp.failAlways
  | [r], k => altExpr r k
  | r :: rs, k => .alt (altExpr r k) (altsExpr rs k)

/-- Rule `i`'s body: arity 1, `.param 0` is the continuation `K`. -/
def ruleBodyFor (alts : List Rhs) : MExp := altsExpr alts (.param 0)

def cfgToMacroPeg (g : CFGrammar) : MGrammar :=
  { rules := g.rules.map (fun alts => { arity := 1, body := ruleBodyFor alts }) }

/-- Top-level start expression: `S(!.)` — "and then end of input". -/
def cfgStartExpr (g : CFGrammar) : MExp := .call g.start [.notP .any]

/-! ## Plumbing lemmas: rule lookup and substitution commute with the translation -/

/-- `ruleAtM` on the translated grammar's rules is `altsAt` composed with
building the rule record — mirrors `List.map`'s index-lookup commutation,
proved by induction on the rule list (matching `altsAt`/`ruleAtM`'s own
structural recursion). -/
theorem ruleAtM_cfgToMacroPeg (g : CFGrammar) (i : Nat) :
    ruleAtM (cfgToMacroPeg g).rules i
      = (altsAt g.rules i).map (fun alts => ({ arity := 1, body := ruleBodyFor alts } : MRule)) := by
  simp only [cfgToMacroPeg]
  induction g.rules generalizing i with
  | nil => cases i <;> rfl
  | cons r rs ih =>
    cases i with
    | zero => rfl
    | succ n => simp only [List.map, ruleAtM, altsAt]; exact ih n

/-- `subst [k]` commutes with `buildCallSeq`: substituting the continuation
placeholder threads `k` into every nested call, by induction on the
nonterminal sequence. -/
theorem subst_buildCallSeq (k : MExp) : ∀ js : List Nat,
    MExp.subst [k] (buildCallSeq js (.param 0)) = buildCallSeq js k
  | [] => by simp [buildCallSeq, MExp.subst, argAt]
  | j :: js => by
      simp only [buildCallSeq, MExp.subst, MExp.substArgs]
      rw [subst_buildCallSeq k js]

/-- `subst [k]` commutes with `altExpr`. -/
theorem subst_altExpr (rhs : Rhs) (k : MExp) :
    MExp.subst [k] (altExpr rhs (.param 0)) = altExpr rhs k := by
  simp only [altExpr]
  cases gnfHead rhs with
  | none => simp [MExp.subst, argAt]
  | some p =>
      obtain ⟨c, js⟩ := p
      simp only [MExp.subst]
      rw [subst_buildCallSeq k js]

/-- `subst [k]` commutes with `altsExpr`, by induction on the alternative
list (mirroring `altsExpr`'s own `[] / [r] / r :: rs` case split). -/
theorem subst_altsExpr (k : MExp) : ∀ alts : List Rhs,
    MExp.subst [k] (altsExpr alts (.param 0)) = altsExpr alts k
  | [] => by simp [altsExpr, MExp.subst, MExp.failAlways]
  | [r] => subst_altExpr r k
  | r :: r' :: rs => by
      show MExp.subst [k] (.alt (altExpr r (.param 0)) (altsExpr (r' :: rs) (.param 0)))
        = .alt (altExpr r k) (altsExpr (r' :: rs) k)
      simp only [MExp.subst]
      rw [subst_altExpr r k, subst_altsExpr k (r' :: rs)]

/-- `subst [k]` applied to rule `i`'s body threads `k` in as the
continuation. -/
theorem subst_ruleBodyFor (alts : List Rhs) (k : MExp) :
    MExp.subst [k] (ruleBodyFor alts) = altsExpr alts k :=
  subst_altsExpr k alts

/-! ## Totality under GNF

Discovered mid-proof (not anticipated in the original plan): a naive
completeness/soundness argument that tracks one SPECIFIC `Gen`/`GenRhs`
witness breaks for ambiguous grammars — Macro PEG's `.alt` commits to
whichever branch succeeds FIRST, so if a "competing" alternative also
succeeds (via a different split) before the one being tracked, determinism
means the actual result follows THAT branch instead. Resolving this needs
knowing, at every choice point, that trying an earlier alternative EITHER
succeeds or fails (never "no answer at all" / diverges) — i.e. TOTALITY of
the translated grammar. `isGnfB`'s ban on bare ε (module docstring) makes
this provable cleanly: every nonterminal call consumes ≥1 character before
recursing further, so recursion depth is bounded by remaining input length. -/

/-- A definite outcome exists for `e` at `input`: either it fails, or it
succeeds with some tree/leftover. Does NOT claim WHICH — only that `MDerives`
doesn't simply have no answer (the "would loop forever" case). -/
def Total (g : CFGrammar) (e : MExp) (input : List Char) : Prop :=
  MDerives (cfgToMacroPeg g) .callByName e input .fail ∨
  ∃ t rest, MDerives (cfgToMacroPeg g) .callByName e input (.ok t rest)

/-- `buildCallSeq` distributes over list append — lets a nested call's
"remaining nonterminals, then the outer continuation" be re-associated to
match a fixed, single outer continuation `k`. -/
theorem buildCallSeq_append (k : MExp) : ∀ (xs ys : List Nat),
    buildCallSeq (xs ++ ys) k = buildCallSeq xs (buildCallSeq ys k)
  | [], _ys => rfl
  | x :: xs, ys => by
      simp only [buildCallSeq, List.cons_append]
      rw [buildCallSeq_append k xs ys]

/-- `altsAt` only ever returns an element actually present in the list. -/
theorem altsAt_mem {rs : List (List Rhs)} {j : Nat} {alts : List Rhs}
    (h : altsAt rs j = some alts) : alts ∈ rs := by
  induction rs generalizing j with
  | nil => cases j <;> simp [altsAt] at h
  | cons r rs ih =>
    cases j with
    | zero =>
        simp only [altsAt, Option.some.injEq] at h
        exact List.mem_cons.mpr (Or.inl h.symm)
    | succ n => simp only [altsAt] at h; exact List.mem_cons_of_mem r (ih h)

/-- `isGnfB g = true` gives every alternative reachable via `altsAt` the
GNF shape (membership-quantified form, matching what `List.all_eq_true`
produces at every nesting level). -/
theorem isGnfB_altsAt {g : CFGrammar} (hgnf : isGnfB g = true) {j : Nat} {alts : List Rhs}
    (hj : altsAt g.rules j = some alts) : ∀ r ∈ alts, rhsIsGnfB r = true := by
  simp only [isGnfB, List.all_eq_true] at hgnf
  exact hgnf alts (altsAt_mem hj)

/-- Unpacks a GNF-shaped `Rhs`'s decidable tag into the actual leading
terminal / all-nonterminal-tail shape it guarantees. -/
theorem rhsIsGnfB_shape {r : Rhs} (h : rhsIsGnfB r = true) :
    ∃ (c : Char) (nts : List Sym), r = .t c :: nts ∧ nts.all symIsNt = true := by
  match r, h with
  | .t c :: nts, h => exact ⟨c, nts, rfl, h⟩

/-- The main totality theorem: under GNF, every `buildCallSeq js k` has a
definite outcome at any input, provided `k` itself does at every position
up to (and including) the same length bound `N`. Proved by STRONG induction
on `input.length`, matching the M-PEG-5 precedent of using a fuel/height
bound as the well-founded measure; the fixed outer bound `N` (rather than
re-deriving a fresh bound at each recursive step) is what makes `hktot`
available uniformly throughout the recursion — see the module docstring. -/
theorem buildCallSeq_total (g : CFGrammar) (hgnf : isGnfB g = true) (k : MExp) (N : Nat)
    (hktot : ∀ mid : List Char, mid.length ≤ N → Total g k mid) :
    ∀ (input : List Char), input.length ≤ N → ∀ (js : List Nat),
      Total g (buildCallSeq js k) input := by
  have main : ∀ (len : Nat) (input : List Char), input.length = len → len ≤ N →
      ∀ (js : List Nat), Total g (buildCallSeq js k) input := by
    intro len
    induction len using Nat.strongRecOn with
    | ind len ih =>
      intro input hlen hleN js
      cases js with
      | nil =>
          exact hktot input (hlen ▸ hleN)
      | cons j js' =>
          show Total g (.call j [buildCallSeq js' k]) input
          -- Alternative-list totality, `alts` freshly quantified so the
          -- induction below doesn't drag in `hj`/`halts` (which mention a
          -- FIXED `alts`) as spurious extra hypotheses in the IH.
          have altsTotal : ∀ (alts : List Rhs), (∀ r ∈ alts, rhsIsGnfB r = true) →
              Total g (altsExpr alts (buildCallSeq js' k)) input := by
            intro alts
            induction alts with
            | nil =>
                intro _
                exact Or.inl (MDerives.notOk .eps input input (.leaf []) (MDerives.eps input))
            | cons r rs ihAlts =>
                intro halts
                have hrGnf : rhsIsGnfB r = true := halts r (List.mem_cons.mpr (Or.inl rfl))
                obtain ⟨c, nts, hrEq, _hntsAll⟩ := rhsIsGnfB_shape hrGnf
                have hgh : gnfHead r = some (c, ntSeq nts) := by subst hrEq; rfl
                have haltExpr : altExpr r (buildCallSeq js' k) =
                    .seq (.chr c) (buildCallSeq (ntSeq nts ++ js') k) := by
                  simp only [altExpr, hgh]
                  rw [buildCallSeq_append]
                have hheadTotal : Total g (altExpr r (buildCallSeq js' k)) input := by
                  rw [haltExpr]
                  cases input with
                  | nil => exact Or.inl (MDerives.seqFail₁ _ _ _ (MDerives.chrEmpty c))
                  | cons d rest =>
                      by_cases hcd : beqChar c d = true
                      · have hchr : MDerives (cfgToMacroPeg g) .callByName (.chr c) (d :: rest)
                            (.ok (.leaf [d]) rest) := MDerives.chrOk c d rest hcd
                        have hlend : (d :: rest).length = len := hlen
                        simp only [List.length_cons] at hlend
                        have hrestLe : rest.length ≤ N := by omega
                        have hrestLt : rest.length < len := by omega
                        have hrec := ih rest.length hrestLt rest rfl hrestLe (ntSeq nts ++ js')
                        rcases hrec with hfail | ⟨t, rest', hok⟩
                        · exact Or.inl (MDerives.seqFail₂ _ _ _ _ _ hchr hfail)
                        · exact Or.inr ⟨.seq (.leaf [d]) t, rest', MDerives.seqOk _ _ _ _ _ _ _ hchr hok⟩
                      · have hbeq : beqChar c d = false := by
                          cases h : beqChar c d with
                          | true => exact absurd h hcd
                          | false => rfl
                        exact Or.inl (MDerives.seqFail₁ _ _ _ (MDerives.chrFail c d rest hbeq))
                match rs, ihAlts with
                | [], _ =>
                    simpa [altsExpr] using hheadTotal
                | r' :: rs', ihAlts =>
                    have htail : Total g (altsExpr (r' :: rs') (buildCallSeq js' k)) input :=
                      ihAlts (fun x hx => halts x (List.mem_cons_of_mem r hx))
                    show Total g (.alt (altExpr r (buildCallSeq js' k))
                        (altsExpr (r' :: rs') (buildCallSeq js' k))) input
                    rcases hheadTotal with hheadFail | ⟨th, resth, hheadOk⟩
                    · rcases htail with htailFail | ⟨tt, restt, htailOk⟩
                      · exact Or.inl (MDerives.altFail _ _ _ hheadFail htailFail)
                      · exact Or.inr ⟨.choiceR tt, restt, MDerives.altR _ _ _ _ _ hheadFail htailOk⟩
                    · exact Or.inr ⟨.choiceL th, resth, MDerives.altL _ _ _ _ _ hheadOk⟩
          rcases hj : altsAt g.rules j with _ | alts
          · -- no such rule: `.call` fails outright
            refine Or.inl ?_
            have hr : ruleAtM (cfgToMacroPeg g).rules j = none := by
              rw [ruleAtM_cfgToMacroPeg]; simp [hj]
            exact MDerives.callMissing j [buildCallSeq js' k] input hr
          · -- rule `j` exists with alternatives `alts`, all GNF-shaped
            have hr : ruleAtM (cfgToMacroPeg g).rules j
                = some ({ arity := 1, body := ruleBodyFor alts } : MRule) := by
              rw [ruleAtM_cfgToMacroPeg]; simp [hj]
            have hgoal := altsTotal alts (isGnfB_altsAt hgnf hj)
            rw [← subst_ruleBodyFor alts (buildCallSeq js' k)] at hgoal
            rcases hgoal with hfail | ⟨t, rest, hok⟩
            · exact Or.inl (MDerives.callNameFail j [buildCallSeq js' k]
                { arity := 1, body := ruleBodyFor alts } input rfl hr rfl hfail)
            · exact Or.inr ⟨.nodeCall j t, rest, MDerives.callNameOk j [buildCallSeq js' k]
                { arity := 1, body := ruleBodyFor alts } input rest t rfl hr rfl hok⟩
  intro input hle js
  exact main input.length input rfl hle js

/-! ## Completeness (`cfg_cps_complete`)

Rather than tracking one SPECIFIC `Gen`/`GenRhs` witness's exact consumption
all the way through (which breaks for ambiguous grammars — a `.alt` commits
to whichever branch succeeds FIRST, so a "competing" alternative winning
first would make the tracked witness's specific outcome false), this proves
the WEAKER but sufficient "does not fail" and combines it with
`buildCallSeq_total` (totality) at the very end: since `MDerives` is
deterministic and total here, "not fail" plus "total" gives "succeeds",
without ever needing to know WHICH internal alternative actually wins. -/

/-- If `r` is one of `alts`' alternatives and the whole chain fails, `r`'s
own (continuation-inclusive) expression fails too — the contrapositive of
"one alternative not failing keeps the whole chain from failing". Purely
structural (list-length) induction, no input-length concerns. -/
theorem altsExpr_fail_of_mem {g : CFGrammar} {alts : List Rhs} {r : Rhs} (hr : r ∈ alts)
    {k' : MExp} {x : List Char}
    (hfail : MDerives (cfgToMacroPeg g) .callByName (altsExpr alts k') x .fail) :
    MDerives (cfgToMacroPeg g) .callByName (altExpr r k') x .fail := by
  induction alts with
  | nil => cases hr
  | cons r0 rs ih =>
      cases rs with
      | nil =>
          have hreq : r = r0 := (List.mem_singleton.mp hr)
          subst hreq
          simpa [altsExpr] using hfail
      | cons r1 rs' =>
          rw [show altsExpr (r0 :: r1 :: rs') k' = .alt (altExpr r0 k') (altsExpr (r1 :: rs') k')
            from rfl] at hfail
          cases hfail with
          | altFail _ _ _ hf0 hf1 =>
              rcases List.mem_cons.mp hr with heq | hmem
              · subst heq; exact hf0
              · exact ih hmem hf1

/-- Dual of `altsExpr_fail_of_mem`: if the WHOLE alt-chain succeeds, SOME
member's own expression succeeds with the SAME outcome (structural
induction on `alts`, inverting `.alt`'s success via `altL`/`altR` — no
input-length concerns, no ambiguity issue: we're deconstructing one ALREADY
GIVEN, concrete success, not constructing one). -/
theorem altsExpr_ok_inv {g : CFGrammar} {k' : MExp} {x : List Char} {rest : List Char} :
    ∀ (alts : List Rhs) {t : MTree},
      MDerives (cfgToMacroPeg g) .callByName (altsExpr alts k') x (.ok t rest) →
      ∃ r ∈ alts, ∃ t', MDerives (cfgToMacroPeg g) .callByName (altExpr r k') x (.ok t' rest) := by
  intro alts
  induction alts with
  | nil =>
      intro t hok
      exact absurd hok (by
        simp only [altsExpr]
        intro h
        cases h with
        | notFail _ _ heps => cases heps)
  | cons r0 rs ih =>
      intro t hok
      cases rs with
      | nil =>
          exact ⟨r0, List.mem_singleton.mpr rfl, t, by simpa [altsExpr] using hok⟩
      | cons r1 rs' =>
          rw [show altsExpr (r0 :: r1 :: rs') k' = .alt (altExpr r0 k') (altsExpr (r1 :: rs') k')
            from rfl] at hok
          cases hok with
          | altL _ _ _ _ t' hL =>
              exact ⟨r0, List.mem_cons.mpr (Or.inl rfl), t', hL⟩
          | altR _ _ _ _ t' hFail hR =>
              obtain ⟨r, hmem, t'', hr⟩ := ih hR
              exact ⟨r, List.mem_cons_of_mem r0 hmem, t'', hr⟩

/-- Inverts a FAILING `.call` derivation into a failing body derivation,
given the rule/arity are already known — collapses all 6 `.fail`-producing
`.call` constructors down to the one (`callNameFail`) that's actually
reachable once the strategy is pinned to `.callByName`, dismissing the
other-strategy branches via their own `hs` hypothesis being a false
`Strategy` equation, and the wrong-rule/wrong-arity branches via `hr`/`ha`. -/
theorem call_fail_inv {mg : MGrammar} {i : Nat} {args : List MExp} {r : MRule} {input : List Char}
    (hr : ruleAtM mg.rules i = some r) (harity : r.arity = args.length)
    (hfail : MDerives mg .callByName (.call i args) input .fail) :
    MDerives mg .callByName (MExp.subst args r.body) input .fail := by
  cases hfail with
  | callNameFail _ _ r' _ _ hr' _ hd =>
      rw [hr] at hr'
      injection hr' with hr'
      subst hr'
      exact hd
  | callParFail _ _ _ _ _ hs _ _ _ _ => exact absurd hs (by decide)
  | callParArgFail _ _ _ _ _ _ _ hs _ _ _ _ => exact absurd hs (by decide)
  | callSeqFail _ _ _ _ _ _ hs _ _ _ _ => exact absurd hs (by decide)
  | callSeqArgFail _ _ _ _ _ _ _ _ hs _ _ _ _ => exact absurd hs (by decide)
  | callMissing _ _ _ hr' => rw [hr] at hr'; injection hr'
  | callArity _ _ r' _ hr' ha' =>
      rw [hr] at hr'
      injection hr' with hr'
      subst hr'
      exact absurd harity ha'

/-- Dual of `call_fail_inv`: inverts a SUCCEEDING `.call` derivation into a
succeeding body derivation (existentially quantifying the inner tree, since
the outer one is wrapped in `.nodeCall`) — collapses the 3 `.ok`-producing
`.call` constructors down to `callNameOk`, dismissing the other-strategy
branches the same way as `call_fail_inv`. -/
theorem call_ok_inv {mg : MGrammar} {i : Nat} {args : List MExp} {r : MRule}
    {input rest : List Char} {tOuter : MTree}
    (hr : ruleAtM mg.rules i = some r) (harity : r.arity = args.length)
    (hok : MDerives mg .callByName (.call i args) input (.ok tOuter rest)) :
    ∃ t, MDerives mg .callByName (MExp.subst args r.body) input (.ok t rest) := by
  cases hok with
  | callNameOk _ _ r' _ _ t _ hr' _ hd =>
      rw [hr] at hr'
      injection hr' with hr'
      subst hr'
      exact ⟨t, hd⟩
  | callParOk _ _ _ _ _ _ _ hs _ _ _ _ => exact absurd hs (by decide)
  | callSeqOk _ _ _ _ _ _ _ _ hs _ _ _ _ => exact absurd hs (by decide)

/-- A symbol list's own CPS expression, defined by direct structural
recursion on `Sym` — mirrors `GenRhs`'s own `nil`/`cons_t`/`cons_nt`
recursive shape exactly (unlike `altExpr`/`buildCallSeq`, which only make
sense for a GNF-shaped, single-leading-terminal `Rhs`), which is what lets
the completeness induction below proceed one `GenRhs` constructor at a time
with no extra "is this rhs GNF-shaped" bookkeeping inside each case. -/
def symsExpr : List Sym → MExp → MExp
  | [], k => k
  | .t c :: rest, k => .seq (.chr c) (symsExpr rest k)
  | .nt j :: rest, k => .call j [symsExpr rest k]

/-- `symsExpr` distributes over list append, composing continuations —
lets a nested rule's own leftover symbols (after its own leading terminal)
be re-associated against a fixed outer continuation. -/
theorem symsExpr_append (k : MExp) : ∀ (xs ys : List Sym),
    symsExpr (xs ++ ys) k = symsExpr xs (symsExpr ys k)
  | [], _ys => rfl
  | .t c :: xs, ys => by simp only [List.cons_append, symsExpr]; rw [symsExpr_append k xs ys]
  | .nt j :: xs, ys => by simp only [List.cons_append, symsExpr]; rw [symsExpr_append k xs ys]

/-- For a GNF-shaped `Rhs`, `symsExpr` and `altExpr` (the construction
`cfgToMacroPeg` actually uses) agree — bridges the two representations at
the one place (`cfg_cps_notfail`'s `prod` case) where a rule's whole
alternative, as looked up via `cfgToMacroPeg`, needs to be related to a
`GenRhs`-driven, symbol-by-symbol induction. -/
theorem symsExpr_eq_altExpr {rhs : Rhs} (h : rhsIsGnfB rhs = true) (k : MExp) :
    symsExpr rhs k = altExpr rhs k := by
  obtain ⟨c, nts, hEq, hAllNt⟩ := rhsIsGnfB_shape h
  subst hEq
  have hgh : gnfHead (Sym.t c :: nts) = some (c, ntSeq nts) := rfl
  simp only [altExpr, hgh, symsExpr]
  congr 1
  clear h hgh
  induction nts with
  | nil => rfl
  | cons s ss ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hAllNt
      match s, hAllNt with
      | .nt j, ⟨_, hAllNt'⟩ =>
          simp only [symsExpr, ntSeq, buildCallSeq]
          rw [ih hAllNt']

/-- Completeness, "does not fail" form (see the section docstring above):
a CFG generation of `w` for nonterminal `i`, combined with a continuation
`k'` that itself doesn't fail at `mid`, means `.call i [k']` doesn't fail at
`w ++ mid` either. Proved by mutual induction on `Gen`/`GenRhs` via the
auto-generated `Gen.rec` combined recursor (`motive_2` — stated via
`symsExpr`, which matches `GenRhs`'s OWN recursive shape symbol-by-symbol,
so no separate "is this rhs GNF-shaped" guard is needed inside the
induction — supplies the `GenRhs` side), generalizing `k'`/`mid` at every
step, since nested calls pass NESTED continuations, not the theorem's own
top-level one. -/
theorem cfg_cps_notfail {g : CFGrammar} (hgnf : isGnfB g = true) {i : Nat} {w : List Char}
    (hgen : Gen g i w) :
    ∀ (k' : MExp) (mid : List Char), ¬ MDerives (cfgToMacroPeg g) .callByName k' mid .fail →
      ¬ MDerives (cfgToMacroPeg g) .callByName (.call i [k']) (w ++ mid) .fail := by
  induction hgen using Gen.rec
    (motive_2 := fun rhs w _ => ∀ (k' : MExp) (mid : List Char),
      ¬ MDerives (cfgToMacroPeg g) .callByName k' mid .fail →
      ¬ MDerives (cfgToMacroPeg g) .callByName (symsExpr rhs k') (w ++ mid) .fail)
  with
  | prod i alts rhs w halts hmem hrhs ihRhs =>
      intro k' mid hnf hfail
      have hgnfRhs : rhsIsGnfB rhs = true := isGnfB_altsAt hgnf halts rhs hmem
      have hr : ruleAtM (cfgToMacroPeg g).rules i
          = some ({ arity := 1, body := ruleBodyFor alts } : MRule) := by
        rw [ruleAtM_cfgToMacroPeg]; simp [halts]
      have hbodyFail : MDerives (cfgToMacroPeg g) .callByName
          (MExp.subst [k'] (ruleBodyFor alts)) (w ++ mid) .fail := call_fail_inv hr rfl hfail
      rw [subst_ruleBodyFor] at hbodyFail
      have hAltFail : MDerives (cfgToMacroPeg g) .callByName (altExpr rhs k') (w ++ mid) .fail :=
        altsExpr_fail_of_mem hmem hbodyFail
      rw [← symsExpr_eq_altExpr hgnfRhs] at hAltFail
      exact ihRhs k' mid hnf hAltFail
  | nil =>
      rename_i k' mid hnf
      intro hfail
      simp only [symsExpr, List.nil_append] at hfail
      exact hnf hfail
  | cons_t c rest w h ih =>
      rename_i k' mid hnf
      intro hfail
      simp only [symsExpr] at hfail
      have hchrOk : MDerives (cfgToMacroPeg g) .callByName (.chr c) (c :: (w ++ mid))
          (.ok (.leaf [c]) (w ++ mid)) := MDerives.chrOk c c (w ++ mid) (by simp [beqChar])
      have heq : c :: (w ++ mid) = (c :: w) ++ mid := rfl
      rw [heq] at hchrOk
      cases hfail with
      | seqFail₁ _ _ _ hcf =>
          exact MOutcome.noConfusion (mderives_det hchrOk hcf)
      | seqFail₂ _ _ _ rest₁ _ hchr' hcf2 =>
          have heqOut := mderives_det hchr' hchrOk
          injection heqOut with _ heqRest
          rw [heqRest] at hcf2
          exact ih k' mid hnf hcf2
  | cons_nt j rest w1 w2 h1 h2 ih1 ih2 =>
      rename_i k' mid hnf
      intro hfail
      simp only [symsExpr] at hfail
      have hrestNotFail := ih2 k' mid hnf
      have hcombined := ih1 (symsExpr rest k') (w2 ++ mid) hrestNotFail
      rw [List.append_assoc] at hfail
      exact hcombined hfail

/-- `cfg_cps_complete`: a CFG generation of `w` for nonterminal `i`,
combined with a continuation `k` that doesn't fail at `mid` and is total up
to a bound `N` covering the whole input, means `.call i [k]` actually
SUCCEEDS at `w ++ mid` (not merely "doesn't fail") — combines
`cfg_cps_notfail` with `buildCallSeq_total` (`.call i [k]` is definitionally
`buildCallSeq [i] k`), using that a total expression which doesn't fail
must succeed. -/
theorem cfg_cps_complete {g : CFGrammar} (hgnf : isGnfB g = true) {i : Nat} {w : List Char}
    (hgen : Gen g i w) (k : MExp) (mid : List Char) (N : Nat)
    (hlenN : (w ++ mid).length ≤ N)
    (hktot : ∀ pos : List Char, pos.length ≤ N → Total g k pos)
    (hknf : ¬ MDerives (cfgToMacroPeg g) .callByName k mid .fail) :
    ∃ t rest, MDerives (cfgToMacroPeg g) .callByName (.call i [k]) (w ++ mid) (.ok t rest) := by
  have hnf := cfg_cps_notfail hgnf hgen k mid hknf
  have htot : Total g (.call i [k]) (w ++ mid) :=
    buildCallSeq_total g hgnf k N hktot (w ++ mid) hlenN [i]
  rcases htot with hfail | hok
  · exact absurd hfail hnf
  · exact hok

/-! ## Soundness (`cfg_cps_sound`)

The reverse direction — reconstructing a CFG derivation from an ALREADY
GIVEN, concrete Macro PEG success — has none of completeness's ambiguity
subtlety (we're deconstructing one fixed outcome, not constructing a
specific one against competing alternatives), so it proceeds by direct
inversion, structured like `buildCallSeq_total`: strong induction on
`input.length` (every nonterminal call consumes ≥1 character under GNF, so
recursion terminates), generalizing over an arbitrary symbol list `rhs`. -/

/-- `beqChar c d = true` forces `d = c` (`Char.toNat` is injective). -/
theorem beqChar_eq {c d : Char} (h : beqChar c d = true) : d = c := by
  simp only [beqChar, beq_iff_eq] at h
  exact (Char.toNat_inj.mp h).symm

/-- Inverts `GenRhs g (.t c :: rest) w`. -/
theorem genRhs_cons_t_inv {g : CFGrammar} {c : Char} {rest : List Sym} {w : List Char}
    (h : GenRhs g (.t c :: rest) w) : ∃ w', w = c :: w' ∧ GenRhs g rest w' := by
  cases h with
  | cons_t _ _ w' hgr => exact ⟨w', rfl, hgr⟩

/-- Inverts `GenRhs g (.nt j :: rest) w`. -/
theorem genRhs_cons_nt_inv {g : CFGrammar} {j : Nat} {rest : List Sym} {w : List Char}
    (h : GenRhs g (.nt j :: rest) w) :
    ∃ w1 w2, w = w1 ++ w2 ∧ Gen g j w1 ∧ GenRhs g rest w2 := by
  cases h with
  | cons_nt _ _ w1 w2 h1 h2 => exact ⟨w1, w2, rfl, h1, h2⟩

/-- `GenRhs` "distributes" over list append of the symbol sequence, matching
how the corresponding strings concatenate — needed to split a nested rule's
own generated prefix off from what follows it in an outer alternative.
Structural induction on `xs`. -/
theorem genRhs_append_split {g : CFGrammar} : ∀ {xs ys : List Sym} {w : List Char},
    GenRhs g (xs ++ ys) w → ∃ w1 w2, w = w1 ++ w2 ∧ GenRhs g xs w1 ∧ GenRhs g ys w2
  | [], _, w, h => ⟨[], w, rfl, GenRhs.nil, h⟩
  | .t c :: xs', ys, w, h => by
      obtain ⟨w', hEq, hgr⟩ := genRhs_cons_t_inv (show GenRhs g (.t c :: (xs' ++ ys)) w from h)
      obtain ⟨w1, w2, hEq2, hgr1, hgr2⟩ := genRhs_append_split hgr
      exact ⟨c :: w1, w2, by rw [hEq, hEq2, List.cons_append], GenRhs.cons_t c xs' w1 hgr1, hgr2⟩
  | .nt j :: xs', ys, w, h => by
      obtain ⟨wj, w', hEq, hgj, hgr⟩ := genRhs_cons_nt_inv (show GenRhs g (.nt j :: (xs' ++ ys)) w from h)
      obtain ⟨w1, w2, hEq2, hgr1, hgr2⟩ := genRhs_append_split hgr
      exact ⟨wj ++ w1, w2, by rw [hEq, hEq2, List.append_assoc], GenRhs.cons_nt j xs' wj w1 hgj hgr1, hgr2⟩

/-- Any `.call` derivation that SUCCEEDS proves its rule actually exists —
`callMissing`/`callArity` only ever produce `.fail`, so a `.ok` outcome
rules them out (and the other-strategy `.ok` constructors are dismissed the
same way as `call_ok_inv`). -/
theorem call_ok_rule_exists {mg : MGrammar} {i : Nat} {args : List MExp} {input rest : List Char}
    {t : MTree} (hok : MDerives mg .callByName (.call i args) input (.ok t rest)) :
    ∃ r, ruleAtM mg.rules i = some r := by
  cases hok with
  | callNameOk _ _ r _ _ _ _ hr _ _ => exact ⟨r, hr⟩
  | callParOk _ _ _ _ _ _ _ hs _ _ _ _ => exact absurd hs (by decide)
  | callSeqOk _ _ _ _ _ _ _ _ hs _ _ _ _ => exact absurd hs (by decide)

/-- The main soundness lemma: `symsExpr rhs k'` succeeding at `input` means
`input` splits into `w ++ mid` where `GenRhs g rhs w` and `k'` itself
succeeds at `mid` with the same leftover `rest`. -/
theorem symsExpr_sound {g : CFGrammar} (hgnf : isGnfB g = true) :
    ∀ (len : Nat) (input : List Char), input.length = len →
      ∀ (rhs : List Sym) (k' : MExp) (t : MTree) (rest : List Char),
        MDerives (cfgToMacroPeg g) .callByName (symsExpr rhs k') input (.ok t rest) →
        ∃ w mid, input = w ++ mid ∧ GenRhs g rhs w ∧
          ∃ tk, MDerives (cfgToMacroPeg g) .callByName k' mid (.ok tk rest) := by
    intro len
    induction len using Nat.strongRecOn with
    | ind len ih =>
      intro input hlen rhs k' t rest hok
      match rhs with
      | [] =>
          simp only [symsExpr] at hok
          exact ⟨[], input, rfl, GenRhs.nil, t, hok⟩
      | Sym.t c :: tail =>
          simp only [symsExpr] at hok
          cases hok with
          | seqOk _ _ _ mid1 _ t1 t2 hchr hbody =>
              cases hchr with
              | chrOk _ d _ hbeq =>
                  have hdc : d = c := beqChar_eq hbeq
                  subst hdc
                  have hlend : (d :: mid1).length = len := hlen
                  simp only [List.length_cons] at hlend
                  have hlt : mid1.length < len := by omega
                  obtain ⟨w', mid, hspl, hgr, tk, hktk⟩ :=
                    ih mid1.length hlt mid1 rfl tail k' t2 rest hbody
                  refine ⟨d :: w', mid, ?_, GenRhs.cons_t d tail w' hgr, tk, hktk⟩
                  rw [hspl]; rfl
      | Sym.nt j :: tail =>
          simp only [symsExpr] at hok
          obtain ⟨r0, hr0⟩ := call_ok_rule_exists hok
          have hjrEq := ruleAtM_cfgToMacroPeg g j
          rw [hr0] at hjrEq
          rcases hja : altsAt g.rules j with _ | alts
          · rw [hja] at hjrEq; simp at hjrEq
          · have hrEq : ruleAtM (cfgToMacroPeg g).rules j
                = some ({ arity := 1, body := ruleBodyFor alts } : MRule) := by
              rw [ruleAtM_cfgToMacroPeg, hja]; rfl
            obtain ⟨t', hbody⟩ := call_ok_inv hrEq rfl hok
            rw [subst_ruleBodyFor] at hbody
            obtain ⟨rhsJ, hmemJ, tJ, hrhsJok⟩ := altsExpr_ok_inv alts hbody
            have hgnfJ : rhsIsGnfB rhsJ = true := isGnfB_altsAt hgnf hja rhsJ hmemJ
            rw [← symsExpr_eq_altExpr hgnfJ] at hrhsJok
            obtain ⟨cJ, ntsJ, hEqJ, _⟩ := rhsIsGnfB_shape hgnfJ
            subst hEqJ
            simp only [symsExpr] at hrhsJok
            cases hrhsJok with
            | seqOk _ _ _ mid1 _ t1 t2 hchr hbody2 =>
                cases hchr with
                | chrOk _ d _ hbeq =>
                    have hdc : d = cJ := beqChar_eq hbeq
                    subst hdc
                    have hlend : (d :: mid1).length = len := hlen
                    simp only [List.length_cons] at hlend
                    have hlt : mid1.length < len := by omega
                    rw [← symsExpr_append k' ntsJ tail] at hbody2
                    obtain ⟨w', mid, hspl, hgr, tk, hktk⟩ :=
                      ih mid1.length hlt mid1 rfl (ntsJ ++ tail) k' t2 rest hbody2
                    obtain ⟨w1, w2, hw'eq, hgr1, hgr2⟩ := genRhs_append_split hgr
                    have hGenJ : Gen g j (d :: w1) :=
                      Gen.prod j alts (Sym.t d :: ntsJ) (d :: w1) hja hmemJ
                        (GenRhs.cons_t d ntsJ w1 hgr1)
                    refine ⟨(d :: w1) ++ w2, mid, ?_,
                      GenRhs.cons_nt j tail (d :: w1) w2 hGenJ hgr2, tk, hktk⟩
                    rw [hspl, hw'eq, List.append_assoc, List.append_assoc, List.cons_append]

/-- `cfg_cps_sound`: the reverse of `cfg_cps_complete` — a Macro PEG
success on `.call i [k]` reconstructs a genuine CFG generation of the
consumed prefix, plus a matching success of the continuation `k` on the
rest. Specializes `symsExpr_sound` at `rhs := [.nt i]` (`.call i [k]` is
definitionally `symsExpr [.nt i] k`) and unwraps the resulting
`GenRhs g [.nt i] w` into `Gen g i w` (the trailing `GenRhs g [] w2` forces
`w2 = []`, so `w = w1`). -/
theorem cfg_cps_sound {g : CFGrammar} (hgnf : isGnfB g = true) {i : Nat} {k : MExp}
    {input : List Char} {t : MTree} {rest : List Char}
    (hok : MDerives (cfgToMacroPeg g) .callByName (.call i [k]) input (.ok t rest)) :
    ∃ w mid, input = w ++ mid ∧ Gen g i w ∧
      ∃ tk, MDerives (cfgToMacroPeg g) .callByName k mid (.ok tk rest) := by
  have hok' : MDerives (cfgToMacroPeg g) .callByName (symsExpr [Sym.nt i] k) input (.ok t rest) := hok
  obtain ⟨w, mid, hspl, hgr, tk, hktk⟩ :=
    symsExpr_sound hgnf input.length input rfl [Sym.nt i] k t rest hok'
  obtain ⟨w1, w2, hweq, hgi, hgr2⟩ := genRhs_cons_nt_inv hgr
  cases hgr2 with
  | nil =>
      refine ⟨w1, mid, ?_, hgi, tk, hktk⟩
      rw [hspl, hweq, List.append_nil]

end Shallot.Cfg
