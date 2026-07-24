import Shallot.Peg.PalindromeEpsFirst

/-!
# T7 evidence, a third priority order tried: eps-MIDDLE makes an entire
alternative structurally unreachable

`Palindrome.lean` tries `ε` last (`a-case / b-case / ε`); `PalindromeEpsFirst.lean`
tries it first (`ε / a-case / b-case`), collapsing `Pal` to always-empty on
every input. This file tries the THIRD qualitatively distinct placement —
`ε` in the MIDDLE (`a-case / ε / b-case`) — and finds a failure mode
neither of the other two exhibits: putting anything unconditionally-
successful strictly between two alternatives makes every alternative AFTER
it structurally dead code, because Ford's prioritized choice commits to
the first alternative that succeeds and `.eps` always succeeds. Here that
means the `b-case` alternative can NEVER be reached: on any input, either
`a-case` succeeds (consuming something), or it fails and `ε` immediately
takes over — `b-case` is only ever tried when both of the PRECEDING
alternatives already failed, but `ε` never fails, so that never happens.

Empirically (checked by direct computation before formalizing, same
discipline as `Palindrome.lean`'s `"aaaa"` witness): this grammar behaves
EXACTLY like `palGrammar` on `'a'`-only inputs (`"aa"` accepted, `"aaaa"`
only partially, for the identical structural reason — the `b-case`'s
position relative to `ε` is irrelevant when the input never reaches it),
but rejects EVERY input starting with `'b'` outright, including the
shortest nontrivial palindrome `"bb"` — a failure `palGrammar` (which
accepts `"bb"`) does not share. So `ε`'s position relative to the FIRST
alternative determines the `"aaaa"`-style failure; its position relative
to LATER alternatives determines whether those alternatives are reachable
at all. These are two independent design mistakes this single family of
constructions can make, not variations on the same one.
-/

namespace Shallot

/-- `Pal ← "a" Pal "a" / ε / "b" Pal "b"` — same three ingredients as
`palBody`/`palEpsFirstBody`, with `ε` placed between the two recursive
alternatives instead of before or after both. -/
def palEpsMiddleBody : PExp :=
  .alt (.seq (.chr 'a') (.seq (.nt PalIdx) (.chr 'a')))
    (.alt .eps (.seq (.chr 'b') (.seq (.nt PalIdx) (.chr 'b'))))

def palEpsMiddleGrammar : Grammar := { rules := [palEpsMiddleBody], start := PalIdx }

/-- The `a-case` alternative always fails when the input doesn't start
with `'a'` — in particular whenever it starts with `'b'`. -/
theorem palEpsMiddle_aCase_fails_on_b {d : Char} (hd : d = 'b') (rest : List Char) :
    Derives palEpsMiddleGrammar (.seq (.chr 'a') (.seq (.nt PalIdx) (.chr 'a')))
      (d :: rest) .fail :=
  .seqFail₁ _ _ _ (.chrFail _ _ _ (by subst hd; decide))

/-- **The headline**: on any input starting with `'b'`, `Pal` commits to
the empty match — the `a-case` alternative fails immediately (wrong
leading character), and `ε` — being tried NEXT, before `b-case` ever gets
a turn — always succeeds, so `.altR`/`.altL` resolve the whole `.alt`
without `b-case` ever being attempted. -/
theorem palEpsMiddle_eps_on_b {d : Char} (hd : d = 'b') (rest : List Char) :
    ∃ t, Derives palEpsMiddleGrammar (.nt PalIdx) (d :: rest) (.ok t (d :: rest)) :=
  ⟨_, .ntOk _ _ _ _ _ rfl
    (.altR _ _ _ _ _ (palEpsMiddle_aCase_fails_on_b hd rest) (.altL _ _ _ _ _ (.eps _)))⟩

/-- Concretely: `"bb"` — a genuine, minimal palindrome, and one `palGrammar`
DOES accept — is rejected by this construction. Proved the same way as
`palEpsFirst_rejects_nonempty`: the always-eps derivation above and any
hypothetical full-match derivation must agree by `derives_det`, but they
report different leftover input whenever the input is non-empty. -/
theorem palEpsMiddle_rejects_bb :
    ¬ ∃ t, Derives palEpsMiddleGrammar (.nt PalIdx) ['b', 'b'] (.ok t []) := by
  rintro ⟨t, hderiv⟩
  obtain ⟨t', hderiv'⟩ := palEpsMiddle_eps_on_b (rfl : 'b' = 'b') ['b']
  have heq := derives_det hderiv hderiv'
  injection heq with _ hrest
  exact List.cons_ne_nil _ _ hrest.symm

end Shallot
