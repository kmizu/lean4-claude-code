import Shallot.Peg.Palindrome

/-!
# T7 evidence, another natural construction tried: eps-first priority order

`Palindrome.lean`'s `palGrammar` transcribes `Pal → a Pal a | b Pal b | ε`
with the recursive alternatives tried BEFORE `ε` (Ford's prioritized choice
tries the first alternative that succeeds, so putting the recursive cases
first means `Pal` only falls back to `ε` when neither `"a" Pal "a"` nor
`"b" Pal "b"` can be made to work at all). That construction is sound but
incomplete (rejects `"aaaa"`).

This file tries the OTHER natural priority order — `ε` tried FIRST — as a
genuinely different construction, not a variant sharing the same failure
mode. The result is a much MORE extreme failure, not a milder one: since
`.eps` always succeeds trivially, `Pal` under this ordering commits to the
empty match on EVERY input, before ever attempting the recursive
alternatives (Ford's choice never backtracks out of an already-successful
alternative to try a `/`-later one instead, and `.eps` is unconditionally
successful). So this grammar rejects every non-palindrome AND every
NON-EMPTY palindrome alike — including the shortest non-trivial case
`"aa"`, a much weaker result than `palGrammar`'s (which at least handles
`"aa"`, `"bb"`, `"abba"`, etc., failing only on longer runs of a repeated
character). This is recorded as evidence that priority order matters in a
specific, machine-checked direction: moving `ε` earlier does not trade one
incompleteness for a smaller one — it collapses the construction almost
entirely, reinforcing (from the opposite direction) that this whole family
of "peel matching characters from both ends" constructions is fragile
around how it schedules base-case termination against recursion, not just
in the recursion order tried in `Palindrome.lean`.
-/

namespace Shallot

/-- `Pal ← ε / "a" Pal "a" / "b" Pal "b"` — same recursive shape as
`palBody`, but with `ε` tried FIRST instead of last. -/
def palEpsFirstBody : PExp :=
  .alt .eps
    (.alt (.seq (.chr 'a') (.seq (.nt PalIdx) (.chr 'a')))
      (.seq (.chr 'b') (.seq (.nt PalIdx) (.chr 'b'))))

def palEpsFirstGrammar : Grammar := { rules := [palEpsFirstBody], start := PalIdx }

/-- Under this priority order, `Pal` commits to the empty match on EVERY
input — `.eps` unconditionally succeeds, so `altL` fires immediately and
the recursive alternatives are never even attempted. -/
theorem palEpsFirst_always_eps (w : List Char) :
    ∃ t, Derives palEpsFirstGrammar (.nt PalIdx) w (.ok t w) :=
  ⟨_, .ntOk _ _ _ _ _ rfl (.altL _ _ _ _ _ (.eps w))⟩

/-- **The headline**: this construction rejects EVERY non-empty input, not
just some carefully chosen counterexample — a far more extreme
incompleteness than `palGrammar`'s single witness `"aaaa"`. Proved directly
from determinism: the always-eps derivation above and any hypothetical
full-match derivation would have to agree (`derives_det`), but they report
different leftover input (`w` vs `[]`) whenever `w` is non-empty. -/
theorem palEpsFirst_rejects_nonempty {w : List Char} (hw : w ≠ []) :
    ¬ ∃ t, Derives palEpsFirstGrammar (.nt PalIdx) w (.ok t []) := by
  rintro ⟨t, hderiv⟩
  obtain ⟨t', hderiv'⟩ := palEpsFirst_always_eps w
  have heq := derives_det hderiv hderiv'
  injection heq with _ hrest
  exact hw hrest.symm

/-- Concretely: even `"aa"`, the shortest non-trivial palindrome and one
`palGrammar` DOES accept, is rejected here. -/
theorem palEpsFirst_rejects_aa :
    ¬ ∃ t, Derives palEpsFirstGrammar (.nt PalIdx) ['a', 'a'] (.ok t []) :=
  palEpsFirst_rejects_nonempty (by simp)

end Shallot
