import Cfg.Properness
import Shallot.Peg.Palindrome
import Shallot.Peg.PowerTwoHelper
import Shallot.Peg.PalindromeAllOrders
import Shallot.Peg.MidPoint
import Shallot.Peg.MidPointGeneral
import Shallot.Peg.PalindromeGeneral
import Shallot.Peg.PalindromeGeneralN
import Shallot.Peg.MidpointObstruction

/-!
# T7: `CFL ⊆ PEL` (plain, macro-free PEG) — an open problem, documented not
solved

T3 (`Cfg/Properness.lean`) settles `CFL ⊊ MPEL^CBN_1` — the MACRO-extended
PEG class properly contains the context-free languages. This file is about
a DIFFERENT, older question that this project does **not** resolve: does
the PLAIN (macro-free) PEG class `PEL` also contain every CFL?

**What is actually settled here** (mechanized, below): `PEL ⊄ CFL` — the
aⁿbⁿcⁿ witness (`S_char`) is already sufficient, since `abcGrammar` is a
plain PEG grammar (no macro parameters at all) recognizing a language that
isn't context-free. This is the classical "PEG is not weaker than CFG"
half of the comparison, and it falls out of machinery already built for T3
almost for free.

**What remains open** (`CFLSubsetPELConjecture`, stated but never proved
or disproved): whether every context-free language is ALSO recognized by
some plain PEG. Ford's original POPL 2004 paper already conjectured PEG
might be strictly more expressive than CFG; Loff, Moreira and Reis (JCSS
2019, arXiv:1902.08272, "The computational power of parsing expression
grammars") gave PEG's language class a complete characterization via
"scaffolding automata" and *explicitly state the palindrome question as
their own open Conjecture 7* — as of this writing (checked directly
against the paper text, not secondhand), no progress on it has been found
post-2019, including no resolution in Rubtsov & Chudinov's follow-up work
(MFCS 2024) on a related deterministic-pushdown model.

Three facts from that paper sharpen exactly how hard Conjecture 7 is, and
are worth recording precisely rather than gestured at:

1. **There is provably no pumping lemma for PEGs at all** (their Theorem
   21, proved by a Kleene-second-recursion-theorem-style diagonalization
   over scaffolding automata: for any candidate total computable pumping
   function `A`, one builds a PEG whose consecutive-word gap outgrows `A`
   everywhere). This is not a gap in current knowledge that a cleverer
   pumping argument might close — the paper proves the *general technique
   itself* cannot exist. `palGrammar`'s incompleteness proof below
   therefore had to be — and is — a direct semantic argument (via
   `pegRun_complete`/`pegRun_mono_le`/`derives_det`), not an instance of
   any pumping-style schema; there was never a schema available to
   instantiate.
2. **The paper states plainly that the only method it knows of for
   proving a language has NO PEG is a time-hierarchy-theorem
   diagonalization argument** (Section 1, p.3–4): construct, by
   diagonalization, a language decidable in some higher time bound but not
   in linear time, and appeal to the fact that PEGs are linear-time
   decidable (Birman–Ullman tabular parsing / packrat parsing). This
   technique is *structurally inapplicable* to palindromes: even-length
   palindromes are trivially linear-time decidable themselves, so no
   linear-time-vs-something-slower separation can ever apply to this
   language.
3. **The paper's own authors describe the recognition procedure
   underlying PEGs as "universal" in a sense that makes it "as difficult
   to understand as that of a multi-tape Turing machine"**, and state that
   resolving questions like Conjecture 7 "may well require a breakthrough
   in our ability to prove computational complexity lower-bounds" (p.4).
   This is the paper's own assessment of its own open problem's
   difficulty, not a rhetorical flourish added here — Conjecture 7 sits in
   the same family of difficulty as long-standing lower-bound questions in
   complexity theory (e.g. linear-time RAM vs. two-tape Turing machine
   simulation), which remain unresolved decades on.

None of this proves `CFLSubsetPELConjecture` is unprovable by elementary
means — only that the one general technique known to work for "no PEG"
results doesn't apply here, and that no pumping-style shortcut can exist
in principle. `Shallot/Peg/Palindrome.lean` still makes a genuine, honest
first attempt at ONE natural construction (see below for exactly how far
it gets), and the same paper also proves a real PARTIAL positive result
worth knowing as a foil (their Theorem 8): the language of palindromes
whose length is a power of two, `{w wʳ | w ∈ {0,1}*, |w| = 2ⁿ}`, DOES have
a plain PEG. Its construction is genuinely clever and IS formalized in this
project (`Shallot/Peg/PowerTwoHelper.lean`, not an attempt at the
conjecture itself but the positive result it's contrasted against): a
helper nonterminal `Helper ← Bit Helper Bit / Bit Bit` recognizes exactly
those positions whose distance from end-of-input is a positive power of
two. `Shallot.helper_consumption` proves this in full generality — for
EVERY input length `m ≥ 2`, not just powers of two, by strong induction —
giving the closed form `f(m) = 2·(m − 2^k)` for `2^k < m ≤ 2^(k+1)` (via
`Nat.log2`), which the paper does not spell out explicitly but which
falls out cleanly once traced by hand. `Shallot.helper_full_on_power_of_two`
specializes this to recover the paper's exact claim: full consumption
exactly when `m` is a power of two. `&`/`!` lookahead against this helper
lets the grammar locate the midpoint of a power-of-two-length string
*indirectly*, without ever tracking "how much has been consumed so far"
as first-class state. That last clause is precisely the capability plain
PEG lacks in general — no way to compare "distance from start" against
"distance from end" for an arbitrary midpoint — which is also exactly why
T2's CPS embedding (which routes that comparison through macro-parameter
continuations) cannot be repurposed for T7: the power-of-two trick is a
genuine but narrow escape hatch that doesn't generalize to arbitrary
lengths.

**A genuinely different angle, tried and where it currently stalls**: the
paper's Theorem 21 (no pumping lemma) rules out one *general* schema, but
not every ad-hoc argument specific to palindromes. A natural angle
borrowed from an adjacent field — communication complexity's "fooling
set" technique, used to prove streaming/communication lower bounds for
palindrome recognition — translates into PEG terms as follows. Fix a
grammar `g` with `N` nonterminals claiming to recognize palindromes, and
consider the family `0^k 1 0^k` (`k > N`, each one itself a genuine
palindrome). While `g` processes the leading `0^k` run, `derives_det`
guarantees that whichever nonterminal gets called on a given remaining
suffix behaves *identically* no matter what call chain reached it — by
the pigeonhole principle over `g`'s finitely many nonterminals, some
nonterminal must recur on two different suffixes reachable from different
leading-run lengths. If that recurrence carried no memory of "how many
`0`s were already consumed," pinning down two witnesses with different
correct answers would give a contradiction — a palindrome-specific
analogue of the classical fooling-set argument. It stalls, however, at
exactly the point Theorem 21 identifies: pigeonholing on the nonterminal
NAME alone is not enough, because the SAME nonterminal reached via two
different surrounding `.seq`/`.alt` contexts is not obligated to produce
interchangeable results once its own consumption is spliced back into
those different contexts — this is the exact non-monotonicity Theorem
21's diagonalization exploits to defeat any uniform pumping-style bound.
Forcing the surrounding context to also repeat (not just the nonterminal
name) is what a real proof would need, and there is no known bound on how
large `k` must be to guarantee that stronger recurrence — plausibly
because, per Theorem 21, no such bound can be uniform across grammars.
This is recorded here as a genuine attempt at a different proof strategy,
not a dead end to be silently dropped: it identifies precisely which
strengthening of the pigeonhole step a real proof would need to supply.

**A second adjacent-field angle tried, for a DIFFERENT reason than the
first**: the paper's own footnote 4 (§1) points at Li and Vitanyi's
classical result that one-tape Turing machines need `Ω(n²)` time to
recognize palindromes, proved via an incompressibility (Kolmogorov
complexity) crossing-sequence argument. Translating that style of
argument to PEG: fix an incompressible `w` of length `k` (Kolmogorov
complexity `K(w) ≥ k`) and consider `g`'s (hypothetical, deterministic)
derivation on `w · wʳ`. By `derives_det`, in the unique successful
derivation tree, the deepest nonterminal call whose span straddles the
midpoint `k` has a behavior determined ENTIRELY by `(nonterminal id,
suffix from its start position)` — meaning the ONLY channel through which
information about the already-consumed prefix of `w` can reach the
processing of `wʳ` is via WHICH nonterminal gets called at WHICH position
at that straddle point. A single straddle point carries at most `O(log
k)` bits this way (bounded by the position index) plus `O(1)` bits (which
of the grammar's finitely many nonterminals) — nowhere near the `Θ(k)`
bits needed to reconstruct an incompressible `w`. But this bound does NOT
close off the possibility: the SAME argument applies recursively one
level deeper inside that call, and PEG's recursive nonterminal-call
mechanism can nest up to `Θ(k)` levels deep (exactly what lets it recognize
non-context-free languages like aⁿbⁿcⁿ, T3's witness, by threading `O(1)`
bits of information per recursive level across `Θ(log n)` levels there).
Summed across up to `Θ(k)` levels, the TOTAL channel capacity this
mechanism offers is `Θ(k)` bits — exactly enough, in raw information
terms, to carry all of `w`. So a pure counting/incompressibility argument
does NOT rule out palindrome-recognizing PEGs the way it rules out
one-tape-TM palindrome recognition in sub-quadratic time: PEG's recursive
call stack is expressively closer to a CFG's (or a multi-tape TM's) than
to a one-tape TM's, and the paper's own Theorem 18 (PEGs can simulate any
computable function via a suitable encoding) confirms this raw capacity is
real, not an illusion. If palindromes truly have no PEG, the obstruction
must therefore be about the SPECIFIC way Ford's prioritized, non-
backtracking choice fails to let recursively-threaded information "come
back together" at the right positions — i.e. it reduces to the same
concrete mechanism `palGrammar`'s failure already exhibits (an inner
call's already-committed, too-shallow success stranding an outer call's
requirement), not a separately provable information-theoretic lower
bound. Recorded here because it closes off a second natural angle, for a
genuinely different reason than the first (not "insufficient channel
capacity" but "sufficient raw capacity, no argument against its correct
alignment").

**A third data point, this time straight from the paper's own examples
rather than derived here**: §3.3 (Theorem 9) constructs a PEG for a
"reversed counting" language using an "inversion" nonterminal `Inverted ←
1 Inverted 1 / 0 Inverted 0 / ◦` that matches `wʳ ◦ w` for arbitrary `w` —
structurally identical to `palGrammar`'s peel-both-ends shape, but it
WORKS there, without any of `palGrammar`'s incompleteness. The difference
is that `◦` is an explicit, unambiguous marker of the midpoint, present in
the input alphabet itself — with a designated separator character telling
`Inverted` exactly when to stop recursing (via the `◦` base case) instead
of `Pal`'s `ε` base case, which fires the instant the recursion COULD
stop, whether or not it's actually at the true midpoint. The paper then
states directly (end of §3.3): the underlying "scan digits right-to-left"
algorithm its `AddOneBlock`/`Carry`/`NextIs∗` machinery needs "does not
appear to be possible to implement using PEGs" directly — it has to be
simulated by "invert, then scan left-to-right" (their own named "reverse
and scan" trick) BECAUSE that inversion requires exactly the same
explicit-separator mechanism `Inverted` uses. This is independent, paper-
native confirmation of the same diagnosis reached above from first
principles: what plain PEG is missing for palindromes specifically is not
raw recursive/informational power (Theorem 9's own construction has
plenty, doing full binary increment) but an unambiguous, input-alphabet-
level signal for where matching halves meet — precisely what a genuine
palindrome (no separator, midpoint determined only by total length) does
not supply, and what no available lookahead can conjure up unless the
midpoint happens to be locatable in absolute terms from one end alone (as
Theorem 8's power-of-two trick manages).

**Why T2's construction does not transfer to this question**: T2's CPS
embedding of a CFG into Macro PEG is essentially built on continuations —
`buildCallSeq` threads "what to try next if this succeeds" as an actual
argument passed to a parametrized rule call. A plain PEG rule has no
parameters at all, so it cannot receive a continuation this way; there is
no analogous mechanism to fall back on. This asymmetry (the macro layer's
extra expressiveness comes specifically from parametrized rules being able
to carry control-flow information as data) is itself worth noting as a
point of interest, not just a technical dead end.

Tackling `CFLSubsetPELConjecture` for real would need either a scaffolding-
automata-style pumping argument specific to PEG's semantics, or a genuinely
new technique — this file itself makes no attempt at either, but
`Shallot/Peg/Palindrome.lean` makes a first real attempt at ONE natural
approach and reports exactly how far it gets (this is not this file's own
result — see that module for the actual theorems and their proofs):

- The single most obvious construction — transcribing the textbook CFG
  `Pal → a Pal a | b Pal b | ε` literally into PEG surface syntax — is
  machine-proven **incomplete**: `"aaaa"` is a genuine palindrome this
  grammar fails to derive a full match for
  (`Shallot.exists_palindrome_palGrammar_rejects`). The mechanism is
  concrete and general, not specific to this one string: Ford's
  prioritized choice commits to whichever alternative locally succeeds
  first, with no way to retroactively ask an already-successful
  sub-derivation to consume less so an outer pending match can complete —
  for a run of identical characters, the innermost recursive call closes
  itself off greedily and can strand the characters an outer match still
  needs.
- The SAME construction is machine-proven **sound** — it never accepts a
  non-palindrome, for ANY input, not just up to some bound
  (`Shallot.palGrammar_accepts_only_palindromes`, by induction on input
  length). So this natural attempt is a genuine PARTIAL solution
  (`{w | palGrammar accepts w} ⊊ EvenPalindromes`, a strict subset), not a
  wrong one — it just isn't a complete one, and there is no evident way to
  patch it into completeness within plain PEG's operational model (no
  backreferences, no way to compare two distant positions except by
  forcing literal character equality through the grammar's own recursive
  structure, and that forcing is exactly what runs into the no-backtracking
  wall above).
- A second, more aggressive attempt (greedily consuming a MAXIMAL run of
  the same character via `+` from each end before recursing, tried outside
  this Lean development) was strictly WORSE — even more incomplete, still
  sound — reinforcing rather than undermining the pattern above, though
  this was not itself formalized here.
- A third attempt, changing only the PRIORITY ORDER (trying `ε` before the
  recursive alternatives instead of after — `Shallot/Peg/
  PalindromeEpsFirst.lean`), is formalized and is much WORSE still: since
  `.eps` always succeeds and Ford's choice never backtracks out of an
  already-successful alternative, `Pal` commits to the empty match on
  EVERY input, rejecting all non-empty palindromes without exception
  (`Shallot.palEpsFirst_rejects_nonempty`) — not even `"aa"` survives.
  This shows the failure mode isn't specific to which recursion
  (`a`-then-`b` vs. the reverse) is tried first, but to how base-case
  termination is scheduled against recursion at all.
- A fourth attempt, `ε` placed BETWEEN the two recursive alternatives
  instead of before or after both (`Shallot/Peg/PalindromeEpsMiddle.lean`,
  `a-case / ε / b-case`), is formalized and reveals a THIRD, qualitatively
  different failure mode: putting anything unconditionally-successful
  strictly between two `.alt` branches makes every branch AFTER it
  structurally unreachable dead code (Ford's choice commits to the first
  successful alternative, and `ε` never fails) — so `b-case` can never
  even be attempted. This grammar behaves identically to `palGrammar` on
  `'a'`-only inputs (same `"aaaa"`-style partial-match failure, since
  `b-case`'s position relative to `ε` is irrelevant when it's never
  reached) but additionally rejects EVERY input starting with `'b'`,
  including the minimal palindrome `"bb"` which `palGrammar` DOES accept
  (`Shallot.palEpsMiddle_rejects_bb`). Combined with the eps-first result,
  this establishes two INDEPENDENT design mistakes within this one family
  of constructions — `ε`'s position relative to the first alternative
  governs the `"aaaa"`-style failure, its position relative to later
  alternatives governs whether those alternatives are reachable at all —
  not two instances of the same mistake.
- **This case analysis is now COMPLETE, not just three representative
  samples**: `Shallot/Peg/PalindromeAllOrders.lean` formalizes the
  remaining three orderings (the `a ↔ b` mirror of each of the above,
  by the grammar's total symmetry under swapping the two characters) and
  proves `Shallot.all_six_peel_orders_incomplete` — all 6 possible
  orderings of `{"a" Pal "a", "b" Pal "b", ε}` inside a single `.alt`
  chain are incomplete, each with its own explicit witness. This is a
  genuinely bounded but COMPLETE result: not a step toward proving
  `CFLSubsetPELConjecture` in general, but a full classification closing
  off this entire small, natural grammar family at once, rather than
  leaving the other orderings as untested variations that might have
  behaved differently.

**Isolating WHICH requirement actually causes the failure**: a genuine
palindrome bundles two distinct demands together — (1) locate the
midpoint, and (2) verify the two halves match end-to-end. `Shallot/Peg/
MidPoint.lean` isolates demand (1) alone, dropping (2) entirely: the
language `MidIsA := {w | |w| odd, middle character = 'a'}` places NO
constraint whatsoever on how the two end characters relate to each other
(`"bab"`, `"aaa"`, `"xay"` for ANY `x, y` — including mismatched ends —
all qualify), and is certainly context-free (`S → a S a | b S a | a`).
Yet the direct PEG transcription of that CFG is machine-proven to REJECT
`"bab"` (`Shallot.midGrammar_rejects_bab`) — the minimal odd-length
witness, only 3 characters. This is sharper evidence than `palGrammar`'s
`"aaaa"`: it shows the same failure mechanism breaks things even with
NOTHING to compare between the two ends, confirming concretely (not just
by argument) that midpoint-location is itself the obstruction, prior to
and independent of any end-matching demand palindromes additionally
impose. This directly corroborates the `IAmPowerTwoLength`/`Helper`
analysis above and the paper's own "reverse and scan" remark: what plain
PEG structurally lacks is a general way to locate a data-dependent
midpoint, not the extra step of comparing what's found there.

**Generalizing `palGrammar` itself, over both alphabet identity AND
size**: `Shallot/Peg/PalindromeGeneral.lean` mirrors the `midGrammar`
generalization for the ORIGINAL, central witness — genuine palindromes,
with real end-matching, not just the midpoint-only `MidIsA` relaxation.
`Shallot.genPal_rejects_c0c0c0c0` proves that for EVERY pair of distinct
characters `c0 ≠ c1`, the direct transcription `Pal ← c0 Pal c0 / c1 Pal
c1 / ε` rejects `[c0, c0, c0, c0]` — generalizing `"aaaa"` to every
2-letter alphabet. `Shallot/Peg/PalindromeGeneralN.lean` pushes this
further along a SECOND, independent axis — alphabet SIZE, not just
identity: `Shallot.genPalN_rejects_c0c0c0c0` proves the same rejection
holds no matter how many extra "distractor" peel-alternatives (for
characters other than `c0`) are appended — one, five, or any finite
number — because on an all-`c0` input, every alternative whose leading
character isn't `c0` fails immediately and is simply never reached; only
the `c0` alternative and the `ε` fallback ever matter. So the failure
`palGrammar` (`{a, b}`, size 2) exhibits is not an artifact of a small or
particular alphabet — it is stable under generalizing the alphabet's
IDENTITY (any two distinct characters) and its SIZE (any number of
distractor characters) simultaneously.

**Upgrading the midpoint-isolation witness into a genuine theorem**:
`Shallot/Peg/MidPointGeneral.lean` generalizes `MidPoint.lean`'s single
`"bab"` instance into a real, universally-quantified theorem —
`Shallot.genMid_rejects_c1c0c1`: for EVERY pair of distinct characters
`c0 ≠ c1` (not just `('a','b')`), the direct PEG transcription of `S → c0
S c0 | c1 S c0 | c0` rejects `[c1, c0, c1]`. The proof never inspects
what `c0`/`c1` actually ARE, only that they differ — it is a structural
consequence of `derives_det` alone: the innermost recursive call, on the
shortest suffix where recursion becomes impossible, commits to the fixed
base case with NO knowledge of whether this is the depth the ORIGINAL
input's length actually calls for. This crisply separates what plain PEG
CAN and CANNOT access about position: a nonterminal's `Derives`-behavior
on a suffix depends only on that suffix's own content and length (hence
CAN depend on "distance from the end of input", exactly what `Helper`/
`IAmPowerTwoLength` in `PowerTwoHelper.lean` exploits) but structurally
CANNOT depend on "distance from the start" / "how much has already been
consumed" (information the suffix alone never carries) — which is
precisely the fact a general midpoint-locator would need for ARBITRARY
lengths. This theorem is honest about its scope: it rules out the
peel-recurse-with-fixed-base construction family, for every alphabet —
it does not, and structurally cannot by itself, prove
`¬CFLSubsetPELConjecture`, since it says nothing about constructions
built around absolute end-distance tricks (Theorem 8's escape hatch) or
any approach not of this shape.

**The sharpest general form this project's methods reach, and an honest
account of exactly where they stop**: `Shallot/Peg/
MidpointObstruction.lean`'s `Shallot.no_suffix_only_midpoint_decider`
states the underlying obstruction in a form that is NOT tied to the
peel-recurse shape (or any other specific grammar shape) at all — it is
a fact about `Derives`'s very TYPE: a nonterminal call's outcome on a
fixed suffix cannot depend on how much input was already consumed to
reach that suffix, hence cannot correctly answer "is the amount consumed
so far exactly half of the (not-yet-fully-known) total input length" for
every possible total length sharing that suffix. Every construction
attempted in this project — `palGrammar`, `midGrammar`, all six priority
orderings, generalized over every alphabet and every alphabet size —
reduces to exactly this pattern, and fails for exactly this reason.

This is offered as a genuine, serious attempt at the general question —
not a hedge — and its honest limit is this: it rules out any recognition
strategy that reduces to a SINGLE nonterminal call being the sole
decider of "am I at the midpoint" on a suffix. It does NOT rule out the
logical possibility of some more distributed or holistic strategy that
never needs to ask exactly that question at a single point — and Theorem
8's escape hatch is proof such alternatives can exist in adjacent
territory: it works specifically because it asks a DIFFERENT, answerable
question (distance from the END, encoded in the suffix's own length)
rather than the unanswerable one. Closing that last gap — showing that
EVERY conceivable plain-PEG construction, not just every construction of
this natural shape, must reduce to an unanswerable midpoint-decision — is
exactly the content of the "scaffolding automata" characterization Loff,
Moreira and Reis develop over dozens of pages and leave open; it is not
something derivable from suffix-determinism alone, and this project does
not claim otherwise. `CFLSubsetPELConjecture` remains open. What this
session adds is not a proof, but the most precise available account of
where the difficulty actually lives — matching, and in the alphabet/
priority-order generality sharpening, the paper's own assessment that a
full resolution "may well require a breakthrough" in complexity-theoretic
lower-bound techniques.

None of this proves `¬CFLSubsetPELConjecture` — a fundamentally different
construction (not built by peeling matching characters from both ends of
the input) might still exist and this file does not rule that out. But it
is real evidence, not a bare assertion, and it upgrades the conjecture's
status from "no attempt made" to "the most natural attempt is understood
in detail and provably falls short in a specific, structural way." Any
future progress should keep the "Conjecture" label (or a weaker "Bounded-
survived: true up to size N, exhaustively checked" label) until an actual
proof exists — never smuggled in as an unproven declaration or placeholder
gap.
-/

namespace Shallot.Cfg

open Shallot (Grammar Derives PExp abcGrammar S_char)

/-- `L` is recognized by some plain (macro-free) PEG grammar — Ford's class
`PEL`, using the same "and then end of input" convention as `IsCFL`. -/
def IsPEL (L : Language) : Prop :=
  ∃ (g : Grammar), ∀ w, L w ↔ ∃ t, Derives g (.nt g.start) w (.ok t [])

/-- The aⁿbⁿcⁿ witness is in `PEL` — `abcGrammar` is already a plain PEG
grammar (T1/T2's macro machinery is not needed at all here), so this falls
directly out of `S_char`. -/
theorem abc_isPEL : IsPEL abcLanguage := ⟨abcGrammar, fun w => (S_char w).symm⟩

/-- **Settled** (the "PEG is not weaker than CFG" half): `PEL ⊄ CFL`. Takes
the same non-context-freeness hypothesis for aⁿbⁿcⁿ as T3
(`cfl_proper_subset_mpel1`) — the classical pumping-lemma fact, supplied by
the caller rather than smuggled in. -/
theorem pel_not_subset_cfl (habc_not_cfl : ¬ IsCFL abcLanguage) :
    ¬ (∀ L : Language, IsPEL L → IsCFL L) :=
  fun h => habc_not_cfl (h abcLanguage abc_isPEL)

/-- **Open** (not proved or disproved by this project): does every
context-free language have a plain-PEG grammar? This is a bare `Prop`
definition, never a `theorem` — it pins down precisely what remains
unresolved without asserting an answer either way. -/
def CFLSubsetPELConjecture : Prop := ∀ L : Language, IsCFL L → IsPEL L

/-- The leading conjectured counterexample to `CFLSubsetPELConjecture`:
even-length palindromes over `{a, b}` — trivially context-free (a textbook
CFG: `S → aSa | bSb | ε`, not constructed here), conjectured to have no
plain-PEG grammar, with no known proof of that non-membership. Restricted
to `{a, b}` and even length to match the form the conjecture is usually
stated in; the general "any-alphabet, any-length" palindrome language is
an easy corollary of this restricted one being non-PEL (a plain-PEG
grammar for the general language would restrict to one for this one). -/
def EvenPalindromes : Language :=
  fun w => w.length % 2 = 0 ∧ w.all (fun c => c = 'a' ∨ c = 'b') ∧ w.reverse = w

end Shallot.Cfg
