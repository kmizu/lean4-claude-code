import Cfg.Properness
import Shallot.Peg.Palindrome
import Shallot.Peg.PowerTwoHelper

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
