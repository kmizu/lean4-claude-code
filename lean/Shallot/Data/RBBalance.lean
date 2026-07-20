import Shallot.Data.RBMap

/-!
# Red-black balance preservation for insertion (Okasaki)

The classic Okasaki proof that `RBNode.insert` preserves the red-black
invariant, in the style of Nipkow's *Functional Data Structures* and
Appel's *Verified Functional Algorithms*.

Invariants:

* `IsRB t c n` — `t` is well-colored with black-height `n`, valid under a
  parent of color `c`: under a red parent (`c = .red`) the root must be
  black (or a leaf); under a black parent any root color is allowed. This
  encodes "red nodes have black children" and "every root-to-leaf path
  passes through exactly `n` black nodes".
* `InsRB t n` — the "infrared" invariant for the intermediate result of
  `ins`: both children are genuine red-black trees of black-height `n`
  (in the permissive `.black` parent context), but if the root is red one
  of its children may itself be red — exactly the one-step violation that
  `balance` at the black grandparent repairs.

Results:

* `balance_rb_left` / `balance_rb_right` / `balance_rb` — `balance`
  restores `IsRB` from the broken configurations.
* `ins_rb` — `ins` maps `IsRB t .black n` to `InsRB _ n` and
  `IsRB t .red n` (black-rooted input) to `IsRB _ .black n`.
* `rb_insert` — insertion preserves the red-black invariant
  (`blacken` fixes the root; the black-height may grow by one).
-/

set_option autoImplicit false

namespace Shallot
namespace RBBalance

/-- `IsRB t c n`: `t` is a well-colored red-black tree with black-height
`n`, valid under a parent of color `c`. A red-rooted tree is only valid
under a black parent (`IsRB.red` concludes at context `.black` and demands
its children be valid under a red parent, i.e. black-rooted), so red nodes
always have black children. Black nodes are valid in any context and add
one to the black height. `IsRB t .red n` (valid under a red parent) is the
stronger statement: it additionally forces the root of `t` to be black. -/
inductive IsRB {α : Type} : RBNode α → RBColor → Nat → Prop where
  | leaf (c : RBColor) : IsRB .leaf c 0
  | red {l r : RBNode α} (k : String) (v : α) {n : Nat}
      (hl : IsRB l .red n) (hr : IsRB r .red n) :
      IsRB (.node .red l k v r) .black n
  | black {l r : RBNode α} (c : RBColor) (k : String) (v : α) {n : Nat}
      (hl : IsRB l .black n) (hr : IsRB r .black n) :
      IsRB (.node .black l k v r) c (n + 1)

/-- The "infrared" invariant for the intermediate `ins` result: both
children are genuine red-black trees of black-height `n` (in the
permissive `.black` context), but a red root is allowed to have a red
child. A black-height-0 leaf is included so that every valid tree in a
black context is infrared (`insRB_of_isRB`). -/
inductive InsRB {α : Type} : RBNode α → Nat → Prop where
  | leaf : InsRB .leaf 0
  | red {l r : RBNode α} (k : String) (v : α) {n : Nat}
      (hl : IsRB l .black n) (hr : IsRB r .black n) :
      InsRB (.node .red l k v r) n
  | black {l r : RBNode α} (k : String) (v : α) {n : Nat}
      (hl : IsRB l .black n) (hr : IsRB r .black n) :
      InsRB (.node .black l k v r) (n + 1)

/-- Context weakening: a tree valid under a red parent (black-rooted) is
valid under a parent of any color. -/
theorem IsRB.weaken {α : Type} {t : RBNode α} {n : Nat} (c : RBColor)
    (h : IsRB t .red n) : IsRB t c n := by
  cases h with
  | leaf => exact .leaf c
  | black => rename_i hl hr; exact .black c _ _ hl hr

/-- Every genuine red-black tree (in the permissive `.black` context) is
in particular infrared. -/
theorem insRB_of_isRB {α : Type} {t : RBNode α} {n : Nat}
    (h : IsRB t .black n) : InsRB t n := by
  cases h with
  | leaf => exact .leaf
  | red => rename_i hl hr; exact .red _ _ (IsRB.weaken _ hl) (IsRB.weaken _ hr)
  | black => rename_i hl hr; exact .black _ _ hl hr

/-- `balance` at a red node is the identity rebuild: none of the four
rotation cases applies. -/
theorem balance_red {α : Type} (l : RBNode α) (k : String) (v : α) (r : RBNode α) :
    RBNode.balance .red l k v r = .node .red l k v r := rfl

/-- `balance` at a black node repairs an infrared left child: if `l` is
infrared with black-height `n` and `r` is a genuine red-black tree with
black-height `n`, the result is a genuine red-black tree with black-height
`n + 1` (possibly red-rooted, hence valid in the `.black` context). -/
theorem balance_rb_left {α : Type} {l r : RBNode α} {k : String} {v : α} {n : Nat} :
    InsRB l n → IsRB r .black n →
    IsRB (RBNode.balance .black l k v r) .black (n + 1) := by
  unfold RBNode.balance
  split
  · -- Case 1: l = node red (node red a xk xv b) yk yv c'
    intro hl hr
    cases hl with
    | red =>
      rename_i h1 h2
      cases h1 with
      | red =>
        rename_i ha hb
        exact .red _ _ (.black _ _ _ (IsRB.weaken _ ha) (IsRB.weaken _ hb))
          (.black _ _ _ h2 hr)
  · -- Case 2: l = node red a xk xv (node red b yk yv c')
    intro hl hr
    cases hl with
    | red =>
      rename_i h1 h2
      cases h2 with
      | red =>
        rename_i hb hc
        exact .red _ _ (.black _ _ _ h1 (IsRB.weaken _ hb))
          (.black _ _ _ (IsRB.weaken _ hc) hr)
  · -- Case 3: r has a red root with a red left child — impossible, r is valid
    intro hl hr
    cases hr with
    | red => rename_i h1 h2; nomatch h1
  · -- Case 4: r has a red root with a red right child — impossible, r is valid
    intro hl hr
    cases hr with
    | red => rename_i h1 h2; nomatch h2
  · -- Catch-all: no rotation fired, so l has no red-red violation at the root
    rename_i h1 h2 h3 h4
    intro hl hr
    refine .black _ _ _ ?_ hr
    cases hl with
    | leaf => exact .leaf _
    | black => rename_i ha hb; exact .black _ _ _ ha hb
    | red =>
      rename_i ha hb
      refine .red _ _ ?_ ?_
      · -- left child of the red root is not red (else case 1 would have fired)
        cases ha with
        | leaf => exact .leaf _
        | black => rename_i hc hd; exact .black _ _ _ hc hd
        | red => exact (h1 _ _ _ _ _ _ _ rfl rfl).elim
      · -- right child of the red root is not red (else case 2 would have fired)
        cases hb with
        | leaf => exact .leaf _
        | black => rename_i hc hd; exact .black _ _ _ hc hd
        | red => exact (h2 _ _ _ _ _ _ _ rfl rfl).elim

/-- `balance` at a black node repairs an infrared right child (mirror of
`balance_rb_left`). -/
theorem balance_rb_right {α : Type} {l r : RBNode α} {k : String} {v : α} {n : Nat} :
    IsRB l .black n → InsRB r n →
    IsRB (RBNode.balance .black l k v r) .black (n + 1) := by
  unfold RBNode.balance
  split
  · -- Case 1: l has a red root with a red left child — impossible, l is valid
    intro hl hr
    cases hl with
    | red => rename_i h1 h2; nomatch h1
  · -- Case 2: l has a red root with a red right child — impossible, l is valid
    intro hl hr
    cases hl with
    | red => rename_i h1 h2; nomatch h2
  · -- Case 3: r = node red (node red b yk yv c') zk zv d
    intro hl hr
    cases hr with
    | red =>
      rename_i h1 h2
      cases h1 with
      | red =>
        rename_i hb hc
        exact .red _ _ (.black _ _ _ hl (IsRB.weaken _ hb))
          (.black _ _ _ (IsRB.weaken _ hc) h2)
  · -- Case 4: r = node red b yk yv (node red c' zk zv d)
    intro hl hr
    cases hr with
    | red =>
      rename_i h1 h2
      cases h2 with
      | red =>
        rename_i hc hd
        exact .red _ _ (.black _ _ _ hl h1)
          (.black _ _ _ (IsRB.weaken _ hc) (IsRB.weaken _ hd))
  · -- Catch-all: no rotation fired, so r has no red-red violation at the root
    rename_i h1 h2 h3 h4
    intro hl hr
    refine .black _ _ _ hl ?_
    cases hr with
    | leaf => exact .leaf _
    | black => rename_i ha hb; exact .black _ _ _ ha hb
    | red =>
      rename_i ha hb
      refine .red _ _ ?_ ?_
      · -- left child of the red root is not red (else case 3 would have fired)
        cases ha with
        | leaf => exact .leaf _
        | black => rename_i hc hd; exact .black _ _ _ hc hd
        | red => exact (h3 _ _ _ _ _ _ _ rfl rfl).elim
      · -- right child of the red root is not red (else case 4 would have fired)
        cases hb with
        | leaf => exact .leaf _
        | black => rename_i hc hd; exact .black _ _ _ hc hd
        | red => exact (h4 _ _ _ _ _ _ _ rfl rfl).elim

/-- `balance_rb`: the balance function restores the red-black invariant
from the broken (infrared) configurations, on either side. -/
theorem balance_rb {α : Type} {l r : RBNode α} {k : String} {v : α} {n : Nat} :
    (InsRB l n → IsRB r .black n →
      IsRB (RBNode.balance .black l k v r) .black (n + 1)) ∧
    (IsRB l .black n → InsRB r n →
      IsRB (RBNode.balance .black l k v r) .black (n + 1)) :=
  ⟨balance_rb_left, balance_rb_right⟩

/-- `ins_rb`: `ins` preserves black-height `n` and produces
* an infrared tree, if the input was a red-black tree in the permissive
  `.black` context (root of any color), and
* a genuine red-black tree (possibly red-rooted), if the input was valid
  under a red parent (black-rooted input).
-/
theorem ins_rb {α : Type} (key : String) (val : α) (t : RBNode α) :
    ∀ n : Nat,
      (IsRB t .black n → InsRB (RBNode.ins key val t) n) ∧
      (IsRB t .red n → IsRB (RBNode.ins key val t) .black n) := by
  induction t with
  | leaf =>
    intro n
    refine ⟨?_, ?_⟩
    · intro h
      cases h
      simp only [RBNode.ins]
      exact .red key val (.leaf _) (.leaf _)
    · intro h
      cases h
      simp only [RBNode.ins]
      exact .red key val (.leaf _) (.leaf _)
  | node c l k v r ihl ihr =>
    intro n
    cases c with
    | red =>
      refine ⟨?_, ?_⟩
      · intro h
        cases h with
        | red =>
          rename_i hl hr
          simp only [RBNode.ins]
          split
          · -- key < k: insert left; the red root may go infrared
            rw [balance_red]
            exact .red k v ((ihl n).2 hl) (IsRB.weaken _ hr)
          · -- key > k: insert right
            rw [balance_red]
            exact .red k v (IsRB.weaken _ hl) ((ihr n).2 hr)
          · -- key = k: overwrite in place
            exact .red key val (IsRB.weaken _ hl) (IsRB.weaken _ hr)
      · -- a red-rooted tree is never valid under a red parent
        intro h
        nomatch h
    | black =>
      refine ⟨?_, ?_⟩
      · intro h
        cases h with
        | black =>
          rename_i hl hr
          simp only [RBNode.ins]
          split
          · exact insRB_of_isRB (balance_rb_left ((ihl _).1 hl) hr)
          · exact insRB_of_isRB (balance_rb_right hl ((ihr _).1 hr))
          · exact .black key val hl hr
      · intro h
        cases h with
        | black =>
          rename_i hl hr
          simp only [RBNode.ins]
          split
          · exact balance_rb_left ((ihl _).1 hl) hr
          · exact balance_rb_right hl ((ihr _).1 hr)
          · exact .black _ key val hl hr

/-- Painting the root black turns any infrared tree into a genuine
red-black tree (black-height grows by one iff the root was red). -/
theorem blacken_rb {α : Type} {t : RBNode α} {n : Nat} (h : InsRB t n) :
    ∃ n', IsRB (RBNode.blacken t) .black n' := by
  cases h with
  | leaf => exact ⟨0, .leaf _⟩
  | red => rename_i hl hr; exact ⟨_, .black _ _ _ hl hr⟩
  | black => rename_i hl hr; exact ⟨_, .black _ _ _ hl hr⟩

/-- **`rb_insert`** — the headline: insertion preserves the red-black
invariant. If `t` is a red-black tree with black-height `n`, then
`insert t key val` is a red-black tree (for some black-height `n'`). -/
theorem rb_insert {α : Type} {t : RBNode α} {n : Nat} (key : String) (val : α)
    (h : IsRB t .black n) :
    ∃ n', IsRB (RBNode.insert t key val) .black n' :=
  blacken_rb ((ins_rb key val t n).1 h)

end RBBalance
end Shallot
