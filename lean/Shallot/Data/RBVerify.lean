import Shallot.Data.RBMap

/-!
# Verified core theorems for the red-black tree map (M6)

Proof inventory over `Shallot.Data.RBMap`:

* **R5** — `cmpStr` order theory: reflexivity, symmetry of `.eq`, the
  `.lt`/`.gt` flip, transitivity of `.lt`, and left/right congruence,
  all built from `cmpChar`/`cmpChars` by list induction (no `String`
  or `Char` extensionality anywhere — we work purely with `Cmp`).
* **Ordered / R1** — the BST invariant (`AllKeys` bounds + `Ordered`),
  `ordered_balance` (Okasaki's four cases + catch-all), and
  `ordered_insert`.
* **R3** — `find_insert`: the find/insert model refinement, via
  `find?_balance` (find? ignores rebalancing) and `find?_blacken`.
* **R6** — `find_fromList`: `find? (fromList l) = assocLookup l`, the
  load-bearing refinement for the interpreter's function table.
-/

namespace Shallot

deriving instance DecidableEq for Cmp

/-! ## Cmp flip -/

/-- Flip a comparison result (what swapping the arguments does). -/
def Cmp.flip : Cmp → Cmp
  | .lt => .gt
  | .eq => .eq
  | .gt => .lt

/-! ## R5a — cmpChar spec: reduce to `Nat` facts on codepoints -/

theorem cmpChar_lt_spec (a b : Char) : cmpChar a b = Cmp.lt ↔ a.toNat < b.toNat := by
  unfold cmpChar
  split
  · rename_i h
    simp at h
    simp [h]
  · rename_i h1
    simp at h1
    split
    · rename_i h2
      simp at h2
      constructor
      · intro hc; cases hc
      · intro hc; omega
    · rename_i h2
      simp at h2
      constructor
      · intro hc; cases hc
      · intro hc; omega

theorem cmpChar_gt_spec (a b : Char) : cmpChar a b = Cmp.gt ↔ b.toNat < a.toNat := by
  unfold cmpChar
  split
  · rename_i h
    simp at h
    constructor
    · intro hc; cases hc
    · intro hc; omega
  · rename_i h1
    simp at h1
    split
    · rename_i h2
      simp at h2
      simp [h2]
    · rename_i h2
      simp at h2
      constructor
      · intro hc; cases hc
      · intro hc; omega

theorem cmpChar_eq_spec (a b : Char) : cmpChar a b = Cmp.eq ↔ a.toNat = b.toNat := by
  unfold cmpChar
  split
  · rename_i h
    simp at h
    constructor
    · intro hc; cases hc
    · intro hc; omega
  · rename_i h1
    simp at h1
    split
    · rename_i h2
      simp at h2
      constructor
      · intro hc; cases hc
      · intro hc; omega
    · rename_i h2
      simp at h2
      simp
      omega

theorem cmpChar_refl (a : Char) : cmpChar a a = Cmp.eq :=
  (cmpChar_eq_spec a a).mpr rfl

theorem cmpChar_flip (a b : Char) : cmpChar b a = (cmpChar a b).flip := by
  cases h : cmpChar a b with
  | lt =>
    rw [cmpChar_lt_spec] at h
    exact (cmpChar_gt_spec b a).mpr h
  | eq =>
    rw [cmpChar_eq_spec] at h
    exact (cmpChar_eq_spec b a).mpr h.symm
  | gt =>
    rw [cmpChar_gt_spec] at h
    exact (cmpChar_lt_spec b a).mpr h

theorem cmpChar_lt_trans {a b c : Char} (h1 : cmpChar a b = Cmp.lt)
    (h2 : cmpChar b c = Cmp.lt) : cmpChar a c = Cmp.lt := by
  rw [cmpChar_lt_spec] at h1 h2 ⊢
  omega

theorem cmpChar_eq_trans {a b c : Char} (h1 : cmpChar a b = Cmp.eq)
    (h2 : cmpChar b c = Cmp.eq) : cmpChar a c = Cmp.eq := by
  rw [cmpChar_eq_spec] at h1 h2 ⊢
  omega

theorem cmpChar_eq_congr_left {a b : Char} (h : cmpChar a b = Cmp.eq) (c : Char) :
    cmpChar a c = cmpChar b c := by
  rw [cmpChar_eq_spec] at h
  unfold cmpChar
  rw [h]

theorem cmpChar_eq_congr_right {b c : Char} (h : cmpChar b c = Cmp.eq) (a : Char) :
    cmpChar a b = cmpChar a c := by
  rw [cmpChar_eq_spec] at h
  unfold cmpChar
  rw [h]

/-! ## R5b — cmpChars: lift the cmpChar facts through list induction -/

theorem cmpChars_refl (l : List Char) : cmpChars l l = Cmp.eq := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [cmpChars, cmpChar_refl]
    exact ih

theorem cmpChars_flip (l1 : List Char) : ∀ (l2 : List Char),
    cmpChars l2 l1 = (cmpChars l1 l2).flip := by
  induction l1 with
  | nil =>
    intro l2
    cases l2 <;> rfl
  | cons a as ih =>
    intro l2
    cases l2 with
    | nil => rfl
    | cons b bs =>
      simp only [cmpChars, cmpChar_flip a b]
      cases hab : cmpChar a b <;> simp [Cmp.flip, ih bs]

theorem cmpChars_cons_lt_iff (a b : Char) (as bs : List Char) :
    cmpChars (a :: as) (b :: bs) = Cmp.lt ↔
      cmpChar a b = Cmp.lt ∨ (cmpChar a b = Cmp.eq ∧ cmpChars as bs = Cmp.lt) := by
  simp only [cmpChars]
  cases h : cmpChar a b <;> simp

theorem cmpChars_cons_eq_iff (a b : Char) (as bs : List Char) :
    cmpChars (a :: as) (b :: bs) = Cmp.eq ↔
      cmpChar a b = Cmp.eq ∧ cmpChars as bs = Cmp.eq := by
  simp only [cmpChars]
  cases h : cmpChar a b <;> simp

theorem cmpChars_lt_trans : ∀ (l1 l2 l3 : List Char),
    cmpChars l1 l2 = Cmp.lt → cmpChars l2 l3 = Cmp.lt → cmpChars l1 l3 = Cmp.lt := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 l3 h1 h2
    cases l2 with
    | nil => simp [cmpChars] at h1
    | cons b bs =>
      cases l3 with
      | nil => simp [cmpChars] at h2
      | cons c cs => rfl
  | cons a as ih =>
    intro l2 l3 h1 h2
    cases l2 with
    | nil => simp [cmpChars] at h1
    | cons b bs =>
      cases l3 with
      | nil => simp [cmpChars] at h2
      | cons c cs =>
        rw [cmpChars_cons_lt_iff] at h1 h2 ⊢
        rcases h1 with hab | ⟨hab, has⟩
        · rcases h2 with hbc | ⟨hbc, hbs⟩
          · exact Or.inl (cmpChar_lt_trans hab hbc)
          · rw [cmpChar_eq_congr_right hbc a] at hab
            exact Or.inl hab
        · rcases h2 with hbc | ⟨hbc, hbs⟩
          · rw [← cmpChar_eq_congr_left hab c] at hbc
            exact Or.inl hbc
          · exact Or.inr ⟨cmpChar_eq_trans hab hbc, ih bs cs has hbs⟩

theorem cmpChars_eq_congr_left : ∀ (l1 l2 l3 : List Char),
    cmpChars l1 l2 = Cmp.eq → cmpChars l1 l3 = cmpChars l2 l3 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 l3 h
    cases l2 with
    | nil => rfl
    | cons b bs => simp [cmpChars] at h
  | cons a as ih =>
    intro l2 l3 h
    cases l2 with
    | nil => simp [cmpChars] at h
    | cons b bs =>
      rw [cmpChars_cons_eq_iff] at h
      obtain ⟨hab, has⟩ := h
      cases l3 with
      | nil => rfl
      | cons c cs =>
        simp only [cmpChars]
        rw [cmpChar_eq_congr_left hab c]
        cases hbc : cmpChar b c <;> simp [ih bs cs has]

/-! ## R5 — cmpStr order theory -/

theorem cmpStr_refl (a : String) : cmpStr a a = Cmp.eq :=
  cmpChars_refl a.toList

theorem cmpStr_flip (a b : String) : cmpStr b a = (cmpStr a b).flip :=
  cmpChars_flip a.toList b.toList

theorem cmpStr_eq_symm {a b : String} (h : cmpStr a b = Cmp.eq) : cmpStr b a = Cmp.eq := by
  rw [cmpStr_flip, h]
  rfl

theorem cmpStr_lt_gt {a b : String} : cmpStr a b = Cmp.lt ↔ cmpStr b a = Cmp.gt := by
  constructor
  · intro h
    rw [cmpStr_flip, h]
    rfl
  · intro h
    rw [cmpStr_flip] at h
    cases hab : cmpStr a b with
    | lt => rfl
    | eq => rw [hab] at h; simp [Cmp.flip] at h
    | gt => rw [hab] at h; simp [Cmp.flip] at h

theorem cmpStr_gt_of_lt {a b : String} (h : cmpStr a b = Cmp.lt) : cmpStr b a = Cmp.gt :=
  cmpStr_lt_gt.mp h

theorem cmpStr_lt_of_gt {a b : String} (h : cmpStr a b = Cmp.gt) : cmpStr b a = Cmp.lt :=
  cmpStr_lt_gt.mpr h

theorem cmpStr_lt_trans {a b c : String} (h1 : cmpStr a b = Cmp.lt)
    (h2 : cmpStr b c = Cmp.lt) : cmpStr a c = Cmp.lt :=
  cmpChars_lt_trans a.toList b.toList c.toList h1 h2

theorem cmpStr_eq_congr_left {a b : String} (h : cmpStr a b = Cmp.eq) (c : String) :
    cmpStr a c = cmpStr b c :=
  cmpChars_eq_congr_left a.toList b.toList c.toList h

theorem cmpStr_eq_congr_right {b c : String} (h : cmpStr b c = Cmp.eq) (a : String) :
    cmpStr a b = cmpStr a c := by
  rw [cmpStr_flip b a, cmpStr_flip c a, cmpStr_eq_congr_left h a]

theorem cmpStr_eq_trans {a b c : String} (h1 : cmpStr a b = Cmp.eq)
    (h2 : cmpStr b c = Cmp.eq) : cmpStr a c = Cmp.eq := by
  rw [cmpStr_eq_congr_left h1 c]
  exact h2

theorem cmpStr_gt_trans {a b c : String} (h1 : cmpStr a b = Cmp.gt)
    (h2 : cmpStr b c = Cmp.gt) : cmpStr a c = Cmp.gt :=
  cmpStr_gt_of_lt (cmpStr_lt_trans (cmpStr_lt_of_gt h2) (cmpStr_lt_of_gt h1))

theorem cmpStr_lt_of_lt_of_eq {a b c : String} (h1 : cmpStr a b = Cmp.lt)
    (h2 : cmpStr b c = Cmp.eq) : cmpStr a c = Cmp.lt := by
  rw [← cmpStr_eq_congr_right h2 a]
  exact h1

theorem cmpStr_lt_of_eq_of_lt {a b c : String} (h1 : cmpStr a b = Cmp.eq)
    (h2 : cmpStr b c = Cmp.lt) : cmpStr a c = Cmp.lt := by
  rw [cmpStr_eq_congr_left h1 c]
  exact h2

/-! ## Bound predicates and the BST invariant -/

namespace RBNode

/-- Every key in the tree satisfies `P`. -/
def AllKeys {α : Type} (P : String → Prop) : RBNode α → Prop
  | .leaf => True
  | .node _ l k _ r => P k ∧ AllKeys P l ∧ AllKeys P r

/-- The BST ordering invariant: at every node, all keys on the left
compare `.lt` to the node key and all keys on the right compare `.gt`. -/
inductive Ordered {α : Type} : RBNode α → Prop where
  | leaf : Ordered .leaf
  | node {c : RBColor} {l : RBNode α} {k : String} {v : α} {r : RBNode α} :
      Ordered l → Ordered r →
      AllKeys (fun x => cmpStr x k = Cmp.lt) l →
      AllKeys (fun x => cmpStr x k = Cmp.gt) r →
      Ordered (RBNode.node c l k v r)

theorem ordered_node_iff {α : Type} {c : RBColor} {l r : RBNode α} {k : String} {v : α} :
    Ordered (RBNode.node c l k v r) ↔
      Ordered l ∧ Ordered r ∧
        AllKeys (fun x => cmpStr x k = Cmp.lt) l ∧
        AllKeys (fun x => cmpStr x k = Cmp.gt) r := by
  constructor
  · intro h
    cases h with
    | node h1 h2 h3 h4 => exact ⟨h1, h2, h3, h4⟩
  · intro h
    exact Ordered.node h.1 h.2.1 h.2.2.1 h.2.2.2

theorem allKeys_imp {α : Type} {P Q : String → Prop} (h : ∀ (x : String), P x → Q x) :
    ∀ (t : RBNode α), AllKeys P t → AllKeys Q t := by
  intro t
  induction t with
  | leaf =>
    intro _
    simp only [AllKeys]
  | node c l k v r ihl ihr =>
    intro ht
    simp only [AllKeys] at ht ⊢
    exact ⟨h k ht.1, ihl ht.2.1, ihr ht.2.2⟩

theorem allKeys_lt_of_lt {α : Type} {t : RBNode α} {a b : String}
    (ht : AllKeys (fun x => cmpStr x a = Cmp.lt) t) (hab : cmpStr a b = Cmp.lt) :
    AllKeys (fun x => cmpStr x b = Cmp.lt) t :=
  allKeys_imp (fun _ hx => cmpStr_lt_trans hx hab) t ht

theorem allKeys_gt_of_gt {α : Type} {t : RBNode α} {a b : String}
    (ht : AllKeys (fun x => cmpStr x b = Cmp.gt) t) (hab : cmpStr a b = Cmp.lt) :
    AllKeys (fun x => cmpStr x a = Cmp.gt) t :=
  allKeys_imp (fun _ hx => cmpStr_gt_trans hx (cmpStr_gt_of_lt hab)) t ht

theorem allKeys_balance {α : Type} {P : String → Prop} (c : RBColor) (l : RBNode α)
    (k : String) (v : α) (r : RBNode α)
    (hl : AllKeys P l) (hk : P k) (hr : AllKeys P r) :
    AllKeys P (balance c l k v r) := by
  unfold balance
  split
  all_goals simp_all [AllKeys]

/-- `balance` preserves the ordering invariant given the component bounds. -/
theorem ordered_balance {α : Type} {c : RBColor} {l r : RBNode α} {k : String} {v : α}
    (hl : Ordered l) (hr : Ordered r)
    (hlk : AllKeys (fun x => cmpStr x k = Cmp.lt) l)
    (hrk : AllKeys (fun x => cmpStr x k = Cmp.gt) r) :
    Ordered (balance c l k v r) := by
  unfold balance
  split
  · -- l = node red (node red a xk xv b) yk yv c'
    simp only [ordered_node_iff, AllKeys] at hl hlk ⊢
    obtain ⟨⟨hOa, hOb, hax, hbx⟩, hOc', ⟨hxy, hay, hby⟩, hcy⟩ := hl
    obtain ⟨hyk, ⟨hxk, hak, hbk⟩, hck⟩ := hlk
    exact ⟨⟨hOa, hOb, hax, hbx⟩, ⟨hOc', hr, hck, hrk⟩, ⟨hxy, hay, hby⟩,
      ⟨cmpStr_gt_of_lt hyk, hcy, allKeys_gt_of_gt hrk hyk⟩⟩
  · -- l = node red a xk xv (node red b yk yv c')
    simp only [ordered_node_iff, AllKeys] at hl hlk ⊢
    obtain ⟨hOa, ⟨hOb, hOc', hby, hcy⟩, hax, ⟨hyx, hbx, hcx⟩⟩ := hl
    obtain ⟨hxk, hak, ⟨hyk, hbk, hck⟩⟩ := hlk
    exact ⟨⟨hOa, hOb, hax, hbx⟩, ⟨hOc', hr, hck, hrk⟩,
      ⟨cmpStr_lt_of_gt hyx, allKeys_lt_of_lt hax (cmpStr_lt_of_gt hyx), hby⟩,
      ⟨cmpStr_gt_of_lt hyk, hcy, allKeys_gt_of_gt hrk hyk⟩⟩
  · -- r = node red (node red b yk yv c') zk zv d
    simp only [ordered_node_iff, AllKeys] at hr hrk ⊢
    obtain ⟨⟨hOb, hOc', hby, hcy⟩, hOd, ⟨hyz, hbz, hcz⟩, hdz⟩ := hr
    obtain ⟨hzk, ⟨hyk, hbk, hck⟩, hdk⟩ := hrk
    exact ⟨⟨hl, hOb, hlk, hbk⟩, ⟨hOc', hOd, hcz, hdz⟩,
      ⟨cmpStr_lt_of_gt hyk, allKeys_lt_of_lt hlk (cmpStr_lt_of_gt hyk), hby⟩,
      ⟨cmpStr_gt_of_lt hyz, hcy, allKeys_gt_of_gt hdz hyz⟩⟩
  · -- r = node red b yk yv (node red c' zk zv d)
    simp only [ordered_node_iff, AllKeys] at hr hrk ⊢
    obtain ⟨hOb, ⟨hOc', hOd, hcz, hdz⟩, hby, ⟨hzy, hcy, hdy⟩⟩ := hr
    obtain ⟨hyk, hbk, ⟨hzk, hck, hdk⟩⟩ := hrk
    exact ⟨⟨hl, hOb, hlk, hbk⟩, ⟨hOc', hOd, hcz, hdz⟩,
      ⟨cmpStr_lt_of_gt hyk, allKeys_lt_of_lt hlk (cmpStr_lt_of_gt hyk), hby⟩,
      ⟨hzy, hcy, hdy⟩⟩
  · -- catch-all: balance is the identity reshaping
    exact Ordered.node hl hr hlk hrk

theorem allKeys_ins {α : Type} {P : String → Prop} (key : String) (val : α) :
    ∀ (t : RBNode α), AllKeys P t → P key → AllKeys P (ins key val t) := by
  intro t
  induction t with
  | leaf =>
    intro _ hk
    simp [ins, AllKeys]
    exact hk
  | node c l k v r ihl ihr =>
    intro ht hk
    simp only [AllKeys] at ht
    obtain ⟨hkk, hall, harr⟩ := ht
    simp only [ins]
    cases hc : cmpStr key k with
    | lt => exact allKeys_balance c (ins key val l) k v r (ihl hall hk) hkk harr
    | gt => exact allKeys_balance c l k v (ins key val r) hall hkk (ihr harr hk)
    | eq =>
      show AllKeys P (RBNode.node c l key val r)
      simp only [AllKeys]
      exact ⟨hk, hall, harr⟩

theorem ordered_ins {α : Type} (key : String) (val : α) :
    ∀ {t : RBNode α}, Ordered t → Ordered (ins key val t) := by
  intro t
  induction t with
  | leaf =>
    intro _
    exact Ordered.node Ordered.leaf Ordered.leaf True.intro True.intro
  | node c l k v r ihl ihr =>
    intro h
    rw [ordered_node_iff] at h
    obtain ⟨hol, hor, hlk, hrk⟩ := h
    simp only [ins]
    cases hc : cmpStr key k with
    | lt => exact ordered_balance (ihl hol) hor (allKeys_ins key val l hlk hc) hrk
    | gt => exact ordered_balance hol (ihr hor) hlk (allKeys_ins key val r hrk hc)
    | eq =>
      refine Ordered.node hol hor ?_ ?_
      · refine allKeys_imp (fun x hx => ?_) l hlk
        rw [← cmpStr_eq_congr_right (cmpStr_eq_symm hc) x]
        exact hx
      · refine allKeys_imp (fun x hx => ?_) r hrk
        rw [← cmpStr_eq_congr_right (cmpStr_eq_symm hc) x]
        exact hx

theorem ordered_blacken {α : Type} {t : RBNode α} (h : Ordered t) : Ordered (blacken t) := by
  cases t with
  | leaf => exact Ordered.leaf
  | node c l k v r =>
    have h' := ordered_node_iff.mp h
    exact Ordered.node h'.1 h'.2.1 h'.2.2.1 h'.2.2.2

/-- **R1** — `insert` preserves the ordering invariant. -/
theorem ordered_insert {α : Type} {t : RBNode α} (h : Ordered t) (k : String) (v : α) :
    Ordered (insert t k v) :=
  ordered_blacken (ordered_ins k v h)

/-! ## R3 — find/insert model -/

/-- `find?` cannot tell a rebalanced node from the unbalanced one,
given the BST side conditions on the components. -/
theorem find?_balance {α : Type} (c : RBColor) (l : RBNode α) (k : String) (v : α)
    (r : RBNode α) (key : String)
    (hl : Ordered l) (hr : Ordered r)
    (hlk : AllKeys (fun x => cmpStr x k = Cmp.lt) l)
    (hrk : AllKeys (fun x => cmpStr x k = Cmp.gt) r) :
    find? (balance c l k v r) key = find? (RBNode.node c l k v r) key := by
  unfold balance
  split
  · -- l = node red (node red a xk xv b) yk yv c'
    simp only [AllKeys] at hlk
    obtain ⟨hyk, -, -⟩ := hlk
    cases h1 : cmpStr key _ with
    | lt =>
      have h2 : cmpStr key k = Cmp.lt := cmpStr_lt_trans h1 hyk
      simp [find?, h1, h2]
    | eq =>
      have h2 : cmpStr key k = Cmp.lt := cmpStr_lt_of_eq_of_lt h1 hyk
      simp [find?, h1, h2]
    | gt =>
      cases h2 : cmpStr key k <;> simp [find?, h1, h2]
  · -- l = node red a xk xv (node red b yk yv c')
    simp only [ordered_node_iff, AllKeys] at hl hlk
    obtain ⟨-, -, -, hyx, -, -⟩ := hl
    obtain ⟨hxk, -, ⟨hyk, -, -⟩⟩ := hlk
    cases h1 : cmpStr key _ with
    | lt =>
      have hky : cmpStr key _ = Cmp.lt := cmpStr_lt_trans h1 (cmpStr_lt_of_gt hyx)
      have hkk : cmpStr key k = Cmp.lt := cmpStr_lt_trans h1 hxk
      simp [find?, h1, hky, hkk]
    | eq =>
      have hky : cmpStr key _ = Cmp.lt := cmpStr_lt_of_eq_of_lt h1 (cmpStr_lt_of_gt hyx)
      have hkk : cmpStr key k = Cmp.lt := cmpStr_lt_of_eq_of_lt h1 hxk
      simp [find?, h1, hky, hkk]
    | gt =>
      cases h2 : cmpStr key _ with
      | lt =>
        have hkk : cmpStr key k = Cmp.lt := cmpStr_lt_trans h2 hyk
        simp [find?, h1, h2, hkk]
      | eq =>
        have hkk : cmpStr key k = Cmp.lt := cmpStr_lt_of_eq_of_lt h2 hyk
        simp [find?, h1, h2, hkk]
      | gt =>
        cases h3 : cmpStr key k <;> simp [find?, h1, h2, h3]
  · -- r = node red (node red b yk yv c') zk zv d
    simp only [ordered_node_iff, AllKeys] at hr hrk
    obtain ⟨-, -, ⟨hyz, -, -⟩, -⟩ := hr
    obtain ⟨-, ⟨hyk, -, -⟩, -⟩ := hrk
    cases h1 : cmpStr key k with
    | lt =>
      have hky : cmpStr key _ = Cmp.lt := cmpStr_lt_trans h1 (cmpStr_lt_of_gt hyk)
      simp [find?, h1, hky]
    | eq =>
      have hky : cmpStr key _ = Cmp.lt := cmpStr_lt_of_eq_of_lt h1 (cmpStr_lt_of_gt hyk)
      simp [find?, h1, hky]
    | gt =>
      cases h2 : cmpStr key _ with
      | lt =>
        have hkz : cmpStr key _ = Cmp.lt := cmpStr_lt_trans h2 hyz
        simp [find?, h1, h2, hkz]
      | eq =>
        have hkz : cmpStr key _ = Cmp.lt := cmpStr_lt_of_eq_of_lt h2 hyz
        simp [find?, h1, h2, hkz]
      | gt => simp [find?, h1, h2]
  · -- r = node red b yk yv (node red c' zk zv d)
    simp only [AllKeys] at hrk
    obtain ⟨hyk, -, -⟩ := hrk
    cases h1 : cmpStr key k with
    | lt =>
      have hky : cmpStr key _ = Cmp.lt := cmpStr_lt_trans h1 (cmpStr_lt_of_gt hyk)
      simp [find?, h1, hky]
    | eq =>
      have hky : cmpStr key _ = Cmp.lt := cmpStr_lt_of_eq_of_lt h1 (cmpStr_lt_of_gt hyk)
      simp [find?, h1, hky]
    | gt => simp [find?, h1]
  · -- catch-all
    rfl

theorem find?_blacken {α : Type} (t : RBNode α) (key : String) :
    find? (blacken t) key = find? t key := by
  cases t <;> rfl

theorem find_ins {α : Type} (key key' : String) (val : α) :
    ∀ {t : RBNode α}, Ordered t →
      find? (ins key val t) key' =
        if cmpStr key' key = Cmp.eq then some val else find? t key' := by
  intro t
  induction t with
  | leaf =>
    intro _
    cases h : cmpStr key' key <;> simp [ins, find?, h]
  | node c l k v r ihl ihr =>
    intro h
    rw [ordered_node_iff] at h
    obtain ⟨hol, hor, hlk, hrk⟩ := h
    simp only [ins]
    cases hc : cmpStr key k with
    | lt =>
      show find? (balance c (ins key val l) k v r) key' = _
      rw [find?_balance c (ins key val l) k v r key' (ordered_ins key val hol) hor
        (allKeys_ins key val l hlk hc) hrk]
      cases hck : cmpStr key' k with
      | lt => simp [find?, hck, ihl hol]
      | eq =>
        have hne : cmpStr key' key = Cmp.gt := by
          rw [cmpStr_eq_congr_left hck key]
          exact cmpStr_gt_of_lt hc
        simp [find?, hck, hne]
      | gt =>
        have hne : cmpStr key' key = Cmp.gt := cmpStr_gt_trans hck (cmpStr_gt_of_lt hc)
        simp [find?, hck, hne]
    | gt =>
      show find? (balance c l k v (ins key val r)) key' = _
      rw [find?_balance c l k v (ins key val r) key' hol (ordered_ins key val hor)
        hlk (allKeys_ins key val r hrk hc)]
      cases hck : cmpStr key' k with
      | gt => simp [find?, hck, ihr hor]
      | eq =>
        have hne : cmpStr key' key = Cmp.lt := by
          rw [cmpStr_eq_congr_left hck key]
          exact cmpStr_lt_of_gt hc
        simp [find?, hck, hne]
      | lt =>
        have hne : cmpStr key' key = Cmp.lt := cmpStr_lt_trans hck (cmpStr_lt_of_gt hc)
        simp [find?, hck, hne]
    | eq =>
      show find? (RBNode.node c l key val r) key' = _
      cases hck : cmpStr key' key with
      | eq => simp [find?, hck]
      | lt =>
        have h2 : cmpStr key' k = Cmp.lt := by
          rw [← cmpStr_eq_congr_right hc key']
          exact hck
        simp [find?, hck, h2]
      | gt =>
        have h2 : cmpStr key' k = Cmp.gt := by
          rw [← cmpStr_eq_congr_right hc key']
          exact hck
        simp [find?, hck, h2]

/-- **R3** — the find/insert model refinement. -/
theorem find_insert {α : Type} {t : RBNode α} (h : Ordered t) (k k' : String) (v : α) :
    find? (insert t k v) k' = if cmpStr k' k = Cmp.eq then some v else find? t k' := by
  show find? (blacken (ins k v t)) k' = _
  rw [find?_blacken]
  exact find_ins k k' v h

/-! ## R6 — the load-bearing model refinement -/

theorem ordered_fromList {α : Type} : ∀ (l : List (String × α)), Ordered (fromList l)
  | [] => Ordered.leaf
  | (k, v) :: rest => ordered_insert (ordered_fromList rest) k v

/-- **R6** — `fromList` refines first-match association lookup.
`fromList` inserts from the right, so the head is inserted LAST and
wins — exactly `assocLookup`'s first-match semantics. -/
theorem find_fromList {α : Type} : ∀ (l : List (String × α)) (k : String),
    find? (fromList l) k = assocLookup l k := by
  intro l
  induction l with
  | nil =>
    intro k
    rfl
  | cons p rest ih =>
    intro k
    obtain ⟨pk, pv⟩ := p
    show find? (insert (fromList rest) pk pv) k = assocLookup ((pk, pv) :: rest) k
    rw [find_insert (ordered_fromList rest)]
    simp only [assocLookup]
    cases h : cmpStr k pk with
    | eq => simp
    | lt => simp [ih]
    | gt => simp [ih]

end RBNode

end Shallot
