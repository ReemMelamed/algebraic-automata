/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Max
public import AlgebraicAutomata.FactorizationForest.Basic

/-!
# Combine Splits Construction

Defines the Simon complexity `nSElement` and sequence `buildXSeq`, and proves the gluing
lemma `combineSplits_props` that assembles a global Ramsey split from interval splits.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

@[expose] public section


namespace RamseySplit

open GreensRelations

variable {S : Type*} [Semigroup S] [Fintype S]

open Classical in
/-- The Simon complexity of `x ∈ S`, recursively summing `nD` along ascending `J`-chains. -/
noncomputable abbrev nSElement (x : S) : ℕ :=
  let currentCost := nD (IsGreenD.eqvClass x)
  let strictlyAbove := Finset.univ.filter
    (fun (y : S) => GreenJClass.mk x < GreenJClass.mk y)
  let maxAbove := strictlyAbove.attach.sup (fun ⟨y, _hy⟩ => nSElement y)
  currentCost + maxAbove
termination_by (Finset.univ.filter
  (fun (y : S) => GreenJClass.mk x < GreenJClass.mk y)).card
decreasing_by
  have h_lt : GreenJClass.mk x < GreenJClass.mk y :=
    (Finset.mem_filter.mp _hy).right
  have h_le : Finset.univ.filter (fun (z : S) => GreenJClass.mk y < GreenJClass.mk z) ⊆
              Finset.univ.filter (fun (z : S) => GreenJClass.mk x < GreenJClass.mk z) := by
    grind
  have h_ne : Finset.univ.filter (fun (z : S) => GreenJClass.mk y < GreenJClass.mk z) ≠
              Finset.univ.filter (fun (z : S) => GreenJClass.mk x < GreenJClass.mk z) := by
    grind
  exact Finset.card_lt_card (lt_of_le_of_ne h_le h_ne)

open Classical in
/-- The maximum Simon complexity over all elements of the semigroup `S`.
This is the global bound used in the statement of Simon's theorem. -/
noncomputable abbrev nS (S : Type*) [Semigroup S] [Fintype S] : ℕ :=
  let all_vals := Finset.univ.image (fun (x : S) => nSElement x)
  if h : all_vals.Nonempty then
    Finset.max' all_vals h
  else
    0

/-- The Simon complexity of any element `x ∈ S` is strictly positive.
This follows from the fact that `nD` is always positive. -/
lemma nSElement_pos (x : S) : 0 < nSElement x := by
  rw [nSElement]
  have h_pos := nD_pos (IsGreenD.eqvClass x) ⟨x, rfl⟩
  omega

/-- `Fin (nSElement x)` is nonempty since `nSElement` is always positive.
This instance is used to satisfy the `Nonempty (Fin h)` hypothesis in the
split construction lemmas. -/
instance instNonemptyFin_nSElement (x : S) : Nonempty (Fin (nSElement x)) :=
  Fin.pos_iff_nonempty.mp (nSElement_pos x)

/-- The Simon complexity `nS S` of any non-empty finite semigroup `S` is strictly positive. -/
lemma nS_pos {S : Type*} [Semigroup S] [Fintype S] [Nonempty S] : 0 < nS S :=
  let ⟨x⟩ : Nonempty S := inferInstance
  have h_mem := Finset.mem_image_of_mem (nSElement : S → ℕ) (Finset.mem_univ x)
  have h_eq : nS S = Finset.max' _ ⟨nSElement x, h_mem⟩ := dite_eq_left ⟨nSElement x, h_mem⟩
  h_eq.symm ▸ (nSElement_pos x).trans_le (Finset.le_max' _ _ h_mem)

/-- `Fin (nS S)` is non-empty for any non-empty finite semigroup `S`. -/
instance instNonemptyFin_nS {S : Type*} [Semigroup S] [Fintype S] [Nonempty S] :
    Nonempty (Fin (nS S)) :=
  Fin.pos_iff_nonempty.mp nS_pos

open Classical in
/-- In a finite semigroup, `nD D` is bounded by the cardinality of `D`. -/
lemma nD_le_card_eqvClass (x : S) :
    nD (IsGreenD.eqvClass x) ≤ (Finset.univ.filter (· ∈ IsGreenD.eqvClass x)).card := by
  dsimp [nD]
  split_ifs with hReg
  · apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.1
  · have hx_mem : x ∈ Finset.univ.filter (· ∈ IsGreenD.eqvClass x) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact IsGreenD.refl x
    exact Finset.card_pos.mpr ⟨x, hx_mem⟩

open Classical in
omit [Fintype S] in
/-- Membership in the $\mathcal{D}$-class coincides with equality of $\mathcal{J}$-classes
in finite semigroups. -/
lemma mem_isGreenD_eqvClass_iff_greenJClass_eq [Finite S] (x z : S) :
    z ∈ IsGreenD.eqvClass x ↔ GreenJClass.mk z = GreenJClass.mk x := by
  grind [GreenJClass.mk_eq_mk_iff, isGreenJ_of_isGreenD, isGreenD_of_isGreenJ]

open Classical in
/-- The fiber of elements $\mathcal{D}$-equivalent to `x` equals the fiber of elements
with the same $\mathcal{J}$-class. -/
lemma filter_isGreenD_eqvClass_eq (x : S) :
    Finset.univ.filter (· ∈ IsGreenD.eqvClass x) =
    Finset.univ.filter (fun z ↦ GreenJClass.mk z = GreenJClass.mk x) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_isGreenD_eqvClass_iff_greenJClass_eq x z

open Classical in
/-- The cost `nD` of the $\mathcal{D}$-class is bounded by the size of the
corresponding $\mathcal{J}$-class. -/
lemma nD_le_card_j_eq (x : S) :
    nD (IsGreenD.eqvClass x) ≤
      (Finset.univ.filter (fun z ↦ GreenJClass.mk z = GreenJClass.mk x)).card := by
  rw [← filter_isGreenD_eqvClass_eq]
  exact nD_le_card_eqvClass x

open Classical in
/-- The number of elements strictly above in the $\mathcal{J}$-order decreases strictly
when moving up. -/
lemma strictlyAbove_card_lt {x y : S} (hlt : GreenJClass.mk x < GreenJClass.mk y) :
    (Finset.univ.filter (fun z ↦ GreenJClass.mk y < GreenJClass.mk z)).card <
    (Finset.univ.filter (fun z ↦ GreenJClass.mk x < GreenJClass.mk z)).card := by
  have h_le : Finset.univ.filter (fun (z : S) => GreenJClass.mk y < GreenJClass.mk z) ⊆
              Finset.univ.filter (fun (z : S) => GreenJClass.mk x < GreenJClass.mk z) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hlt.trans hz
  have h_ne' : Finset.univ.filter (fun (z : S) => GreenJClass.mk y < GreenJClass.mk z) ≠
              Finset.univ.filter (fun (z : S) => GreenJClass.mk x < GreenJClass.mk z) := by
    intro heq
    have h_mem : y ∈ Finset.univ.filter (fun (z : S) => GreenJClass.mk x < GreenJClass.mk z) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlt
    rw [← heq] at h_mem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_mem
    exact lt_irrefl _ h_mem
  exact Finset.card_lt_card (lt_of_le_of_ne h_le h_ne')

open Classical in
/-- Auxiliary bound on `nSElement x` by elements with $\mathcal{J}$-class $\ge \mathcal{J}(x)$,
by induction on the strictly above count. -/
theorem nSElement_le_card_ge_aux (n : ℕ) (x : S)
    (hn : (Finset.univ.filter (fun y ↦ GreenJClass.mk x < GreenJClass.mk y)).card ≤ n) :
    nSElement x ≤ (Finset.univ.filter (fun z ↦ GreenJClass.mk x ≤ GreenJClass.mk z)).card := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    rw [nSElement]
    dsimp only
    set currentCost := nD (IsGreenD.eqvClass x)
    set strictlyAbove := Finset.univ.filter (fun (y : S) => GreenJClass.mk x < GreenJClass.mk y)
    set maxAbove := strictlyAbove.attach.sup (fun ⟨y, _hy⟩ => nSElement y)
    set A := Finset.univ.filter (fun z ↦ GreenJClass.mk z = GreenJClass.mk x)
    have h_nD : currentCost ≤ A.card := nD_le_card_j_eq x
    set Target := Finset.univ.filter (fun z ↦ GreenJClass.mk x ≤ GreenJClass.mk z)
    have h_A_sub : A ⊆ Target := by
      intro z hz
      have h_eq : GreenJClass.mk z = GreenJClass.mk x := (Finset.mem_filter.mp hz).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h_eq]⟩
    have h_A_le : A.card ≤ Target.card := Finset.card_le_card h_A_sub
    have h_sup_le : maxAbove ≤ Target.card - A.card := by
      apply Finset.sup_le
      rintro ⟨y, hy_mem⟩ -
      have hy_lt : GreenJClass.mk x < GreenJClass.mk y :=
        (Finset.mem_filter.mp hy_mem).2
      have h_card_y := strictlyAbove_card_lt hy_lt
      have h_y_lt_n : (Finset.univ.filter (fun z ↦ GreenJClass.mk y < GreenJClass.mk z)).card < n :=
        h_card_y.trans_le hn
      have ih_y := ih (Finset.univ.filter (fun z ↦ GreenJClass.mk y < GreenJClass.mk z)).card
        h_y_lt_n y le_rfl
      set B := Finset.univ.filter (fun z ↦ GreenJClass.mk y ≤ GreenJClass.mk z)
      have h_disj : Disjoint A B := by
        rw [Finset.disjoint_filter]
        intro z _ hzA hzB
        rw [hzA] at hzB
        exact lt_irrefl _ (hy_lt.trans_le hzB)
      have h_sub : A ∪ B ⊆ Target := by
        intro z hz
        rcases Finset.mem_union.mp hz with hA | hB
        · have h_eq := (Finset.mem_filter.mp hA).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h_eq]⟩
        · have h_le := (Finset.mem_filter.mp hB).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy_lt.le.trans h_le⟩
      have h_union_card : (A ∪ B).card = A.card + B.card :=
        Finset.card_union_of_disjoint h_disj
      have h_card_le := Finset.card_le_card h_sub
      rw [h_union_card] at h_card_le
      have : nSElement y ≤ Target.card - A.card := by omega
      exact this
    change currentCost + maxAbove ≤ Target.card
    omega

open Classical in
/-- The Simon complexity of `x ∈ S` is bounded by the number of elements with J-class ≥ x. -/
theorem nSElement_le_card_ge (x : S) :
    nSElement x ≤ (Finset.univ.filter (fun z ↦ GreenJClass.mk x ≤ GreenJClass.mk z)).card :=
  nSElement_le_card_ge_aux _ x le_rfl

open Classical in
/-- Simon complexity of an element is bounded by the cardinality of `S`. -/
theorem nSElement_le_card (x : S) : nSElement x ≤ Fintype.card S := by
  apply (nSElement_le_card_ge x).trans
  have h_sub : Finset.univ.filter (fun z ↦ GreenJClass.mk x ≤ GreenJClass.mk z) ⊆ Finset.univ :=
    Finset.filter_subset _ _
  have h_le := Finset.card_le_card h_sub
  rw [Finset.card_univ] at h_le
  exact h_le

open Classical in
/-- The Simon complexity `nS S` is bounded by the cardinality of `S` (Colcombet line 361). -/
theorem nS_le_card : nS S ≤ Fintype.card S := by
  dsimp [nS]
  split_ifs with h
  · have h_mem := Finset.max'_mem _ h
    rw [Finset.mem_image] at h_mem
    obtain ⟨x, _, hx_eq⟩ := h_mem
    rw [← hx_eq]
    exact nSElement_le_card x
  · exact Nat.zero_le _


open Classical in
/-- Constructs jump points partitioning the domain, stepping to the minimal `y > x`
with `IsGreenD (σ(x, y)) a`. -/
noncomputable abbrev buildXSeq (a : S) {α : Type*} [LinearOrder α] [Fintype α]
    (σ : MultiplicativeLabeling S α) (x : α) : List α :=
  let candidates := Finset.univ.filter (fun y => x < y ∧ IsGreenD (σ.σ x y) a)
  if h : candidates.Nonempty then
    let y := Finset.min' candidates h
    x :: buildXSeq a σ y
  else
    [x]
termination_by (Finset.univ.filter (fun z => x < z)).card
decreasing_by
  have h_lt : x < y := (Finset.mem_filter.mp (Finset.min'_mem _ h)).2.1
  have h_le : Finset.univ.filter (y < ·) ⊆ Finset.univ.filter (x < ·) :=
    fun _ hz ↦ Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hz).1, h_lt.trans (Finset.mem_filter.mp hz).2⟩
  have h_ne : Finset.univ.filter (y < ·) ≠ Finset.univ.filter (x < ·) :=
    fun heq ↦ lt_irrefl y (Finset.mem_filter.mp
      (heq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ y, h_lt⟩ : y ∈ _)).2
  exact Finset.card_lt_card (lt_of_le_of_ne h_le h_ne)

/-- The elements built by `buildXSeq` cover the interval `[x₀, ∞)`: any
element `x ≥ x₀` that is not in the sequence lies strictly between two
consecutive sequence elements. -/
lemma buildXSeq_covers {S α : Type*} [Semigroup S] [Fintype S]
    [LinearOrder α] [Fintype α]
    (a : S) (σ : MultiplicativeLabeling S α) (x₀ : α) (x : α)
    (h_x0_le_x : x₀ ≤ x) :
    x ∉ buildXSeq a σ x₀ →
    ∃ (i : ℕ) (hi_lt : i < (buildXSeq a σ x₀).length),
      (buildXSeq a σ x₀).get ⟨i, hi_lt⟩ < x ∧
      ∀ (hi_succ_lt : i + 1 < (buildXSeq a σ x₀).length),
        x < (buildXSeq a σ x₀).get ⟨i + 1, hi_succ_lt⟩ := fun h_not_in ↦ by
  have h_x0_in : x₀ ∈ buildXSeq a σ x₀ := by
    rw [buildXSeq]
    split_ifs <;> exact .head _
  exact list_interval_covers x _ h_not_in
    ⟨x₀, h_x0_in, lt_of_le_of_ne h_x0_le_x (fun heq ↦ h_not_in (heq ▸ h_x0_in))⟩



/-- The first element of the sequence `buildXSeq a σ w` is exactly `w`. -/
lemma buildXSeq_head (a : S) {α : Type*} [LinearOrder α] [Fintype α]
    (σ : MultiplicativeLabeling S α) (w : α)
    (h : 0 < (buildXSeq a σ w).length) :
    (buildXSeq a σ w).get ⟨0, h⟩ = w := by
  classical
  generalize h_xs : buildXSeq a σ w = xs at h ⊢
  have h_eq : buildXSeq a σ w =
    if h_cond : (Finset.univ.filter
        (fun y => w < y ∧ IsGreenD (σ.σ w y) a)).Nonempty then
      w :: buildXSeq a σ (Finset.min' _ h_cond)
    else [w] := by rw [buildXSeq]
  rw [h_eq] at h_xs
  split_ifs at h_xs <;> subst h_xs <;> rfl

/-- Sequence points are `≥ w`, strictly monotone, pairwise `D`-related, with no intermediate
`D`-related points. -/
lemma buildXSeq_properties (a : S) {α : Type*} [LinearOrder α] [Fintype α]
    (σ : MultiplicativeLabeling S α) (h_img : labelingIn σ (jUp a)) (w : α) :
    (∀ y ∈ buildXSeq a σ w, w ≤ y) ∧
    (∀ x ∈ buildXSeq a σ w, ∀ y ∈ buildXSeq a σ w,
        x < y → IsGreenD (σ.σ x y) a) ∧
    (∀ (i : ℕ) (hi_lt : i < (buildXSeq a σ w).length) (y : α),
      (buildXSeq a σ w).get ⟨i, hi_lt⟩ < y →
      (∀ hi_succ_lt : i + 1 < (buildXSeq a σ w).length,
        y < (buildXSeq a σ w).get ⟨i + 1, hi_succ_lt⟩) →
      ¬ IsGreenD (σ.σ ((buildXSeq a σ w).get ⟨i, hi_lt⟩) y) a) ∧
    (∀ (i j : ℕ) (hi_lt : i < (buildXSeq a σ w).length)
        (hj_lt : j < (buildXSeq a σ w).length),
      i < j → (buildXSeq a σ w).get ⟨i, hi_lt⟩ <
        (buildXSeq a σ w).get ⟨j, hj_lt⟩) := by
  classical
  have h_eq : buildXSeq a σ w =
    if h_cond : (Finset.univ.filter
        (fun y => w < y ∧ IsGreenD (σ.σ w y) a)).Nonempty then
      w :: buildXSeq a σ (Finset.min' _ h_cond)
    else [w] := by rw [buildXSeq]
  by_cases h : (Finset.univ.filter
      (fun y => w < y ∧ IsGreenD (σ.σ w y) a)).Nonempty
  · let w' := Finset.min' _ h
    have hw' : w < w' ∧ IsGreenD (σ.σ w w') a :=
      Finset.mem_filter.mp (Finset.min'_mem _ h) |>.right
    have ih := buildXSeq_properties a σ h_img w'
    obtain ⟨ih_ge, ih_range, ih_gap, ih_mono⟩ := ih
    have h_xs : buildXSeq a σ w = w :: buildXSeq a σ w' := by
      rw [h_eq, dite_eq_left h]
    constructor
    · grind
    constructor
    · intro x hx y hy hlt
      rw [h_xs] at hx hy
      exact match List.mem_cons.mp hx, List.mem_cons.mp hy with
      | Or.inl hx_eq, Or.inl hy_eq => by
        rw [hx_eq, hy_eq] at hlt
        nomatch (lt_irrefl w hlt)
      | Or.inl hx_eq, Or.inr hy_tail =>
          hx_eq ▸ isGreenD_of_prefix a σ h_img w w' y hw'.1
            (ih_ge y hy_tail) hw'.2
      | Or.inr hx_tail, Or.inl hy_eq => by
        rw [hy_eq] at hlt
        nomatch (lt_irrefl w
          (lt_trans (lt_of_lt_of_le hw'.1 (ih_ge x hx_tail)) hlt))
      | Or.inr hx_tail, Or.inr hy_tail =>
          ih_range x hx_tail y hy_tail hlt
    constructor
    · intro i hi_lt y h_lt h_gt h_D
      generalize h_xs_gen : buildXSeq a σ w = xs at hi_lt h_lt h_gt h_D ⊢
      rw [h_xs] at h_xs_gen
      subst h_xs_gen
      cases i with
      | zero =>
        have hy_mem : y ∈ Finset.univ.filter
            (fun z => w < z ∧ IsGreenD (σ.σ w z) a) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ y, h_lt, h_D⟩
        have hw'_le_y : w' ≤ y := Finset.min'_le _ _ hy_mem
        have hw_len_lt : 1 < (w :: buildXSeq a σ w').length := by
          simp only [List.length_cons, Nat.succ_lt_succ_iff]
          rw [buildXSeq]
          split_ifs <;> exact Nat.zero_lt_succ _
        have h_y_lt_w' : y < w' :=
          buildXSeq_head a σ w' _ ▸ h_gt hw_len_lt
        exact lt_irrefl _ (lt_of_lt_of_le h_y_lt_w' hw'_le_y)
      | succ i' =>
        have hi_tail : i' < (buildXSeq a σ w').length :=
          Nat.succ_lt_succ_iff.mp hi_lt
        exact ih_gap i' hi_tail y h_lt
          (fun hi_succ_lt => h_gt (Nat.succ_lt_succ hi_succ_lt)) h_D
    · intro i j hi_lt hj_lt hij
      generalize h_xs_gen : buildXSeq a σ w = xs at hi_lt hj_lt ⊢
      rw [h_xs] at h_xs_gen
      subst h_xs_gen
      cases j with
      | zero => omega
      | succ j' =>
        cases i with
        | zero =>
          exact lt_of_lt_of_le hw'.1
            (ih_ge _ (List.mem_iff_get.mpr ⟨⟨j', Nat.succ_lt_succ_iff.mp hj_lt⟩, rfl⟩))
        | succ i' =>
          exact ih_mono i' j' (Nat.succ_lt_succ_iff.mp hi_lt)
            (Nat.succ_lt_succ_iff.mp hj_lt) (Nat.succ_lt_succ_iff.mp hij)
  · have h_xs : buildXSeq a σ w = [w] := by rw [h_eq, dite_eq_right h]
    have h_cov : ∀ (i : ℕ) (hi_lt : i < (buildXSeq a σ w).length) (y : α),
        (buildXSeq a σ w).get ⟨i, hi_lt⟩ < y →
        (∀ (hi_succ_lt : i + 1 < (buildXSeq a σ w).length),
          y < (buildXSeq a σ w).get ⟨i + 1, hi_succ_lt⟩) →
        ¬IsGreenD (σ.σ ((buildXSeq a σ w).get ⟨i, hi_lt⟩) y) a := by
      intro i hi_lt y h_lt h_gt h_D
      generalize h_xs_gen : buildXSeq a σ w = xs at hi_lt h_lt h_gt h_D ⊢
      rw [h_xs] at h_xs_gen
      subst h_xs_gen
      cases i with
      | zero => exact h ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, h_lt, h_D⟩⟩
      | succ i' => nomatch (Nat.not_lt_zero i' (Nat.succ_lt_succ_iff.mp hi_lt))
    have h_mono : ∀ (i j : ℕ) (hi_lt : i < (buildXSeq a σ w).length)
        (hj_lt : j < (buildXSeq a σ w).length),
        i < j → (buildXSeq a σ w).get ⟨i, hi_lt⟩ < (buildXSeq a σ w).get ⟨j, hj_lt⟩ := by
      intro i j hi_lt hj_lt hij
      generalize h_xs_gen : buildXSeq a σ w = xs at hi_lt hj_lt ⊢
      rw [h_xs] at h_xs_gen
      subst h_xs_gen
      cases j with
      | zero => omega
      | succ j' => nomatch (Nat.not_lt_zero _ (Nat.succ_lt_succ_iff.mp hj_lt))
    exact ⟨by simp [h_xs], by simp [h_xs], h_cov, h_mono⟩
termination_by (Finset.univ.filter (fun z => w < z)).card
decreasing_by
  classical
  have hw_lt : w < Finset.min' _ h := (Finset.mem_filter.mp (Finset.min'_mem _ h)).2.1
  have h_le : Finset.univ.filter (Finset.min' _ h < ·) ⊆ Finset.univ.filter (w < ·) :=
    fun _ hz ↦ Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hz).1, hw_lt.trans (Finset.mem_filter.mp hz).2⟩
  have h_ne : Finset.univ.filter (Finset.min' _ h < ·) ≠ Finset.univ.filter (w < ·) :=
    fun heq ↦ lt_irrefl _ (Finset.mem_filter.mp
      (heq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw_lt⟩ : _ ∈ _)).2
  exact Finset.card_lt_card (lt_of_le_of_ne h_le h_ne)

/-- If two elements `p` and `q` (both not in `xs`) are split-related under a
combined split, they must lie in the same open interval. This key lemma shows
that the split relation cannot straddle an interval boundary. -/
lemma buildXSeq_same_interval_of_splitRelation {α : Type*} [LinearOrder α]
    {n : ℕ}
    (xs : List α)
    (s : Split α n)
    (C : ℕ)
    (h_xs_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length)
        (hj_lt : j < xs.length), i < j →
      xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩)
    (rank_ge_diff_of_mem : ∀ z, z ∈ xs → C ≤ (s z).val)
    (rank_lt_diff_of_not_mem : ∀ z, z ∉ xs → (s z).val < C)
    (p q : α)
    (hp : p ∉ xs) (hq : q ∉ xs)
    (hsr_pq : SplitRelation s p q)
    (i j : ℕ)
    (p_oi : OpenIntervalType xs i) (q_oi : OpenIntervalType xs j)
    (hp_eq : p_oi.val = p) (hq_eq : q_oi.val = q) :
    i = j := by
  have h_not_lt : ∀ (i j : ℕ) (p q : α) (hp : p ∉ xs)
      (p_oi : OpenIntervalType xs i) (q_oi : OpenIntervalType xs j)
      (hp_eq : p_oi.val = p) (hq_eq : q_oi.val = q)
      (hsr_pq : SplitRelation s p q), i < j → False := by
    intro i j p q hp p_oi q_oi hp_eq hq_eq hsr_pq h_ij
    obtain ⟨_, _, h_gt_pi⟩ := p_oi.prop
    obtain ⟨hj_lt, h_lt_qj, _⟩ := q_oi.prop
    rw [hp_eq] at h_gt_pi
    rw [hq_eq] at h_lt_qj
    have hi_succ_lt : i + 1 < xs.length := by omega
    have h_px : p < xs.get ⟨i + 1, hi_succ_lt⟩ := h_gt_pi hi_succ_lt
    have h_xj : xs.get ⟨i + 1, hi_succ_lt⟩ ≤ xs.get ⟨j, hj_lt⟩ :=
      (Nat.succ_le_of_lt h_ij).eq_or_lt.elim
        (fun e => le_of_eq (congrArg xs.get (Fin.ext e)))
        (fun h => le_of_lt (h_xs_mono _ _ _ _ h))
    have h_pq : p < q := lt_trans h_px (lt_of_le_of_lt h_xj h_lt_qj)
    have hb := hsr_pq.right _ ((min_eq_left (le_of_lt h_pq)).symm ▸ le_of_lt h_px)
      ((max_eq_right (le_of_lt h_pq)).symm ▸ le_trans h_xj (le_of_lt h_lt_qj))
    grind [rank_lt_diff_of_not_mem p hp, min_eq_left (le_of_lt h_pq)]
  grind

/-- Applies induction to each open interval of `xs` to obtain local Ramsey splits. -/
lemma build_interval_splits_of_ih {S : Type*} [Semigroup S] [Fintype S]
    (a : S) {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α) (h_img : labelingIn σ (jUp a))
    (xs : List α)
    (h_not_D : ∀ (i : ℕ) (hi_lt : i < xs.length) (y : α),
        xs.get ⟨i, hi_lt⟩ < y →
        (∀ h_next_lt : i + 1 < xs.length, y < xs.get ⟨i + 1, h_next_lt⟩) →
        ¬ IsGreenD (σ.σ (xs.get ⟨i, hi_lt⟩) y) a)
    (ih : ∀ b : S, nSElement b < nSElement a →
      ∀ (xs : List α) (i : ℕ) [Nonempty (OpenIntervalType xs i)]
      (σ_β : MultiplicativeLabeling S (OpenIntervalType xs i)),
      labelingIn σ_β (jUp b) →
      ∃ (s : Split (OpenIntervalType xs i) (nSElement b)),
        IsNormalized s ∧ IsRamsey σ_β s) :
    ∀ i [Nonempty (OpenIntervalType xs i)],
      ∃ (s : Split (OpenIntervalType xs i) (nSElement a)),
      IsRamsey
        (⟨fun x y => σ.σ x.val y.val,
          fun x y z hx hy => σ.prop x.val y.val z.val hx hy⟩ :
        MultiplicativeLabeling S (OpenIntervalType xs i)) s ∧
      ∀ z, (s z).val < nSElement a - nD (IsGreenD.eqvClass a) := by
  intro i h_ne
  let Y := OpenIntervalType xs i
  let y_min := Finset.min' (Finset.univ : Finset Y) Finset.univ_nonempty
  let y_max := Finset.max' (Finset.univ : Finset Y) Finset.univ_nonempty
  let σ_Y : MultiplicativeLabeling S (OpenIntervalType xs i) :=
    ⟨fun x y => σ.σ x.val y.val,
     fun x y z hx hy => σ.prop x.val y.val z.val hx hy⟩
  classical
  have h_eq_a :
      nSElement a = nD (IsGreenD.eqvClass a) + (Finset.univ.filter
      (fun (y : S) => GreenJClass.mk a < GreenJClass.mk y)).attach.sup
      (fun ⟨y, _hy⟩ => nSElement y) := by
    conv =>
      lhs
      unfold nSElement
  by_cases h_lt : y_min < y_max
  · let b := σ_Y.σ y_min y_max
    obtain ⟨hi_lt, h_x_lt_ymin, _⟩ := y_min.prop
    obtain ⟨_, _, h_ymax_gt⟩ := y_max.prop
    let x_val := xs.get ⟨i, hi_lt⟩
    have h_x_lt_ymax : x_val < y_max.val := lt_trans h_x_lt_ymin h_lt
    have h_b_le : GreenJClass.mk (σ.σ x_val y_max.val) ≤ GreenJClass.mk b := by
      rw [(σ.prop x_val y_min.val y_max.val h_x_lt_ymin h_lt).symm]
      exact IsGreenJRel.mul_left (σ.σ x_val y_min.val) rfl
    have h_a_le : GreenJClass.mk a ≤ GreenJClass.mk (σ.σ x_val y_max.val) :=
      h_img x_val y_max.val h_x_lt_ymax
    have h_a_ne_b : GreenJClass.mk a ≠ GreenJClass.mk b := fun heq =>
      have h_eq_mid :
          GreenJClass.mk (σ.σ x_val y_max.val) = GreenJClass.mk a :=
        le_antisymm (heq ▸ h_b_le) h_a_le
      h_not_D i hi_lt y_max.val h_x_lt_ymax h_ymax_gt
        (isGreenD_of_isGreenJ (GreenJClass.mk_eq_mk_iff.mp h_eq_mid))
    have h_b_in :
        b ∈ Finset.univ.filter
          (fun y : S => GreenJClass.mk a < GreenJClass.mk y) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ b,
        lt_of_le_of_ne (le_trans h_a_le h_b_le) h_a_ne_b⟩
    have h_sup : nSElement b ≤ _ :=
      Finset.le_sup (f := fun ⟨y, _hy⟩ => nSElement y)
        (Finset.mem_attach _ ⟨b, h_b_in⟩)
    have h_lt_a : nSElement b < nSElement a := by
      have h_pos := nD_pos _ ⟨a, rfl⟩
      rw [h_eq_a]
      omega
    have h_img_b : labelingIn σ_Y (jUp b) :=
      fun u v huv =>
        labeling_factor_le_J σ y_min.val u.val v.val y_max.val
          (Finset.min'_le _ _ (Finset.mem_univ u)) huv
          (Finset.le_max' _ _ (Finset.mem_univ v))
    obtain ⟨s_b, _, hs_b_ramsey⟩ := ih b h_lt_a xs i σ_Y h_img_b
    let s_lift : Split (OpenIntervalType xs i) (nSElement a) :=
      fun x => ⟨(s_b x).val, Nat.lt_trans (s_b x).isLt h_lt_a⟩
    have hsr_iff : ∀ u v, SplitRelation s_lift u v ↔ SplitRelation s_b u v :=
      fun u v ↦ SplitRelation.comp_strictMono s_b (fun x ↦ ⟨x.val, Nat.lt_trans x.isLt h_lt_a⟩)
        (fun _ _ hij ↦ hij) u v
    have hs_lift_ramsey : IsRamsey σ_Y s_lift :=
      ⟨fun u v w huv hvw h1 h2 ↦
        hs_b_ramsey.1 u v w huv hvw ((hsr_iff u v).mp h1) ((hsr_iff v w).mp h2),
       fun x y u v hx hu hxy huv hxu ↦
        hs_b_ramsey.2 x y u v hx hu ((hsr_iff x y).mp hxy) ((hsr_iff u v).mp huv)
          ((hsr_iff x u).mp hxu)⟩
    have h_bound : ∀ z, (s_lift z).val < nSElement a - nD (IsGreenD.eqvClass a) := fun z => by
      have hz := (s_b z).isLt
      change (s_b z).val < _
      rw [h_eq_a]
      omega
    exact ⟨s_lift, hs_lift_ramsey, h_bound⟩
  · have h_no_lt : ∀ u v : Y, u < v → False := fun u v huv ↦
      h_lt (lt_of_le_of_lt (Finset.min'_le _ _ (Finset.mem_univ u))
        (lt_of_lt_of_le huv (Finset.le_max' _ _ (Finset.mem_univ v))))
    have h_ramsey_vacuous : IsRamsey σ_Y (fun _ => ⟨0, nSElement_pos a⟩) :=
      ⟨fun u v _ huv ↦ (h_no_lt u v huv).elim, fun x y _ _ hxy ↦ (h_no_lt x y hxy).elim⟩
    have h_Delta_pos : 0 < nSElement a - nD (IsGreenD.eqvClass a) := by
      obtain ⟨y, hi_lt, hw_lt_y, h_y_lt_z⟩ := Classical.choice h_ne
      let b := σ.σ (xs.get ⟨i, hi_lt⟩) y
      have h_a_ne_b : GreenJClass.mk a ≠ GreenJClass.mk b := fun heq =>
        h_not_D i hi_lt y hw_lt_y h_y_lt_z
          (isGreenD_of_isGreenJ (GreenJClass.mk_eq_mk_iff.mp heq.symm))
      have h_b_in : b ∈ Finset.univ.filter (fun y : S => GreenJClass.mk a < GreenJClass.mk y) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ b,
          lt_of_le_of_ne (h_img (xs.get ⟨i, hi_lt⟩) y hw_lt_y) h_a_ne_b⟩
      have h_sup : nSElement b ≤ _ :=
        Finset.le_sup (f := fun ⟨y, _hy⟩ => nSElement y) (Finset.mem_attach _ ⟨b, h_b_in⟩)
      have h_pos := nSElement_pos b
      rw [h_eq_a]
      omega
    exact ⟨fun _ => ⟨0, nSElement_pos a⟩, h_ramsey_vacuous, fun _ => h_Delta_pos⟩

/-- Combines a split on `xs` with splits on open intervals into a global split. -/
noncomputable abbrev combineSplits {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α)
    (rankX : {x // x ∈ xs} → Fin (nSElement a))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a)) :
    Split α (nSElement a) := fun x =>
  if hx : x ∈ xs then
    rankX ⟨x, hx⟩
  else if h_ex : ∃ i, ∃ (hi_lt : i < xs.length),
    xs.get ⟨i, hi_lt⟩ < x ∧
    ∀ (h_next_lt : i + 1 < xs.length), x < xs.get ⟨i + 1, h_next_lt⟩ then
    @sY (Classical.choose h_ex) ⟨⟨x, Classical.choose_spec h_ex⟩⟩
      ⟨x, Classical.choose_spec h_ex⟩
  else
    ⟨0, nSElement_pos a⟩

/-- Value of `combineSplits` on an element of an open interval `OpenIntervalType xs k`. -/
lemma combineSplits_of_openInterval {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α)
    (rankX : {x // x ∈ xs} → Fin (nSElement a))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)], Split (OpenIntervalType xs i) (nSElement a))
    (h_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length) (hj_lt : j < xs.length), i < j →
      xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩)
    (k : ℕ) (w_val : OpenIntervalType xs k) :
    combineSplits a xs rankX sY w_val.val = @sY k ⟨w_val⟩ w_val := by
  have hw_not : w_val.val ∉ xs := not_mem_of_openInterval h_mono k w_val.val w_val.prop
  simp only [combineSplits, dite_eq_right hw_not]
  have hw_ex : ∃ m, ∃ hm : m < xs.length,
      xs.get ⟨m, hm⟩ < w_val.val ∧
      ∀ h_next_lt, w_val.val < xs.get ⟨m + 1, h_next_lt⟩ := ⟨k, w_val.prop⟩
  rw [dite_eq_left hw_ex]
  have heq_idx : Classical.choose hw_ex = k := by
    obtain ⟨hk_lt, h_lt_w, h_gt_w⟩ := Classical.choose_spec hw_ex
    obtain ⟨hk_val_lt, h_val_lt, h_val_gt⟩ := w_val.prop
    exact openInterval_unique xs h_mono w_val.val _ k hk_lt hk_val_lt
      h_lt_w h_gt_w h_val_lt h_val_gt
  have helper : ∀ k' (hk' : Nonempty _) (heq : k' = k) wk',
      wk'.val = w_val.val →
      @sY k' hk' wk' = @sY k ⟨w_val⟩ w_val := by
    rintro k' hk' rfl wk' h_val
    rw [Subtype.ext h_val]
  exact helper (Classical.choose hw_ex) _ heq_idx _ rfl

/-- Lifting a split relation on `combineSplits` between elements of the same
open interval to `sY`. -/
lemma splitRelation_sY_of_combineSplits {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α)
    (rankX : {x // x ∈ xs} → Fin (nSElement a))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)], Split (OpenIntervalType xs i) (nSElement a))
    (h_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length) (hj_lt : j < xs.length), i < j →
      xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩)
    (i : ℕ) (x_oi y_oi : OpenIntervalType xs i)
    (hsr : SplitRelation (combineSplits a xs rankX sY) x_oi.val y_oi.val) :
    SplitRelation (@sY i ⟨x_oi⟩) x_oi y_oi := by
  have : Nonempty (OpenIntervalType xs i) := ⟨x_oi⟩
  have sY_val_eq (z_oi : OpenIntervalType xs i) :
      (combineSplits a xs rankX sY z_oi.val).val = (sY i z_oi).val :=
    congrArg Fin.val (combineSplits_of_openInterval a xs rankX sY h_mono i z_oi)
  refine ⟨Fin.ext ((sY_val_eq y_oi).symm ▸ (sY_val_eq x_oi).symm ▸ congrArg Fin.val hsr.left),
    fun z_oi hz_ge hz_le ↦ Fin.le_iff_val_le_val.mpr ?_⟩
  have hs_min : (combineSplits a xs rankX sY (min x_oi.val y_oi.val)).val =
      (sY i (min x_oi y_oi)).val := by
    rcases min_choice (x_oi : α) y_oi with h | h
    · have h_le : x_oi ≤ y_oi := show x_oi.val ≤ y_oi.val from h.symm ▸ min_le_right ..
      rw [h, min_eq_left h_le, sY_val_eq x_oi]
    · have h_le : y_oi ≤ x_oi := show y_oi.val ≤ x_oi.val from h.symm ▸ min_le_left ..
      rw [h, min_eq_right h_le, sY_val_eq y_oi]
  have h_bound := Fin.le_iff_val_le_val.mp (hsr.right z_oi.val hz_ge hz_le)
  exact hs_min.symm ▸ (sY_val_eq z_oi).symm ▸ h_bound

/-- Split-related elements in the combined split outside `xs` belong to the same interval. -/
lemma combineSplits_interval_ramsey {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α)
    (rankX : {x // x ∈ xs} → Fin (nSElement a))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a))
    (C : ℕ)
    (h_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length)
      (hj_lt : j < xs.length),
      i < j → xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩)
    (h_covers : ∀ x, x ∉ xs →
      ∃ i, ∃ hi_lt : i < xs.length,
        xs.get ⟨i, hi_lt⟩ < x ∧
        ∀ h_next_lt : i + 1 < xs.length,
          x < xs.get ⟨i + 1, h_next_lt⟩)
    (h_sY_bound : ∀ i [Nonempty (OpenIntervalType xs i)]
      (z : OpenIntervalType xs i), (sY i z).val < C)
    (h_rankX_bound : ∀ x, C ≤ (rankX x).val) :
    ∀ x y, x ∉ xs → x < y →
      SplitRelation (combineSplits a xs rankX sY) x y →
      ∃ (i : ℕ) (x_val y_val : OpenIntervalType xs i),
        x_val.val = x ∧ y_val.val = y ∧
        SplitRelation (@sY i ⟨x_val⟩) x_val y_val := by
  intros x y hx_not_in hlt hsr
  obtain ⟨i, hx_lt, h_lt_x, h_gt_x⟩ := h_covers x hx_not_in
  let x_val : OpenIntervalType xs i := ⟨x, hx_lt, h_lt_x, h_gt_x⟩
  have hs_x_val : (combineSplits a xs rankX sY x).val < C :=
    (combineSplits_of_openInterval a xs rankX sY h_mono i x_val).symm ▸ @h_sY_bound i ⟨x_val⟩ x_val
  have hy_not_in : y ∉ xs := fun hy_in => by
    have hs_y_val : C ≤ (combineSplits a xs rankX sY y).val := by
      simp only [combineSplits, dite_eq_left hy_in]
      exact h_rankX_bound ⟨y, hy_in⟩
    have h_eq : (combineSplits a xs rankX sY x).val =
        (combineSplits a xs rankX sY y).val :=
      congrArg Fin.val hsr.left
    omega
  obtain ⟨j, hy_lt, h_lt_y, h_gt_y⟩ := h_covers y hy_not_in
  have hij : i = j := by
    rcases lt_trichotomy i j with h_ij | rfl | h_ji
    · have hi_succ_lt : i + 1 < xs.length := by omega
      let z := xs.get ⟨i + 1, hi_succ_lt⟩
      have hz_in : z ∈ xs := xs.get_mem ⟨i + 1, hi_succ_lt⟩
      have h_z_gt_y : y < z := by
        by_contra h_not_lt
        have hz_bound : min x y ≤ z ∧ z ≤ max x y := by
          rw [min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)]
          exact ⟨le_of_lt (h_gt_x hi_succ_lt), not_lt.mp h_not_lt⟩
        have h_sz_val : C ≤ (combineSplits a xs rankX sY z).val := by
          simp only [combineSplits, dite_eq_left hz_in]
          exact h_rankX_bound ⟨z, hz_in⟩
        have h_le_val := Fin.le_iff_val_le_val.mp
          (hsr.right z hz_bound.1 hz_bound.2)
        rw [min_eq_left (le_of_lt hlt)] at h_le_val
        omega
      have h_z_le_j : z ≤ xs.get ⟨j, hy_lt⟩ :=
        (Nat.succ_le_of_lt h_ij).eq_or_lt.elim
          (fun e => le_of_eq (congrArg xs.get (Fin.ext e)))
          (fun h => le_of_lt (h_mono _ _ _ _ h))
      nomatch (lt_irrefl y
        (lt_of_lt_of_le (lt_of_lt_of_le h_z_gt_y h_z_le_j) (le_of_lt h_lt_y)))
    · rfl
    · have hj_succ_lt : j + 1 < xs.length := by omega
      have h_w_le_x : xs.get ⟨j + 1, hj_succ_lt⟩ ≤ xs.get ⟨i, hx_lt⟩ :=
        (Nat.succ_le_of_lt h_ji).eq_or_lt.elim
          (fun e => le_of_eq (congrArg xs.get (Fin.ext e)))
          (fun h => le_of_lt (h_mono _ _ _ _ h))
      nomatch (lt_irrefl x
        (lt_trans hlt (lt_of_lt_of_le (h_gt_y hj_succ_lt)
          (le_trans h_w_le_x (le_of_lt h_lt_x)))))
  subst hij
  let y_val : OpenIntervalType xs i := ⟨y, hy_lt, h_lt_y, h_gt_y⟩
  exact ⟨i, x_val, y_val, rfl, rfl,
    splitRelation_sY_of_combineSplits a xs rankX sY h_mono i x_val y_val hsr⟩

/-- A context bundle packaging the parameters and hypotheses for combining interval splits. -/
structure CombineContext (S α : Type*)
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S] where
  a : S
  xs : List α
  C : ℕ
  σ : MultiplicativeLabeling S α
  σ_Y : ∀ (i : ℕ), MultiplicativeLabeling S (OpenIntervalType xs i)
  rankX : {x // x ∈ xs} → Fin (nSElement a)
  sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)], Split (OpenIntervalType xs i) (nSElement a)
  hsY_ramsey : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)], IsRamsey (σ_Y i) (sY i)
  h_σ_Y : ∀ i x y, (σ_Y i).σ x y = σ.σ x.val y.val
  h_cov : ∀ x, x ∉ xs →
    ∃ (i : ℕ) (hi_lt : i < xs.length),
      xs.get ⟨i, hi_lt⟩ < x ∧
      ∀ (h_next_lt : i + 1 < xs.length), x < xs.get ⟨i + 1, h_next_lt⟩
  hsY_strict : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)]
    (z : OpenIntervalType xs i), (sY i z).val < C
  h_rankX_ge : ∀ x (hx : x ∈ xs), C ≤ (rankX ⟨x, hx⟩).val
  h_xs_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length) (hj_lt : j < xs.length), i < j →
    xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩
  h_interval_ramsey : ∀ x y, x ∉ xs → x < y →
    SplitRelation (combineSplits a xs rankX sY) x y →
    ∃ (i : ℕ) (x_val y_val : OpenIntervalType xs i),
      x_val.val = x ∧ y_val.val = y ∧
      SplitRelation (@sY i ⟨x_val⟩) x_val y_val
  h_X_ramsey_1 : ∀ x y z, x ∈ xs → y ∈ xs → z ∈ xs →
    x < y → y < z →
    SplitRelation (combineSplits a xs rankX sY) x y →
    SplitRelation (combineSplits a xs rankX sY) y z →
    σ.σ x y * σ.σ x y = σ.σ x y
  h_X_ramsey_2 : ∀ x y u v,
    x ∈ xs → y ∈ xs → u ∈ xs → v ∈ xs →
    x < y → u < v →
    SplitRelation (combineSplits a xs rankX sY) x y →
    SplitRelation (combineSplits a xs rankX sY) u v →
    SplitRelation (combineSplits a xs rankX sY) x u →
    σ.σ x y = σ.σ u v
  h_min_norm : (combineSplits a xs rankX sY
    (Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty)).val =
    nSElement a - 1
  h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
    Finset.univ_nonempty).val = nSElement a - 1

/-- The combined split satisfies normalization and the Ramsey property. -/
lemma combineSplits_props {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α) (C : ℕ)
    (σ : MultiplicativeLabeling S α)
    (σ_Y : ∀ (i : ℕ), MultiplicativeLabeling S (OpenIntervalType xs i))
    (rankX : {x // x ∈ xs} → Fin (nSElement a))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a))
    (hsY_ramsey : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      IsRamsey (σ_Y i) (sY i))
    (h_σ_Y : ∀ i x y, (σ_Y i).σ x y = σ.σ x.val y.val)
    (h_cov : ∀ x, x ∉ xs →
      ∃ (i : ℕ) (hi_lt : i < xs.length),
        xs.get ⟨i, hi_lt⟩ < x ∧
        ∀ (h_next_lt : i + 1 < xs.length),
          x < xs.get ⟨i + 1, h_next_lt⟩)
    (hsY_strict : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)]
      (z : OpenIntervalType xs i), (sY i z).val < C)
    (h_rankX_ge : ∀ x (hx : x ∈ xs), C ≤ (rankX ⟨x, hx⟩).val)
    (h_xs_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length)
        (hj_lt : j < xs.length), i < j →
      xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩)
    (h_interval_ramsey : ∀ x y, x ∉ xs → x < y →
      SplitRelation (combineSplits a xs rankX sY) x y →
      ∃ (i : ℕ) (x_val y_val : OpenIntervalType xs i),
        x_val.val = x ∧ y_val.val = y ∧
        SplitRelation (@sY i ⟨x_val⟩) x_val y_val)
    (h_X_ramsey_1 : ∀ x y z, x ∈ xs → y ∈ xs → z ∈ xs →
      x < y → y < z →
      SplitRelation (combineSplits a xs rankX sY) x y →
      SplitRelation (combineSplits a xs rankX sY) y z →
      σ.σ x y * σ.σ x y = σ.σ x y)
    (h_X_ramsey_2 : ∀ x y u v,
      x ∈ xs → y ∈ xs → u ∈ xs → v ∈ xs →
      x < y → u < v →
      SplitRelation (combineSplits a xs rankX sY) x y →
      SplitRelation (combineSplits a xs rankX sY) u v →
      SplitRelation (combineSplits a xs rankX sY) x u →
      σ.σ x y = σ.σ u v)
    (h_min_norm : (combineSplits a xs rankX sY
      (Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty)).val =
      nSElement a - 1)
    (h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
      Finset.univ_nonempty).val = nSElement a - 1) :
    IsNormalized (combineSplits a xs rankX sY) ∧
    IsRamsey σ (combineSplits a xs rankX sY) := by
  constructor
  · apply Fin.ext
    simp only [combineSplits]
    rw [h_min_norm, h_max_val]
  · have rank_lt_diff_of_not_mem : ∀ z, z ∉ xs →
          (combineSplits a xs rankX sY z).val < C := by
      intro z hz
      have h_ex := h_cov z hz
      simp only [combineSplits, hz, h_ex, ↓reduceDIte]
      exact @hsY_strict _ ⟨⟨z, Classical.choose_spec h_ex⟩⟩
        ⟨z, Classical.choose_spec h_ex⟩
    have rank_ge_diff_of_mem : ∀ z, z ∈ xs → C ≤ (combineSplits a xs rankX sY z).val :=
      fun z hz ↦ by simpa [combineSplits, hz] using h_rankX_ge z hz
    have mem_of_sr_mem : ∀ p q, p ∈ xs →
        SplitRelation (combineSplits a xs rankX sY) p q → q ∈ xs := by
      intro p q hp hsr
      by_contra hnq
      have h_q_lt := rank_lt_diff_of_not_mem q hnq
      have h_p_ge := rank_ge_diff_of_mem p hp
      have h_val_eq := congrArg Fin.val hsr.left
      omega
    have not_mem_of_sr_not_mem : ∀ p q, p ∉ xs →
        SplitRelation (combineSplits a xs rankX sY) p q → q ∉ xs := by
      intro p q hp hsr hq
      have h_p_lt := rank_lt_diff_of_not_mem p hp
      have h_q_ge := rank_ge_diff_of_mem q hq
      have h_val_eq := congrArg Fin.val hsr.left
      omega
    have same_interval : ∀ (p q : α),
          p ∉ xs → q ∉ xs →
          SplitRelation (combineSplits a xs rankX sY) p q →
          ∀ (i j : ℕ) (p_oi : OpenIntervalType xs i)
            (q_oi : OpenIntervalType xs j),
          p_oi.val = p → q_oi.val = q → i = j :=
      buildXSeq_same_interval_of_splitRelation xs
        (combineSplits a xs rankX sY) C
        h_xs_mono rank_ge_diff_of_mem rank_lt_diff_of_not_mem
    constructor
    · intro x y z hlt_xy hlt_yz hsr_xy hsr_yz
      by_cases hx : x ∈ xs
      · have hy : y ∈ xs := mem_of_sr_mem x y hx hsr_xy
        have hz : z ∈ xs := mem_of_sr_mem y z hy hsr_yz
        exact h_X_ramsey_1 x y z hx hy hz hlt_xy hlt_yz hsr_xy hsr_yz
      · obtain ⟨i, x_val, y_val, hx_eq, hy_eq, hsr_Y_xy⟩ :=
            h_interval_ramsey x y hx hlt_xy hsr_xy
        have hy_not_mem := not_mem_of_sr_not_mem x y hx hsr_xy
        obtain ⟨j, y_val_2, z_val, hy_eq_2, hz_eq, hsr_Y_yz⟩ :=
          h_interval_ramsey y z hy_not_mem hlt_yz hsr_yz
        have hij : i = j :=
          same_interval x y hx hy_not_mem hsr_xy i j x_val y_val_2
            hx_eq hy_eq_2
        subst hij
        have hy_val_eq : y_val = y_val_2 :=
          Subtype.ext (hy_eq.trans hy_eq_2.symm)
        rw [← hy_val_eq] at hsr_Y_yz
        have hlt_xy_Y : x_val < y_val := by
          change x_val.val < y_val.val
          exact hx_eq ▸ hy_eq ▸ hlt_xy
        have hlt_yz_Y : y_val < z_val := by
          change y_val.val < z_val.val
          exact hy_eq ▸ hz_eq ▸ hlt_yz
        have h_ramsey :=
          (@hsY_ramsey i ⟨x_val⟩).1 x_val y_val z_val
            hlt_xy_Y hlt_yz_Y hsr_Y_xy hsr_Y_yz
        rw [h_σ_Y i x_val y_val] at h_ramsey
        exact hx_eq ▸ hy_eq ▸ h_ramsey
    · intro x y u v hlt_xy hlt_uv hsr_xy hsr_uv hsr_xu
      by_cases hx : x ∈ xs
      · have hu := mem_of_sr_mem x u hx hsr_xu
        have hy := mem_of_sr_mem x y hx hsr_xy
        have hv := mem_of_sr_mem u v hu hsr_uv
        exact h_X_ramsey_2 x y u v hx hy hu hv
            hlt_xy hlt_uv hsr_xy hsr_uv hsr_xu
      · have hu := not_mem_of_sr_not_mem x u hx hsr_xu
        obtain ⟨i, x_oi, y_oi, hx_eq, hy_eq, hsr_Y_xy⟩ :=
          h_interval_ramsey _ _ hx hlt_xy hsr_xy
        obtain ⟨j, u_oi, v_oi, hu_eq, hv_eq, hsr_Y_uv⟩ :=
          h_interval_ramsey _ _ hu hlt_uv hsr_uv
        have hij : i = j :=
          same_interval x u hx hu hsr_xu i j x_oi u_oi hx_eq hu_eq
        subst hij
        have hsr_Y_xu : SplitRelation (@sY i ⟨x_oi⟩) x_oi u_oi :=
          splitRelation_sY_of_combineSplits a xs rankX sY h_xs_mono i x_oi u_oi
            (by rwa [hx_eq, hu_eq])
        have h_ramsey := (@hsY_ramsey i ⟨x_oi⟩).2 x_oi y_oi u_oi v_oi
          (hx_eq.symm ▸ hy_eq.symm ▸ hlt_xy : x_oi.val < y_oi.val)
          (hu_eq.symm ▸ hv_eq.symm ▸ hlt_uv : u_oi.val < v_oi.val)
          hsr_Y_xy hsr_Y_uv hsr_Y_xu
        exact hx_eq ▸ hy_eq ▸ hu_eq ▸ hv_eq ▸
          (h_σ_Y i x_oi y_oi) ▸ (h_σ_Y i u_oi v_oi) ▸ h_ramsey

/-- The bundled version of `combineSplits_props`. -/
lemma CombineContext.props {S α : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (ctx : CombineContext S α) :
    IsNormalized (combineSplits ctx.a ctx.xs ctx.rankX ctx.sY) ∧
    IsRamsey ctx.σ (combineSplits ctx.a ctx.xs ctx.rankX ctx.sY) :=
  combineSplits_props ctx.a ctx.xs ctx.C ctx.σ ctx.σ_Y ctx.rankX ctx.sY
    ctx.hsY_ramsey ctx.h_σ_Y ctx.h_cov ctx.hsY_strict ctx.h_rankX_ge ctx.h_xs_mono
    ctx.h_interval_ramsey ctx.h_X_ramsey_1 ctx.h_X_ramsey_2 ctx.h_min_norm ctx.h_max_val

end RamseySplit
