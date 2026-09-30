/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import AlgebraicAutomata.FactorizationForest.Combine

/-!
# Simon's Split Theorem — Regular `D`-Class Case

Constructs the Simon split (`ramsey_split_regular_case`) for the case where the `D`-class
is regular, using `H`-class coloring and idempotent selection.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace RamseySplit

open GreensRelations

section RegularDClassCase

variable {S α : Type*} [Semigroup S] [LinearOrder α]

/-- A context bundle packaging the common parameters for the Simon split construction
over a regular `D`-class. -/
structure SplitContext (S α : Type*) [Semigroup S] [LinearOrder α] where
  σ : MultiplicativeLabeling S α
  D : Set S
  x₀ : S
  hx₀ : D = IsGreenD.eqvClass x₀
  hReg : IsRegularDClass D
  h_range : ∀ x y, x < y → σ.σ x y ∈ D

open Classical in
/-- Computes the target Green's `L`-class for the element `x` based on the Simon
context `ctx`. This is the `L`-class of the product `σ(y, x)` for any `y < x`,
or a canonical class derived from an idempotent if `x` is minimal. -/
noncomputable abbrev lOf (ctx : SplitContext S α) (x : α) : Set S :=
  if h_min : IsMin x then
    if h_max : IsMax x then
      IsGreenL.eqvClass ctx.x₀
    else
      have ha_D : ctx.σ.σ x (choose (not_isMax_iff.mp h_max)) ∈ ctx.D :=
        ctx.h_range x _ (choose_spec (not_isMax_iff.mp h_max))
      IsGreenL.eqvClass
        (choose (MulSeq.exists_idempotent_in_greenR_of_regular (ctx.hReg _ ha_D)))
  else
    IsGreenL.eqvClass (ctx.σ.σ (choose (not_isMin_iff.mp h_min)) x)

open Classical in
/-- Computes the target Green's `R`-class for the element `x` based on the Simon
context `ctx`. This is the `R`-class of the product `σ(x, y)` for any `y > x`,
or a canonical class derived from an idempotent if `x` is maximal. -/
noncomputable abbrev rOf (ctx : SplitContext S α) (x : α) : Set S :=
  if h_max : IsMax x then
    if h_min : IsMin x then
      have ha_D : ctx.x₀ ∈ ctx.D := ctx.hx₀ ▸ IsGreenD.refl ctx.x₀
      IsGreenR.eqvClass
        (choose (MulSeq.exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D)))
    else
      have ha_D : ctx.σ.σ (choose (not_isMin_iff.mp h_min)) x ∈ ctx.D :=
        ctx.h_range _ x (choose_spec (not_isMin_iff.mp h_min))
      IsGreenR.eqvClass
        (choose (MulSeq.exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D)))
  else
    IsGreenR.eqvClass (ctx.σ.σ x (choose (not_isMax_iff.mp h_max)))

/-- Computes the target Green's `H`-class for the element `x`, defined as the
intersection of its assigned `L`-class and `R`-class. -/
noncomputable abbrev hOf (ctx : SplitContext S α) (x : α) : Set S :=
  lOf ctx x ∩ rOf ctx x

section WithFiniteS

variable [Finite S]

/-- The assigned `L`-class depends only on elements strictly smaller than `x`
(it does not depend on which particular element `y < x` we choose). -/
lemma lOf_well_defined_of_le (ctx : SplitContext S α) (x y1 y2 : α)
    (h_y1_lt_x : y1 < x) (h_y2_lt_x : y2 < x) (h_le : y1 ≤ y2) :
    IsGreenL.eqvClass (ctx.σ.σ y1 x) = IsGreenL.eqvClass (ctx.σ.σ y2 x) := by
  rcases h_le.eq_or_lt with rfl | h_lt
  · rfl
  have hp := (ctx.σ.prop y1 y2 x h_lt h_y2_lt_x).symm
  have hL : IsGreenL (ctx.σ.σ y2 x) (ctx.σ.σ y1 x) :=
    hp ▸ (mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩ _ _
      (ctx.h_range y1 y2 h_lt) (ctx.h_range y2 x h_y2_lt_x) (hp ▸ ctx.h_range y1 x h_y1_lt_x)).1.2
  exact Set.ext fun _ ↦ ⟨fun hz ↦ hz.trans hL.symm, fun hz ↦ hz.trans hL⟩

/-- The assigned `L`-class depends only on elements strictly smaller than `x`
(it does not depend on which particular element `y < x` we choose). -/
lemma lOf_well_defined (ctx : SplitContext S α) (x y1 y2 : α)
    (h_y1_lt_x : y1 < x) (h_y2_lt_x : y2 < x) :
    IsGreenL.eqvClass (ctx.σ.σ y1 x) = IsGreenL.eqvClass (ctx.σ.σ y2 x) :=
  (le_total y1 y2).elim (lOf_well_defined_of_le ctx x y1 y2 h_y1_lt_x h_y2_lt_x)
    fun h ↦ (lOf_well_defined_of_le ctx x y2 y1 h_y2_lt_x h_y1_lt_x h).symm

lemma rOf_well_defined_of_le (ctx : SplitContext S α) (x y1 y2 : α)
    (h_x_lt_y1 : x < y1) (h_x_lt_y2 : x < y2) (h_le : y1 ≤ y2) :
    IsGreenR.eqvClass (ctx.σ.σ x y1) = IsGreenR.eqvClass (ctx.σ.σ x y2) := by
  rcases h_le.eq_or_lt with rfl | h_lt
  · rfl
  have hp := ctx.σ.prop x y1 y2 h_x_lt_y1 h_lt
  have hR : IsGreenR (ctx.σ.σ x y1) (ctx.σ.σ x y2) :=
    hp ▸ (mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩ _ _
      (ctx.h_range x y1 h_x_lt_y1) (ctx.h_range y1 y2 h_lt)
      (hp.symm ▸ ctx.h_range x y2 h_x_lt_y2)).1.1
  exact Set.ext fun _ ↦ ⟨fun hz ↦ hz.trans hR, fun hz ↦ hz.trans hR.symm⟩

/-- The assigned `R`-class depends only on elements strictly greater than `x`
(it does not depend on which particular element `y > x` we choose). -/
lemma rOf_well_defined (ctx : SplitContext S α) (x y1 y2 : α)
    (h_x_lt_y1 : x < y1) (h_x_lt_y2 : x < y2) :
    IsGreenR.eqvClass (ctx.σ.σ x y1) = IsGreenR.eqvClass (ctx.σ.σ x y2) :=
  (le_total y1 y2).elim (rOf_well_defined_of_le ctx x y1 y2 h_x_lt_y1 h_x_lt_y2)
    fun h ↦ (rOf_well_defined_of_le ctx x y2 y1 h_x_lt_y2 h_x_lt_y1 h).symm

open Classical in
/-- An element's assigned `H`-class contains at least one idempotent element. -/
lemma hOf_has_idempotent (ctx : SplitContext S α) (x : α) :
    ∃ e_id : S, e_id ∈ hOf ctx x ∧ e_id * e_id = e_id := by
  by_cases h_min : IsMin x
  · by_cases h_max : IsMax x
    · have h_ex := MulSeq.exists_idempotent_in_greenL_of_regular
        (ctx.hReg ctx.x₀ (ctx.hx₀ ▸ IsGreenD.refl ctx.x₀))
      exact ⟨choose h_ex, by grind, (choose_spec h_ex).2⟩
    · have h_ex := MulSeq.exists_idempotent_in_greenR_of_regular
        (ctx.hReg _ (ctx.h_range x _ (choose_spec (not_isMax_iff.mp h_max))))
      exact ⟨choose h_ex, by grind, (choose_spec h_ex).2⟩
  · by_cases h_max : IsMax x
    · have h_ex := MulSeq.exists_idempotent_in_greenL_of_regular
        (ctx.hReg _ (ctx.h_range _ x (choose_spec (not_isMin_iff.mp h_min))))
      exact ⟨choose h_ex, by grind, (choose_spec h_ex).2⟩
    · have hy : _ < x := choose_spec (not_isMin_iff.mp h_min)
      have hz : x < _ := choose_spec (not_isMax_iff.mp h_max)
      obtain ⟨_, ⟨ex, _, he_idem, hLe, hRe⟩⟩ :=
        mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩ _ _
        (ctx.h_range _ _ hy) (ctx.h_range _ _ hz)
        ((ctx.σ.prop _ _ _ hy hz).symm ▸ ctx.h_range _ _ (hy.trans hz))
      exact ⟨ex, by grind, he_idem⟩

/-- Chooses an idempotent element belonging to the `H`-class assigned to `x`. -/
noncomputable abbrev eId (ctx : SplitContext S α) (x : α) : S :=
  Classical.choose (hOf_has_idempotent ctx x)

/-- The chosen idempotent `eId ctx x` is indeed an element of `hOf ctx x`. -/
lemma eId_mem (ctx : SplitContext S α) (x : α) : eId ctx x ∈ hOf ctx x :=
  (Classical.choose_spec (hOf_has_idempotent ctx x)).1

/-- The chosen element `eId ctx x` is an idempotent. -/
@[simp] lemma eId_idem (ctx : SplitContext S α) (x : α) : eId ctx x * eId ctx x = eId ctx x :=
  (Classical.choose_spec (hOf_has_idempotent ctx x)).2

/-- The `H`-class of `z` is exactly the `H`-class of its chosen idempotent. -/
lemma hOf_eq_class (ctx : SplitContext S α) (z : α) :
    hOf ctx z = IsGreenH.eqvClass (eId ctx z) := by
  ext w
  have he := eId_mem ctx z
  simp only [hOf, lOf, rOf, IsGreenH.eqvClass, IsGreenL.eqvClass, IsGreenR.eqvClass,
    IsGreenH, Set.mem_inter_iff, Set.mem_ofPred_eq] at he ⊢
  split_ifs at he ⊢ <;> exact ⟨fun ⟨hwL, hwR⟩ ↦ ⟨hwL.trans he.1.symm, hwR.trans he.2.symm⟩,
    fun ⟨hwL, hwR⟩ ↦ ⟨hwL.trans he.1, hwR.trans he.2⟩⟩

open Classical in
/-- Under the hypothesis that `mz < z` and `hOf ctx mz = hOf ctx z`, the
product `σ(mz, z)` interacts with the chosen idempotent in a specific way:
`eId ctx z * σ(mz, z) * eId ctx z = σ(mz, z)` and `σ(mz, z)` is `H`-related to `eId ctx z`. -/
lemma sigma_props (ctx : SplitContext S α) (z mz : α) (h_mz : mz < z)
    (hm_H : hOf ctx mz = hOf ctx z) :
    eId ctx z * ctx.σ.σ mz z * eId ctx z = ctx.σ.σ mz z ∧
    IsGreenH (ctx.σ.σ mz z) (eId ctx z) := by
  have hn_min : ¬ IsMin z := fun h ↦ lt_irrefl mz (lt_of_lt_of_le h_mz (h (le_of_lt h_mz)))
  have hn_max : ¬ IsMax mz := fun h ↦ lt_irrefl z (lt_of_le_of_lt (h (le_of_lt h_mz)) h_mz)
  have hl_eq : lOf ctx z = IsGreenL.eqvClass (ctx.σ.σ mz z) := by
    simp only [lOf, dite_eq_right hn_min,
      lOf_well_defined ctx z _ mz (choose_spec (not_isMin_iff.mp hn_min)) h_mz]
  have hr_eq : rOf ctx mz = IsGreenR.eqvClass (ctx.σ.σ mz z) := by
    simp only [rOf, dite_eq_right hn_max,
      rOf_well_defined ctx mz _ z (choose_spec (not_isMax_iff.mp hn_max)) h_mz]
  have hH : IsGreenH (ctx.σ.σ mz z) (eId ctx z) :=
    ⟨(hl_eq ▸ (eId_mem ctx z).1).symm, (hr_eq ▸ (hm_H ▸ eId_mem ctx z).2).symm⟩
  have ⟨h1, h2⟩ := MulSeq.mul_eq_self_of_isGreenH_idempotent hH (eId_idem ctx z)
  exact ⟨by rw [mul_assoc, h1, h2], hH⟩

open Classical in
/-- The chosen idempotent `eId ctx x` belongs to the `D`-class `ctx.D`. -/
lemma eId_mem_D (ctx : SplitContext S α) (x : α) : eId ctx x ∈ ctx.D := by
  have he_L : eId ctx x ∈ lOf ctx x := (eId_mem ctx x).1
  by_cases h_min : IsMin x
  · by_cases h_max : IsMax x
    · simp only [lOf, h_min, h_max, ctx.hx₀] at *
      exact ⟨ctx.x₀, he_L, .refl _⟩
    · have ha_D := ctx.h_range x _ (choose_spec (not_isMax_iff.mp h_max))
      have h_ex := MulSeq.exists_idempotent_in_greenR_of_regular (ctx.hReg _ ha_D)
      simp only [lOf, h_min, h_max, ctx.hx₀] at *
      exact IsGreenD.trans ⟨_, he_L, (choose_spec h_ex).left⟩ ha_D
  · have ha_D := ctx.h_range _ x (choose_spec (not_isMin_iff.mp h_min))
    simp only [lOf, h_min, ctx.hx₀] at *
    exact IsGreenD.trans ⟨_, he_L, .refl _⟩ ha_D

/-- Helper lemma for fColoring. -/
lemma fColoring_helper_val_in (ctx : SplitContext S α) (x m : α)
    (h_mx : m < x) (hm_H : hOf ctx m = hOf ctx x) :
    (eId ctx x * ctx.σ.σ m x * eId ctx x) ∈ ctx.D ∧
    ∃ e' ∈ ctx.D, e' * e' = e' ∧ IsGreenH (eId ctx x * ctx.σ.σ m x * eId ctx x) e' :=
  let ⟨h_eq, hH⟩ := sigma_props ctx x m h_mx hm_H
  let h_val_H_e : IsGreenH (eId ctx x * ctx.σ.σ m x * eId ctx x) (eId ctx x) := h_eq.symm ▸ hH
  let he_eqv : eId ctx x ∈ IsGreenD.eqvClass ctx.x₀ := ctx.hx₀ ▸ eId_mem_D ctx x
  let h_val_D : (eId ctx x * ctx.σ.σ m x * eId ctx x) ∈ ctx.D :=
    ctx.hx₀.symm ▸ (IsGreenD.trans ⟨_, .refl _, h_val_H_e.2⟩ he_eqv :
      (eId ctx x * ctx.σ.σ m x * eId ctx x) ∈ IsGreenD.eqvClass ctx.x₀)
  ⟨h_val_D, eId ctx x, eId_mem_D ctx x, eId_idem ctx x, h_val_H_e⟩

section WithFintypeAlpha
variable [Fintype α]

open Classical in
/-- The coloring function mapping an element `x` to a subtype representing
its value and properties in the `D`-class. -/
noncomputable abbrev fColoring (ctx : SplitContext S α) (x : α) :
    { y : S // y ∈ ctx.D ∧ ∃ e ∈ ctx.D, e * e = e ∧ IsGreenH y e } :=
  let mClass := Finset.univ.filter (fun y ↦ hOf ctx y = hOf ctx x)
  have hm_nonempty : mClass.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
  let m := Finset.min' mClass hm_nonempty
  if h_mx : m < x then
    ⟨eId ctx x * ctx.σ.σ m x * eId ctx x, fColoring_helper_val_in ctx x m h_mx
      (Finset.mem_filter.mp (Finset.min'_mem mClass hm_nonempty)).2⟩
  else
    ⟨eId ctx x, eId_mem_D ctx x, eId ctx x, eId_mem_D ctx x, eId_idem ctx x, .refl _⟩

/-- The element returned by `fColoring` belongs to the correct Green's `H`-class. -/
lemma fColoring_isGreenH (ctx : SplitContext S α) (z : α) :
    IsGreenH (fColoring ctx z).val (eId ctx z) := by
  classical
  let mClass := Finset.univ.filter (fun w ↦ hOf ctx w = hOf ctx z)
  have hm_nonempty : mClass.Nonempty := ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, rfl⟩⟩
  let mz := Finset.min' mClass hm_nonempty
  have hm_H : hOf ctx mz = hOf ctx z := (Finset.mem_filter.mp (Finset.min'_mem _ hm_nonempty)).2
  dsimp only [fColoring]
  split_ifs with h_mz
  · have h_props := sigma_props ctx z mz h_mz hm_H
    grind
  · exact IsGreenH.refl (eId ctx z)

section WithFintypeSNonemptyAlpha

variable [Fintype S] [Nonempty α]

/-- Normalized Ramsey split when all values of `σ` lie in a single regular `D`-class `D`. -/
lemma ramsey_regular_d_case
    (σ : MultiplicativeLabeling S α)
    (D : Set S)
    (hD : ∃ x, D = IsGreenD.eqvClass x)
    (hReg : IsRegularDClass D)
    (h_range : ∀ x y, x < y → σ.σ x y ∈ D)
    (h_ne : Nonempty (Fin (nD D)) := Fin.pos_iff_nonempty.mp (nD_pos D hD)) :
    ∃ (s : Split α (nD D)), IsNormalized s ∧ IsRamsey σ s := by
  classical
  obtain ⟨x₀, hx₀⟩ := hD
  let ctx : SplitContext S α := ⟨σ, D, x₀, hx₀, hReg, h_range⟩
  have h_card_G_D : Fintype.card { y : S // y ∈ D ∧ ∃ e ∈ D, e * e = e ∧ IsGreenH y e } = nD D :=
    by
    simp only [nD, ite_eq_left hReg, Fintype.card_subtype]
  let equiv := Fintype.equivOfCardEq (h_card_G_D.trans (Fintype.card_fin _).symm)
  have h_pos : 0 < nD D := Fin.pos_iff_nonempty.mpr h_ne
  let maxRank : Fin (nD D) := ⟨nD D - 1, by omega⟩
  let indexMap := equiv.trans (Equiv.swap (equiv (fColoring ctx
      (Finset.min' Finset.univ Finset.univ_nonempty))) maxRank)
  have h_sig_eq_eId : ∀ x y, x < y → SplitRelation (fun y ↦ indexMap (fColoring ctx y)) x y →
      σ.σ x y = eId ctx x := fun x y hlt hsr ↦ by
    have val_eq := congrArg Subtype.val (indexMap.injective hsr.1)
    have he_eq_ey : eId ctx x = eId ctx y := MulSeq.eq_of_isGreenH_of_idempotent
      (IsGreenH.trans (fColoring_isGreenH ctx x).symm (val_eq ▸ fColoring_isGreenH ctx y))
      (eId_idem ctx x) (eId_idem ctx y)
    let mClass w := Finset.univ.filter (fun z ↦ hOf ctx z = hOf ctx w)
    have hmx : (mClass x).Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
    have hmy : (mClass y).Nonempty := ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, rfl⟩⟩
    let mx := Finset.min' (mClass x) hmx
    let my := Finset.min' (mClass y) hmy
    have min_x_eq_min_y : mx = my := by
      have h_mclass_eq : mClass x = mClass y := by simp only [mClass, hOf_eq_class, he_eq_ey]
      grind
    have h_ese_eq_e : eId ctx x * σ.σ x y * eId ctx x = eId ctx x := by
      by_cases h_mx_lt_x : mx < x
      · have h_prop_x := sigma_props ctx x mx h_mx_lt_x
          (Finset.mem_filter.mp (Finset.min'_mem (mClass x) hmx)).2
        have h_my_lt_y : my < y := min_x_eq_min_y ▸ h_mx_lt_x.trans hlt
        have h_prop_y := sigma_props ctx y my h_my_lt_y
          (Finset.mem_filter.mp (Finset.min'_mem (mClass y) hmy)).2
        have h_sig_mx_x_mul_xy : σ.σ mx x * σ.σ x y = σ.σ mx x := by
          obtain ⟨val_x_eq, h_val_y⟩ :
            (fColoring ctx x).val = σ.σ mx x ∧ (fColoring ctx y).val = σ.σ my y := by
            simp only [fColoring]
            exact ⟨dite_eq_left h_mx_lt_x ▸ h_prop_x.1, dite_eq_left h_my_lt_y ▸ h_prop_y.1⟩
          rw [σ.prop mx x y h_mx_lt_x hlt, ← val_x_eq, val_eq, h_val_y, min_x_eq_min_y]
        have h_e_xy : eId ctx x * σ.σ x y = eId ctx x := by
          rcases h_prop_x.2.1.2 with heq | ⟨w, hw⟩
          · exact heq ▸ h_sig_mx_x_mul_xy
          · rw [hw, mul_assoc, h_sig_mx_x_mul_xy, ← hw]
        exact h_e_xy.symm ▸ eId_idem ctx x
      · have h_mx_eq_x : mx = x := le_antisymm
          (Finset.min'_le (mClass x) x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩))
          (not_lt.mp h_mx_lt_x)
        have h_my_lt_y : my < y := min_x_eq_min_y ▸ h_mx_eq_x ▸ hlt
        have h_prop_y := sigma_props ctx y my h_my_lt_y
          (Finset.mem_filter.mp (Finset.min'_mem (mClass y) hmy)).2
        grind
    have hn_y : ¬ IsMin y := fun h ↦ lt_irrefl x (lt_of_lt_of_le hlt (h (le_of_lt hlt)))
    have hn_x : ¬ IsMax x := fun h ↦ lt_irrefl y (lt_of_le_of_lt (h (le_of_lt hlt)) hlt)
    have hL_y : lOf ctx y = IsGreenL.eqvClass (σ.σ x y) := by
      rw [lOf, dite_eq_right hn_y,
        lOf_well_defined ctx y _ x (Classical.choose_spec (not_isMin_iff.mp hn_y)) hlt]
    have hR_x : rOf ctx x = IsGreenR.eqvClass (σ.σ x y) := by
      rw [rOf, dite_eq_right hn_x,
        rOf_well_defined ctx x _ y (Classical.choose_spec (not_isMax_iff.mp hn_x)) hlt]
    have he_L : eId ctx x ∈ IsGreenL.eqvClass (σ.σ x y) := hL_y ▸ he_eq_ey ▸ (eId_mem ctx y).1
    have he_R : eId ctx x ∈ IsGreenR.eqvClass (σ.σ x y) := hR_x ▸ (eId_mem ctx x).2
    have h_sig_H : IsGreenH (σ.σ x y) (eId ctx x) := IsGreenH.symm ⟨he_L, he_R⟩
    obtain ⟨hid1, hid2⟩ := MulSeq.mul_eq_self_of_isGreenH_idempotent h_sig_H (eId_idem ctx x)
    simpa [hid1, hid2] using h_ese_eq_e
  exact ⟨fun y ↦ indexMap (fColoring ctx y), by
      simp only [IsNormalized, indexMap, Equiv.trans_apply, Equiv.swap_apply_left]
      symm
      rw [Finset.max'_eq_iff]
      exact ⟨Finset.mem_univ _, fun _ _ ↦ by grind⟩,
    fun x y z h_lt_xy _ h_rel_xy _ ↦ by simp [h_sig_eq_eId x y h_lt_xy h_rel_xy],
    fun x y u v hlt_xy hlt_uv hsr_xy hsr_uv hsr_xu ↦ by
      have he_eq := MulSeq.eq_of_isGreenH_of_idempotent
        (IsGreenH.trans (fColoring_isGreenH ctx x).symm
          (congrArg Subtype.val (indexMap.injective hsr_xu.1) ▸ fColoring_isGreenH ctx u))
        (eId_idem ctx x) (eId_idem ctx u)
      rw [h_sig_eq_eId x y hlt_xy hsr_xy, h_sig_eq_eId u v hlt_uv hsr_uv, he_eq]⟩

end WithFintypeSNonemptyAlpha
end WithFintypeAlpha
end WithFiniteS
end RegularDClassCase

section SplitConstruction

/-- Combines splits for regular `D`-classes, shifting sequence ranks above interval ranks. -/
noncomputable abbrev regularSplits {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α) [Nonempty {x // x ∈ xs}]
    [Nonempty (Fin (nD (IsGreenD.eqvClass a)))]
    (sX : Split {x // x ∈ xs} (nD (IsGreenD.eqvClass a)))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a)) :
    Split α (nSElement a) :=
  combineSplits a xs
    (fun x => ⟨(sX x).val + (nSElement a - nD (IsGreenD.eqvClass a)), by
      have hsX_lt := (sX x).isLt
      rw [nSElement]
      omega⟩) sY

/-- Proves the normalization and Ramsey properties for a `regularSplits`
combined split. This is the main interface lemma that assembles the
regular case from its components. -/
lemma regularSplits_props {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α) [Nonempty {x // x ∈ xs}]
    [Nonempty (Fin (nD (IsGreenD.eqvClass a)))]
    (σ : MultiplicativeLabeling S α)
    (σ_X : MultiplicativeLabeling S {x // x ∈ xs})
    (σ_Y : ∀ (i : ℕ), MultiplicativeLabeling S (OpenIntervalType xs i))
    (sX : Split {x // x ∈ xs} (nD (IsGreenD.eqvClass a)))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a))
    (hsX_ramsey : IsRamsey σ_X sX)
    (hsY_ramsey : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      IsRamsey (σ_Y i) (sY i))
    (h_min_in : (Finset.min' (Finset.univ : Finset α)
      Finset.univ_nonempty) ∈ xs)
    (h_σ_X : ∀ x y, σ_X.σ x y = σ.σ x.val y.val)
    (h_σ_Y : ∀ i x y, (σ_Y i).σ x y = σ.σ x.val y.val)
    (h_cov : ∀ x, x ∉ xs → ∃ (i : ℕ) (hi_lt : i < xs.length),
      xs.get ⟨i, hi_lt⟩ < x ∧
      ∀ (h_next_lt : i + 1 < xs.length), x < xs.get ⟨i + 1, h_next_lt⟩)
    (hsY_strict : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)]
      (z : OpenIntervalType xs i),
      (sY i z).val < nSElement a - nD (IsGreenD.eqvClass a))
    (h_xs_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length) (hj_lt : j < xs.length), i < j →
      xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩)
    (h_interval_ramsey : ∀ x y, x ∉ xs → x < y →
      SplitRelation (regularSplits a xs sX sY) x y →
      ∃ (i : ℕ) (x_val y_val : OpenIntervalType xs i),
        x_val.val = x ∧ y_val.val = y ∧
        SplitRelation (@sY i ⟨x_val⟩) x_val y_val)
    (h_min_sX : (sX ⟨Finset.min' (Finset.univ : Finset α)
      Finset.univ_nonempty, h_min_in⟩).val =
      nD (IsGreenD.eqvClass a) - 1)
    (h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
      Finset.univ_nonempty).val = nSElement a - 1)
    (h_N_pos : 0 < nD (IsGreenD.eqvClass a))
    (h_N_le_M : nD (IsGreenD.eqvClass a) ≤ nSElement a) :
    IsNormalized (regularSplits a xs sX sY) ∧
    IsRamsey σ (regularSplits a xs sX sY) := by
  let rankX (x : {x // x ∈ xs}) : Fin (nSElement a) :=
    ⟨(sX x).val + (nSElement a - nD (IsGreenD.eqvClass a)), by
      have hsX_lt := (sX x).isLt
      rw [nSElement]
      omega⟩
  have convert_sr_X : ∀ (p q : α) (hp : p ∈ xs) (hq : q ∈ xs),
      SplitRelation (regularSplits a xs sX sY) p q →
      SplitRelation sX ⟨p, hp⟩ ⟨q, hq⟩ := by
    intro p q hp hq hsr_pq
    constructor
    · apply Fin.ext
      have h_rp : (regularSplits a xs sX sY p).val =
        (sX ⟨p, hp⟩).val + (nSElement a - nD (IsGreenD.eqvClass a)) := by
        simp only [regularSplits, combineSplits, dite_eq_left hp]
      have h_rq : (regularSplits a xs sX sY q).val =
        (sX ⟨q, hq⟩).val + (nSElement a - nD (IsGreenD.eqvClass a)) := by
        simp only [regularSplits, combineSplits, dite_eq_left hq]
      have h_eq := congrArg Fin.val hsr_pq.left
      rw [h_rp, h_rq] at h_eq
      omega
    · intro z hz_ge hz_le
      rcases le_total (⟨p, hp⟩ : {x // x ∈ xs}) ⟨q, hq⟩ with hpq | hqp
      · rw [min_eq_left hpq] at hz_ge ⊢
        rw [max_eq_right hpq] at hz_le
        have hb := hsr_pq.right z.val ((min_eq_left (show p ≤ q from hpq)).symm ▸ hz_ge)
          ((max_eq_right (show p ≤ q from hpq)).symm ▸ hz_le)
        rw [min_eq_left (show p ≤ q from hpq)] at hb
        simpa [regularSplits, combineSplits, hp, z.property] using hb
      · rw [min_eq_right hqp] at hz_ge ⊢
        rw [max_eq_left hqp] at hz_le
        have hb := hsr_pq.right z.val ((min_eq_right (show q ≤ p from hqp)).symm ▸ hz_ge)
          ((max_eq_left (show q ≤ p from hqp)).symm ▸ hz_le)
        rw [min_eq_right (show q ≤ p from hqp)] at hb
        simpa [regularSplits, combineSplits, hq, z.property] using hb
  exact combineSplits_props a xs (nSElement a - nD (IsGreenD.eqvClass a))
    σ σ_Y rankX sY hsY_ramsey h_σ_Y h_cov hsY_strict
    (fun _ _ ↦ Nat.le_add_left _ _) h_xs_mono h_interval_ramsey
    (fun x y z hx hy hz hlt_xy hlt_yz hsr_xy hsr_yz ↦ by
      simpa only [h_σ_X] using hsX_ramsey.1 ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ hlt_xy hlt_yz
        (convert_sr_X x y hx hy hsr_xy) (convert_sr_X y z hy hz hsr_yz))
    (fun x y u v hx hy hu hv hlt_xy hlt_uv hsr_xy hsr_uv hsr_xu ↦ by
      simpa only [h_σ_X] using hsX_ramsey.2 ⟨x, hx⟩ ⟨y, hy⟩ ⟨u, hu⟩ ⟨v, hv⟩
        hlt_xy hlt_uv (convert_sr_X x y hx hy hsr_xy)
        (convert_sr_X u v hu hv hsr_uv) (convert_sr_X x u hx hu hsr_xu))
    (by grind) h_max_val

/-- Constructs a normalized Ramsey split when the `D`-class of `a` is regular. -/
lemma ramsey_split_regular_case {S : Type*} [Semigroup S] [Fintype S]
    (a : S) {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α) (h_img : labelingIn σ (jUp a))
    (h_reg : IsRegularDClass (IsGreenD.eqvClass a))
    (ih : ∀ b : S, nSElement b < nSElement a →
    ∀ (xs : List α) (i : ℕ) [Nonempty (OpenIntervalType xs i)]
    (σ_β : MultiplicativeLabeling S (OpenIntervalType xs i)), labelingIn σ_β (jUp b) →
    ∃ (s : Split (OpenIntervalType xs i) (nSElement b)), IsNormalized s ∧ IsRamsey σ_β s) :
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s := by
  let x₀ := Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty
  let xs := buildXSeq a σ x₀
  have h_x0_in : x₀ ∈ xs := by
    change x₀ ∈ buildXSeq a σ x₀
    rw [buildXSeq]
    split_ifs <;> exact List.Mem.head _
  have instNonemptyXs : Nonempty {x // x ∈ xs} := ⟨⟨x₀, h_x0_in⟩⟩
  have h_pos := nD_pos (IsGreenD.eqvClass a) ⟨a, rfl⟩
  have instNonemptyFin : Nonempty (Fin (nD (IsGreenD.eqvClass a))) := Fin.pos_iff_nonempty.mp h_pos
  let σ_X : MultiplicativeLabeling S {x // x ∈ xs} :=
    ⟨fun x y ↦ σ.σ x.val y.val, fun x y z hx hy ↦ σ.prop x.val y.val z.val hx hy⟩
  let σ_Y (i : ℕ) : MultiplicativeLabeling S (OpenIntervalType xs i) :=
    ⟨fun x y ↦ σ.σ x.val y.val, fun x y z hx hy ↦ σ.prop x.val y.val z.val hx hy⟩
  obtain ⟨sX, hsX_norm, hsX_ramsey⟩ :=
    ramsey_regular_d_case σ_X (IsGreenD.eqvClass a) ⟨a, rfl⟩ h_reg
    (fun x y hlt ↦ (buildXSeq_properties a σ h_img x₀).2.1 x.val x.prop y.val y.prop hlt)
  choose sY hsY_ramsey hsY_strict using build_interval_splits_of_ih a σ h_img xs
    (buildXSeq_properties a σ h_img x₀).2.2.1 ih
  have hm_max : (Finset.max' (Finset.univ : Finset (Fin (nSElement a))) Finset.univ_nonempty).val =
      nSElement a - 1 := congrArg Fin.val
    ((Finset.max'_eq_iff _ _ ⟨nSElement a - 1, Nat.sub_lt (nSElement_pos a) (by decide)⟩).mpr
      ⟨Finset.mem_univ _, fun w _ ↦ Fin.le_iff_val_le_val.mpr (Nat.le_pred_of_lt w.isLt)⟩)
  exact ⟨regularSplits a xs sX sY, regularSplits_props a xs σ σ_X σ_Y sX sY hsX_ramsey hsY_ramsey
    h_x0_in (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun x hx ↦ buildXSeq_covers a σ x₀ x (Finset.min'_le _ _ (Finset.mem_univ x)) hx) hsY_strict
    (buildXSeq_properties a σ h_img x₀).2.2.2
    (h_interval_ramsey := combineSplits_interval_ramsey a xs
      (fun x : {x // x ∈ xs} ↦ ⟨(sX x).val + (nSElement a - nD (IsGreenD.eqvClass a)), by
        have hsX_lt := (sX x).isLt
        rw [nSElement]
        omega⟩)
      sY (nSElement a - nD (IsGreenD.eqvClass a)) (buildXSeq_properties a σ h_img x₀).2.2.2
      (fun x hx ↦ buildXSeq_covers a σ x₀ x (Finset.min'_le _ _ (Finset.mem_univ x)) hx) hsY_strict
      (fun _ ↦ Nat.le_add_left _ _))
    (h_min_sX := by
      have h_min_eq : (⟨Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty, h_x0_in⟩ :
          {x // x ∈ xs}) = Finset.min' Finset.univ Finset.univ_nonempty :=
        Subtype.ext (le_antisymm (Finset.min'_le _ _ (Finset.mem_univ _))
          (Finset.min'_le (Finset.univ : Finset {x // x ∈ xs}) ⟨x₀, h_x0_in⟩ (Finset.mem_univ _)))
      have hm : Finset.max' (Finset.univ : Finset (Fin (nD (IsGreenD.eqvClass a))))
          Finset.univ_nonempty = ⟨nD (IsGreenD.eqvClass a) - 1, Nat.sub_lt h_pos (by decide)⟩ :=
        (Finset.max'_eq_iff _ _ _).mpr
          ⟨Finset.mem_univ _, fun w _ ↦ Fin.le_iff_val_le_val.mpr (Nat.le_pred_of_lt w.isLt)⟩
      rw [h_min_eq, hsX_norm, hm])
    (h_max_val := hm_max) (h_N_pos := h_pos)
    (h_N_le_M := by unfold nSElement; simp)⟩

end SplitConstruction

end RamseySplit
