/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max
import AlgebraicAutomata.Semigroup.GreensRelations.Order

/-!
# Ramsey Splits — Basic Definitions

Core structures and definitions for Ramsey splits, including multiplicative
labelings, splits, Ramsey condition, and Green's relation invariants.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace RamseySplit

open GreensRelations

section SplitDefinitions

variable {S α : Type*} [Semigroup S] [LinearOrder α]

variable {h : ℕ}

/-- A multiplicative labeling over a linearly ordered type `α` into a semigroup
`S`, satisfying the property that `σ x y * σ y z = σ x z` for all `x < y < z`.
This models the evaluation of subwords in a factorization. -/
structure MultiplicativeLabeling (S α : Type*) [Semigroup S] [LinearOrder α] where
  /-- The labeling function, mapping a pair of indices to a semigroup element. -/
  σ : α → α → S
  /-- Multiplicativity: adjacent subwords multiply together correctly. -/
  prop : ∀ x y z : α, x < y → y < z → σ x y * σ y z = σ x z

/-- A split is a function assigning each element of `α` a bounded integer rank
in `Fin h`. The rank encodes the "level" at which an element participates in the
factorization forest construction. -/
abbrev Split (α : Type*) (h : ℕ) := α → Fin h

/-- `SplitRelation s x y` holds when `x` and `y` have the same rank under `s`,
and every element `z` between them (in the linear order) has a rank at most
equal to that of the minimum of `x` and `y`. -/
abbrev SplitRelation (s : Split α h) (x y : α) : Prop :=
  s x = s y ∧ ∀ z, min x y ≤ z → z ≤ max x y → s z ≤ s (min x y)

/-- A strictly monotone transformation of ranks preserves `SplitRelation`. -/
lemma SplitRelation.comp_strictMono {h₁ h₂ : ℕ} (s : Split α h₁) (f : Fin h₁ → Fin h₂)
    (hf : StrictMono f) (x y : α) :
    SplitRelation (f ∘ s) x y ↔ SplitRelation s x y := by
  simp only [SplitRelation, Function.comp_apply, hf.injective.eq_iff, hf.le_iff_le]

lemma splitRelation_of_le_between {α : Type*} [LinearOrder α] {h : ℕ} (s : Split α h)
    {a b : α} (hab : a < b) (heq : s a = s b)
    (hbetween : ∀ z, a < z → z < b → s z ≤ s a) : SplitRelation s a b := by
  refine ⟨heq, fun z hz1 hz2 ↦ ?_⟩
  rw [min_eq_left hab.le] at hz1 ⊢
  rw [max_eq_right hab.le] at hz2
  rcases hz1.eq_or_lt with rfl | ha
  · rfl
  rcases hz2.eq_or_lt with rfl | hb
  · rw [heq]
  exact hbetween z ha hb

/-- A split function is normalized if the minimal element of `α` receives the
maximal possible rank `Finset.max' Finset.univ`. This normalization ensures
the split is compatible with the inductive structure of the proof. -/
abbrev IsNormalized [Fintype α] [Nonempty α] [Nonempty (Fin h)]
    (s : Split α h) : Prop :=
  let min_α := Finset.min' Finset.univ Finset.univ_nonempty
  s min_α = Finset.max' Finset.univ Finset.univ_nonempty

/-- `IsRamsey L s` holds if adjacent split-related points evaluate to idempotents and
cross-related points evaluate uniformly. -/
abbrev IsRamsey (L : MultiplicativeLabeling S α) (s : Split α h) : Prop :=
  (∀ x y z : α, x < y → y < z → SplitRelation s x y → SplitRelation s y z →
    L.σ x y * L.σ x y = L.σ x y) ∧
  (∀ x y u v : α, x < y → u < v →
    SplitRelation s x y → SplitRelation s u v → SplitRelation s x u →
    L.σ x y = L.σ u v)

lemma isRamsey_idem_step {L : MultiplicativeLabeling S α} {s : Split α h} (h_ramsey : IsRamsey L s)
    {x y z : α} (hxy : x < y) (hyz : y < z)
    (h_rel_xy : SplitRelation s x y) (h_rel_yz : SplitRelation s y z) :
    L.σ x y * L.σ x y = L.σ x y ∧
    L.σ x y = L.σ y z ∧
    L.σ x z = L.σ x y ∧
    L.σ x z * L.σ x z = L.σ x z ∧
    L.σ y z = L.σ x z := by
  have h_eq := h_ramsey.2 x y y z hxy hyz h_rel_xy h_rel_yz h_rel_xy
  have h_idem := h_ramsey.1 x y z hxy hyz h_rel_xy h_rel_yz
  have h_tot := L.prop x y z hxy hyz
  have h_xz : L.σ x z = L.σ x y := by rw [← h_tot, ← h_eq, h_idem]
  refine ⟨h_idem, h_eq, h_xz, by rw [h_xz, h_idem], by rw [h_xz, h_eq]⟩

end SplitDefinitions

section WordDefinitions

/-- Multiplicative labeling mapping `(i, j)` to `eval(u[i..j])`. -/
abbrev wordLabeling {A S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) : MultiplicativeLabeling S (Fin (u.length + 1)) where
  σ := fun i j => eval ((u.drop i.val).take (j.val - i.val))
  prop := by
    intros x y z hxy hyz
    have h_ne : ∀ (a b : Fin (u.length + 1)), a < b →
        (u.drop a.val).take (b.val - a.val) ≠ [] := by
      intro a b hab
      simp [List.take_eq_nil_iff]
      omega
    have hd : u.drop y.val = (u.drop x.val).drop (y.val - x.val) := by
      rw [List.drop_drop]
      congr 1
      omega
    have h_cat : (u.drop x.val).take (y.val - x.val) ++ (u.drop y.val).take (z.val - y.val) =
        (u.drop x.val).take (z.val - x.val) := by
      rw [hd, ← List.take_add]
      congr 1
      omega
    rw [← hmul _ _ (h_ne x y hxy) (h_ne y z hyz), h_cat]

end WordDefinitions

section nD

variable {S : Type*} [Semigroup S] [Fintype S]

open Classical in
/-- Number of elements in `D` in the `H`-class of some idempotent, or 1 if non-regular. -/
noncomputable abbrev nD (D : Set S) : ℕ :=
  if IsRegularDClass D then
    (Finset.univ.filter (fun x ↦
      x ∈ D ∧ ∃ e ∈ D, e * e = e ∧ IsGreenH x e
    )).card
  else
    1

open Classical in
/-- The value `nD D` is strictly positive for any Green's `D`-class `D`. -/
theorem nD_pos (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) : 0 < nD D := by
  dsimp [nD]
  split_ifs with hReg
  · obtain ⟨e, heD, he_idem⟩ := (isRegularDClass_iff_exists_idempotent D hD).mp hReg
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, heD, e, heD, he_idem, IsGreenH.refl _⟩⟩
  · decide

end nD

section LabelingProperties

variable {S : Type*} [Semigroup S]

/-- The set of elements of `S` whose Green's `J`-class is at least as large as
that of `a`, i.e., `b` such that `a ≤_J b`. Used to bound the image of a
multiplicative labeling during the induction in Simon's theorem. -/
abbrev jUp (a : S) : Set S := { b | GreenJClass.mk a ≤ GreenJClass.mk b }

/-- States that all strictly ordered pairs `(x, y)` under the labeling `σ`
map into the set `U`. This is the hypothesis that the labeling takes values
in the relevant J-upward closure. -/
abbrev labelingIn {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (U : Set S) : Prop :=
  ∀ x y : α, x < y → σ.σ x y ∈ U

/-- Factors are J-greater than or equal to the product containing them. -/
lemma labeling_factor_le_J {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (u v w x : α)
    (huv : u ≤ v) (hvw : v < w) (hwx : w ≤ x) :
    GreenJClass.mk (σ.σ u x) ≤ GreenJClass.mk (σ.σ v w) :=
  have h1 : GreenJClass.mk (σ.σ u x) ≤ GreenJClass.mk (σ.σ v x) :=
    huv.eq_or_lt.elim (fun | rfl => le_rfl) fun h ↦
      (σ.prop u v x h (hvw.trans_le hwx)).symm ▸ IsGreenJRel.mul_left _ rfl
  have h2 : GreenJClass.mk (σ.σ v x) ≤ GreenJClass.mk (σ.σ v w) :=
    hwx.eq_or_lt.elim (fun | rfl => le_rfl) fun h ↦
      (σ.prop v w x hvw h).symm ▸ IsGreenJRel.mul_right _ rfl
  h1.trans h2

variable [Finite S]

/-- If a prefix product is `D`-related to `a`, the extended product is also `D`-related to `a`. -/
lemma isGreenD_of_prefix (a : S) {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (h_img : labelingIn σ (jUp a))
    (u v w : α) (huv : u < v) (hvw : v ≤ w) (hD : IsGreenD (σ.σ u v) a) :
    IsGreenD (σ.σ u w) a :=
  hvw.eq_or_lt.elim (fun | rfl => hD) fun hvw_lt ↦
    isGreenD_of_isGreenJ (GreenJClass.mk_eq_mk_iff.mp (le_antisymm
      (GreenJClass.mk_eq_mk_iff.mpr (isGreenJ_of_isGreenD hD) ▸
        labeling_factor_le_J σ u u v w le_rfl huv hvw)
      (h_img u w (huv.trans hvw_lt))))

end LabelingProperties

section GeneralUtility

/-- A subtype of `α` representing elements strictly between `xs[i]` and
`xs[i+1]` (or between `xs[i]` and +∞ if `i` is the last index).
Used to restrict the inductive hypothesis to proper sub-intervals. -/
abbrev OpenIntervalType {α : Type*} [LinearOrder α] (xs : List α) (i : ℕ) :=
  { y : α // ∃ (hi_lt : i < xs.length),
    xs.get ⟨i, hi_lt⟩ < y ∧
    ∀ (h_next_lt : i + 1 < xs.length), y < xs.get ⟨i + 1, h_next_lt⟩ }

/-- A strictly increasing sequence covering a domain bounds any element `x`
either at one of the sequence points or within a consecutive interval.
This is the key covering lemma used in the split combination construction. -/
lemma list_interval_covers {α : Type*} [LinearOrder α] (x : α) :
    ∀ (xs : List α), x ∉ xs →
    (∃ y ∈ xs, y < x) →
    ∃ (i : ℕ) (hi_lt : i < xs.length),
      xs.get ⟨i, hi_lt⟩ < x ∧
      ∀ (hi_succ_lt : i + 1 < xs.length), x < xs.get ⟨i + 1, hi_succ_lt⟩
  | [], _, ⟨_, hy, _⟩ => nomatch hy
  | a :: tail, h_not_in, h_lb => by
    by_cases h_tail : ∃ y ∈ tail, y < x
    · obtain ⟨i, hi, hlt, hgt⟩ :=
        list_interval_covers x tail (fun h => h_not_in (List.Mem.tail _ h)) h_tail
      exact ⟨i + 1, Nat.succ_lt_succ hi, hlt, fun h ↦ hgt (Nat.lt_of_succ_lt_succ h)⟩
    · grind

/-- An element in an open interval `OpenIntervalType xs i` is never a member
of the sequence `xs` itself (since it is strictly between two consecutive
sequence points, while the sequence is strictly monotone). -/
lemma not_mem_of_openInterval {α : Type*} [LinearOrder α] {xs : List α}
    (h_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length) (hj_lt : j < xs.length),
      i < j → xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩)
    (i : ℕ) (z : α)
    (h_in : ∃ (hi_lt : i < xs.length),
      xs.get ⟨i, hi_lt⟩ < z ∧ ∀ (hi_succ_lt : i + 1 < xs.length),
      z < xs.get ⟨i + 1, hi_succ_lt⟩) : z ∉ xs := by
  grind [List.mem_iff_get]

/-- Two open intervals defined by the same strictly increasing sequence are
disjoint: if an element `x` lies in both interval `i` and interval `k`,
then `i = k`. -/
lemma openInterval_unique {α : Type*} [LinearOrder α] (xs : List α)
    (h_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length)
      (hj_lt : j < xs.length), i < j →
      xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩)
    (x : α) (i k : ℕ) (hi : i < xs.length) (hk : k < xs.length)
    (hlt_i : xs.get ⟨i, hi⟩ < x)
    (hgt_i : ∀ h_next_lt : i + 1 < xs.length,
      x < xs.get ⟨i + 1, h_next_lt⟩)
    (hlt_k : xs.get ⟨k, hk⟩ < x)
    (hgt_k : ∀ h_next_lt : k + 1 < xs.length,
      x < xs.get ⟨k + 1, h_next_lt⟩) :
    i = k := by
  rcases lt_trichotomy i k with h | rfl | h <;> first | rfl | cases (show False by grind)

end GeneralUtility

end RamseySplit
