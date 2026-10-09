/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Topology.Order
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import AlgebraicAutomata.FactorizationForest.Split

/-!
# Infinitary Simon's Theorem over ℕ

Formalization of the infinitary variant of
Simon's Factorization Forest Theorem for the linear order ⟨ℕ, <⟩.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

@[expose] public section


open scoped Topology

namespace RamseySplit

section RamseySplitInfinitary

variable {S : Type*} [Semigroup S] [Fintype S]
variable [Nonempty (Fin (nS S))]
variable (σ : MultiplicativeLabeling S ℕ)

/-- Restricts a multiplicative labeling on `ℕ` to `Fin (N + 1)`. -/
def restrictLabeling (N : ℕ) : MultiplicativeLabeling S (Fin (N + 1)) where
  σ := fun i j => σ.σ i.val j.val
  prop := fun x y z hxy hyz => σ.prop x.val y.val z.val hxy hyz

/-- A choice of Ramsey split on `Fin (N + 1)` for the restricted labeling. -/
noncomputable def finSplit (N : ℕ) : Split (Fin (N + 1)) (nS S) :=
  (simon_split (restrictLabeling σ N)).choose

/-- The chosen split `finSplit` is a Ramsey split for the restricted labeling. -/
lemma isRamsey_finSplit (N : ℕ) : IsRamsey (restrictLabeling σ N) (finSplit σ N) :=
  (simon_split (restrictLabeling σ N)).choose_spec.2

/-- Extension of `finSplit` to all of `ℕ` by a default value outside `[0, N]`. -/
noncomputable def extendFinSplit (N : ℕ) : ℕ → Fin (nS S) :=
  fun k =>
    if hk : k ≤ N then
      finSplit σ N ⟨k, Nat.lt_succ_of_le hk⟩
    else
      Classical.choice inferInstance

/-- The extension `extendFinSplit` agrees with `finSplit` on indices within `[0, N]`. -/
lemma extendFinSplit_of_le {N k : ℕ} (hk : k ≤ N) :
    extendFinSplit σ N k = finSplit σ N ⟨k, Nat.lt_succ_of_le hk⟩ :=
  dite_eq_left hk

/-- By compactness of `ℕ → Fin (nS S)`, the sequence of extended splits has a cluster point. -/
lemma exists_clusterPt :
    ∃ s : ℕ → Fin (nS S), MapClusterPt s Filter.atTop (extendFinSplit σ) :=
  (isCompact_univ.exists_mapClusterPt
    (show Filter.map (extendFinSplit σ) Filter.atTop ≤ Filter.principal Set.univ by simp)).imp
    fun _ ↦ And.right

/-- Since `s` is a cluster point, for any finite bound `M`, there is `N ≥ M`
such that `extendFinSplit` coincides with `s` on `[0, M]`. -/
lemma exists_coinciding_bound (s : ℕ → Fin (nS S))
    (hs : MapClusterPt s Filter.atTop (extendFinSplit σ)) (M : ℕ) :
    ∃ N, M ≤ N ∧ ∀ k ≤ M, extendFinSplit σ N k = s k :=
  (Filter.frequently_atTop.mp (mapClusterPt_iff_frequently.mp hs _
    (set_pi_mem_nhds (Set.finite_Iic M) fun _ _ => (isOpen_discrete _).mem_nhds rfl)) M).imp
    fun _ ⟨hM, h_pi⟩ ↦ ⟨hM, fun _ hk ↦ (h_pi _ hk).symm⟩

/-- If a split `s_fin` on `Fin (N + 1)` agrees with a split `s` on `ℕ` up to `max x y`,
then the split relation `SplitRelation s x y` is inherited by `s_fin`. -/
lemma splitRelation_of_agree {n N : ℕ} (s : Split ℕ n) (s_fin : Split (Fin (N + 1)) n)
    (x y : Fin (N + 1)) (h_agree : ∀ k ≤ max x y, s_fin k = s k.val)
    (hsr : SplitRelation s x.val y.val) : SplitRelation s_fin x y := by
  grind

/-- The split relation on `ℕ` is reflected to `finSplit σ N` for points within range `M ≤ N`. -/
lemma splitRelation_finSplit {s : ℕ → Fin (nS S)} {M N : ℕ} (hMN : M ≤ N)
    (h_ext : ∀ k ≤ M, extendFinSplit σ N k = s k) {a b : ℕ} (ha : a ≤ M) (hb : b ≤ M)
    (h : SplitRelation s a b) :
    SplitRelation (finSplit σ N) ⟨a, by omega⟩ ⟨b, by omega⟩ := by
  apply splitRelation_of_agree s (finSplit σ N) ⟨a, by omega⟩ ⟨b, by omega⟩ _ h
  intro k hk
  have hkM : k.val ≤ M := by grind
  have hkN : k.val ≤ N := hkM.trans hMN
  exact (extendFinSplit_of_le σ hkN).symm.trans (h_ext k.val hkM)

/-- The infinitary Ramsey split theorem for `ℕ`:
for any multiplicative labeling `σ` over `ℕ` into a finite semigroup `S`,
there exists a Ramsey split of size `nS S`. -/
theorem exists_ramseySplit_nat :
    ∃ s : Split ℕ (nS S), IsRamsey σ s := by
  obtain ⟨s, hs⟩ := exists_clusterPt σ
  use s
  constructor
  · intro x y z hxy hyz hsr_xy hsr_yz
    obtain ⟨N, hMN, h_ext⟩ := exists_coinciding_bound σ s hs z
    exact (isRamsey_finSplit σ N).1 ⟨x, by omega⟩ ⟨y, by omega⟩ ⟨z, by omega⟩
      (Fin.lt_def.mpr hxy) (Fin.lt_def.mpr hyz)
      (splitRelation_finSplit σ hMN h_ext (by omega) (by omega) hsr_xy)
      (splitRelation_finSplit σ hMN h_ext (by omega) (by omega) hsr_yz)
  · intro x y u v hxy huv hsr_xy hsr_uv hsr_xu
    obtain ⟨N, hMN, h_ext⟩ := exists_coinciding_bound σ s hs (max y v)
    exact (isRamsey_finSplit σ N).2 ⟨x, by omega⟩ ⟨y, by omega⟩ ⟨u, by omega⟩ ⟨v, by omega⟩
      (Fin.lt_def.mpr hxy) (Fin.lt_def.mpr huv)
      (splitRelation_finSplit σ hMN h_ext (by omega) (by omega) hsr_xy)
      (splitRelation_finSplit σ hMN h_ext (by omega) (by omega) hsr_uv)
      (splitRelation_finSplit σ hMN h_ext (by omega) (by omega) hsr_xu)

end RamseySplitInfinitary

end RamseySplit
