/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Order.CompleteLattice.Finset
import AlgebraicAutomata.FactorizationForest.Combine
import AlgebraicAutomata.FactorizationForest.Tree
import AlgebraicAutomata.Mathlib.Data.List.SemigroupProd
/-!
# Locally Finite Semigroups and Brown's Lemma

Locally finite semigroups, Brown's Lemma, and Colcombet's Set-Family Fixed Point Theorem.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

/-- A semigroup S is locally finite if every finite subset generates a finite subsemigroup. -/
def IsLocallyFinite (S : Type*) [Semigroup S] : Prop :=
  ∀ (X : Set S), X.Finite → (Subsemigroup.closure X : Set S).Finite

namespace BrownLemma

open Set RamseySplit FactorizationTree
open scoped Pointwise

variable {S T : Type*} [Semigroup S] [Semigroup T]

section ClosureSequence

/-- The inductive sequence of subsets `X_seq ϕ X n ⊆ S`:
`X_seq ϕ X 0 = X`.
`X_seq ϕ X (n + 1) = X_seq ϕ X n ∪ (X_seq ϕ X n * X_seq ϕ X n) ∪`
  `⋃_{e ∈ T, e² = e} ⟨X_seq ϕ X n ∩ ϕ⁻¹(e)⟩_S`. -/
def X_seq (ϕ : S →ₙ* T) (X : Set S) : ℕ → Set S
  | 0 => X
  | n + 1 =>
    let Xn := X_seq ϕ X n
    Xn ∪ (Xn * Xn) ∪ ⋃ (e : T) (_he : e * e = e), (Subsemigroup.closure (Xn ∩ ϕ ⁻¹' {e}) : Set S)

/-- Xₘ ⊆ Xₙ whenever m ≤ n. -/
lemma X_seq_mono (ϕ : S →ₙ* T) (X : Set S) {m n : ℕ} (h : m ≤ n) :
    X_seq ϕ X m ⊆ X_seq ϕ X n :=
  Nat.le.recOn h subset_rfl (fun _ ih ↦ ih.trans (subset_union_left.trans subset_union_left))

/-- Xₙ ⊆ ⟨X⟩_S for all n. -/
lemma X_seq_subset_closure (ϕ : S →ₙ* T) (X : Set S) (n : ℕ) :
    X_seq ϕ X n ⊆ Subsemigroup.closure X := by
  induction n with
  | zero => exact Subsemigroup.subset_closure
  | succ n ih =>
    dsimp [X_seq]
    apply union_subset
    · apply union_subset
      · exact ih
      · rintro _ ⟨a, ha, b, hb, rfl⟩
        exact Subsemigroup.mul_mem _ (ih ha) (ih hb)
    · simp only [iUnion_subset_iff, SetLike.coe_subset_coe, Subsemigroup.closure_le]
      intro e he x hx
      exact ih hx.1

end ClosureSequence

section TreeLemmas

omit [Semigroup S] in
mutual
  /-- The yield of a Ramsey factorization tree is always non-empty. -/
  lemma tree_value_ne_nil (t : FactorizationTree S) (eval : List S → T)
      (ht : t.IsRamsey eval) : t.value ≠ [] := by
    cases t with
    | leaf a => simp [FactorizationTree.value]
    | binary l r => exact fun h ↦ tree_value_ne_nil l eval ht.1 (List.append_eq_nil_iff.mp h).1
    | idempotent cs => exact listTree_value_ne_nil cs eval ht.2.1 (fun h ↦ by cases h ▸ ht.1)

  /-- The yield of a list of Ramsey factorization trees is non-empty if the list is non-empty. -/
  lemma listTree_value_ne_nil (cs : List (FactorizationTree S)) (eval : List S → T)
      (hcs : FactorizationTree.listIsRamsey eval cs) (hne : cs ≠ []) :
      FactorizationTree.listValue cs ≠ [] := by
    rcases cs with _ | ⟨c, _⟩
    · contradiction
    · exact fun h ↦ tree_value_ne_nil c eval hcs.1 (List.append_eq_nil_iff.mp h).1
end

mutual
  /-- Product of the yield of a Ramsey tree is contained in `X_seq` at its height. -/
  lemma tree_prod_in_X_seq (ϕ : S →ₙ* T) (X : Set S)
      (eval : List S → T)
      (h_eval : ∀ w hw, eval w = ϕ (listProdNE w hw))
      (t : FactorizationTree S) (ht : t.IsRamsey eval)
      (hX : ∀ x ∈ t.value, x ∈ X)
      (ht_ne : t.value ≠ []) :
      listProdNE t.value ht_ne ∈ X_seq ϕ X t.height := by
    cases t with
    | leaf a => exact hX a (by simp [FactorizationTree.value])
    | binary l r =>
      have hl_ne := tree_value_ne_nil l eval ht.1
      have hr_ne := tree_value_ne_nil r eval ht.2
      have ih_l := X_seq_mono ϕ X (le_max_left l.height r.height)
        (tree_prod_in_X_seq ϕ X eval h_eval l ht.1
          (fun x hx ↦ hX x (by simp [FactorizationTree.value, hx])) hl_ne)
      have ih_r := X_seq_mono ϕ X (le_max_right l.height r.height)
        (tree_prod_in_X_seq ϕ X eval h_eval r ht.2
          (fun x hx ↦ hX x (by simp [FactorizationTree.value, hx])) hr_ne)
      have h_prod : listProdNE (l.binary r).value ht_ne =
          listProdNE l.value hl_ne * listProdNE r.value hr_ne := by
        rw [listProdNE_eq (l.binary r).value (l.value ++ r.value) ht_ne
          (by simp [hl_ne, hr_ne]) rfl]
        exact listProdNE_concat l.value r.value hl_ne hr_ne
      rw [h_prod]
      dsimp [FactorizationTree.height]
      rw [add_comm 1]
      dsimp [X_seq]
      exact Or.inl (Or.inr ⟨_, ih_l, _, ih_r, rfl⟩)
    | idempotent cs =>
      obtain ⟨hlen, hcs_ramsey, e, he_idem, he_eval⟩ := ht
      have hcs_ne : cs ≠ [] := by
        rintro rfl
        dsimp at hlen
        omega
      have ih := listTree_prod_in_closure ϕ X eval h_eval cs hcs_ramsey hcs_ne e he_eval hX
      dsimp [FactorizationTree.height]
      rw [add_comm 1]
      dsimp [X_seq]
      exact Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he_idem, ih⟩⟩)

  /-- Auxiliary induction for the children of an idempotent node. -/
  lemma listTree_prod_in_closure (ϕ : S →ₙ* T) (X : Set S)
      (eval : List S → T)
      (h_eval : ∀ w hw, eval w = ϕ (listProdNE w hw))
      (cs : List (FactorizationTree S)) (hcs : FactorizationTree.listIsRamsey eval cs)
      (hne : cs ≠ []) (e : T)
      (he_eval : ∀ c ∈ cs, eval c.value = e)
      (hX : ∀ x ∈ FactorizationTree.listValue cs, x ∈ X) :
      listProdNE (FactorizationTree.listValue cs) (listTree_value_ne_nil cs eval hcs hne) ∈
        (Subsemigroup.closure
          (X_seq ϕ X (FactorizationTree.listHeight cs) ∩ ϕ ⁻¹' {e}) : Set S) := by
    cases cs with
    | nil => contradiction
    | cons c rest =>
      have hc_ne := tree_value_ne_nil c eval hcs.1
      have ih_c := X_seq_mono ϕ X (le_max_left c.height (FactorizationTree.listHeight rest))
        (tree_prod_in_X_seq ϕ X eval h_eval c hcs.1
          (fun x hx ↦ hX x (by simp [FactorizationTree.listValue, hx])) hc_ne)
      have hc_phi : ϕ (listProdNE c.value hc_ne) = e := by
        have h_eval_c := h_eval c.value hc_ne
        rw [he_eval c (by simp)] at h_eval_c
        exact h_eval_c.symm
      have hc_in : listProdNE c.value hc_ne ∈
          Subsemigroup.closure
            (X_seq ϕ X (FactorizationTree.listHeight (c :: rest)) ∩ ϕ ⁻¹' {e}) :=
        Subsemigroup.subset_closure ⟨ih_c, hc_phi⟩
      by_cases hrest : rest = []
      · subst hrest
        rw [listProdNE_eq _ _ _ hc_ne (by simp [FactorizationTree.listValue])]
        exact hc_in
      · have hrest_val_ne := listTree_value_ne_nil rest eval hcs.2 hrest
        have ih_rest := listTree_prod_in_closure ϕ X eval h_eval rest hcs.2 hrest e
          (fun t ht ↦ he_eval t (by simp [ht]))
          (fun x hx ↦ hX x (by simp [FactorizationTree.listValue, hx]))
        have h_sub :
            (Subsemigroup.closure (X_seq ϕ X (FactorizationTree.listHeight rest) ∩ ϕ ⁻¹' {e}) :
              Set S) ⊆
            Subsemigroup.closure
              (X_seq ϕ X (FactorizationTree.listHeight (c :: rest)) ∩ ϕ ⁻¹' {e}) := by
          simp only [SetLike.coe_subset_coe, Subsemigroup.closure_le]
          exact fun x hx ↦ Subsemigroup.subset_closure
            ⟨X_seq_mono ϕ X (le_max_right _ _) hx.1, hx.2⟩
        have h_prod :
            listProdNE (FactorizationTree.listValue (c :: rest))
              (listTree_value_ne_nil (c :: rest) eval hcs hne) =
            listProdNE c.value hc_ne *
              listProdNE (FactorizationTree.listValue rest) hrest_val_ne := by
          rw [listProdNE_eq (FactorizationTree.listValue (c :: rest))
            (c.value ++ FactorizationTree.listValue rest) _
            (by simp [hc_ne, hrest_val_ne]) rfl]
          exact listProdNE_concat c.value (FactorizationTree.listValue rest) hc_ne hrest_val_ne
        rw [h_prod]
        exact Subsemigroup.mul_mem _ hc_in (h_sub ih_rest)
end

end TreeLemmas

section AlgebraicPresentation

/-- Algebraic Presentation Theorem: `⟨X⟩_S = X_{3 * nS T - 1}`. -/
theorem closure_eq_X_seq [Fintype T] [Nonempty T] (ϕ : S →ₙ* T) (X : Set S) :
    (Subsemigroup.closure X : Set S) = X_seq ϕ X (3 * nS T - 1) := by
  ext s
  constructor
  · intro hs
    rcases (mem_closure_iff_exists_list X s).mp hs with ⟨u, hu, huX, rfl⟩
    obtain ⟨t, ht_val, ht_ramsey, ht_height⟩ :=
      factorization_forest_theorem_mulHom ϕ u hu
    let eval_T : List S → T :=
      fun w ↦ if hw : w = [] then Classical.arbitrary T else ϕ (listProdNE w hw)
    have ht_X : ∀ x ∈ t.value, x ∈ X := ht_val.symm ▸ huX
    have ht_ne : t.value ≠ [] := ht_val.symm ▸ hu
    have h_in_3n := X_seq_mono ϕ X ht_height
      (tree_prod_in_X_seq ϕ X eval_T (by grind) t ht_ramsey ht_X ht_ne)
    grind
  · exact fun hs ↦ X_seq_subset_closure ϕ X (3 * nS T - 1) hs

end AlgebraicPresentation

section SetFamilyFixedPoint

/-- Condition (1):
For all a ∈ T, {x ∈ X | ϕ(x) = a} ∈ P. -/
def Cond1 (ϕ : S →ₙ* T) (X : Set S) (P : Set (Set S)) : Prop :=
  ∀ a : T, {x ∈ X | ϕ x = a} ∈ P

/-- Condition (1'):
If A ⊆ B and B ∈ P, then A ∈ P (down-closed / hereditary). -/
def Cond1' (P : Set (Set S)) : Prop :=
  ∀ ⦃A B : Set S⦄, A ⊆ B → B ∈ P → A ∈ P

/-- Condition (1''):
X ∈ P. -/
def Cond1'' (X : Set S) (P : Set (Set S)) : Prop := X ∈ P

/-- Condition (2):
For all A, B ∈ P, A ∪ B ∈ P. -/
def Cond2 (P : Set (Set S)) : Prop :=
  ∀ ⦃A B : Set S⦄, A ∈ P → B ∈ P → A ∪ B ∈ P

/-- Condition (3):
For all A, B ∈ P, A * B ∈ P. -/
def Cond3 (P : Set (Set S)) : Prop :=
  ∀ ⦃A B : Set S⦄, A ∈ P → B ∈ P → A * B ∈ P

/-- Condition (4):
For all A ∈ P, if A ⊆ ϕ⁻¹({e}) for an idempotent e ∈ T,
then ⟨A⟩_S ∈ P. -/
def Cond4 (ϕ : S →ₙ* T) (P : Set (Set S)) : Prop :=
  ∀ ⦃A : Set S⦄, A ∈ P → (∃ e : T, e * e = e ∧ A ⊆ ϕ ⁻¹' {e}) →
  (Subsemigroup.closure A : Set S) ∈ P

/-- `Cond1'` (down-closed) and `Cond1''` (X ∈ P) together imply `Cond1`. -/
lemma cond1_of_cond1'_and_cond1'' (ϕ : S →ₙ* T) (X : Set S) (P : Set (Set S))
    (h1' : Cond1' P) (h1'' : Cond1'' X P) : Cond1 ϕ X P :=
  fun _ ↦ h1' (fun _ hx ↦ hx.1) h1''

omit [Semigroup S] in
/-- Finite union closure under `Cond2`:
If P satisfies `Cond2` and ∅ ∈ P, then any finite union of sets in P is in P. -/
lemma finset_bUnion_mem_P (P : Set (Set S)) (h2 : Cond2 P) (h_empty : ∅ ∈ P)
    {α : Type*} (s : Finset α) (f : α → Set S) (hf : ∀ a ∈ s, f a ∈ P) :
    (⋃ a ∈ s, f a) ∈ P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h_empty]
  | insert a s' ha ih =>
    rw [Finset.set_biUnion_insert]
    exact h2 (hf a (Finset.mem_insert_self a s')) (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))


open Classical in
lemma mul_inter_preimage_eq (ϕ : S →ₙ* T) (A B : Set S) (c : T) :
    (A * B) ∩ ϕ ⁻¹' {c} = ⋃ (a : T) (b : T) (_hab : a * b = c),
      (A ∩ ϕ ⁻¹' {a}) * (B ∩ ϕ ⁻¹' {b}) := by
  ext x
  simp only [mem_inter_iff, mem_mul, mem_preimage, mem_singleton_iff, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨⟨u, hu, v, hv, rfl⟩, hx⟩
    exact ⟨ϕ u, ϕ v, by simpa [ϕ.map_mul] using hx, u, ⟨hu, rfl⟩, v, ⟨hv, rfl⟩, rfl⟩
  · rintro ⟨a, b, hab, u, ⟨hu, rfl⟩, v, ⟨hv, rfl⟩, rfl⟩
    exact ⟨⟨u, hu, v, hv, rfl⟩, by simp [ϕ.map_mul, hab]⟩

lemma closure_subset_preimage_of_idempotent (ϕ : S →ₙ* T) {A : Set S} {e : T} (he : e * e = e)
    (hA : A ⊆ ϕ ⁻¹' {e}) : (Subsemigroup.closure A : Set S) ⊆ ϕ ⁻¹' {e} := by
  intro x hx
  induction hx using Subsemigroup.closure_induction with
  | mem y hy => exact hA hy
  | mul y z _ _ ihy ihz =>
    simp only [mem_preimage, mem_singleton_iff] at ihy ihz ⊢
    simp [ϕ.map_mul, ihy, ihz, he]

open Classical in
lemma closure_inter_preimage_of_idempotent (ϕ : S →ₙ* T) {A : Set S} {e : T} (he : e * e = e)
    (hA : A ⊆ ϕ ⁻¹' {e}) (c : T) :
    (Subsemigroup.closure A : Set S) ∩ ϕ ⁻¹' {c} =
      if c = e then (Subsemigroup.closure A : Set S) else ∅ := by
  have h_sub := closure_subset_preimage_of_idempotent ϕ he hA
  ext x
  split_ifs with hc
  · simp only [hc, mem_inter_iff, mem_preimage, mem_singleton_iff, and_iff_left_iff_imp]
    exact fun hx ↦ h_sub hx
  · simp only [mem_inter_iff, mem_preimage, mem_singleton_iff,
      mem_empty_iff_false, iff_false, not_and]
    exact fun hx hxc ↦ hc (hxc.symm.trans (h_sub hx))

omit [Semigroup S] in
lemma finset_bUnion_mem_P_or_empty (P : Set (Set S)) (h2 : Cond2 P)
    {α : Type*} (s : Finset α) (f : α → Set S) (hf : ∀ a ∈ s, f a = ∅ ∨ f a ∈ P) :
    (⋃ a ∈ s, f a) = ∅ ∨ (⋃ a ∈ s, f a) ∈ P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s' ha ih =>
    rw [Finset.set_biUnion_insert]
    rcases hf a (Finset.mem_insert_self a s') with hfa | hfa
    · rcases ih (fun b hb ↦ hf b (Finset.mem_insert_of_mem hb)) with hU | hU
      · left; rw [hfa, hU, union_empty]
      · right; rw [hfa, empty_union]; exact hU
    · rcases ih (fun b hb ↦ hf b (Finset.mem_insert_of_mem hb)) with hU | hU
      · right; rw [hU, union_empty]; exact hfa
      · right; exact h2 hfa hU

/-- Restriction family `P'` of sets in `P` whose fiber slices are in `P ∪ {∅}`. -/
def restrictionFamily (ϕ : S →ₙ* T) (P : Set (Set S)) : Set (Set S) :=
  { A | A = ∅ ∨ (A ∈ P ∧ ∀ c : T, A ∩ ϕ ⁻¹' {c} = ∅ ∨ A ∩ ϕ ⁻¹' {c} ∈ P) }

lemma union_mem_restrictionFamily (ϕ : S →ₙ* T) (P : Set (Set S)) (h2 : Cond2 P)
    {A B : Set S} (hA : A ∈ restrictionFamily ϕ P) (hB : B ∈ restrictionFamily ϕ P) :
    A ∪ B ∈ restrictionFamily ϕ P := by
  rcases hA with rfl | ⟨hAP, hAc⟩
  · simpa using hB
  rcases hB with rfl | ⟨hBP, hBc⟩
  · exact Or.inr (by simpa using ⟨hAP, hAc⟩)
  right
  constructor
  · exact h2 hAP hBP
  · intro c
    rw [union_inter_distrib_right]
    rcases hAc c with hAc_emp | hAc_P
    · simpa [hAc_emp] using hBc c
    · rcases hBc c with hBc_emp | hBc_P
      · simpa [hBc_emp] using Or.inr hAc_P
      · exact Or.inr (h2 hAc_P hBc_P)

lemma finset_bUnion_mem_restrictionFamily (ϕ : S →ₙ* T) (P : Set (Set S)) (h2 : Cond2 P)
    {α : Type*} (s : Finset α) (f : α → Set S) (hf : ∀ a ∈ s, f a ∈ restrictionFamily ϕ P) :
    (⋃ a ∈ s, f a) ∈ restrictionFamily ϕ P :=
  finset_bUnion_mem_P (restrictionFamily ϕ P) (fun _ _ ↦ union_mem_restrictionFamily ϕ P h2)
    (Or.inl rfl) s f hf

open Classical in
lemma mul_mem_restrictionFamily [Finite T] (ϕ : S →ₙ* T) (P : Set (Set S))
    (h2 : Cond2 P) (h3 : Cond3 P)
    {A B : Set S} (hA : A ∈ restrictionFamily ϕ P) (hB : B ∈ restrictionFamily ϕ P) :
    A * B ∈ restrictionFamily ϕ P := by
  rcases hA with rfl | ⟨hAP, hAc⟩
  · left; rw [empty_mul]
  rcases hB with rfl | ⟨hBP, hBc⟩
  · left; rw [mul_empty]
  right
  have instFintypeT : Fintype T := Fintype.ofFinite T
  constructor
  · exact h3 hAP hBP
  · intro c
    rw [mul_inter_preimage_eq]
    have h_fin : (⋃ (a : T) (b : T) (_hab : a * b = c), (A ∩ ϕ ⁻¹' {a}) * (B ∩ ϕ ⁻¹' {b})) =
        ⋃ p ∈ (Finset.univ.filter (fun (p : T × T) ↦ p.1 * p.2 = c)),
          (A ∩ ϕ ⁻¹' {p.1}) * (B ∩ ϕ ⁻¹' {p.2}) := by
      ext x
      simp only [mem_iUnion, exists_prop, Prod.exists, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h_fin]
    apply finset_bUnion_mem_P_or_empty P h2
    intro p _
    rcases hAc p.1 with hA_emp | hA_P
    · left; rw [hA_emp, empty_mul]
    rcases hBc p.2 with hB_emp | hB_P
    · left; rw [hB_emp, mul_empty]
    · right; exact h3 hA_P hB_P

open Classical in
lemma idempotent_closure_mem_restrictionFamily (ϕ : S →ₙ* T) (P : Set (Set S))
    (h4 : Cond4 ϕ P) {A : Set S} (hA : A ∈ restrictionFamily ϕ P)
    (e : T) (he : e * e = e) :
    (Subsemigroup.closure (A ∩ ϕ ⁻¹' {e}) : Set S) ∈ restrictionFamily ϕ P := by
  rcases hA with rfl | ⟨hAP, hAc⟩
  · left; simp [Subsemigroup.closure_empty]
  rcases hAc e with he_emp | he_P
  · left; simp [he_emp, Subsemigroup.closure_empty]
  right
  have h_sub : A ∩ ϕ ⁻¹' {e} ⊆ ϕ ⁻¹' {e} := inter_subset_right
  have h_cl_P := h4 he_P ⟨e, he, h_sub⟩
  constructor
  · exact h_cl_P
  · intro c
    rw [closure_inter_preimage_of_idempotent ϕ he h_sub c]
    grind

open Classical in
lemma X_mem_restrictionFamily [Finite T] (ϕ : S →ₙ* T) (X : Set S) (P : Set (Set S))
    (h1 : Cond1 ϕ X P) (h2 : Cond2 P) :
    X ∈ restrictionFamily ϕ P := by
  have instFintypeT : Fintype T := Fintype.ofFinite T
  have h_eq : X = ⋃ a ∈ (Finset.univ : Finset T), {x ∈ X | ϕ x = a} := by ext; simp
  rw [h_eq]
  apply finset_bUnion_mem_restrictionFamily ϕ P h2
  intro a _
  right
  have haP := h1 a
  constructor
  · exact haP
  · intro c
    have h_slice : {x ∈ X | ϕ x = a} ∩ ϕ ⁻¹' {c} =
        if c = a then {x ∈ X | ϕ x = a} else ∅ := by
      split_ifs with hc
      · subst hc
        ext x
        simp (config := {contextual := true})
      · ext x; simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff,
          mem_empty_iff_false, iff_false, not_and]
        rintro ⟨-, hxa⟩ hxc
        exact hc (hxc.symm.trans hxa)
    rw [h_slice]
    grind

open Classical in
/-- Set-Family Fixed Point Theorem (Colcombet Theorem 4.2):
if `P` satisfies conditions (1)-(4), then `⟨X⟩_S ∈ P`. -/
theorem closure_mem_set_family [Finite T] [Nonempty T] (ϕ : S →ₙ* T) (X : Set S) (P : Set (Set S))
    (h1 : Cond1 ϕ X P)
    (h2 : Cond2 P)
    (h3 : Cond3 P)
    (h4 : Cond4 ϕ P) :
    (Subsemigroup.closure X : Set S) ∈ P := by
  have instFintypeT : Fintype T := Fintype.ofFinite T
  have h_Xn : ∀ n, X_seq ϕ X n ∈ restrictionFamily ϕ P := by
    intro n
    induction n with
    | zero => exact X_mem_restrictionFamily ϕ X P h1 h2
    | succ n ih =>
      dsimp [X_seq]
      apply union_mem_restrictionFamily ϕ P h2
      · apply union_mem_restrictionFamily ϕ P h2 ih
        exact mul_mem_restrictionFamily ϕ P h2 h3 ih ih
      · have h_reindex : (⋃ (e : T) (he : e * e = e),
            (Subsemigroup.closure (X_seq ϕ X n ∩ ϕ ⁻¹' {e}) : Set S)) =
            ⋃ e ∈ (Finset.univ.filter (fun (e : T) ↦ e * e = e)),
              (Subsemigroup.closure (X_seq ϕ X n ∩ ϕ ⁻¹' {e}) : Set S) := by ext; simp
        rw [h_reindex]
        apply finset_bUnion_mem_restrictionFamily ϕ P h2
        intro e he
        exact idempotent_closure_mem_restrictionFamily ϕ P h4 ih e (Finset.mem_filter.mp he).2
  have h_cl_res : (Subsemigroup.closure X : Set S) ∈ restrictionFamily ϕ P := by
    rw [closure_eq_X_seq ϕ X]
    exact h_Xn (3 * nS T - 1)
  rcases h_cl_res with h_cl_emp | ⟨h_cl_P, _⟩
  · have h_X_emp : X = ∅ := by
      have h_sub : X ⊆ Subsemigroup.closure X := Subsemigroup.subset_closure
      rw [h_cl_emp] at h_sub
      exact subset_empty_iff.mp h_sub
    have h_empty_P : ∅ ∈ P := by
      have h1_any := h1 (Classical.arbitrary T)
      have h_set_emp : {x ∈ X | ϕ x = Classical.arbitrary T} = ∅ := by
        rw [h_X_emp]
        exact empty_inter _
      rwa [h_set_emp] at h1_any
    rwa [h_cl_emp]
  · exact h_cl_P

/-- Set-Family Fixed Point Theorem with hereditary condition:
if `P` satisfies conditions (1')-(4), then `⟨X⟩_S ∈ P`. -/
theorem closure_mem_set_family_of_cond1' [Finite T] [Nonempty T]
    (ϕ : S →ₙ* T) (X : Set S) (P : Set (Set S))
    (_h1' : Cond1' P) (h1 : Cond1 ϕ X P) (h2 : Cond2 P) (h3 : Cond3 P) (h4 : Cond4 ϕ P) :
    (Subsemigroup.closure X : Set S) ∈ P :=
  closure_mem_set_family ϕ X P h1 h2 h3 h4

end SetFamilyFixedPoint

section BrownLemmaTheorem

/-- The fiber subsemigroup of an idempotent e ∈ T under a morphism `f`. -/
def fiberSubsemigroup (f : S →ₙ* T) (e : T) (he : e * e = e) : Subsemigroup S where
  carrier := f ⁻¹' {e}
  mul_mem' {x y} (hx : f x = e) (hy : f y = e) :=
    (f.map_mul x y).trans ((congrArg₂ (· * ·) hx hy).trans he)

/-- Brown's Lemma: if `T` and all idempotent fiber subsemigroups are locally finite,
then `S` is locally finite. -/
theorem brown_lemma (f : S →ₙ* T)
    (hT : IsLocallyFinite T)
    (h_fibers : ∀ (e : T) (he : e * e = e), IsLocallyFinite (fiberSubsemigroup f e he)) :
    IsLocallyFinite S := by
  intro X hX
  obtain rfl | hX_ne := X.eq_empty_or_nonempty
  · simp [Subsemigroup.closure_empty, finite_empty]
  obtain ⟨x0, hx0⟩ := hX_ne
  let S' := Subsemigroup.closure X
  let T' := Subsemigroup.closure (f '' X)
  have instFintypeT' : Fintype T' := (hT (f '' X) (hX.image f)).fintype
  have instNonemptyT' : Nonempty T' :=
    ⟨⟨f x0, Subsemigroup.subset_closure (mem_image_of_mem f hx0)⟩⟩
  have instNonemptyFinT' : Nonempty (Fin (nS T')) := instNonemptyFin_nS
  let f' : S' →ₙ* T' := {
    toFun := fun ⟨x, hx⟩ ↦ ⟨f x, by
      induction hx using Subsemigroup.closure_induction with
      | mem a ha => exact Subsemigroup.subset_closure (mem_image_of_mem f ha)
      | mul a b _ _ iha ihb => exact f.map_mul a b ▸ Subsemigroup.mul_mem _ iha ihb⟩
    map_mul' := fun x y ↦ Subtype.ext (f.map_mul x.1 y.1)
  }
  let P : Set (Set S') := { A | A.Finite }
  have h1' : Cond1' P := fun A B hAB hB ↦ hB.subset hAB
  let X_S' : Set S' := range (fun (x : X) ↦ ⟨x.1, Subsemigroup.subset_closure x.2⟩)
  have h1'' : Cond1'' X_S' P := by
    have instFintypeX : Fintype X := hX.fintype
    exact finite_range _
  have h1 : Cond1 f' X_S' P := cond1_of_cond1'_and_cond1'' f' _ P h1' h1''
  have h2 : Cond2 P := fun A B hA hB ↦ hA.union hB
  have h3 : Cond3 P := fun A B hA hB ↦ hA.mul hB
  have h4 : Cond4 f' P := by
    intro A hA ⟨e', he', hAe'⟩
    have h_idem : e'.1 * e'.1 = e'.1 := Subtype.ext_iff.mp he'
    have instFiniteA : Finite A := hA.to_subtype
    let A_fiber : Set (fiberSubsemigroup f e'.1 h_idem) :=
      range (fun (x : A) ↦ ⟨x.1.1, Subtype.ext_iff.mp (hAe' x.2)⟩)
    have hA_fiber_fin : A_fiber.Finite := finite_range _
    have h_closure_fin := h_fibers e'.1 h_idem A_fiber hA_fiber_fin
    have h_sub_fiber : ∀ x ∈ Subsemigroup.closure A, f x.1 = e'.1 := by
      intro x hx
      induction hx using Subsemigroup.closure_induction with
      | mem y hy => exact Subtype.ext_iff.mp (hAe' hy)
      | mul y z _ _ ihy ihz =>
        rw [show f (y * z).1 = f y.1 * f z.1 from f.map_mul _ _, ihy, ihz, h_idem]
    let g : ↥(Subsemigroup.closure A) → ↥(Subsemigroup.closure A_fiber) := fun ⟨x, hx⟩ ↦
      ⟨⟨x.1, h_sub_fiber x hx⟩, by
        induction hx using Subsemigroup.closure_induction with
        | mem y hy => exact Subsemigroup.subset_closure ⟨⟨y, hy⟩, rfl⟩
        | mul y z _ _ ihy ihz => exact Subsemigroup.mul_mem _ ihy ihz⟩
    have g_inj : Function.Injective g :=
      fun ⟨x1, _⟩ ⟨x2, _⟩ h ↦ Subtype.ext (Subtype.ext (congrArg (fun a ↦ a.1.1) h))
    have instFiniteClosure : Finite ↥(Subsemigroup.closure A) := by
      have instFinClosureFiber : Finite ↥(Subsemigroup.closure A_fiber) :=
        h_closure_fin.to_subtype
      exact Finite.of_injective g g_inj
    exact Set.toFinite _
  have h_closure_P := closure_mem_set_family f' _ P h1 h2 h3 h4
  have h_univ : (Subsemigroup.closure X_S' : Set S') = Set.univ := by
    ext ⟨s, hs⟩
    simp only [Set.mem_univ, iff_true]
    induction hs using Subsemigroup.closure_induction with
    | mem x hx => exact Subsemigroup.subset_closure ⟨⟨x, hx⟩, rfl⟩
    | mul x y _ _ ihx ihy => exact Subsemigroup.mul_mem _ ihx ihy
  have instFiniteS' : Finite S' := Set.finite_univ_iff.mp (h_univ ▸ h_closure_P)
  exact Set.toFinite _

end BrownLemmaTheorem

end BrownLemma

export BrownLemma (brown_lemma)
