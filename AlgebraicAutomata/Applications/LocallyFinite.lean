module

/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Subsemigroup.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Order.CompleteLattice.Finset
public import AlgebraicAutomata.FactorizationForest.Tree
public import AlgebraicAutomata.ForMathlib.Data.List.SemigroupProd

@[expose] public section

/-!
# Locally Finite Semigroups and Brown's Lemma

Locally finite semigroups, Brown's Lemma, and Colcombet's Set-Family Fixed Point Theorem.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

/-- A semigroup `S` is locally finite if every finite subset generates a finite subsemigroup. -/
def IsLocallyFinite (S : Type*) [Semigroup S] : Prop :=
  ∀ (X : Set S), X.Finite → (Subsemigroup.closure X : Set S).Finite

namespace BrownLemma

open Set RamseySplit FactorizationTree
open scoped Pointwise

variable {S T : Type*} [Semigroup S] [Semigroup T]

section ClosureSequence

/-- Inductive sequence of subsets approximating the subsemigroup closure. -/
def closureSeq (ϕ : S →ₙ* T) (X : Set S) : ℕ → Set S
  | 0 => X
  | n + 1 =>
    let Xn := closureSeq ϕ X n
    Xn ∪ (Xn * Xn) ∪ ⋃ (e : T) (_he : e * e = e), (Subsemigroup.closure (Xn ∩ ϕ ⁻¹' {e}) : Set S)

/-- Monotonicity of the closure sequence with respect to the index. -/
lemma closureSeq_mono (ϕ : S →ₙ* T) (X : Set S) {m n : ℕ} (h : m ≤ n) :
    closureSeq ϕ X m ⊆ closureSeq ϕ X n :=
  Nat.le.recOn h subset_rfl (fun _ ih ↦ ih.trans (subset_union_left.trans subset_union_left))

/-- Every stage of the closure sequence is contained in the generated subsemigroup closure. -/
lemma closureSeq_subset_closure (ϕ : S →ₙ* T) (X : Set S) (n : ℕ) :
    closureSeq ϕ X n ⊆ Subsemigroup.closure X := by
  induction n with
  | zero => exact Subsemigroup.subset_closure
  | succ n ih =>
    dsimp [closureSeq]
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
/-- The yield of a list of Ramsey factorization trees is non-empty if the list is non-empty. -/
lemma listTree_value_ne_nil (cs : List (FactorizationTree S)) (eval : List S → T)
    (hcs : FactorizationTree.listIsRamsey eval cs) (hne : cs ≠ []) :
    FactorizationTree.listValue cs ≠ [] := by
  rcases cs with _ | ⟨c, rest⟩
  · contradiction
  · simp [FactorizationTree.listValue_cons, FactorizationTree.tree_value_ne_nil c hcs.1]

mutual
  /-- The evaluation product of the yield of a
  Ramsey tree is contained in the closure sequence at its height. -/
  lemma tree_prod_in_closureSeq (ϕ : S →ₙ* T) (X : Set S)
      (eval : List S → T)
      (h_eval : ∀ w hw, eval w = ϕ (listProdNE w hw))
      (t : FactorizationTree S) (ht : t.IsRamsey eval)
      (hX : ∀ x ∈ t.value, x ∈ X)
      (ht_ne : t.value ≠ []) :
      listProdNE t.value ht_ne ∈ closureSeq ϕ X t.height := by
    cases t with
    | leaf a =>
      have h_prod : listProdNE (FactorizationTree.leaf a).value ht_ne = a := by
        rw [listProdNE_eq _ [a] _ (by simp) (FactorizationTree.value_leaf a)]
        rfl
      have ha_X : a ∈ X := hX a (by grind [FactorizationTree.value_leaf])
      grind [FactorizationTree.height_leaf, closureSeq]
    | binary l r =>
      rw [FactorizationTree.isRamsey_binary] at ht
      obtain ⟨ht_l, ht_r⟩ := ht
      have hl_ne := FactorizationTree.tree_value_ne_nil l ht_l
      have hr_ne := FactorizationTree.tree_value_ne_nil r ht_r
      obtain ⟨hX_l, hX_r⟩ : (∀ x ∈ l.value, x ∈ X) ∧ (∀ x ∈ r.value, x ∈ X) := by
        grind [FactorizationTree.value_binary]
      have ih_l := closureSeq_mono ϕ X (le_max_left l.height r.height)
        (tree_prod_in_closureSeq ϕ X eval h_eval l ht_l hX_l hl_ne)
      have ih_r := closureSeq_mono ϕ X (le_max_right l.height r.height)
        (tree_prod_in_closureSeq ϕ X eval h_eval r ht_r hX_r hr_ne)
      have h_prod : listProdNE (FactorizationTree.binary l r).value ht_ne =
          listProdNE l.value hl_ne * listProdNE r.value hr_ne := by
        rw [listProdNE_eq (FactorizationTree.binary l r).value (l.value ++ r.value) ht_ne
          (by simp [hl_ne, hr_ne]) (FactorizationTree.value_binary l r)]
        exact listProdNE_concat l.value r.value hl_ne hr_ne
      rw [h_prod, FactorizationTree.height_binary, add_comm 1, closureSeq]
      exact Or.inl (Or.inr ⟨_, ih_l, _, ih_r, rfl⟩)
    | idempotent cs =>
      rw [FactorizationTree.isRamsey_idempotent] at ht
      obtain ⟨hlen, hcs_ramsey, e, he_idem, he_eval⟩ := ht
      have hcs_ne : cs ≠ [] := by grind
      have hX_cs : ∀ x ∈ FactorizationTree.listValue cs, x ∈ X := fun x hx ↦ by
        grind [FactorizationTree.value_idempotent]
      have ih := listTree_prod_in_closure ϕ X eval h_eval cs hcs_ramsey hcs_ne e he_eval hX_cs
      have h_prod : listProdNE (FactorizationTree.idempotent cs).value ht_ne =
          listProdNE (FactorizationTree.listValue cs)
            (listTree_value_ne_nil cs eval hcs_ramsey hcs_ne) :=
        listProdNE_eq _ _ ht_ne (listTree_value_ne_nil cs eval hcs_ramsey hcs_ne)
          (FactorizationTree.value_idempotent cs)
      rw [FactorizationTree.height_idempotent, add_comm 1, closureSeq, h_prod]
      exact Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he_idem, ih⟩⟩)

  /-- Product of the yields of children in an idempotent node
  belongs to the corresponding idempotent fiber closure. -/
  lemma listTree_prod_in_closure (ϕ : S →ₙ* T) (X : Set S)
      (eval : List S → T)
      (h_eval : ∀ w hw, eval w = ϕ (listProdNE w hw))
      (cs : List (FactorizationTree S)) (hcs : FactorizationTree.listIsRamsey eval cs)
      (hne : cs ≠ []) (e : T)
      (he_eval : ∀ c ∈ cs, eval c.value = e)
      (hX : ∀ x ∈ FactorizationTree.listValue cs, x ∈ X) :
      listProdNE (FactorizationTree.listValue cs) (listTree_value_ne_nil cs eval hcs hne) ∈
        (Subsemigroup.closure
          (closureSeq ϕ X (FactorizationTree.listHeight cs) ∩ ϕ ⁻¹' {e}) : Set S) := by
    cases cs with
    | nil => contradiction
    | cons c rest =>
      have hc_ne := FactorizationTree.tree_value_ne_nil c hcs.1
      have hX_c : ∀ x ∈ c.value, x ∈ X := fun x hx ↦ hX x (List.mem_append_left _ hx)
      have ih_c := closureSeq_mono ϕ X (le_max_left c.height (FactorizationTree.listHeight rest))
        (tree_prod_in_closureSeq ϕ X eval h_eval c hcs.1 hX_c hc_ne)
      have hc_phi : ϕ (listProdNE c.value hc_ne) = e := by
        have h_eval_c := h_eval c.value hc_ne
        exact (he_eval c (by simp)).symm ▸ h_eval_c.symm
      have hc_in : listProdNE c.value hc_ne ∈
          Subsemigroup.closure
            (closureSeq ϕ X (FactorizationTree.listHeight (c :: rest)) ∩ ϕ ⁻¹' {e}) :=
        Subsemigroup.subset_closure ⟨ih_c, hc_phi⟩
      by_cases hrest : rest = []
      · subst hrest
        rw [listProdNE_eq _ _ _ hc_ne (by simp [FactorizationTree.listValue])]
        exact hc_in
      · have hrest_val_ne := listTree_value_ne_nil rest eval hcs.2 hrest
        have hX_rest : ∀ x ∈ FactorizationTree.listValue rest, x ∈ X :=
          fun x hx ↦ hX x (List.mem_append_right _ hx)
        have ih_rest := listTree_prod_in_closure ϕ X eval h_eval rest hcs.2 hrest e
          (fun t ht ↦ he_eval t (by simp [ht])) hX_rest
        have h_sub :
            (Subsemigroup.closure (closureSeq ϕ X (FactorizationTree.listHeight rest) ∩ ϕ ⁻¹' {e}) :
              Set S) ⊆
            Subsemigroup.closure
              (closureSeq ϕ X (FactorizationTree.listHeight (c :: rest)) ∩ ϕ ⁻¹' {e}) := by
          simp only [SetLike.coe_subset_coe, Subsemigroup.closure_le]
          exact fun x hx ↦ Subsemigroup.subset_closure
            ⟨closureSeq_mono ϕ X (le_max_right _ _) hx.1, hx.2⟩
        have h_prod :
            listProdNE (FactorizationTree.listValue (c :: rest))
              (listTree_value_ne_nil (c :: rest) eval hcs hne) =
            listProdNE c.value hc_ne *
              listProdNE (FactorizationTree.listValue rest) hrest_val_ne := by
          rw [listProdNE_eq (FactorizationTree.listValue (c :: rest))
            (c.value ++ FactorizationTree.listValue rest) _
            (by simp [hc_ne, hrest_val_ne]) (FactorizationTree.listValue_cons c rest)]
          exact listProdNE_concat c.value (FactorizationTree.listValue rest) hc_ne hrest_val_ne
        exact h_prod ▸ Subsemigroup.mul_mem _ hc_in (h_sub ih_rest)
end

end TreeLemmas

section AlgebraicPresentation

/-- The subsemigroup closure stabilizes and equals the closure sequence at index `3 * nS T - 1`. -/
theorem closure_eq_closureSeq [Fintype T] [Nonempty T] (ϕ : S →ₙ* T) (X : Set S) :
    (Subsemigroup.closure X : Set S) = closureSeq ϕ X (3 * nS T - 1) := by
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
    have h_in_height := closureSeq_mono ϕ X ht_height
      (tree_prod_in_closureSeq ϕ X eval_T (fun w hw ↦ dite_eq_right hw) t ht_ramsey ht_X ht_ne)
    exact listProdNE_eq t.value u ht_ne hu ht_val ▸ h_in_height
  · exact fun hs ↦ closureSeq_subset_closure ϕ X (3 * nS T - 1) hs

end AlgebraicPresentation

section SetFamilyFixedPoint

/-- Every fiber slice `{x ∈ X | ϕ(x) = a}` belongs to the family `P`. -/
def FiberSlicesInFamily (ϕ : S →ₙ* T) (X : Set S) (P : Set (Set S)) : Prop :=
  ∀ a : T, {x ∈ X | ϕ x = a} ∈ P

/-- A family of sets is down-closed under subset inclusion. -/
def IsDownClosed (P : Set (Set S)) : Prop :=
  ∀ ⦃A B : Set S⦄, A ⊆ B → B ∈ P → A ∈ P

/-- The base generating set `X` belongs to the family `P`. -/
def BaseSetInFamily (X : Set S) (P : Set (Set S)) : Prop :=
  X ∈ P

/-- A family of sets is closed under binary unions. -/
def IsUnionClosed (P : Set (Set S)) : Prop :=
  ∀ ⦃A B : Set S⦄, A ∈ P → B ∈ P → A ∪ B ∈ P

/-- A family of sets is closed under pointwise set multiplication. -/
def IsMulClosed (P : Set (Set S)) : Prop :=
  ∀ ⦃A B : Set S⦄, A ∈ P → B ∈ P → A * B ∈ P

/-- A family of sets is closed under subsemigroup closures of idempotent fiber subsets. -/
def IsIdempotentClosureClosed (ϕ : S →ₙ* T) (P : Set (Set S)) : Prop :=
  ∀ ⦃A : Set S⦄, A ∈ P → (∃ e : T, e * e = e ∧ A ⊆ ϕ ⁻¹' {e}) →
    (Subsemigroup.closure A : Set S) ∈ P

/-- A down-closed family containing `X` contains all fiber slices of `X`. -/
lemma fiberSlicesInFamily_of_isDownClosed (ϕ : S →ₙ* T) (X : Set S) (P : Set (Set S))
    (h_down : IsDownClosed P) (hX : BaseSetInFamily X P) : FiberSlicesInFamily ϕ X P :=
  fun _ ↦ h_down (fun _ hx ↦ hx.1) hX

omit [Semigroup S] in
/-- If `P` is closed under binary unions and contains `∅`,
any finite union of sets in `P` belongs to `P`. -/
lemma finset_bUnion_mem_of_isUnionClosed (P : Set (Set S)) (hu : IsUnionClosed P) (he : ∅ ∈ P)
    {α : Type*} (s : Finset α) (f : α → Set S) (hf : ∀ a ∈ s, f a ∈ P) :
    (⋃ a ∈ s, f a) ∈ P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [he]
  | insert a s' ha ih =>
    rw [Finset.set_biUnion_insert]
    exact hu (hf a (Finset.mem_insert_self a s'))
      (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))

open Classical in
/-- The fiber slice of a pointwise product decomposes into a union of products of fiber slices. -/
lemma mul_inter_preimage_eq (ϕ : S →ₙ* T) (A B : Set S) (c : T) :
    (A * B) ∩ ϕ ⁻¹' {c} = ⋃ (a : T) (b : T) (_hab : a * b = c),
      (A ∩ ϕ ⁻¹' {a}) * (B ∩ ϕ ⁻¹' {b}) := by
  ext x
  simp only [mem_inter_iff, mem_mul, mem_preimage, mem_singleton_iff, mem_iUnion, exists_prop]
  grind

/-- The subsemigroup closure of a subset of an idempotent fiber remains within that fiber. -/
lemma closure_subset_preimage_of_idempotent (ϕ : S →ₙ* T) {A : Set S} {e : T} (he : e * e = e)
    (hA : A ⊆ ϕ ⁻¹' {e}) : (Subsemigroup.closure A : Set S) ⊆ ϕ ⁻¹' {e} := by
  intro x hx
  induction hx using Subsemigroup.closure_induction with
  | mem y hy => exact hA hy
  | mul y z _ _ ihy ihz => grind

open Classical in
/-- The intersection of an idempotent fiber closure with
another fiber is either the whole closure or empty. -/
lemma closure_inter_preimage_of_idempotent (ϕ : S →ₙ* T) {A : Set S} {e : T} (he : e * e = e)
    (hA : A ⊆ ϕ ⁻¹' {e}) (c : T) :
    (Subsemigroup.closure A : Set S) ∩ ϕ ⁻¹' {c} =
      if c = e then (Subsemigroup.closure A : Set S) else ∅ := by
  grind [closure_subset_preimage_of_idempotent ϕ he hA]

omit [Semigroup S] in
/-- A finite union of elements from `P ∪ {∅}` is either empty or in `P` when `P` is union-closed. -/
lemma finset_bUnion_mem_or_empty (P : Set (Set S)) (h_union : IsUnionClosed P)
    {α : Type*} (s : Finset α) (f : α → Set S) (hf : ∀ a ∈ s, f a = ∅ ∨ f a ∈ P) :
    (⋃ a ∈ s, f a) = ∅ ∨ (⋃ a ∈ s, f a) ∈ P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s' ha ih =>
    rw [Finset.set_biUnion_insert]
    rcases hf a (Finset.mem_insert_self a s') with hfa | hfa
    · rcases ih (fun b hb ↦ hf b (Finset.mem_insert_of_mem hb)) with hU | hU
        <;> simp [hfa, hU]
    · rcases ih (fun b hb ↦ hf b (Finset.mem_insert_of_mem hb)) with hU | hU
      · right
        rw [hU, union_empty]
        exact hfa
      · right
        exact h_union hfa hU

/-- Restriction family `P'` of sets in `P` whose fiber slices are in `P ∪ {∅}`. -/
def restrictionFamily (ϕ : S →ₙ* T) (P : Set (Set S)) : Set (Set S) :=
  { A | A = ∅ ∨ (A ∈ P ∧ ∀ c : T, A ∩ ϕ ⁻¹' {c} = ∅ ∨ A ∩ ϕ ⁻¹' {c} ∈ P) }

/-- The restriction family is closed under binary unions. -/
lemma union_mem_restrictionFamily (ϕ : S →ₙ* T) (P : Set (Set S)) (h_union : IsUnionClosed P)
    {A B : Set S} (hA : A ∈ restrictionFamily ϕ P) (hB : B ∈ restrictionFamily ϕ P) :
    A ∪ B ∈ restrictionFamily ϕ P := by
  rcases hA with rfl | ⟨hAP, hAc⟩
  · simpa using hB
  rcases hB with rfl | ⟨hBP, hBc⟩
  · exact Or.inr (by simpa using ⟨hAP, hAc⟩)
  right
  constructor
  · exact h_union hAP hBP
  · intro c
    rw [union_inter_distrib_right]
    rcases hAc c with hAc_emp | hAc_P
    · simpa [hAc_emp] using hBc c
    · rcases hBc c with hBc_emp | hBc_P
      · simpa [hBc_emp] using Or.inr hAc_P
      · exact Or.inr (h_union hAc_P hBc_P)

/-- The restriction family is closed under finite unions. -/
lemma finset_bUnion_mem_restrictionFamily (ϕ : S →ₙ* T) (P : Set (Set S)) (hu : IsUnionClosed P)
    {α : Type*} (s : Finset α) (f : α → Set S) (hf : ∀ a ∈ s, f a ∈ restrictionFamily ϕ P) :
    (⋃ a ∈ s, f a) ∈ restrictionFamily ϕ P :=
  finset_bUnion_mem_of_isUnionClosed (restrictionFamily ϕ P)
    (fun _ _ ↦ union_mem_restrictionFamily ϕ P hu)
    (Or.inl rfl) s f hf

open Classical in
/-- The restriction family is closed under pointwise set multiplication. -/
lemma mul_mem_restrictionFamily [Finite T] (ϕ : S →ₙ* T) (P : Set (Set S))
    (h_union : IsUnionClosed P) (h_mul : IsMulClosed P)
    {A B : Set S} (hA : A ∈ restrictionFamily ϕ P) (hB : B ∈ restrictionFamily ϕ P) :
    A * B ∈ restrictionFamily ϕ P := by
  rcases hA with rfl | ⟨hAP, hAc⟩
  · left
    rw [empty_mul]
  rcases hB with rfl | ⟨hBP, hBc⟩
  · left
    rw [mul_empty]
  right
  have instFintypeT : Fintype T := Fintype.ofFinite T
  constructor
  · exact h_mul hAP hBP
  · intro c
    rw [mul_inter_preimage_eq]
    have h_fin : (⋃ (a : T) (b : T) (_hab : a * b = c), (A ∩ ϕ ⁻¹' {a}) * (B ∩ ϕ ⁻¹' {b})) =
        ⋃ p ∈ (Finset.univ.filter (fun (p : T × T) ↦ p.1 * p.2 = c)),
          (A ∩ ϕ ⁻¹' {p.1}) * (B ∩ ϕ ⁻¹' {p.2}) := by
      ext x
      simp only [mem_iUnion, exists_prop, Prod.exists, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h_fin]
    apply finset_bUnion_mem_or_empty P h_union
    intro p _
    rcases hAc p.1 with hA_emp | hA_P
    · left
      rw [hA_emp, empty_mul]
    rcases hBc p.2 with hB_emp | hB_P
    · left
      rw [hB_emp, mul_empty]
    · right
      exact h_mul hA_P hB_P

open Classical in
/-- The restriction family is closed under subsemigroup closures of idempotent fiber subsets. -/
lemma idempotent_closure_mem_restrictionFamily (ϕ : S →ₙ* T) (P : Set (Set S))
    (h_idem_cl : IsIdempotentClosureClosed ϕ P) {A : Set S} (hA : A ∈ restrictionFamily ϕ P)
    (e : T) (he : e * e = e) :
    (Subsemigroup.closure (A ∩ ϕ ⁻¹' {e}) : Set S) ∈ restrictionFamily ϕ P := by
  rcases hA with rfl | ⟨hAP, hAc⟩
  · left
    simp [Subsemigroup.closure_empty]
  rcases hAc e with he_emp | he_P
  · left
    simp [he_emp, Subsemigroup.closure_empty]
  right
  have h_sub : A ∩ ϕ ⁻¹' {e} ⊆ ϕ ⁻¹' {e} := inter_subset_right
  have h_cl_P := h_idem_cl he_P ⟨e, he, h_sub⟩
  constructor
  · exact h_cl_P
  · intro c
    rw [closure_inter_preimage_of_idempotent ϕ he h_sub c]
    split_ifs <;> [exact Or.inr h_cl_P; exact Or.inl rfl]

open Classical in
/-- The base generating set `X` belongs to the restriction family. -/
lemma baseSet_mem_restrictionFamily [Finite T] (ϕ : S →ₙ* T) (X : Set S) (P : Set (Set S))
    (h_fibers : FiberSlicesInFamily ϕ X P) (h_union : IsUnionClosed P) :
    X ∈ restrictionFamily ϕ P := by
  have instFintypeT : Fintype T := Fintype.ofFinite T
  have h_eq : X = ⋃ a ∈ (Finset.univ : Finset T), {x ∈ X | ϕ x = a} := by
    ext
    simp
  rw [h_eq]
  apply finset_bUnion_mem_restrictionFamily ϕ P h_union
  intro a _
  right
  have haP := h_fibers a
  constructor
  · exact haP
  · intro c
    have h_slice : {x ∈ X | ϕ x = a} ∩ ϕ ⁻¹' {c} =
        if c = a then {x ∈ X | ϕ x = a} else ∅ := by
      split_ifs with hc
      · subst hc
        ext x
        simp (config := {contextual := true})
      · ext x
        simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff,
          mem_empty_iff_false, iff_false, not_and]
        rintro ⟨-, hxa⟩ hxc
        exact hc (hxc.symm.trans hxa)
    rw [h_slice]
    split_ifs <;> [exact Or.inr haP; exact Or.inl rfl]

open Classical in
/-- If `P` satisfies the closure conditions, the subsemigroup closure `⟨X⟩_S` belongs to `P`. -/
theorem closure_mem_set_family [Finite T] [Nonempty T] (ϕ : S →ₙ* T) (X : Set S) (P : Set (Set S))
    (h_fibers : FiberSlicesInFamily ϕ X P)
    (h_union : IsUnionClosed P)
    (h_mul : IsMulClosed P)
    (h_idem_cl : IsIdempotentClosureClosed ϕ P) :
    (Subsemigroup.closure X : Set S) ∈ P := by
  have instFintypeT : Fintype T := Fintype.ofFinite T
  have h_Xn : ∀ n, closureSeq ϕ X n ∈ restrictionFamily ϕ P := by
    intro n
    induction n with
    | zero => exact baseSet_mem_restrictionFamily ϕ X P h_fibers h_union
    | succ n ih =>
      dsimp [closureSeq]
      apply union_mem_restrictionFamily ϕ P h_union
      · apply union_mem_restrictionFamily ϕ P h_union ih
        exact mul_mem_restrictionFamily ϕ P h_union h_mul ih ih
      · have h_reindex : (⋃ (e : T) (he : e * e = e),
            (Subsemigroup.closure (closureSeq ϕ X n ∩ ϕ ⁻¹' {e}) : Set S)) =
            ⋃ e ∈ (Finset.univ.filter (fun (e : T) ↦ e * e = e)),
              (Subsemigroup.closure (closureSeq ϕ X n ∩ ϕ ⁻¹' {e}) : Set S) := by
          ext
          simp
        rw [h_reindex]
        apply finset_bUnion_mem_restrictionFamily ϕ P h_union
        intro e he
        exact idempotent_closure_mem_restrictionFamily
          ϕ P h_idem_cl ih e (Finset.mem_filter.mp he).2
  have h_cl_res : (Subsemigroup.closure X : Set S) ∈ restrictionFamily ϕ P := by
    exact closure_eq_closureSeq ϕ X ▸ h_Xn (3 * nS T - 1)
  rcases h_cl_res with h_cl_emp | ⟨h_cl_P, _⟩
  · have h_X_emp : X = ∅ := by
      have h_sub : X ⊆ Subsemigroup.closure X := Subsemigroup.subset_closure
      rw [h_cl_emp] at h_sub
      exact subset_empty_iff.mp h_sub
    have h_empty_P : ∅ ∈ P := by
      have h_any := h_fibers (Classical.arbitrary T)
      have h_set_emp : {x ∈ X | ϕ x = Classical.arbitrary T} = ∅ := by
        rw [h_X_emp]
        exact empty_inter _
      rwa [h_set_emp] at h_any
    rwa [h_cl_emp]
  · exact h_cl_P

/-- If `P` is down-closed and satisfies the closure conditions,
the subsemigroup closure belongs to `P`. -/
theorem closure_mem_set_family_of_isDownClosed [Finite T] [Nonempty T]
    (ϕ : S →ₙ* T) (X : Set S) (P : Set (Set S))
    (_h_down : IsDownClosed P) (h_fibers : FiberSlicesInFamily ϕ X P)
    (h_union : IsUnionClosed P) (h_mul : IsMulClosed P)
    (h_idem_cl : IsIdempotentClosureClosed ϕ P) :
    (Subsemigroup.closure X : Set S) ∈ P :=
  closure_mem_set_family ϕ X P h_fibers h_union h_mul h_idem_cl

end SetFamilyFixedPoint

section LocallyFiniteFibers

/-- The fiber subsemigroup associated with an idempotent `e ∈ T` under a homomorphism `f`. -/
def fiberSubsemigroup (f : S →ₙ* T) (e : T) (he : e * e = e) : Subsemigroup S where
  carrier := f ⁻¹' {e}
  mul_mem' {x y} (hx : f x = e) (hy : f y = e) :=
    (f.map_mul x y).trans ((congrArg₂ (· * ·) hx hy).trans he)

/-- If the codomain and all idempotent fiber subsemigroups are locally finite,
then the domain is locally finite. -/
theorem isLocallyFinite_of_locallyFinite_fibers (f : S →ₙ* T)
    (hT : IsLocallyFinite T)
    (h_fibers : ∀ (e : T) (he : e * e = e), IsLocallyFinite (fiberSubsemigroup f e he)) :
    IsLocallyFinite S := by
  intro X hX
  obtain rfl | hX_ne := X.eq_empty_or_nonempty
  · simp [Subsemigroup.closure_empty, finite_empty]
  obtain ⟨x_wit, hx_wit⟩ := hX_ne
  let S' := Subsemigroup.closure X
  let T' := Subsemigroup.closure (f '' X)
  have instFintypeT' : Fintype T' := (hT (f '' X) (hX.image f)).fintype
  have instNonemptyT' : Nonempty T' :=
    ⟨⟨f x_wit, Subsemigroup.subset_closure (mem_image_of_mem f hx_wit)⟩⟩
  have instNonemptyFinT' : Nonempty (Fin (nS T')) := instNonemptyFin_nS
  let f' : S' →ₙ* T' := {
    toFun := fun ⟨x, hx⟩ ↦ ⟨f x, by
      induction hx using Subsemigroup.closure_induction with
      | mem a ha => exact Subsemigroup.subset_closure (mem_image_of_mem f ha)
      | mul a b _ _ iha ihb => exact f.map_mul a b ▸ Subsemigroup.mul_mem _ iha ihb⟩
    map_mul' := fun x y ↦ Subtype.ext (f.map_mul x.1 y.1)
  }
  let P : Set (Set S') := { A | A.Finite }
  have h_down : IsDownClosed P := fun A B hAB hB ↦ hB.subset hAB
  let X_S' : Set S' := range (fun (x : X) ↦ ⟨x.1, Subsemigroup.subset_closure x.2⟩)
  have h_base : BaseSetInFamily X_S' P := by
    have instFintypeX : Fintype X := hX.fintype
    exact finite_range _
  have h_fibers_in_P : FiberSlicesInFamily f' X_S' P :=
    fiberSlicesInFamily_of_isDownClosed f' _ P h_down h_base
  have h_union : IsUnionClosed P := fun A B hA hB ↦ hA.union hB
  have h_mul : IsMulClosed P := fun A B hA hB ↦ hA.mul hB
  have h_idem_cl : IsIdempotentClosureClosed f' P := by
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
      fun ⟨x_fst, _⟩ ⟨x_snd, _⟩ h ↦ Subtype.ext (Subtype.ext (congrArg (fun a ↦ a.1.1) h))
    have instFiniteClosure : Finite ↥(Subsemigroup.closure A) := by
      have instFinClosureFiber : Finite ↥(Subsemigroup.closure A_fiber) :=
        h_closure_fin.to_subtype
      exact Finite.of_injective g g_inj
    exact Set.toFinite _
  have h_closure_P := closure_mem_set_family f' _ P h_fibers_in_P h_union h_mul h_idem_cl
  have h_univ : (Subsemigroup.closure X_S' : Set S') = Set.univ := by
    ext ⟨s, hs⟩
    simp only [Set.mem_univ, iff_true]
    induction hs using Subsemigroup.closure_induction with
    | mem x hx => exact Subsemigroup.subset_closure ⟨⟨x, hx⟩, rfl⟩
    | mul x y _ _ ihx ihy => exact Subsemigroup.mul_mem _ ihx ihy
  have instFiniteS' : Finite S' := Set.finite_univ_iff.mp (h_univ ▸ h_closure_P)
  exact Set.toFinite _

end LocallyFiniteFibers

end BrownLemma
