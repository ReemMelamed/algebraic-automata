/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import AlgebraicAutomata.FactorizationForest.Basic
import AlgebraicAutomata.FactorizationForest.Combine
import AlgebraicAutomata.FactorizationForest.Split
import AlgebraicAutomata.Mathlib.Data.List.SemigroupProd

/-!
# Simon's Factorization Forest Theorem (Tree Version)

Formalization of the tree version of Simon's Factorization Forest Theorem,
constructing a Ramsey factorization tree of height at most `3 * nS S - 1` from
a Ramsey split (`simon_word`).

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

open RamseySplit

/-- An inductive type representing a factorization tree over an alphabet `A`. -/
inductive FactorizationTree (A : Type*) where
  /-- A leaf node labeled by a letter `a : A`. -/
  | leaf (a : A) : FactorizationTree A
  /-- A binary product node combining two subtrees `l` and `r`. -/
  | binary (l r : FactorizationTree A) : FactorizationTree A
  /-- An idempotent n-ary node with children list `children`. -/
  | idempotent (children : List (FactorizationTree A)) : FactorizationTree A

namespace FactorizationTree

section TreeDefinitions

variable {A : Type*}

mutual
  /-- The yield (spelled word) of a factorization tree, obtained by reading its leaves
  from left to right. -/
  def value : FactorizationTree A → List A
    | leaf a => [a]
    | binary l r => value l ++ value r
    | idempotent children => listValue children

  /-- Auxiliary concatenation of yields for a list of factorization trees. -/
  def listValue : List (FactorizationTree A) → List A
    | [] => []
    | t :: ts => value t ++ listValue ts
end

/-- Decomposition of `listValue` on a non-empty list of trees. -/
lemma listValue_cons (t : FactorizationTree A) (ts : List (FactorizationTree A)) :
    listValue (t :: ts) = value t ++ listValue ts := rfl

mutual
  /-- The height of a factorization tree, measuring the maximum number of edges
  from the root to any leaf. Leaves have height 0. -/
  def height : FactorizationTree A → ℕ
    | leaf _ => 0
    | binary l r => 1 + max (height l) (height r)
    | idempotent children => 1 + listHeight children

  /-- Auxiliary height function for lists of factorization trees. -/
  def listHeight : List (FactorizationTree A) → ℕ
    | [] => 0
    | t :: ts => max (height t) (listHeight ts)
end

/-- Bounding the height of a list of trees when each individual tree's height is bounded. -/
lemma listHeight_le {H : ℕ} : ∀ (ts : List (FactorizationTree A)),
    (∀ t ∈ ts, height t ≤ H) → listHeight ts ≤ H
  | [], _ => Nat.zero_le H
  | t :: ts, h => max_le (h t (.head _)) (listHeight_le ts fun x hx ↦ h x (.tail _ hx))

variable {S : Type*} [Semigroup S]

mutual
  /-- Predicate verifying that a factorization tree is Ramsey for `eval`. -/
  def IsRamsey (eval : List A → S) : FactorizationTree A → Prop
    | leaf _ => True
    | binary l r => IsRamsey eval l ∧ IsRamsey eval r
    | idempotent children =>
        2 ≤ children.length ∧
        listIsRamsey eval children ∧
        ∃ e : S, e * e = e ∧ ∀ t ∈ children, eval (value t) = e

  /-- Auxiliary predicate verifying that all trees in a list are Ramsey. -/
  def listIsRamsey (eval : List A → S) : List (FactorizationTree A) → Prop
    | [] => True
    | t :: ts => IsRamsey eval t ∧ listIsRamsey eval ts
end

/-- A leaf node is unconditionally Ramsey for any evaluation map. -/
lemma leaf_isRamsey (eval : List A → S) (a : A) : (leaf a).IsRamsey eval := trivial

/-- A binary node is Ramsey if and only if both children are Ramsey. -/
lemma binary_isRamsey (eval : List A → S) {l r : FactorizationTree A}
    (hl : l.IsRamsey eval) (hr : r.IsRamsey eval) :
    (binary l r).IsRamsey eval := ⟨hl, hr⟩

/-- An idempotent node is Ramsey if it has at least two children, all children are Ramsey,
and all children evaluate to the same idempotent. -/
lemma idempotent_isRamsey (eval : List A → S) {children : List (FactorizationTree A)}
    (hlen : 2 ≤ children.length) (hlist : listIsRamsey eval children)
    {e : S} (he : e * e = e) (he_eval : ∀ t ∈ children, eval (value t) = e) :
    (idempotent children).IsRamsey eval := ⟨hlen, hlist, e, he, he_eval⟩

/-- Characterization of `listIsRamsey` via universal quantification over tree elements. -/
lemma listIsRamsey_iff (eval : List A → S) :
    ∀ (ts : List (FactorizationTree A)), listIsRamsey eval ts ↔ ∀ t ∈ ts, t.IsRamsey eval
  | [] => by simp [listIsRamsey]
  | t :: ts => by simp [listIsRamsey, listIsRamsey_iff eval ts]

/-- Any element of a Ramsey list of trees is itself Ramsey. -/
lemma isRamsey_of_mem_listIsRamsey {eval : List A → S} {cs : List (FactorizationTree A)}
    (h : listIsRamsey eval cs) {c : FactorizationTree A} (hc : c ∈ cs) : c.IsRamsey eval :=
  (listIsRamsey_iff eval cs).mp h c hc

/-- Any letter in the concatenation of tree yields comes from some tree in the list. -/
lemma mem_listValue {cs : List (FactorizationTree A)} {x : A}
    (h : x ∈ listValue cs) : ∃ c ∈ cs, x ∈ c.value := by
  induction cs with
  | nil => contradiction
  | cons head tail ih =>
    rw [listValue_cons, List.mem_append] at h
    rcases h with h | h
    · exact ⟨head, .head _, h⟩
    · obtain ⟨c, hc, hxc⟩ := ih h
      exact ⟨c, List.mem_cons_of_mem _ hc, hxc⟩

end TreeDefinitions

end FactorizationTree

section ListSlices

/-- Concatenating consecutive slices of a list yields the merged slice. -/
lemma list_drop_take_append {A : Type*} (u : List A) (i k j : ℕ) (hik : i ≤ k) (hkj : k ≤ j) :
    (u.drop i).take (k - i) ++ (u.drop k).take (j - k) = (u.drop i).take (j - i) := by
  have h_drop : u.drop k = (u.drop i).drop (k - i) := by
    rw [List.drop_drop, Nat.add_sub_cancel' hik]
  rw [h_drop]
  have h_take_drop (l : List A) (a b : ℕ) : l.take a ++ (l.drop a).take b = l.take (a + b) := by
    grind
  grind

/-- Slicing a single element from index `i` yields `[u[i]]`. -/
lemma list_drop_take_one {A : Type*} (u : List A) (i : ℕ) (hi : i < u.length) :
    (u.drop i).take 1 = [u[i]] :=
  congrArg (List.take 1) (List.drop_eq_getElem_cons hi)

end ListSlices

section SplitToTree

variable {A S : Type*} [Semigroup S]
variable (eval : List A → S)
variable (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
variable (u : List A)

/-- Inner induction: constructs a list of trees evaluating to the same idempotent
for points with intermediate cuts of rank at most `m`. -/
lemma split_to_tree_inner {n : ℕ} (m : ℕ) (_ : m < n)
    (s : Split (Fin (u.length + 1)) n)
    (h_ramsey : IsRamsey (wordLabeling eval hmul u) s)
    (ih : ∀ (i j : Fin (u.length + 1)) (_ : (i : ℕ) < (j : ℕ)),
      (∀ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) < m) →
      ∃ t : FactorizationTree A,
        t.value = (u.drop i).take (j - i) ∧
        t.IsRamsey eval ∧
        t.height ≤ 3 * m) :
    ∀ (i j : Fin (u.length + 1)) (_ : (i : ℕ) < (j : ℕ)),
    (s i : ℕ) = m → (s j : ℕ) = m →
    (∀ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) ≤ m) →
    ∃ (trees : List (FactorizationTree A)),
      trees ≠ [] ∧
      FactorizationTree.listValue trees = (u.drop i).take (j - i) ∧
      FactorizationTree.listIsRamsey eval trees ∧
      (∀ t ∈ trees, eval (t.value) = (wordLabeling eval hmul u).σ i j) ∧
      (∀ t ∈ trees, t.height ≤ 3 * m) ∧
      ((∃ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) ∧ (x : ℕ) < (j : ℕ) ∧ (s x : ℕ) = m) →
        2 ≤ trees.length) := by
  intro i j
  have H : ∀ (len : ℕ) (i j : Fin (u.length + 1))
      (hij : (i : ℕ) < (j : ℕ)) (hlen : (j : ℕ) - (i : ℕ) = len),
      (s i : ℕ) = m → (s j : ℕ) = m →
      (∀ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) ≤ m) →
      ∃ (trees : List (FactorizationTree A)),
        trees ≠ [] ∧
        FactorizationTree.listValue trees = (u.drop i).take (j - i) ∧
        FactorizationTree.listIsRamsey eval trees ∧
        (∀ t ∈ trees, eval (t.value) = (wordLabeling eval hmul u).σ i j) ∧
        (∀ t ∈ trees, t.height ≤ 3 * m) ∧
        ((∃ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) ∧ (x : ℕ) < (j : ℕ) ∧ (s x : ℕ) = m) →
          2 ≤ trees.length) := by
    intro len
    induction len using Nat.strong_induction_on with
    | h len ih_strong =>
      intro i j hij hlen hsi hsj h_between
      by_cases h_cut : ∃ x : Fin (u.length + 1),
        (i : ℕ) < (x : ℕ) ∧ (x : ℕ) < (j : ℕ) ∧ (s x : ℕ) = m
      · let S_cuts :=
          (Finset.univ : Finset (Fin (u.length + 1))).filter
          (fun (x : Fin (u.length + 1)) =>
          (i : ℕ) < (x : ℕ) ∧ (x : ℕ) < (j : ℕ) ∧ (s x : ℕ) = m)
        have h_nonempty : S_cuts.Nonempty := by
          rcases h_cut with ⟨x, hix, hxj, hsx⟩
          exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨hix, hxj, hsx⟩⟩⟩
        let k := S_cuts.min' h_nonempty
        have hk_mem := Finset.min'_mem S_cuts h_nonempty
        have hk_prop := (Finset.mem_filter.mp hk_mem).2
        have hik : (i : ℕ) < (k : ℕ) := hk_prop.1
        have hkj : (k : ℕ) < (j : ℕ) := hk_prop.2.1
        have hsk : (s k : ℕ) = m := hk_prop.2.2
        have h_less : ∀ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) →
          (x : ℕ) < (k : ℕ) → (s x : ℕ) < m := by
          intro x hix hxk
          have h_bet := h_between x hix (hxk.trans hkj)
          have h_not_eq : ¬ ((s x : ℕ) = m) := by
            intro hc
            have hx_mem : x ∈ S_cuts :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨hix, hxk.trans hkj, hc⟩⟩
            have h_min := Finset.min'_le S_cuts x hx_mem
            omega
          omega
        obtain ⟨t_outer, ht_outer_val, ht_outer_ramsey, ht_outer_height⟩ := ih i k hik h_less
        have h_len : (j : ℕ) - (k : ℕ) < len := by omega
        obtain ⟨trees_inner, h_inner_ne, h_inner_val, h_inner_ramsey,
                h_inner_eval, h_inner_height, _⟩ :=
          ih_strong ((j : ℕ) - (k : ℕ)) h_len k j hkj rfl hsk hsj
            (fun x hkx hxj => h_between x (hik.trans hkx) hxj)
        have h_rel_ik : SplitRelation s i k :=
          splitRelation_of_le_between s hik (Fin.ext (by omega))
            (fun z hz1 hz2 ↦ Fin.le_iff_val_le_val.2
              (by rw [hsi]; exact h_between z hz1 (hz2.trans hkj)))
        have h_rel_kj : SplitRelation s k j :=
          splitRelation_of_le_between s hkj (Fin.ext (by omega))
            (fun z hz1 hz2 ↦ Fin.le_iff_val_le_val.2
              (by rw [hsk]; exact h_between z (hik.trans hz1) hz2))
        obtain ⟨h_color_idem, h_color_eq, h_eval_ij_ik, -, h_eval_kj_eq_ij⟩ :=
          isRamsey_idem_step h_ramsey hik hkj h_rel_ik h_rel_kj
        have h_eval_ik_eq_ij := h_eval_ij_ik.symm
        have h_val_concat :
          FactorizationTree.listValue (t_outer :: trees_inner) = (u.drop i).take (j - i) := by
          rw [FactorizationTree.listValue_cons, ht_outer_val, h_inner_val]
          exact list_drop_take_append u i k j hik.le hkj.le
        have h_trees_ramsey :
          FactorizationTree.listIsRamsey eval (t_outer :: trees_inner) :=
          ⟨ht_outer_ramsey, h_inner_ramsey⟩
        have h_trees_eval_all :
            ∀ t ∈ (t_outer :: trees_inner), eval (t.value) = (wordLabeling eval hmul u).σ i j :=
          List.forall_mem_cons.2 ⟨ht_outer_val.symm ▸ h_eval_ik_eq_ij,
            fun t ht ↦ (h_inner_eval t ht).trans h_eval_kj_eq_ij⟩
        have h_height : ∀ t ∈ t_outer :: trees_inner, t.height ≤ 3 * m :=
          List.forall_mem_cons.2 ⟨ht_outer_height, h_inner_height⟩
        grind
      · obtain ⟨t_outer, ht_outer_val, ht_outer_ramsey, ht_outer_height⟩ :=
          ih i j hij (by grind)
        refine ⟨[t_outer], by simp, by simp [FactorizationTree.listValue, ht_outer_val],
          ⟨ht_outer_ramsey, trivial⟩, List.forall_mem_singleton.2 (ht_outer_val.symm ▸ rfl),
          List.forall_mem_singleton.2 ht_outer_height, fun hc ↦ (h_cut hc).elim⟩
  intro hij hsi hsj h_between
  exact H ((j : ℕ) - (i : ℕ)) i j hij rfl hsi hsj h_between

/-- Outer induction: constructs a Ramsey tree of height `≤ 3 * m` for subsegments
whose internal points have rank `< m`. -/
lemma split_to_tree_outer {n : ℕ}
    (s : Split (Fin (u.length + 1)) n)
    (h_ramsey : IsRamsey (wordLabeling eval hmul u) s) :
    ∀ (m : ℕ), m ≤ n → ∀ (i j : Fin (u.length + 1)), (i : ℕ) < (j : ℕ) →
    (∀ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) < m) →
    ∃ t : FactorizationTree A,
      t.value = (u.drop i).take (j - i) ∧
      t.IsRamsey eval ∧
      t.height ≤ 3 * m := by
  intro m
  induction m with
  | zero =>
    intro hm i j hij h_less
    have h_empty : ∀ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → False := by
      intro x hix hxj
      have h1 := h_less x hix hxj
      omega
    have hj_eq : (j : ℕ) = (i : ℕ) + 1 := by
      by_contra
      let x : Fin (u.length + 1) := ⟨(i : ℕ) + 1, by omega⟩
      have hix : (i : ℕ) < (x : ℕ) := by
        dsimp [x]
        omega
      have hxj : (x : ℕ) < (j : ℕ) := by
        dsimp [x]
        omega
      exact h_empty x hix hxj
    have hi_lt : (i : ℕ) < u.length := by
      have hj_lt := j.isLt
      omega
    let t := FactorizationTree.leaf u[i.val]
    have ht_val : t.value = (u.drop i).take (j - i) := by
      dsimp [t, FactorizationTree.value]
      rw [hj_eq]
      have h_diff : (i : ℕ) + 1 - (i : ℕ) = 1 := by omega
      rw [h_diff]
      exact (list_drop_take_one u i.val hi_lt).symm
    refine ⟨t, ht_val, FactorizationTree.leaf_isRamsey eval _, le_rfl⟩
  | succ m' ih_m' =>
    intro hm i j hij h_less
    let S_cuts :=
      (Finset.univ : Finset (Fin (u.length + 1))).filter
      (fun (x : Fin (u.length + 1)) =>
      (i : ℕ) < (x : ℕ) ∧ (x : ℕ) < (j : ℕ) ∧ (s x : ℕ) = m')
    by_cases h_empty : S_cuts = ∅
    · have h_less' :
          ∀ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) < m' := by
        intro x hix hxj
        have h_sx_lt := h_less x hix hxj
        by_contra
        have h_mem : x ∈ S_cuts := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hix, hxj, by omega⟩
        have h_empty_x := Finset.ext_iff.mp h_empty x
        simp [h_mem] at h_empty_x
      obtain ⟨t, ht_val, ht_ramsey, ht_height⟩ := ih_m' (by omega) i j hij h_less'
      exact ⟨t, ht_val, ht_ramsey, by omega⟩
    · have h_nonempty : S_cuts.Nonempty := Finset.nonempty_of_ne_empty h_empty
      let k_1 := S_cuts.min' h_nonempty
      have hk1_mem := Finset.min'_mem S_cuts h_nonempty
      have hk1_prop := (Finset.mem_filter.mp hk1_mem).2
      let k_r := S_cuts.max' h_nonempty
      have hkr_mem := Finset.max'_mem S_cuts h_nonempty
      have hkr_prop := (Finset.mem_filter.mp hkr_mem).2
      have hik1 : (i : ℕ) < (k_1 : ℕ) := hk1_prop.1
      have h_less_ik1 : ∀ x :
        Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (k_1 : ℕ) → (s x : ℕ) < m' := by
        intro x hix hxk
        have h_sx_lt := h_less x hix (hxk.trans hk1_prop.2.1)
        by_contra
        have h_min_le := Finset.min'_le S_cuts x
          (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hix, hxk.trans hk1_prop.2.1, by omega⟩)
        omega
      obtain ⟨t_ik1, ht_ik1_val, ht_ik1_ramsey, ht_ik1_height⟩ :=
        ih_m' (by omega) i k_1 hik1 h_less_ik1
      have hkrj : (k_r : ℕ) < (j : ℕ) := hkr_prop.2.1
      have h_less_krj : ∀ x :
        Fin (u.length + 1), (k_r : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) < m' := by
        intro x hkx hxj
        have h_sx_lt := h_less x (by omega) hxj
        by_contra
        have h_le_max := Finset.le_max' S_cuts x
          (Finset.mem_filter.mpr ⟨Finset.mem_univ x, by omega, hxj, by omega⟩)
        omega
      obtain ⟨t_krj, ht_krj_val, ht_krj_ramsey, ht_krj_height⟩ :=
        ih_m' (by omega) k_r j hkrj h_less_krj
      by_cases h_eq : k_1 = k_r
      · obtain ⟨t_k1j, ht_k1j_val, ht_k1j_ramsey, ht_k1j_height⟩ :=
          ih_m' (by omega) k_1 j (h_eq ▸ hkrj) (h_eq ▸ h_less_krj)
        have ht_val : (FactorizationTree.binary t_ik1 t_k1j).value = (u.drop i).take (j - i) := by
          simp [FactorizationTree.value, ht_ik1_val, ht_k1j_val,
            list_drop_take_append u i.val k_1.val j.val hik1.le (h_eq ▸ hkrj).le]
        exact ⟨.binary t_ik1 t_k1j, ht_val, ⟨ht_ik1_ramsey, ht_k1j_ramsey⟩, by
          dsimp [FactorizationTree.height]
          omega⟩
      · have hk1kr : (k_1 : ℕ) < (k_r : ℕ) := by
          have hle : k_1 ≤ k_r := Finset.min'_le S_cuts k_r hkr_mem
          omega
        have hk1j : (k_1 : ℕ) < (j : ℕ) := hk1kr.trans hkrj
        have h_mid : ∃ t_mid : FactorizationTree A,
            t_mid.value = (u.drop k_1).take (k_r - k_1) ∧
            t_mid.IsRamsey eval ∧
            t_mid.height ≤ 1 + 3 * m' := by
          by_cases h_no_mid : ∀ x :
            Fin (u.length + 1), (k_1 : ℕ) < (x : ℕ) → (x : ℕ) < (k_r : ℕ) → (s x : ℕ) < m'
          · obtain ⟨t_mid, ht_mid_val, ht_mid_ramsey, ht_mid_height⟩ :=
              ih_m' (by omega) k_1 k_r hk1kr h_no_mid
            exact ⟨t_mid, ht_mid_val, ht_mid_ramsey, by omega⟩
          · push Not at h_no_mid
            rcases h_no_mid with ⟨k_2, hk12, hk2r, h_not_less⟩
            have hk2_prop : (s k_2 : ℕ) = m' := by
              have h_sk2_lt := h_less k_2 (hik1.trans hk12) (hk2r.trans hkrj)
              omega
            have heq1 : (s k_1 : ℕ) = m' := hk1_prop.2.2
            have h_rel_12 : SplitRelation s k_1 k_2 :=
              splitRelation_of_le_between s hk12 (Fin.ext (heq1.trans hk2_prop.symm))
                (fun x hx1 hx2 ↦ Fin.le_iff_val_le_val.2
                  (by rw [heq1]; have := h_less x (by omega) (by omega); omega))
            have h_rel_2r : SplitRelation s k_2 k_r :=
              splitRelation_of_le_between s hk2r (Fin.ext (hk2_prop.trans hkr_prop.2.2.symm))
                (fun x hx1 hx2 ↦ Fin.le_iff_val_le_val.2
                  (by rw [hk2_prop]; have := h_less x (by omega) (by omega); omega))
            obtain ⟨-, -, -, h_idem_1r, -⟩ :=
              isRamsey_idem_step h_ramsey hk12 hk2r h_rel_12 h_rel_2r
            have h_inner := split_to_tree_inner eval hmul u m' (by omega) s h_ramsey
              (fun i j hij hless => ih_m' (by omega) i j hij hless)
              k_1 k_r hk1kr hk1_prop.2.2 hkr_prop.2.2 (by
                intro x hk1x hxkr
                have h_sx_lt := h_less x (by omega) (by omega)
                omega
              )
            obtain ⟨trees, _, h_trees_val, h_trees_ramsey, h_trees_eval,
                    h_trees_height, h_trees_len⟩ := h_inner
            have h_len2 : 2 ≤ trees.length := h_trees_len ⟨k_2, hk12, hk2r, hk2_prop⟩
            exact ⟨.idempotent trees, h_trees_val,
              ⟨h_len2, h_trees_ramsey, _, h_idem_1r, h_trees_eval⟩, by
              dsimp [FactorizationTree.height]
              have h_h_le := FactorizationTree.listHeight_le trees h_trees_height
              omega⟩
        obtain ⟨t_mid, ht_mid_val, ht_mid_ramsey, _⟩ := h_mid
        have ht_val : (FactorizationTree.binary t_ik1 (.binary t_mid t_krj)).value =
            (u.drop i).take (j - i) := by
          simp [FactorizationTree.value, ht_ik1_val, ht_mid_val, ht_krj_val,
            list_drop_take_append u k_1.val k_r.val j.val hk1kr.le hkrj.le,
            list_drop_take_append u i.val k_1.val j.val hik1.le hk1j.le]
        exact ⟨.binary t_ik1 (.binary t_mid t_krj), ht_val,
          ⟨ht_ik1_ramsey, ht_mid_ramsey, ht_krj_ramsey⟩, by
          dsimp [FactorizationTree.height]
          omega⟩

end SplitToTree

section ForestTheorem

/-- Simon's Factorization Forest Theorem: every non-empty word admits
a Ramsey factorization tree of height at most `3 * nS S - 1`. -/
theorem factorization_forest_theorem {A S : Type*} [Semigroup S] [Fintype S]
    [Nonempty S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ t : FactorizationTree A,
      t.value = u ∧
      t.IsRamsey eval ∧
      t.height ≤ 3 * nS S - 1 := by
  have instNonemptyFin : Nonempty (Fin (nS S)) := instNonemptyFin_nS
  obtain ⟨s, h_norm, h_ramsey⟩ := simon_word eval hmul u
  let n := nS S
  have hn_pos : 0 < n := nS_pos
  let m := n - 1
  have hm_lt : m < n := Nat.sub_lt hn_pos (by omega)
  let i : Fin (u.length + 1) := ⟨0, by omega⟩
  let j : Fin (u.length + 1) := ⟨u.length, by omega⟩
  have hij : (i : ℕ) < (j : ℕ) := by cases u with | nil => contradiction | cons => simp [i, j]
  have h_bound_all : ∀ x : Fin (u.length + 1), (s x : ℕ) ≤ m :=
    fun x ↦ Nat.le_pred_of_lt (s x).isLt
  have hsi : (s i : ℕ) = m := by
    have h_min :
        (Finset.min' (Finset.univ : Finset (Fin (u.length + 1))) Finset.univ_nonempty) = i :=
      (Finset.min'_eq_iff _ _ i).mpr ⟨Finset.mem_univ i, fun w _ ↦ Fin.zero_le w⟩
    have h_max :
        ((Finset.max' (Finset.univ : Finset (Fin (nS S))) Finset.univ_nonempty :
          Fin (nS S)) : ℕ) = m :=
      congrArg Fin.val ((Finset.max'_eq_iff _ _
        (⟨m, hm_lt⟩ : Fin (nS S))).mpr ⟨Finset.mem_univ _, fun w _ ↦ Fin.le_iff_val_le_val.mpr
        (Nat.le_pred_of_lt w.isLt)⟩)
    have h_norm' : s (Finset.min' Finset.univ Finset.univ_nonempty) =
      Finset.max' Finset.univ Finset.univ_nonempty := h_norm
    rw [h_min] at h_norm'
    exact congrArg Fin.val h_norm' ▸ h_max
  let S_cuts :=
    (Finset.univ : Finset (Fin (u.length + 1))).filter
    (fun (x : Fin (u.length + 1)) =>
    (i : ℕ) < (x : ℕ) ∧ (x : ℕ) < (j : ℕ) ∧ (s x : ℕ) = m)
  have h_u_val : (u.drop i).take (j - i) = u := by
    dsimp [i, j]
    simp [List.take_length]
  by_cases h_empty : S_cuts = ∅
  · have h_less : ∀ x : Fin (u.length + 1),
      (i : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) < m := by
      intro x hix hxj
      have h_bound_x := h_bound_all x
      by_contra
      have h_mem : x ∈ S_cuts := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hix, hxj, by omega⟩
      have h_empty_x := Finset.ext_iff.mp h_empty x
      simp [h_mem] at h_empty_x
    obtain ⟨t, ht_val, ht_ramsey, ht_height⟩ :=
      split_to_tree_outer eval hmul u s h_ramsey m hm_lt.le i j hij h_less
    exact ⟨t, ht_val.trans h_u_val, ht_ramsey, by omega⟩
  · have h_nonempty : S_cuts.Nonempty := Finset.nonempty_of_ne_empty h_empty
    let k_r := S_cuts.max' h_nonempty
    have hkr_mem := Finset.max'_mem S_cuts h_nonempty
    have hkr_prop := (Finset.mem_filter.mp hkr_mem).2
    have hikr : (i : ℕ) < (k_r : ℕ) := hkr_prop.1
    have hkrj : (k_r : ℕ) < (j : ℕ) := hkr_prop.2.1
    have hskr : (s k_r : ℕ) = m := hkr_prop.2.2
    have h_less_krj : ∀ x :
      Fin (u.length + 1), (k_r : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) < m := by
      intro x hkx hxj
      have h_bound_x := h_bound_all x
      by_contra
      have h_le_max := Finset.le_max' S_cuts x
        (Finset.mem_filter.mpr ⟨Finset.mem_univ x, by omega, hxj, by omega⟩)
      omega
    obtain ⟨t_krj, ht_krj_val, ht_krj_ramsey, ht_krj_height⟩ :=
      split_to_tree_outer eval hmul u s h_ramsey m hm_lt.le k_r j hkrj h_less_krj
    have h_mid : ∃ t_mid : FactorizationTree A,
        t_mid.value = (u.drop i).take (k_r - i) ∧
        t_mid.IsRamsey eval ∧
        t_mid.height ≤ 1 + 3 * m := by
      by_cases h_no_mid : ∀ x :
        Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (k_r : ℕ) → (s x : ℕ) < m
      · obtain ⟨t_mid, ht_mid_val, ht_mid_ramsey, ht_mid_height⟩ :=
          split_to_tree_outer eval hmul u s h_ramsey m hm_lt.le i k_r hikr h_no_mid
        exact ⟨t_mid, ht_mid_val, ht_mid_ramsey, by omega⟩
      · push Not at h_no_mid
        rcases h_no_mid with ⟨k_2, hik2, hk2r, h_not_less⟩
        have hk2_prop : (s k_2 : ℕ) = m := by
          have h_bound_k2 := h_bound_all k_2
          omega
        have h_rel_i2 : SplitRelation s i k_2 := ⟨Fin.ext (by omega), fun x hx1 hx2 => by grind⟩
        have h_rel_2r : SplitRelation s k_2 k_r :=
          splitRelation_of_le_between s hk2r (Fin.ext (by omega))
            (fun x _ _ ↦ Fin.le_iff_val_le_val.2 (by rw [hk2_prop]; exact h_bound_all x))
        obtain ⟨-, -, -, h_idem_ir, -⟩ :=
          isRamsey_idem_step h_ramsey hik2 hk2r h_rel_i2 h_rel_2r
        have h_inner := split_to_tree_inner eval hmul u m hm_lt s h_ramsey
          (fun a b hab hless => split_to_tree_outer eval hmul u s h_ramsey m hm_lt.le a b hab hless)
          i k_r hikr hsi hskr (fun x _ _ => h_bound_all x)
        obtain ⟨trees, _, h_trees_val, h_trees_ramsey, h_trees_eval,
                h_trees_height, h_trees_len⟩ := h_inner
        have h_len2 : 2 ≤ trees.length := h_trees_len ⟨k_2, hik2, hk2r, hk2_prop⟩
        exact ⟨.idempotent trees, h_trees_val,
          ⟨h_len2, h_trees_ramsey, _, h_idem_ir, h_trees_eval⟩, by
          dsimp [FactorizationTree.height]
          have h_h_le := FactorizationTree.listHeight_le trees h_trees_height
          omega⟩
    obtain ⟨t_mid, ht_mid_val, ht_mid_ramsey, _⟩ := h_mid
    have ht_val : (FactorizationTree.binary t_mid t_krj).value = u := by
      simp [FactorizationTree.value, ht_mid_val, ht_krj_val,
        list_drop_take_append u i.val k_r.val j.val hikr.le hkrj.le, h_u_val]
    exact ⟨.binary t_mid t_krj, ht_val, ⟨ht_mid_ramsey, ht_krj_ramsey⟩, by
      dsimp [FactorizationTree.height]
      omega⟩

/-- Convenience wrapper for `factorization_forest_theorem` using a semigroup
homomorphism `ϕ : S →ₙ* T`.
Every non-empty word in `S` admits a Ramsey tree of height at most `3 * nS T - 1`
under the natural evaluation `w ↦ ϕ (listProdNE w hw)`. -/
theorem factorization_forest_theorem_mulHom {S T : Type*} [Semigroup S] [Semigroup T]
    [Fintype T] [Nonempty T] (ϕ : S →ₙ* T) (u : List S) (hu : u ≠ []) :
    let eval_T : List S → T :=
      fun w ↦ if hw : w = [] then Classical.arbitrary T else ϕ (listProdNE w hw)
    ∃ t : FactorizationTree S,
      t.value = u ∧ t.IsRamsey eval_T ∧ t.height ≤ 3 * nS T - 1 := by
  intro eval_T
  have hmul_T (v w : List S) (hv : v ≠ []) (hw : w ≠ []) :
      eval_T (v ++ w) = eval_T v * eval_T w := by
    dsimp [eval_T]
    rw [dite_eq_right (by simp [hv, hw]), dite_eq_right hv, dite_eq_right hw,
      listProdNE_concat v w hv hw, ϕ.map_mul]
  exact factorization_forest_theorem eval_T hmul_T u hu

end ForestTheorem
