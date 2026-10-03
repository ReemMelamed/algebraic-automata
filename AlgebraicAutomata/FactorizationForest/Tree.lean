/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import AlgebraicAutomata.FactorizationForest.Basic
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

/-- The yield (spelled word) of a factorization tree, obtained by reading its leaves
from left to right. -/
def value (t : FactorizationTree A) : List A :=
  match t with
  | leaf a => [a]
  | binary l r => value l ++ value r
  | idempotent children =>
    (children.attach.map fun ⟨c, _⟩ => value c).flatten
termination_by t

@[simp]
lemma value_leaf (a : A) : (leaf a).value = [a] := by
  unfold value
  rfl

@[simp]
lemma value_binary (l r : FactorizationTree A) : (binary l r).value = l.value ++ r.value := by
  rw [value]

/-- Auxiliary concatenation of yields for a list of factorization trees. -/
def listValue (ts : List (FactorizationTree A)) : List A :=
  (ts.map value).flatten

@[simp]
lemma listValue_nil : listValue ([] : List (FactorizationTree A)) = [] := rfl

/-- Decomposition of `listValue` on a non-empty list of trees. -/
@[simp]
lemma listValue_cons (t : FactorizationTree A) (ts : List (FactorizationTree A)) :
    listValue (t :: ts) = value t ++ listValue ts := rfl

@[simp]
lemma value_idempotent (children : List (FactorizationTree A)) :
    (idempotent children).value = listValue children := by
  unfold value listValue
  simp

/-- The height of a factorization tree, measuring the maximum number of edges
from the root to any leaf. Leaves have height 0. -/
def height (t : FactorizationTree A) : ℕ :=
  match t with
  | leaf _ => 0
  | binary l r => 1 + max (height l) (height r)
  | idempotent children =>
    1 + (children.attach.map fun ⟨c, _⟩ => height c).foldr max 0
termination_by t

@[simp]
lemma height_leaf (a : A) : (leaf a).height = 0 := by
  unfold height
  rfl

@[simp]
lemma height_binary (l r : FactorizationTree A) :
  (binary l r).height = 1 + max l.height r.height := by
  rw [height]

/-- Auxiliary height function for lists of factorization trees. -/
def listHeight : List (FactorizationTree A) → ℕ
  | [] => 0
  | t :: ts => max (height t) (listHeight ts)

@[simp]
lemma listHeight_nil : listHeight ([] : List (FactorizationTree A)) = 0 := rfl

@[simp]
lemma listHeight_cons (t : FactorizationTree A) (ts : List (FactorizationTree A)) :
    listHeight (t :: ts) = max (height t) (listHeight ts) := rfl

@[simp]
lemma height_idempotent (children : List (FactorizationTree A)) :
    (idempotent children).height = 1 + listHeight children := by
  unfold height
  congr 1
  simp only [List.map_subtype, List.unattach_attach]
  induction children with
  | nil => rfl
  | cons c cs ih =>
    simp [listHeight, ih]

/-- Bounding the height of a list of trees when each individual tree's height is bounded. -/
lemma listHeight_le {H : ℕ} : ∀ (ts : List (FactorizationTree A)),
    (∀ t ∈ ts, height t ≤ H) → listHeight ts ≤ H
  | [], _ => Nat.zero_le H
  | t :: ts, h => max_le (h t (.head _)) (listHeight_le ts fun x hx ↦ h x (.tail _ hx))

lemma height_le_listHeight {c : FactorizationTree A} {ts : List (FactorizationTree A)}
  (h : c ∈ ts) : c.height ≤ listHeight ts := by
  induction ts with
  | nil => contradiction
  | cons t ts ih =>
    rcases List.mem_cons.mp h with rfl | hmem
    · dsimp [listHeight]
      omega
    · dsimp [listHeight]
      exact (ih hmem).trans (by omega)

/-- Structural induction principle for `FactorizationTree` without mutual induction. -/
@[elab_as_elim]
lemma induction_on {P : FactorizationTree A → Prop} (t : FactorizationTree A)
    (h_leaf : ∀ a, P (.leaf a))
    (h_binary : ∀ l r, P l → P r → P (.binary l r))
    (h_idempotent : ∀ children, (∀ t ∈ children, P t) → P (.idempotent children)) : P t := by
  induction h : t.height using Nat.strong_induction_on generalizing t with
  | h _ ih =>
    cases t with
    | leaf a => exact h_leaf a
    | binary l r =>
      rw [height_binary] at h
      exact h_binary l r
        (ih l.height (by omega) l rfl)
        (ih r.height (by omega) r rfl)
    | idempotent children =>
      rw [height_idempotent] at h
      apply h_idempotent
      intro c hc
      have h_le := height_le_listHeight hc
      exact ih c.height (by omega) c rfl

variable {S : Type*} [Semigroup S]

/-- Predicate verifying that a factorization tree is Ramsey for `eval`. -/
def IsRamsey (eval : List A → S) (t : FactorizationTree A) : Prop :=
  match t with
  | leaf _ => True
  | binary l r => IsRamsey eval l ∧ IsRamsey eval r
  | idempotent children =>
      2 ≤ children.length ∧
      (∀ c ∈ children, IsRamsey eval c) ∧
      ∃ e : S, e * e = e ∧ ∀ t ∈ children, eval (value t) = e
termination_by t

@[simp]
lemma isRamsey_leaf (eval : List A → S) (a : A) : (leaf a).IsRamsey eval ↔ True := by
  unfold IsRamsey
  rfl

@[simp]
lemma isRamsey_binary (eval : List A → S) (l r : FactorizationTree A) :
    (binary l r).IsRamsey eval ↔ l.IsRamsey eval ∧ r.IsRamsey eval := by
  rw [IsRamsey]

/-- Auxiliary predicate verifying that all trees in a list are Ramsey. -/
def listIsRamsey (eval : List A → S) : List (FactorizationTree A) → Prop
  | [] => True
  | t :: ts => IsRamsey eval t ∧ listIsRamsey eval ts

/-- A leaf node is unconditionally Ramsey for any evaluation map. -/
lemma leaf_isRamsey (eval : List A → S) (a : A) : (leaf a).IsRamsey eval := by
  simp only [isRamsey_leaf]

/-- A binary node is Ramsey if and only if both children are Ramsey. -/
lemma binary_isRamsey (eval : List A → S) {l r : FactorizationTree A}
    (hl : l.IsRamsey eval) (hr : r.IsRamsey eval) :
    (binary l r).IsRamsey eval := (isRamsey_binary eval l r).mpr ⟨hl, hr⟩

/-- Characterization of `listIsRamsey` via universal quantification over tree elements. -/
lemma listIsRamsey_iff (eval : List A → S) :
    ∀ (ts : List (FactorizationTree A)), listIsRamsey eval ts ↔ ∀ t ∈ ts, t.IsRamsey eval
  | [] => by simp [listIsRamsey]
  | t :: ts => by simp [listIsRamsey, listIsRamsey_iff eval ts]

@[simp]
lemma isRamsey_idempotent (eval : List A → S) (children : List (FactorizationTree A)) :
    (idempotent children).IsRamsey eval ↔
      2 ≤ children.length ∧
      listIsRamsey eval children ∧
      ∃ e : S, e * e = e ∧ ∀ t ∈ children, eval (value t) = e := by
  unfold IsRamsey
  rw [listIsRamsey_iff]

/-- An idempotent node is Ramsey if it has at least two children, all children are Ramsey,
and all children evaluate to the same idempotent. -/
lemma idempotent_isRamsey (eval : List A → S) {children : List (FactorizationTree A)}
    (hlen : 2 ≤ children.length) (hlist : listIsRamsey eval children)
    {e : S} (he : e * e = e) (he_eval : ∀ t ∈ children, eval (value t) = e) :
    (idempotent children).IsRamsey eval :=
      (isRamsey_idempotent eval children).mpr ⟨hlen, hlist, e, he, he_eval⟩

/-- Any element of a Ramsey list of trees is itself Ramsey. -/
lemma isRamsey_of_mem_listIsRamsey {eval : List A → S} {cs : List (FactorizationTree A)}
    (h : listIsRamsey eval cs) {c : FactorizationTree A} (hc : c ∈ cs) : c.IsRamsey eval :=
  (listIsRamsey_iff eval cs).mp h c hc

/-- Any letter in the concatenation of tree yields comes from some tree in the list. -/
lemma mem_listValue {cs : List (FactorizationTree A)} {x : A}
    (h : x ∈ listValue cs) : ∃ c ∈ cs, x ∈ c.value := by
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
  exact ⟨c, hc, hx⟩
/-- The yield of a Ramsey factorization tree is always non-empty. -/
lemma tree_value_ne_nil {eval : List A → S} (t : FactorizationTree A)
    (ht : t.IsRamsey eval) : t.value ≠ [] := by
  induction t using FactorizationTree.induction_on with
  | h_leaf a => simp
  | h_binary l r ih_l ih_r =>
    rw [isRamsey_binary] at ht
    simp [value_binary, ih_l ht.1]
  | h_idempotent children ih =>
    rw [isRamsey_idempotent] at ht
    rcases ht with ⟨hlen, hlist, -⟩
    rcases children with _ | ⟨c, cs⟩
    · change 2 ≤ 0 at hlen
      omega
    · have hc_ramsey : c.IsRamsey eval := (listIsRamsey_iff eval (c :: cs)).mp hlist c (.head _)
      simp [value_idempotent, ih c (.head _) hc_ramsey]

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

lemma list_drop_take_append_left {A : Type*} (u v : List A) (i j : ℕ) (hj : j ≤ u.length) :
    ((u ++ v).drop i).take (j - i) = (u.drop i).take (j - i) := by
  by_cases hij : i ≤ j
  · simpa [List.drop_take] using congrArg (List.drop i) (List.take_append_of_le_length hj)
  · simp [show j - i = 0 by omega]

lemma list_drop_take_append_right {A : Type*} (u v : List A) (i j : ℕ) (hi : u.length ≤ i) :
    ((u ++ v).drop i).take (j - i) = (v.drop (i - u.length)).take (j - i) := by
  rw [List.drop_append, List.drop_eq_nil_of_le hi, List.nil_append]

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
              (by
                rw [hsi]
                exact h_between z hz1 (hz2.trans hkj)))
        have h_rel_kj : SplitRelation s k j :=
          splitRelation_of_le_between s hkj (Fin.ext (by omega))
            (fun z hz1 hz2 ↦ Fin.le_iff_val_le_val.2
              (by
                rw [hsk]
                exact h_between z (hik.trans hz1) hz2))
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
      simp only [FactorizationTree.value_leaf, t]
      rw [hj_eq]
      have h_diff : (i : ℕ) + 1 - (i : ℕ) = 1 := by omega
      rw [h_diff]
      exact (list_drop_take_one u i.val hi_lt).symm
    refine ⟨t, ht_val, FactorizationTree.leaf_isRamsey eval _, by simp [t]⟩
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
          simp [ht_ik1_val, ht_k1j_val,
            list_drop_take_append u i.val k_1.val j.val hik1.le (h_eq ▸ hkrj).le]
        exact ⟨.binary t_ik1 t_k1j, ht_val,
          FactorizationTree.binary_isRamsey eval ht_ik1_ramsey ht_k1j_ramsey, by
            simp
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
                  (by
                    rw [heq1]
                    have := h_less x (by omega) (by omega)
                    omega))
            have h_rel_2r : SplitRelation s k_2 k_r :=
              splitRelation_of_le_between s hk2r (Fin.ext (hk2_prop.trans hkr_prop.2.2.symm))
                (fun x hx1 hx2 ↦ Fin.le_iff_val_le_val.2
                  (by
                    rw [hk2_prop]
                    have := h_less x (by omega) (by omega)
                    omega))
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
            refine ⟨.idempotent trees, ?_, ?_, ?_⟩
            · rw [FactorizationTree.value_idempotent]
              exact h_trees_val
            · rw [FactorizationTree.isRamsey_idempotent]
              exact ⟨h_len2, h_trees_ramsey, _, h_idem_1r, h_trees_eval⟩
            · rw [FactorizationTree.height_idempotent]
              have h_h_le := FactorizationTree.listHeight_le trees h_trees_height
              omega
        obtain ⟨t_mid, ht_mid_val, ht_mid_ramsey, _⟩ := h_mid
        have ht_val : (FactorizationTree.binary t_ik1 (.binary t_mid t_krj)).value =
            (u.drop i).take (j - i) := by
          simp [ht_ik1_val, ht_mid_val, ht_krj_val,
            list_drop_take_append u k_1.val k_r.val j.val hk1kr.le hkrj.le,
            list_drop_take_append u i.val k_1.val j.val hik1.le hk1j.le]
        exact ⟨.binary t_ik1 (.binary t_mid t_krj), ht_val,
          FactorizationTree.binary_isRamsey eval ht_ik1_ramsey
          (FactorizationTree.binary_isRamsey eval ht_mid_ramsey ht_krj_ramsey), by
            simp
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
            (fun x _ _ ↦ Fin.le_iff_val_le_val.2
              (by
                rw [hk2_prop]
                exact h_bound_all x))
        obtain ⟨-, -, -, h_idem_ir, -⟩ :=
          isRamsey_idem_step h_ramsey hik2 hk2r h_rel_i2 h_rel_2r
        have h_inner := split_to_tree_inner eval hmul u m hm_lt s h_ramsey
          (fun a b hab hless => split_to_tree_outer eval hmul u s h_ramsey m hm_lt.le a b hab hless)
          i k_r hikr hsi hskr (fun x _ _ => h_bound_all x)
        obtain ⟨trees, _, h_trees_val, h_trees_ramsey, h_trees_eval,
                h_trees_height, h_trees_len⟩ := h_inner
        have h_len2 : 2 ≤ trees.length := h_trees_len ⟨k_2, hik2, hk2r, hk2_prop⟩
        refine ⟨.idempotent trees, ?_, ?_, ?_⟩
        · rw [FactorizationTree.value_idempotent]
          exact h_trees_val
        · rw [FactorizationTree.isRamsey_idempotent]
          exact ⟨h_len2, h_trees_ramsey, _, h_idem_ir, h_trees_eval⟩
        · rw [FactorizationTree.height_idempotent]
          have h_h_le := FactorizationTree.listHeight_le trees h_trees_height
          omega
    obtain ⟨t_mid, ht_mid_val, ht_mid_ramsey, _⟩ := h_mid
    have ht_val : (FactorizationTree.binary t_mid t_krj).value = u := by
      simp [ht_mid_val, ht_krj_val, list_drop_take_append u i.val k_r.val j.val hikr.le hkrj.le,
        h_u_val]
    exact ⟨.binary t_mid t_krj, ht_val,
      FactorizationTree.binary_isRamsey eval ht_mid_ramsey ht_krj_ramsey, by
        simp
        grind⟩

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

/-- Simon's Factorization Forest Theorem with classical bound: every non-empty word admits
a Ramsey factorization tree of height at most `3 * |S| - 1` (Colcombet line 361). -/
theorem factorization_forest_classical_bound {A S : Type*} [Semigroup S] [Fintype S]
    [Nonempty S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ t : FactorizationTree A,
      t.value = u ∧
      t.IsRamsey eval ∧
      t.height ≤ 3 * Fintype.card S - 1 := by
  obtain ⟨t, ht_val, ht_ramsey, ht_ht⟩ := factorization_forest_theorem eval hmul u hu
  refine ⟨t, ht_val, ht_ramsey, ?_⟩
  have h_le := nS_le_card (S := S)
  omega

/-- Simon's Factorization Forest Theorem with classical bound `3 * |T| - 1` for a semigroup
homomorphism `ϕ : S →ₙ* T`. -/
theorem factorization_forest_classical_bound_mulHom {S T : Type*} [Semigroup S] [Semigroup T]
    [Fintype T] [Nonempty T] (ϕ : S →ₙ* T) (u : List S) (hu : u ≠ []) :
    let eval_T : List S → T :=
      fun w ↦ if hw : w = [] then Classical.arbitrary T else ϕ (listProdNE w hw)
    ∃ t : FactorizationTree S,
      t.value = u ∧ t.IsRamsey eval_T ∧ t.height ≤ 3 * Fintype.card T - 1 := by
  intro eval_T
  have hmul_T (v w : List S) (hv : v ≠ []) (hw : w ≠ []) :
      eval_T (v ++ w) = eval_T v * eval_T w := by
    dsimp [eval_T]
    rw [dite_eq_right (by simp [hv, hw]), dite_eq_right hv, dite_eq_right hw,
      listProdNE_concat v w hv hw, ϕ.map_mul]
  exact factorization_forest_classical_bound eval_T hmul_T u hu

end ForestTheorem

section TreeToSplit

open FactorizationTree

variable {A : Type*}

/-- Locate which child cut `i` falls into, or if it is an internal boundary between children. -/
def locateCut : (cs : List (FactorizationTree A)) → ℕ →
    Option ({ c : FactorizationTree A // c ∈ cs } × ℕ) ⊕ Unit
  | [], _ => .inr ()
  | [c], i =>
    let nc := c.value.length
    if i < nc then .inl (some (⟨c, by simp⟩, i)) else .inr ()
  | c :: cs, i =>
    let nc := c.value.length
    if i < nc then .inl (some (⟨c, by simp⟩, i))
    else if i = nc then .inl none
    else
      match locateCut cs (i - nc) with
      | .inr () => .inr ()
      | .inl none => .inl none
      | .inl (some (⟨c', hc'⟩, idx)) => .inl (some (⟨c', by simp [hc']⟩, idx))

/-- Raw height of the lowest common ancestor node in `t` separating leaf `i - 1` and leaf `i`
(Colcombet 2008, Lemma 3.5(a)). Returns 0 for leaves or boundary cuts. -/
def lcaHeightRaw (t : FactorizationTree A) (i : ℕ) : ℕ :=
  match t with
  | .leaf _ => 0
  | .binary l r =>
    let nl := l.value.length
    if i < nl then
      lcaHeightRaw l i
    else if i = nl then
      t.height
    else
      lcaHeightRaw r (i - nl)
  | .idempotent children =>
    match locateCut children i with
    | .inr () => 0
    | .inl none => t.height
    | .inl (some (⟨c, _⟩, idx)) => lcaHeightRaw c idx
termination_by t

/-- Height of the lowest common ancestor node in `t` separating leaf `i - 1` and leaf `i`,
bounded by `t.height`. -/
def lcaHeight (t : FactorizationTree A) (i : ℕ) : Fin (t.height + 1) :=
  ⟨min (lcaHeightRaw t i) t.height, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The split induced by a factorization tree `t` on its cut positions `Fin (t.value.length + 1)`
(Colcombet 2008, Lemma 3.5(a)). Each inner cut between adjacent leaves receives the height
of their lowest common ancestor in `t`. -/
def treeToSplit (t : FactorizationTree A) : Split (Fin (t.value.length + 1)) (t.height + 1) :=
  fun i ↦ lcaHeight t i.val

lemma lcaHeightRaw_le_height (t : FactorizationTree A) (i : ℕ) :
    lcaHeightRaw t i ≤ t.height := by
  induction t using FactorizationTree.induction_on generalizing i with
  | h_leaf a =>
    unfold lcaHeightRaw height
    omega
  | h_binary l r ih_l ih_r =>
    unfold lcaHeightRaw height
    dsimp only
    split_ifs with h1 h2
    · have := ih_l i
      omega
    · omega
    · have := ih_r (i - l.value.length)
      omega
  | h_idempotent children ih =>
    unfold lcaHeightRaw
    rw [height_idempotent]
    cases locateCut children i with
    | inr u =>
      dsimp only
      omega
    | inl opt =>
      cases opt with
      | none =>
        dsimp only
        omega
      | some pair =>
        rcases pair with ⟨⟨c, hc⟩, idx⟩
        dsimp only
        have := ih c hc idx
        have h_le := height_le_listHeight hc
        omega

@[simp]
lemma lcaHeight_val (t : FactorizationTree A) (i : ℕ) :
    (lcaHeight t i).val = lcaHeightRaw t i := by
  dsimp [lcaHeight]
  rw [min_eq_left (lcaHeightRaw_le_height t i)]

@[simp]
lemma treeToSplit_val (t : FactorizationTree A) (i : Fin (t.value.length + 1)) :
    (treeToSplit t i).val = lcaHeightRaw t i.val := by
  dsimp [treeToSplit]
  rw [lcaHeight_val]

lemma lcaHeightRaw_binary_mid (l r : FactorizationTree A) :
    lcaHeightRaw (.binary l r) l.value.length = (binary l r).height := by
  rw [lcaHeightRaw]
  split_ifs with h1 h2
  · omega
  · rfl
  · omega

lemma lcaHeightRaw_binary_left (l r : FactorizationTree A) {i : ℕ} (hi : i < l.value.length) :
    lcaHeightRaw (.binary l r) i = lcaHeightRaw l i := by
  rw [lcaHeightRaw]
  split_ifs
  rfl

lemma lcaHeightRaw_binary_right (l r : FactorizationTree A) {i : ℕ} (hi : l.value.length < i) :
    lcaHeightRaw (.binary l r) i = lcaHeightRaw r (i - l.value.length) := by
  rw [lcaHeightRaw]
  split_ifs with h1 h2
  · omega
  · omega
  · rfl

lemma lcaHeightRaw_binary_lt (l r : FactorizationTree A) {i : ℕ} (hi : i ≠ l.value.length) :
    lcaHeightRaw (.binary l r) i < (binary l r).height := by
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · rw [lcaHeightRaw_binary_left l r hlt]
    have := lcaHeightRaw_le_height l i
    rw [height_binary]
    omega
  · rw [lcaHeightRaw_binary_right l r hgt]
    have := lcaHeightRaw_le_height r (i - l.value.length)
    rw [height_binary]
    omega

lemma splitRelation_comm {α : Type*} [LinearOrder α] {h : ℕ} (s : Split α h) (x y : α) :
    SplitRelation s x y ↔ SplitRelation s y x := by
  have H (a b : α) (hab : SplitRelation s a b) : SplitRelation s b a :=
    ⟨hab.1.symm, fun z hz1 hz2 ↦
      hab.2 z (by simpa [min_comm] using hz1) (by simpa [max_comm] using hz2)⟩
  exact ⟨H x y, H y x⟩

lemma splitRelation_refl {α : Type*} [LinearOrder α] {h : ℕ} (s : Split α h) (x : α) :
    SplitRelation s x x :=
  ⟨rfl, fun z hz1 hz2 ↦ by
    have : z = x := le_antisymm hz2 (by simpa using hz1)
    rw [this]⟩

lemma splitRelation_binary_cases {l r : FactorizationTree A}
    {x y : Fin ((binary l r).value.length + 1)} (hxy : x < y)
    (hrel : SplitRelation (treeToSplit (.binary l r)) x y) :
    y.val < l.value.length ∨ l.value.length < x.val := by
  set nl := l.value.length
  by_contra h_contra
  push Not at h_contra
  rcases h_contra with ⟨hy, hx⟩
  have h_mid_val : lcaHeightRaw (.binary l r) nl = (binary l r).height :=
    lcaHeightRaw_binary_mid l r
  have h_sx_eq_sy : (treeToSplit (.binary l r) x).val = (treeToSplit (.binary l r) y).val :=
    congrArg Fin.val hrel.1
  rw [treeToSplit_val, treeToSplit_val] at h_sx_eq_sy
  by_cases hx_eq : x.val = nl
  · have hy_gt : nl < y.val := by omega
    have hy_lt : lcaHeightRaw (.binary l r) y.val < (binary l r).height :=
      lcaHeightRaw_binary_lt l r (by omega)
    rw [hx_eq, h_mid_val] at h_sx_eq_sy
    omega
  · have hx_lt : x.val < nl := by omega
    by_cases hy_eq : y.val = nl
    · rw [hy_eq, h_mid_val] at h_sx_eq_sy
      have hx_lt' : lcaHeightRaw (.binary l r) x.val < (binary l r).height :=
        lcaHeightRaw_binary_lt l r (by omega)
      omega
    · have hy_gt : nl < y.val := by omega
      have hnl_lt : nl < (binary l r).value.length + 1 := by
        simp [value_binary]
        omega
      let mid : Fin ((binary l r).value.length + 1) := ⟨nl, hnl_lt⟩
      have hx_le_mid : x ≤ mid := by
        rw [Fin.le_iff_val_le_val]
        dsimp [mid]
        omega
      have h_mid_le_y : mid ≤ y := by
        rw [Fin.le_iff_val_le_val]
        dsimp [mid]
        omega
      have h_min : min x y = x := min_eq_left hxy.le
      have h_max : max x y = y := max_eq_right hxy.le
      have h_bet := hrel.2 mid (by
        rw [h_min]
        exact hx_le_mid) (by
        rw [h_max]
        exact h_mid_le_y)
      rw [h_min] at h_bet
      have h_bet_val := Fin.le_iff_val_le_val.mp h_bet
      rw [treeToSplit_val, treeToSplit_val] at h_bet_val
      change lcaHeightRaw (.binary l r) nl ≤ lcaHeightRaw (.binary l r) x.val at h_bet_val
      rw [h_mid_val] at h_bet_val
      have hx_lt' : lcaHeightRaw (.binary l r) x.val < (binary l r).height :=
        lcaHeightRaw_binary_lt l r (by omega)
      omega

lemma splitRelation_binary_left {l r : FactorizationTree A}
    {x y : Fin ((binary l r).value.length + 1)} (hxy : x < y)
    (hy : y.val < l.value.length)
    (hrel : SplitRelation (treeToSplit (.binary l r)) x y) :
    SplitRelation (treeToSplit l)
      ⟨x.val, by
        have := y.isLt
        omega⟩
      ⟨y.val, by
        have := y.isLt
        omega⟩ := by
  have hx : x.val < l.value.length := by omega
  refine ⟨?_, ?_⟩
  · have h1 := congrArg Fin.val hrel.1
    rw [treeToSplit_val, treeToSplit_val] at h1
    rw [lcaHeightRaw_binary_left l r hx, lcaHeightRaw_binary_left l r hy] at h1
    exact Fin.ext (by rw [treeToSplit_val, treeToSplit_val, h1])
  · intro z hz1 hz2
    have hz1_val := Fin.le_iff_val_le_val.mp hz1
    have hz2_val := Fin.le_iff_val_le_val.mp hz2
    have hz_lt : z.val < l.value.length := by
      change min x.val y.val ≤ z.val at hz1_val
      change z.val ≤ max x.val y.val at hz2_val
      omega
    let z_bin : Fin ((binary l r).value.length + 1) := ⟨z.val, by
      simp [value_binary]
      omega⟩
    have hz1_bin : min x y ≤ z_bin := by
      rw [Fin.le_iff_val_le_val]
      change min x.val y.val ≤ z.val
      exact hz1_val
    have hz2_bin : z_bin ≤ max x y := by
      rw [Fin.le_iff_val_le_val]
      change z.val ≤ max x.val y.val
      exact hz2_val
    have h_bet := hrel.2 z_bin hz1_bin hz2_bin
    have h_bet_val := Fin.le_iff_val_le_val.mp h_bet
    rw [treeToSplit_val, treeToSplit_val] at h_bet_val
    rw [lcaHeightRaw_binary_left l r hz_lt] at h_bet_val
    have h_min_lt : (min x y).val < l.value.length := by
      change min x.val y.val < l.value.length
      omega
    rw [lcaHeightRaw_binary_left l r h_min_lt] at h_bet_val
    rw [Fin.le_iff_val_le_val, treeToSplit_val, treeToSplit_val]
    have : (min (⟨x.val, by
                have := y.isLt
                omega⟩ : Fin (l.value.length + 1))
                (⟨y.val, by
                have := y.isLt
                omega⟩ : Fin (l.value.length + 1))).val =
           (min x y).val := by
      change min x.val y.val = min x.val y.val
      rfl
    rw [this]
    exact h_bet_val

lemma splitRelation_binary_right {l r : FactorizationTree A}
    {x y : Fin ((binary l r).value.length + 1)} (hxy : x < y)
    (hx : l.value.length < x.val)
    (hrel : SplitRelation (treeToSplit (.binary l r)) x y) :
    SplitRelation (treeToSplit r)
      ⟨x.val - l.value.length, by
        have := x.isLt
        simp [value_binary] at this
        omega⟩
      ⟨y.val - l.value.length, by
        have := y.isLt
        simp [value_binary] at this
        omega⟩ := by
  have hy : l.value.length < y.val := by omega
  refine ⟨?_, ?_⟩
  · have h1 := congrArg Fin.val hrel.1
    rw [treeToSplit_val, treeToSplit_val] at h1
    rw [lcaHeightRaw_binary_right l r hx, lcaHeightRaw_binary_right l r hy] at h1
    exact Fin.ext (by rw [treeToSplit_val, treeToSplit_val, h1])
  · intro z hz1 hz2
    have hz1_val := Fin.le_iff_val_le_val.mp hz1
    have hz2_val := Fin.le_iff_val_le_val.mp hz2
    have hz_ge : l.value.length < z.val + l.value.length := by
      change min (x.val - l.value.length) (y.val - l.value.length) ≤ z.val at hz1_val
      omega
    let z_bin : Fin ((binary l r).value.length + 1) := ⟨z.val + l.value.length, by
      have := z.isLt
      simp [value_binary]
      omega⟩
    have hz1_bin : min x y ≤ z_bin := by
      rw [Fin.le_iff_val_le_val]
      change min x.val y.val ≤ z.val + l.value.length
      change min (x.val - l.value.length) (y.val - l.value.length) ≤ z.val at hz1_val
      omega
    have hz2_bin : z_bin ≤ max x y := by
      rw [Fin.le_iff_val_le_val]
      change z.val + l.value.length ≤ max x.val y.val
      change z.val ≤ max (x.val - l.value.length) (y.val - l.value.length) at hz2_val
      omega
    have h_bet := hrel.2 z_bin hz1_bin hz2_bin
    have h_bet_val := Fin.le_iff_val_le_val.mp h_bet
    rw [treeToSplit_val, treeToSplit_val] at h_bet_val
    rw [lcaHeightRaw_binary_right l r hz_ge] at h_bet_val
    have h_min_ge : l.value.length < (min x y).val := by
      change l.value.length < min x.val y.val
      omega
    rw [lcaHeightRaw_binary_right l r h_min_ge] at h_bet_val
    rw [Fin.le_iff_val_le_val, treeToSplit_val, treeToSplit_val]
    have : z.val + l.value.length - l.value.length = z.val := by omega
    rw [this] at h_bet_val
    have h_min_eq : (min (⟨x.val - l.value.length, by
        have := x.isLt
        simp [value_binary] at this
        omega⟩ : Fin (r.value.length + 1))
      (⟨y.val - l.value.length, by
        have := y.isLt
        simp [value_binary] at this
        omega⟩ : Fin (r.value.length + 1))).val =
      (min x y).val - l.value.length := by
      change min (x.val - l.value.length)
        (y.val - l.value.length) = min x.val y.val - l.value.length
      omega
    rw [h_min_eq]
    exact h_bet_val

lemma wordLabeling_binary_left {S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (l r : FactorizationTree A)
    (x y : Fin ((binary l r).value.length + 1))
    (hxy : x.val ≤ y.val)
    (hy : y.val ≤ l.value.length) :
    (wordLabeling eval hmul (binary l r).value).σ x y =
    (wordLabeling eval hmul l.value).σ ⟨x.val, by omega⟩
      ⟨y.val, by omega⟩ := by
  dsimp [wordLabeling]
  rw [value_binary, list_drop_take_append_left _ _ _ _ hy]

lemma wordLabeling_binary_right {S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (l r : FactorizationTree A)
    (x y : Fin ((binary l r).value.length + 1))
    (hx : l.value.length ≤ x.val)
    (hxy : x.val ≤ y.val) :
    (wordLabeling eval hmul (binary l r).value).σ x y =
    (wordLabeling eval hmul r.value).σ
      ⟨x.val - l.value.length, by
        have := x.isLt
        simp [value_binary] at this
        omega⟩
      ⟨y.val - l.value.length, by
        have := y.isLt
        simp [value_binary] at this
        omega⟩ := by
  dsimp [wordLabeling]
  rw [show y.val - l.value.length - (x.val - l.value.length) = y.val - x.val by omega,
    value_binary, list_drop_take_append_right _ _ _ _ hx]

lemma lcaHeightRaw_idempotent_eq_height {cs : List (FactorizationTree A)} {i : ℕ} :
    lcaHeightRaw (.idempotent cs) i = (idempotent cs).height ↔
    locateCut cs i = .inl none := by
  rw [lcaHeightRaw, height_idempotent]
  cases h : locateCut cs i with
  | inr u =>
    simp
    omega
  | inl opt =>
    cases opt with
    | none => simp
    | some pair =>
      obtain ⟨⟨c, hc⟩, idx⟩ := pair
      dsimp only
      have := (lcaHeightRaw_le_height c idx).trans (height_le_listHeight hc)
      simp
      omega

lemma locateCut_cons_mid (c : FactorizationTree A) (cs : List (FactorizationTree A))
    (hcs : cs ≠ []) :
    locateCut (c :: cs) c.value.length = .inl none := by
  cases cs with
  | nil => contradiction
  | cons c' cs' =>
    dsimp [locateCut]
    split_ifs with h1 h2
    · omega
    · rfl
    · omega

lemma locateCut_cons_left (c : FactorizationTree A) (cs : List (FactorizationTree A))
    {i : ℕ} (hi : i < c.value.length) :
    locateCut (c :: cs) i = .inl (some (⟨c, by simp⟩, i)) := by
  cases cs with
  | nil =>
    dsimp [locateCut]
    split_ifs
    rfl
  | cons c' cs' =>
    dsimp [locateCut]
    split_ifs
    rfl

lemma lcaHeightRaw_idempotent_cons_left (c : FactorizationTree A) (cs : List (FactorizationTree A))
    {i : ℕ} (hi : i < c.value.length) :
    lcaHeightRaw (.idempotent (c :: cs)) i = lcaHeightRaw c i := by
  rw [lcaHeightRaw, locateCut_cons_left c cs hi]

lemma lcaHeightRaw_idempotent_cons_left_lt (c : FactorizationTree A)
    (cs : List (FactorizationTree A)) {i : ℕ} (hi : i < c.value.length) :
    lcaHeightRaw (.idempotent (c :: cs)) i < (idempotent (c :: cs)).height := by
  rw [lcaHeightRaw_idempotent_cons_left c cs hi, height_idempotent]
  have h1 := lcaHeightRaw_le_height c i
  have h2 : c.height ≤ listHeight (c :: cs) := height_le_listHeight (by simp)
  omega

lemma locateCut_singleton_length (c : FactorizationTree A) :
    locateCut [c] c.value.length = .inr () := by
  dsimp [locateCut]
  split_ifs with h
  · omega
  · rfl

lemma lcaHeightRaw_idempotent_singleton_length (c : FactorizationTree A) :
    lcaHeightRaw (.idempotent [c]) c.value.length = 0 := by
  rw [lcaHeightRaw, locateCut_singleton_length]

lemma locateCut_at_length (cs : List (FactorizationTree A))
    (h_ne : ∀ c ∈ cs, c.value ≠ []) :
    locateCut cs (listValue cs).length = .inr () := by
  induction cs with
  | nil =>
    rfl
  | cons c cs ih =>
    cases cs with
    | nil =>
      have : (listValue [c]).length = c.value.length := by simp [listValue]
      rw [this]
      exact locateCut_singleton_length c
    | cons c' cs' =>
      dsimp [locateCut]
      have hc' := h_ne c' (by simp)
      have hc'_pos : 0 < c'.value.length := by
        cases h : c'.value
        · exact False.elim (hc' h)
        · simp
      have h_tail_pos : 0 < (listValue (c' :: cs')).length := by
        rw [listValue_cons, List.length_append]
        omega
      split_ifs with h1 h2
      · have : (c.value ++ (c'.value ++ listValue cs')).length =
            c.value.length + (listValue (c' :: cs')).length := by
          simp [listValue_cons, List.length_append]
        omega
      · have : (c.value ++ (c'.value ++ listValue cs')).length =
            c.value.length + (listValue (c' :: cs')).length := by
          simp [listValue_cons, List.length_append]
        omega
      · have h_sub : (c.value ++ (c'.value ++ listValue cs')).length - c.value.length =
            (listValue (c' :: cs')).length := by
          simp [listValue_cons, List.length_append]
        rw [h_sub]
        have ih_res := ih (fun d hd ↦ h_ne d (by simp [hd]))
        rw [ih_res]

lemma lcaHeightRaw_at_length {S : Type*} [Semigroup S] {eval : List A → S} (t : FactorizationTree A)
    (ht : t.IsRamsey eval) :
    lcaHeightRaw t t.value.length = 0 := by
  induction t using FactorizationTree.induction_on with
  | h_leaf a =>
    rw [lcaHeightRaw]
  | h_binary l r ih_l ih_r =>
    rw [isRamsey_binary] at ht
    have hr_ne := tree_value_ne_nil r ht.2
    have hr_pos : 0 < r.value.length := by
      cases h : r.value
      · exact False.elim (hr_ne h)
      · simp
    rw [lcaHeightRaw]
    rw [value_binary, List.length_append]
    split_ifs with h1 h2
    · omega
    · omega
    · have h_sub : l.value.length + r.value.length - l.value.length = r.value.length := by omega
      rw [h_sub]
      exact ih_r ht.2
  | h_idempotent children ih =>
    rw [isRamsey_idempotent] at ht
    rcases ht with ⟨hlen, hlist, e, he, he_eval⟩
    have h_ne : ∀ c ∈ children, c.value ≠ [] := fun c hc ↦
      tree_value_ne_nil c ((listIsRamsey_iff eval children).mp hlist c hc)
    rw [lcaHeightRaw]
    have h_loc := locateCut_at_length children h_ne
    have h_val := value_idempotent children
    rw [h_val, h_loc]

lemma splitRelation_idempotent_cases {c : FactorizationTree A} {cs : List (FactorizationTree A)}
    (hcs : cs ≠ [])
    {x y : Fin ((idempotent (c :: cs)).value.length + 1)} (hxy : x < y)
    (hrel : SplitRelation (treeToSplit (.idempotent (c :: cs))) x y) :
    y.val < c.value.length ∨ c.value.length ≤ x.val := by
  set nc := c.value.length
  by_contra h_contra
  push Not at h_contra
  rcases h_contra with ⟨hy, hx⟩
  have h_mid_val : lcaHeightRaw (.idempotent (c :: cs)) nc = (idempotent (c :: cs)).height := by
    rw [lcaHeightRaw, locateCut_cons_mid c cs hcs]
  have hx_lt : lcaHeightRaw (.idempotent (c :: cs)) x.val < (idempotent (c :: cs)).height :=
    lcaHeightRaw_idempotent_cons_left_lt c cs (by omega)
  have h_sx_eq_sy : (treeToSplit (.idempotent (c :: cs)) x).val =
                    (treeToSplit (.idempotent (c :: cs)) y).val :=
    congrArg Fin.val hrel.1
  rw [treeToSplit_val, treeToSplit_val] at h_sx_eq_sy
  by_cases hy_eq : y.val = nc
  · rw [hy_eq, h_mid_val] at h_sx_eq_sy
    omega
  · have hy_gt : nc < y.val := by omega
    have hnc_lt : nc < (idempotent (c :: cs)).value.length + 1 := by
      have : (idempotent (c :: cs)).value = c.value ++ listValue cs := by
        rw [value_idempotent, listValue_cons]
      rw [this]
      simp only [List.length_append]
      omega
    let mid : Fin ((idempotent (c :: cs)).value.length + 1) := ⟨nc, hnc_lt⟩
    have hx_le_mid : x ≤ mid := by
      rw [Fin.le_def]
      dsimp [mid]
      omega
    have h_mid_le_y : mid ≤ y := by
      rw [Fin.le_def]
      dsimp [mid]
      omega
    have h_min : min x y = x := min_eq_left hxy.le
    have h_max : max x y = y := max_eq_right hxy.le
    have h_bet := hrel.2 mid (by
      rw [h_min]
      exact hx_le_mid) (by
      rw [h_max]
      exact h_mid_le_y)
    rw [h_min] at h_bet
    have h_bet_val := Fin.le_def.mp h_bet
    rw [treeToSplit_val, treeToSplit_val] at h_bet_val
    change lcaHeightRaw (.idempotent (c :: cs)) nc ≤
           lcaHeightRaw (.idempotent (c :: cs)) x.val at h_bet_val
    rw [h_mid_val] at h_bet_val
    omega

lemma wordLabeling_idempotent_left {S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (c : FactorizationTree A) (cs : List (FactorizationTree A))
    (x y : Fin ((idempotent (c :: cs)).value.length + 1))
    (hxy : x.val ≤ y.val)
    (hy : y.val ≤ c.value.length) :
    (wordLabeling eval hmul (idempotent (c :: cs)).value).σ x y =
    (wordLabeling eval hmul c.value).σ ⟨x.val, by omega⟩
      ⟨y.val, by omega⟩ := by
  dsimp [wordLabeling]
  rw [value_idempotent, listValue_cons, list_drop_take_append_left _ _ _ _ hy]

lemma splitRelation_idempotent_left {c : FactorizationTree A}
    {cs : List (FactorizationTree A)}
    {x y : Fin ((idempotent (c :: cs)).value.length + 1)} (hxy : x < y)
    (hy : y.val < c.value.length)
    (hrel : SplitRelation (treeToSplit (.idempotent (c :: cs))) x y) :
    SplitRelation (treeToSplit c)
      ⟨x.val, by
        have := y.isLt
        omega⟩
      ⟨y.val, by
        have := y.isLt
        omega⟩ := by
  have hx : x.val < c.value.length := by omega
  refine ⟨?_, ?_⟩
  · have h1 := congrArg Fin.val hrel.1
    rw [treeToSplit_val, treeToSplit_val] at h1
    rw [lcaHeightRaw_idempotent_cons_left c cs hx,
        lcaHeightRaw_idempotent_cons_left c cs hy] at h1
    exact Fin.ext (by rw [treeToSplit_val, treeToSplit_val, h1])
  · intro z hz1 hz2
    have hz1_val := Fin.le_iff_val_le_val.mp hz1
    have hz2_val := Fin.le_iff_val_le_val.mp hz2
    have hz_lt : z.val < c.value.length := by
      change min x.val y.val ≤ z.val at hz1_val
      change z.val ≤ max x.val y.val at hz2_val
      omega
    have hz_lt_all : z.val < (idempotent (c :: cs)).value.length + 1 := by
      have := z.isLt
      have hval : (idempotent (c :: cs)).value = c.value ++ listValue cs := by
        rw [value_idempotent, listValue_cons]
      rw [hval]
      simp only [List.length_append]
      omega
    let z_idem : Fin ((idempotent (c :: cs)).value.length + 1) := ⟨z.val, hz_lt_all⟩
    have hz1_idem : min x y ≤ z_idem := by
      rw [Fin.le_iff_val_le_val]
      change min x.val y.val ≤ z.val
      exact hz1_val
    have hz2_idem : z_idem ≤ max x y := by
      rw [Fin.le_iff_val_le_val]
      change z.val ≤ max x.val y.val
      exact hz2_val
    have h_bet := hrel.2 z_idem hz1_idem hz2_idem
    have h_bet_val := Fin.le_iff_val_le_val.mp h_bet
    rw [treeToSplit_val, treeToSplit_val] at h_bet_val
    rw [lcaHeightRaw_idempotent_cons_left c cs hz_lt] at h_bet_val
    have h_min_lt : (min x y).val < c.value.length := by
      change min x.val y.val < c.value.length
      omega
    rw [lcaHeightRaw_idempotent_cons_left c cs h_min_lt] at h_bet_val
    rw [Fin.le_iff_val_le_val, treeToSplit_val, treeToSplit_val]
    have : (min (⟨x.val, by
                have := y.isLt
                omega⟩ : Fin (c.value.length + 1))
                (⟨y.val, by
                have := y.isLt
                omega⟩ : Fin (c.value.length + 1))).val =
           (min x y).val := by
      change min x.val y.val = min x.val y.val
      rfl
    rw [this]
    exact h_bet_val

lemma locateCut_cons_right (c : FactorizationTree A) (cs : List (FactorizationTree A))
    {i : ℕ} (hi : c.value.length < i) :
    locateCut (c :: cs) i =
      match locateCut cs (i - c.value.length) with
      | .inr () => .inr ()
      | .inl none => .inl none
      | .inl (some (⟨c', hc'⟩, idx)) => .inl (some (⟨c', by simp [hc']⟩, idx)) := by
  cases cs with
  | nil =>
    dsimp [locateCut]
    split_ifs with h1
    · omega
    · rfl
  | cons c' cs' =>
    dsimp [locateCut]
    split_ifs with h1 h2
    · omega
    · omega
    · rfl

lemma lcaHeightRaw_idempotent_cons_right_of_lt (c : FactorizationTree A)
    (cs : List (FactorizationTree A)) {i : ℕ} (hi : c.value.length < i)
    (hlt : lcaHeightRaw (.idempotent (c :: cs)) i < (idempotent (c :: cs)).height) :
    lcaHeightRaw (.idempotent (c :: cs)) i =
    lcaHeightRaw (.idempotent cs) (i - c.value.length) := by
  have h_loc : locateCut (c :: cs) i =
      match locateCut cs (i - c.value.length) with
      | .inr () => .inr ()
      | .inl none => .inl none
      | .inl (some (⟨c', hc'⟩, idx)) => .inl (some (⟨c', by simp [hc']⟩, idx)) :=
    locateCut_cons_right c cs hi
  rw [lcaHeightRaw, h_loc]
  cases h : locateCut cs (i - c.value.length) with
  | inr u =>
    rw [lcaHeightRaw, h]
  | inl opt =>
    cases opt with
    | none =>
      have h1 : locateCut (c :: cs) i = .inl none := by rw [h_loc, h]
      have h2 : lcaHeightRaw (.idempotent (c :: cs)) i = (idempotent (c :: cs)).height := by
        rw [lcaHeightRaw, h1]
      omega
    | some pair =>
      rcases pair with ⟨⟨c', hc'⟩, idx⟩
      rw [lcaHeightRaw, h]

lemma wordLabeling_idempotent_right {S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (c : FactorizationTree A) (cs : List (FactorizationTree A))
    (x y : Fin ((idempotent (c :: cs)).value.length + 1))
    (hx : c.value.length ≤ x.val)
    (_ : x.val ≤ y.val) :
    (wordLabeling eval hmul (idempotent (c :: cs)).value).σ x y =
    eval (((listValue cs).drop (x.val - c.value.length)).take (y.val - x.val)) := by
  dsimp [wordLabeling]
  rw [value_idempotent, listValue_cons, list_drop_take_append_right _ _ _ _ hx]

lemma length_idempotent_cons (c : FactorizationTree A) (cs : List (FactorizationTree A)) :
    (idempotent (c :: cs)).value.length = c.value.length + (idempotent cs).value.length := by
  simp only [value_idempotent, listValue_cons, List.length_append]

lemma wordLabeling_idempotent_cons_right {S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (c : FactorizationTree A) (cs : List (FactorizationTree A))
    (x y : Fin ((idempotent (c :: cs)).value.length + 1))
    (hx : c.value.length ≤ x.val)
    (hxy : x.val ≤ y.val) :
    (wordLabeling eval hmul (idempotent (c :: cs)).value).σ x y =
    (wordLabeling eval hmul (idempotent cs).value).σ
      ⟨x.val - c.value.length, by
        have h_len := length_idempotent_cons c cs
        have := x.isLt
        omega⟩
      ⟨y.val - c.value.length, by
        have h_len := length_idempotent_cons c cs
        have := y.isLt
        omega⟩ := by
  rw [wordLabeling_idempotent_right eval hmul c cs x y hx hxy]
  dsimp [wordLabeling]
  rw [show y.val - c.value.length - (x.val - c.value.length) = y.val - x.val by omega,
    value_idempotent]

lemma splitRelation_idempotent_cons_right {c : FactorizationTree A}
    {cs : List (FactorizationTree A)}
    {x y : Fin ((idempotent (c :: cs)).value.length + 1)} (hxy : x < y)
    (hx : c.value.length < x.val)
    (hx_lt : (treeToSplit (.idempotent (c :: cs)) x).val < (idempotent (c :: cs)).height)
    (hrel : SplitRelation (treeToSplit (.idempotent (c :: cs))) x y) :
    SplitRelation (treeToSplit (.idempotent cs))
      ⟨x.val - c.value.length, by
        have h_len := length_idempotent_cons c cs
        have := x.isLt
        omega⟩
      ⟨y.val - c.value.length, by
        have h_len := length_idempotent_cons c cs
        have := y.isLt
        omega⟩ := by
  have hy : c.value.length < y.val := by omega
  have H_val (z : Fin ((idempotent (c :: cs)).value.length + 1))
      (hz : c.value.length < z.val)
      (hz_lt : (treeToSplit (.idempotent (c :: cs)) z).val < (idempotent (c :: cs)).height) :
      (treeToSplit (.idempotent (c :: cs)) z).val =
      (treeToSplit (.idempotent cs) ⟨z.val - c.value.length, by
        have h_len := length_idempotent_cons c cs
        have := z.isLt
        omega⟩).val := by
    rw [treeToSplit_val, treeToSplit_val]
    rw [treeToSplit_val] at hz_lt
    exact lcaHeightRaw_idempotent_cons_right_of_lt c cs hz hz_lt
  have hy_lt : (treeToSplit (.idempotent (c :: cs)) y).val < (idempotent (c :: cs)).height := by
    have h1 := congrArg Fin.val hrel.1
    rw [← h1]
    exact hx_lt
  refine ⟨?_, ?_⟩
  · have h1 := congrArg Fin.val hrel.1
    have hx_eq := H_val x hx hx_lt
    have hy_eq := H_val y hy hy_lt
    exact Fin.ext (by rw [← hx_eq, ← hy_eq, h1])
  · intro z hz1 hz2
    have hz1_val := Fin.le_iff_val_le_val.mp hz1
    have hz2_val := Fin.le_iff_val_le_val.mp hz2
    change min (x.val - c.value.length) (y.val - c.value.length) ≤ z.val at hz1_val
    change z.val ≤ max (x.val - c.value.length) (y.val - c.value.length) at hz2_val
    have hz_gt : c.value.length < z.val + c.value.length := by omega
    have hz_lt_all : z.val + c.value.length < (idempotent (c :: cs)).value.length + 1 := by
      have h_len := length_idempotent_cons c cs
      have := z.isLt
      omega
    let z_idem : Fin ((idempotent (c :: cs)).value.length + 1) :=
      ⟨z.val + c.value.length, hz_lt_all⟩
    have hz1_idem : min x y ≤ z_idem := by
      rw [Fin.le_iff_val_le_val]
      change min x.val y.val ≤ z.val + c.value.length
      omega
    have hz2_idem : z_idem ≤ max x y := by
      rw [Fin.le_iff_val_le_val]
      change z.val + c.value.length ≤ max x.val y.val
      omega
    have h_bet := hrel.2 z_idem hz1_idem hz2_idem
    have h_bet_val := Fin.le_iff_val_le_val.mp h_bet
    have hz_idem_lt : (treeToSplit (.idempotent (c :: cs)) z_idem).val <
        (idempotent (c :: cs)).height := by
      have h_min_lt : (treeToSplit (.idempotent (c :: cs)) (min x y)).val <
          (idempotent (c :: cs)).height := by
        have : min x y = x := min_eq_left hxy.le
        rw [this]
        exact hx_lt
      rw [treeToSplit_val, treeToSplit_val] at h_bet_val
      omega
    have hz_eq := H_val z_idem hz_gt hz_idem_lt
    have hx_eq := H_val x hx hx_lt
    have h_min_eq : min x y = x := min_eq_left hxy.le
    rw [h_min_eq] at h_bet_val
    rw [hz_eq, hx_eq] at h_bet_val
    have h_sub_val : (⟨z_idem.val - c.value.length, by
        have h_len := length_idempotent_cons c cs
        have := z_idem.isLt
        omega⟩ :
        Fin ((idempotent cs).value.length + 1)) = z := by
      ext
      dsimp [z_idem]
      omega
    rw [h_sub_val] at h_bet_val
    rw [Fin.le_iff_val_le_val]
    have h_min_small : min (⟨x.val - c.value.length, by
        have h_len := length_idempotent_cons c cs
        have := x.isLt
        omega⟩ :
        Fin ((idempotent cs).value.length + 1))
      ⟨y.val - c.value.length, by
        have h_len := length_idempotent_cons c cs
        have := y.isLt
        omega⟩ =
      ⟨x.val - c.value.length, by
        have h_len := length_idempotent_cons c cs
        have := x.isLt
        omega⟩ := by
      apply min_eq_left
      rw [Fin.le_iff_val_le_val]
      dsimp
      omega
    rw [h_min_small]
    exact h_bet_val
lemma locateCut_nil (i : ℕ) : locateCut ([] : List (FactorizationTree A)) i = .inr () := rfl

lemma locateCut_singleton (c : FactorizationTree A) (i : ℕ) :
    locateCut [c] i = if i < c.value.length then .inl (some (⟨c, by simp⟩, i)) else .inr () := rfl

lemma locateCut_cons_cons (c c' : FactorizationTree A) (cs : List (FactorizationTree A)) (i : ℕ) :
    locateCut (c :: c' :: cs) i =
      if i < c.value.length then .inl (some (⟨c, by simp⟩, i))
      else if i = c.value.length then .inl none
      else match locateCut (c' :: cs) (i - c.value.length) with
      | .inr () => .inr ()
      | .inl none => .inl none
      | .inl (some (⟨c'', hc''⟩, idx)) => .inl (some (⟨c'', by simp [hc'']⟩, idx)) := by
          simp only [locateCut]
          grind

lemma locateCut_singleton_ne_inl_none (c : FactorizationTree A) (i : ℕ) :
    locateCut [c] i ≠ .inl none := by
  rw [locateCut_singleton]
  split_ifs <;> intro h <;> cases h

lemma locateCut_cons_cons_inl_none_iff (c c' : FactorizationTree A)
    (cs : List (FactorizationTree A)) (i : ℕ) :
    locateCut (c :: c' :: cs) i = .inl none ↔
    i = c.value.length ∨ (c.value.length < i ∧ locateCut (c' :: cs)
    (i - c.value.length) = .inl none) := by
  rw [locateCut_cons_cons]
  split_ifs with h1 h2
  · simp [h1.ne, not_lt.mpr h1.le]
  · simp [h2]
  · have h_gt : c.value.length < i := by omega
    cases h : locateCut (c' :: cs) (i - c.value.length) with
    | inr u =>
      simp [h2]
    | inl opt =>
      cases opt with
      | none =>
        simp [h_gt]
      | some pair =>
        simp [h2]

lemma eval_take_of_locateCut_eq_none {S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (e : S) (he : e * e = e)
    (cs : List (FactorizationTree A))
    (h_eval : ∀ c ∈ cs, eval c.value = e)
    (h_ne : ∀ c ∈ cs, c.value ≠ [])
    {i : ℕ} (hi : locateCut cs i = .inl none) :
    eval ((listValue cs).take i) = e := by
  induction cs generalizing i with
  | nil =>
    rw [locateCut_nil] at hi
    cases hi
  | cons c cs' ih =>
    cases cs' with
    | nil =>
      exact False.elim (locateCut_singleton_ne_inl_none c i hi)
    | cons c' cs'' =>
      rw [locateCut_cons_cons_inl_none_iff] at hi
      rcases hi with rfl | ⟨h_gt, h_tail⟩
      · rw [listValue_cons]
        have h_take : (c.value ++ listValue (c' :: cs'')).take c.value.length = c.value :=
          List.take_left
        rw [h_take]
        exact h_eval c (.head _)
      · rw [listValue_cons]
        have ih_res := ih (fun x hx ↦ h_eval x (.tail _ hx))
          (fun x hx ↦ h_ne x (.tail _ hx)) h_tail
        have h_take : (c.value ++ listValue (c' :: cs'')).take i =
            c.value ++ (listValue (c' :: cs'')).take (i - c.value.length) := by
          rw [List.take_append, List.take_of_length_le (by omega)]
        rw [h_take]
        have h_c_ne := h_ne c (.head _)
        have h_tail_ne : (listValue (c' :: cs'')).take (i - c.value.length) ≠ [] := by
          intro h_nil
          have h_len := congrArg List.length h_nil
          simp only [List.length_take, List.length_nil] at h_len
          have hc'_ne := h_ne c' (by simp)
          have : 1 ≤ (listValue (c' :: cs'')).length := by
            simp only [listValue_cons, List.length_append]
            have := List.length_pos_iff_ne_nil.mpr hc'_ne
            omega
          omega
        rw [hmul _ _ h_c_ne h_tail_ne, h_eval c (.head _), ih_res, he]

lemma eval_slice_of_locateCut_eq_none {S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (e : S) (he : e * e = e)
    (cs : List (FactorizationTree A))
    (h_eval : ∀ c ∈ cs, eval c.value = e)
    (h_ne : ∀ c ∈ cs, c.value ≠ [])
    {x y : ℕ} (hxy : x < y)
    (hx : locateCut cs x = .inl none)
    (hy : locateCut cs y = .inl none) :
    eval (((listValue cs).drop x).take (y - x)) = e := by
  induction cs generalizing x y with
  | nil =>
    rw [locateCut_nil] at hx
    cases hx
  | cons c cs' ih =>
    cases cs' with
    | nil =>
      exact False.elim (locateCut_singleton_ne_inl_none c x hx)
    | cons c' cs'' =>
      rw [locateCut_cons_cons_inl_none_iff] at hx hy
      rcases hx with rfl | ⟨hx_gt, hx_tail⟩
      · rcases hy with rfl | ⟨hy_gt, hy_tail⟩
        · omega
        · rw [listValue_cons]
          have h_drop : (c.value ++ listValue (c' :: cs'')).drop c.value.length =
              listValue (c' :: cs'') := List.drop_left
          rw [h_drop]
          exact eval_take_of_locateCut_eq_none eval hmul e he (c' :: cs'')
            (fun z hz ↦ h_eval z (.tail _ hz)) (fun z hz ↦ h_ne z (.tail _ hz)) hy_tail
      · rcases hy with rfl | ⟨hy_gt, hy_tail⟩
        · omega
        · rw [listValue_cons]
          have h_slice := list_drop_take_append_right c.value (listValue (c' :: cs'')) x y hx_gt.le
          rw [h_slice]
          have h_diff : y - x = y - c.value.length - (x - c.value.length) := by omega
          rw [h_diff]
          have hxy_sub : x - c.value.length < y - c.value.length := by omega
          exact ih (fun z hz ↦ h_eval z (.tail _ hz))
            (fun z hz ↦ h_ne z (.tail _ hz)) hxy_sub hx_tail hy_tail

/-- Base case of Lemma 3.5(a): a leaf node induces a Ramsey split on its cuts. -/
lemma treeToSplit_leaf_isRamsey {S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (a : A) :
    IsRamsey (wordLabeling eval hmul (FactorizationTree.leaf a).value) (treeToSplit (.leaf a)) := by
  refine ⟨fun x y z _ _ _ _ ↦ by
    have := z.isLt
    simp only [value_leaf] at this
    omega,
  fun x y u v _ _ _ _ _ ↦ by
    have hx := x.isLt
    have hy := y.isLt
    have hu := u.isLt
    have hv := v.isLt
    simp only [value_leaf] at hx hy hu hv
    have : x = u := Fin.ext (by omega)
    have : y = v := Fin.ext (by omega)
    subst_vars
    rfl⟩

lemma idempotent_of_lt {S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (e : S) (_he : e * e = e) :
    ∀ (cs : List (FactorizationTree A)),
      (∀ c ∈ cs, eval c.value = e) →
      (∀ c ∈ cs, c.value ≠ []) →
      (∀ c ∈ cs, c.IsRamsey eval) →
      (∀ c ∈ cs, IsRamsey (wordLabeling eval hmul c.value) (treeToSplit c)) →
      (∀ (x y z : Fin ((idempotent cs).value.length + 1)),
        x < y → y < z →
        (treeToSplit (.idempotent cs) x).val < (idempotent cs).height →
        SplitRelation (treeToSplit (.idempotent cs)) x y →
        SplitRelation (treeToSplit (.idempotent cs)) y z →
        (wordLabeling eval hmul (idempotent cs).value).σ x y *
          (wordLabeling eval hmul (idempotent cs).value).σ x y =
        (wordLabeling eval hmul (idempotent cs).value).σ x y) ∧
      (∀ (x y u v : Fin ((idempotent cs).value.length + 1)),
        x < y → u < v →
        (treeToSplit (.idempotent cs) x).val < (idempotent cs).height →
        SplitRelation (treeToSplit (.idempotent cs)) x y →
        SplitRelation (treeToSplit (.idempotent cs)) u v →
        SplitRelation (treeToSplit (.idempotent cs)) x u →
        (wordLabeling eval hmul (idempotent cs).value).σ x y =
        (wordLabeling eval hmul (idempotent cs).value).σ u v) := by
  intro cs
  induction cs with
  | nil =>
    intro _ _ _ _
    refine ⟨fun x y _ _ ↦ by
      have hx := x.isLt
      have hy := y.isLt
      simp [value_idempotent, listValue] at hx hy
      omega,
    fun x y _ _ _ ↦ by
      have hx := x.isLt
      have hy := y.isLt
      simp [value_idempotent, listValue] at hx hy
      omega⟩
  | cons c cs ih_cs =>
    intro h_eval h_ne h_ramsey ih_trees
    have hc_ramsey := h_ramsey c (.head _)
    have ih_c := ih_trees c (.head _)
    have ih_tail := ih_cs (fun d hd ↦ h_eval d (.tail _ hd))
      (fun d hd ↦ h_ne d (.tail _ hd))
      (fun d hd ↦ h_ramsey d (.tail _ hd))
      (fun d hd ↦ ih_trees d (.tail _ hd))
    by_cases hcs_emp : cs = []
    · subst hcs_emp
      have hc_val : (idempotent [c]).value = c.value := by
        simp [value_idempotent, listValue]
      have hc_len : (idempotent [c]).value.length = c.value.length :=
        congrArg List.length hc_val
      let toC (w : Fin ((idempotent [c]).value.length + 1)) : Fin (c.value.length + 1) :=
        ⟨w.val, by
          have := w.isLt
          simp [value_idempotent, listValue] at this
          omega⟩
      have h_split_val : ∀ (i : Fin ((idempotent [c]).value.length + 1)),
          (treeToSplit (.idempotent [c]) i).val = (treeToSplit c (toC i)).val := by
        intro i
        rw [treeToSplit_val, treeToSplit_val]
        have hi_le : i.val ≤ c.value.length := Nat.le_of_lt_succ (toC i).isLt
        rcases lt_or_eq_of_le hi_le with hi_lt | hi_eq
        · rw [lcaHeightRaw_idempotent_cons_left c [] hi_lt]
        · rw [hi_eq, lcaHeightRaw_idempotent_singleton_length,
            lcaHeightRaw_at_length c hc_ramsey]
      have h_rel_to_c : ∀ {a b : Fin ((idempotent [c]).value.length + 1)},
          SplitRelation (treeToSplit (.idempotent [c])) a b →
          SplitRelation (treeToSplit c) (toC a) (toC b) := by
        intro a b hrel
        refine ⟨?_, ?_⟩
        · have h1 := congrArg Fin.val hrel.1
          rw [h_split_val a, h_split_val b] at h1
          exact Fin.ext h1
        · intro z hz1 hz2
          have hz_val_bound : z.val < (idempotent [c]).value.length + 1 := by
            simp [value_idempotent, listValue]
          let z_idem : Fin ((idempotent [c]).value.length + 1) := ⟨z.val, hz_val_bound⟩
          have hz1_idem : min a b ≤ z_idem := hz1
          have hz2_idem : z_idem ≤ max a b := hz2
          have h_bet := hrel.2 z_idem hz1_idem hz2_idem
          have h_bet_val := Fin.le_def.mp h_bet
          rw [h_split_val z_idem] at h_bet_val
          rw [Fin.le_def]
          rcases le_total a b with hab | hba
          · have hab_c : toC a ≤ toC b := hab
            simpa [min_eq_left hab, min_eq_left hab_c, h_split_val a] using h_bet_val
          · have hba_c : toC b ≤ toC a := hba
            simpa [min_eq_right hba, min_eq_right hba_c, h_split_val b] using h_bet_val
      refine ⟨?_, ?_⟩
      · intro x y z hxy hyz hx_lt hrel_xy hrel_yz
        have hxy_c : toC x < toC y := hxy
        have hyz_c : toC y < toC z := hyz
        have hrel_xy_c := h_rel_to_c hrel_xy
        have hrel_yz_c := h_rel_to_c hrel_yz
        have hy_le : y.val ≤ c.value.length := Nat.le_of_lt_succ (toC y).isLt
        have h_wl := wordLabeling_idempotent_left eval hmul c [] x y hxy.le hy_le
        rw [h_wl]
        exact ih_c.1 _ _ _ hxy_c hyz_c hrel_xy_c hrel_yz_c
      · intro x y u v hxy huv hx_lt hrel_xy hrel_uv hrel_xu
        have hxy_c : toC x < toC y := hxy
        have huv_c : toC u < toC v := huv
        have hrel_xy_c := h_rel_to_c hrel_xy
        have hrel_uv_c := h_rel_to_c hrel_uv
        have hrel_xu_c := h_rel_to_c hrel_xu
        have hy_le : y.val ≤ c.value.length := Nat.le_of_lt_succ (toC y).isLt
        have hv_le : v.val ≤ c.value.length := Nat.le_of_lt_succ (toC v).isLt
        have h_wl_xy := wordLabeling_idempotent_left eval hmul c [] x y hxy.le hy_le
        have h_wl_uv := wordLabeling_idempotent_left eval hmul c [] u v huv.le hv_le
        rw [h_wl_xy, h_wl_uv]
        exact ih_c.2 _ _ _ _ hxy_c huv_c hrel_xy_c hrel_uv_c hrel_xu_c
    · refine ⟨?_, ?_⟩
      · intro x y z hxy hyz hx_lt hrel_xy hrel_yz
        rcases splitRelation_idempotent_cases hcs_emp hxy hrel_xy with hy_lt | hx_ge
        · rcases splitRelation_idempotent_cases hcs_emp hyz hrel_yz with hz_lt | hy_ge
          · have hrel_xy_c := splitRelation_idempotent_left hxy hy_lt hrel_xy
            have hrel_yz_c := splitRelation_idempotent_left hyz hz_lt hrel_yz
            have h_wl := wordLabeling_idempotent_left eval hmul c cs x y hxy.le hy_lt.le
            rw [h_wl]
            have hxy_c : (⟨x.val, by omega⟩ : Fin (c.value.length + 1)) < ⟨y.val, by omega⟩ := hxy
            have hyz_c : (⟨y.val, by omega⟩ : Fin (c.value.length + 1)) < ⟨z.val, by omega⟩ := hyz
            exact ih_c.1 _ _ _ hxy_c hyz_c hrel_xy_c hrel_yz_c
          · omega
        · rcases splitRelation_idempotent_cases hcs_emp hyz hrel_yz with hz_lt | hy_ge
          · omega
          · have hx_gt : c.value.length < x.val := by
              by_contra!
              have hx_eq : x.val = c.value.length := by omega
              have h_mid := locateCut_cons_mid c cs hcs_emp
              have h_ht : (treeToSplit (.idempotent (c :: cs)) x).val =
                  (idempotent (c :: cs)).height := by
                rw [treeToSplit_val, hx_eq, lcaHeightRaw, h_mid]
              omega
            have hy_gt : c.value.length < y.val := by omega
            have hrel_xy_cs := splitRelation_idempotent_cons_right hxy hx_gt hx_lt hrel_xy
            have hy_lt_ht : (treeToSplit (.idempotent (c :: cs)) y).val <
                (idempotent (c :: cs)).height := by
              have h1 := congrArg Fin.val hrel_xy.1
              omega
            have hrel_yz_cs := splitRelation_idempotent_cons_right hyz hy_gt hy_lt_ht hrel_yz
            have h_wl := wordLabeling_idempotent_cons_right eval hmul c cs x y hx_ge hxy.le
            rw [h_wl]
            have hxy_cs : (⟨x.val - c.value.length, by
                have := x.isLt
                have h_len := length_idempotent_cons c cs
                omega⟩ :
                Fin ((idempotent cs).value.length + 1)) <
              ⟨y.val - c.value.length, by
                have := y.isLt
                have h_len := length_idempotent_cons c cs
                omega⟩ := by
              rw [Fin.lt_def]
              dsimp
              omega
            have hyz_cs : (⟨y.val - c.value.length, by
                have := y.isLt
                have h_len := length_idempotent_cons c cs
                omega⟩ :
                Fin ((idempotent cs).value.length + 1)) <
              ⟨z.val - c.value.length, by
                have := z.isLt
                have h_len := length_idempotent_cons c cs
                omega⟩ := by
              rw [Fin.lt_def]
              dsimp
              omega
            have hx_cs_lt : (treeToSplit (.idempotent cs) ⟨x.val - c.value.length, by
                have := x.isLt
                have h_len := length_idempotent_cons c cs
                omega⟩).val <
                (idempotent cs).height := by
              rw [treeToSplit_val]
              have h1 : lcaHeightRaw (.idempotent cs) (x.val - c.value.length) =
                  lcaHeightRaw (.idempotent (c :: cs)) x.val := by
                have := lcaHeightRaw_idempotent_cons_right_of_lt c cs hx_gt
                rw [treeToSplit_val] at hx_lt
                exact (this hx_lt).symm
              rw [h1]
              by_contra! h_ge
              have h_eq : lcaHeightRaw (.idempotent (c :: cs)) x.val =
                  (idempotent cs).height := by
                have h_le := lcaHeightRaw_le_height (.idempotent cs) (x.val - c.value.length)
                omega
              have h_none : locateCut cs (x.val - c.value.length) = .inl none := by
                have h_le := lcaHeightRaw_le_height (.idempotent cs) (x.val - c.value.length)
                have h_loc_eq : lcaHeightRaw (.idempotent cs) (x.val - c.value.length) =
                    (idempotent cs).height := by omega
                exact lcaHeightRaw_idempotent_eq_height.mp h_loc_eq
              have h_loc_c : locateCut (c :: cs) x.val = .inl none := by
                rw [locateCut_cons_right c cs hx_gt, h_none]
              have h_top : lcaHeightRaw (.idempotent (c :: cs)) x.val =
                  (idempotent (c :: cs)).height := by
                rw [lcaHeightRaw, h_loc_c]
              rw [treeToSplit_val] at hx_lt
              omega
            exact ih_tail.1 _ _ _ hxy_cs hyz_cs hx_cs_lt hrel_xy_cs hrel_yz_cs
      · intro x y u v hxy huv hx_lt hrel_xy hrel_uv hrel_xu
        rcases splitRelation_idempotent_cases hcs_emp hxy hrel_xy with hy_lt | hx_ge
        · have hu_lt : u.val < c.value.length := by
            rcases lt_trichotomy x u with hxu | rxu | hux
            · rcases splitRelation_idempotent_cases hcs_emp hxu hrel_xu with hu_lt' | hx_gt'
              · exact hu_lt'
              · omega
            · rw [← rxu]
              omega
            · have hrel_ux : SplitRelation (treeToSplit (.idempotent (c :: cs))) u x := by
                rw [splitRelation_comm]
                exact hrel_xu
              rcases splitRelation_idempotent_cases hcs_emp hux hrel_ux with hx_lt' | hu_gt'
              · omega
              · omega
          rcases splitRelation_idempotent_cases hcs_emp huv hrel_uv with hv_lt | hu_ge
          · have hrel_xy_c := splitRelation_idempotent_left hxy hy_lt hrel_xy
            have hrel_uv_c := splitRelation_idempotent_left huv hv_lt hrel_uv
            have h_wl_xy := wordLabeling_idempotent_left eval hmul c cs x y hxy.le hy_lt.le
            have h_wl_uv := wordLabeling_idempotent_left eval hmul c cs u v huv.le hv_lt.le
            rw [h_wl_xy, h_wl_uv]
            have hrel_xu_c : SplitRelation (treeToSplit c) ⟨x.val, by omega⟩ ⟨u.val, by omega⟩ := by
              rcases lt_trichotomy x u with hxu | rxu | hux
              · exact splitRelation_idempotent_left hxu hu_lt hrel_xu
              · subst rxu
                exact splitRelation_refl _ _
              · have hrel_ux : SplitRelation (treeToSplit (.idempotent (c :: cs))) u x := by
                  rw [splitRelation_comm]
                  exact hrel_xu
                have := splitRelation_idempotent_left hux (by omega) hrel_ux
                rwa [splitRelation_comm]
            have hxy_c : (⟨x.val, by omega⟩ : Fin (c.value.length + 1)) < ⟨y.val, by omega⟩ := hxy
            have huv_c : (⟨u.val, by omega⟩ : Fin (c.value.length + 1)) < ⟨v.val, by omega⟩ := huv
            exact ih_c.2 _ _ _ _ hxy_c huv_c hrel_xy_c hrel_uv_c hrel_xu_c
          · omega
        · have hx_gt : c.value.length < x.val := by
            by_contra!
            have hx_eq : x.val = c.value.length := by omega
            have h_mid := locateCut_cons_mid c cs hcs_emp
            have h_ht : (treeToSplit (.idempotent (c :: cs)) x).val =
                (idempotent (c :: cs)).height := by
              rw [treeToSplit_val, hx_eq, lcaHeightRaw, h_mid]
            omega
          have hu_gt : c.value.length < u.val := by
            rcases lt_trichotomy x u with hxu | rxu | hux
            · rcases splitRelation_idempotent_cases hcs_emp hxu hrel_xu with hu_lt' | hx_gt'
              · omega
              · by_contra!
                have hu_eq : u.val = c.value.length := by omega
                have h_mid := locateCut_cons_mid c cs hcs_emp
                have h_ht : (treeToSplit (.idempotent (c :: cs)) u).val =
                    (idempotent (c :: cs)).height := by
                  rw [treeToSplit_val, hu_eq, lcaHeightRaw, h_mid]
                have h1 := congrArg Fin.val hrel_xu.1
                omega
            · rw [← rxu]
              exact hx_gt
            · have hrel_ux : SplitRelation (treeToSplit (.idempotent (c :: cs))) u x := by
                rw [splitRelation_comm]
                exact hrel_xu
              rcases splitRelation_idempotent_cases hcs_emp hux hrel_ux with hx_lt' | hu_gt'
              · omega
              · by_contra!
                have hu_eq : u.val = c.value.length := by omega
                have h_mid := locateCut_cons_mid c cs hcs_emp
                have h_ht : (treeToSplit (.idempotent (c :: cs)) u).val =
                    (idempotent (c :: cs)).height := by
                  rw [treeToSplit_val, hu_eq, lcaHeightRaw, h_mid]
                have h1 := congrArg Fin.val hrel_xu.1
                omega
          rcases splitRelation_idempotent_cases hcs_emp huv hrel_uv with hv_lt | hu_ge
          · omega
          · have hrel_xy_cs := splitRelation_idempotent_cons_right hxy hx_gt hx_lt hrel_xy
            have hu_lt_ht : (treeToSplit (.idempotent (c :: cs)) u).val <
                (idempotent (c :: cs)).height := by
              have h1 := congrArg Fin.val hrel_xu.1
              omega
            have hrel_uv_cs := splitRelation_idempotent_cons_right huv hu_gt hu_lt_ht hrel_uv
            have hrel_xu_cs : SplitRelation (treeToSplit (.idempotent cs))
                ⟨x.val - c.value.length, by
                  have := x.isLt
                  have h_len := length_idempotent_cons c cs
                  omega⟩
                ⟨u.val - c.value.length, by
                  have := u.isLt
                  have h_len := length_idempotent_cons c cs
                  omega⟩ := by
              rcases lt_trichotomy x u with hxu | rxu | hux
              · exact splitRelation_idempotent_cons_right hxu hx_gt hx_lt hrel_xu
              · subst rxu
                exact splitRelation_refl _ _
              · have hrel_ux : SplitRelation (treeToSplit (.idempotent (c :: cs))) u x := by
                  rw [splitRelation_comm]
                  exact hrel_xu
                have := splitRelation_idempotent_cons_right hux hu_gt hu_lt_ht hrel_ux
                rwa [splitRelation_comm]
            have h_wl_xy := wordLabeling_idempotent_cons_right eval hmul c cs x y hx_ge hxy.le
            have h_wl_uv := wordLabeling_idempotent_cons_right eval hmul c cs u v hu_ge huv.le
            rw [h_wl_xy, h_wl_uv]
            have hxy_cs : (⟨x.val - c.value.length, by
                have := x.isLt
                have h_len := length_idempotent_cons c cs
                omega⟩ :
                Fin ((idempotent cs).value.length + 1)) <
              ⟨y.val - c.value.length, by
                have := y.isLt
                have h_len := length_idempotent_cons c cs
                omega⟩ := by
              rw [Fin.lt_def]
              dsimp
              omega
            have huv_cs : (⟨u.val - c.value.length, by
                have := u.isLt
                have h_len := length_idempotent_cons c cs
                omega⟩ :
                Fin ((idempotent cs).value.length + 1)) <
              ⟨v.val - c.value.length, by
                have := v.isLt
                have h_len := length_idempotent_cons c cs
                omega⟩ := by
              rw [Fin.lt_def]
              dsimp
              omega
            have hx_cs_lt : (treeToSplit (.idempotent cs) ⟨x.val - c.value.length, by
                have := x.isLt
                have h_len := length_idempotent_cons c cs
                omega⟩).val <
                (idempotent cs).height := by
              rw [treeToSplit_val]
              have h1 : lcaHeightRaw (.idempotent cs) (x.val - c.value.length) =
                  lcaHeightRaw (.idempotent (c :: cs)) x.val := by
                have := lcaHeightRaw_idempotent_cons_right_of_lt c cs hx_gt
                rw [treeToSplit_val] at hx_lt
                exact (this hx_lt).symm
              rw [h1]
              by_contra! h_ge
              have h_eq : lcaHeightRaw (.idempotent (c :: cs)) x.val =
                  (idempotent cs).height := by
                have h_le := lcaHeightRaw_le_height (.idempotent cs) (x.val - c.value.length)
                omega
              have h_none : locateCut cs (x.val - c.value.length) = .inl none := by
                have h_le := lcaHeightRaw_le_height (.idempotent cs) (x.val - c.value.length)
                have h_loc_eq : lcaHeightRaw (.idempotent cs) (x.val - c.value.length) =
                    (idempotent cs).height := by omega
                exact lcaHeightRaw_idempotent_eq_height.mp h_loc_eq
              have h_loc_c : locateCut (c :: cs) x.val = .inl none := by
                rw [locateCut_cons_right c cs hx_gt, h_none]
              have h_top : lcaHeightRaw (.idempotent (c :: cs)) x.val =
                  (idempotent (c :: cs)).height := by
                rw [lcaHeightRaw, h_loc_c]
              rw [treeToSplit_val] at hx_lt
              omega
            exact ih_tail.2 _ _ _ _ hxy_cs huv_cs hx_cs_lt hrel_xy_cs hrel_uv_cs hrel_xu_cs

theorem tree_to_split_isRamsey {S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (t : FactorizationTree A) (ht : t.IsRamsey eval) :
    IsRamsey (wordLabeling eval hmul t.value) (treeToSplit t) := by
  induction t using FactorizationTree.induction_on generalizing eval with
  | h_leaf a =>
    exact treeToSplit_leaf_isRamsey eval hmul a
  | h_binary l r ih_l ih_r =>
    rw [isRamsey_binary] at ht
    rcases ht with ⟨hl, hr⟩
    have ihl := ih_l eval hmul hl
    have ihr := ih_r eval hmul hr
    refine ⟨?_, ?_⟩
    · intro x y z hxy hyz hrel_xy hrel_yz
      rcases splitRelation_binary_cases hxy hrel_xy with hy_lt | hx_gt
      · rcases splitRelation_binary_cases hyz hrel_yz with hz_lt | hy_gt
        · have hx_le : x.val ≤ y.val := hxy.le
          have h_wl := wordLabeling_binary_left eval hmul l r x y hx_le (by omega)
          rw [h_wl]
          have hrel_xy_l := splitRelation_binary_left hxy hy_lt hrel_xy
          have hrel_yz_l := splitRelation_binary_left hyz hz_lt hrel_yz
          have hxy_l : (⟨x.val, by omega⟩ : Fin (l.value.length + 1)) < ⟨y.val, by omega⟩ := hxy
          have hyz_l : (⟨y.val, by omega⟩ : Fin (l.value.length + 1)) < ⟨z.val, by omega⟩ := hyz
          exact ihl.1 _ _ _ hxy_l hyz_l hrel_xy_l hrel_yz_l
        · omega
      · rcases splitRelation_binary_cases hyz hrel_yz with hz_lt | hy_gt
        · have : x.val < y.val := hxy
          omega
        · have hx_le : x.val ≤ y.val := hxy.le
          have h_wl := wordLabeling_binary_right eval hmul l r x y hx_gt.le hx_le
          rw [h_wl]
          have hrel_xy_r := splitRelation_binary_right hxy hx_gt hrel_xy
          have hrel_yz_r := splitRelation_binary_right hyz (by omega) hrel_yz
          have hxy_r : (⟨x.val - l.value.length, by
              have := x.isLt
              simp [value_binary] at this
              omega⟩ : Fin (r.value.length + 1)) <
            ⟨y.val - l.value.length, by
              have := y.isLt
              simp [value_binary] at this
              omega⟩ := by
            rw [Fin.lt_def]
            dsimp
            omega
          have hyz_r : (⟨y.val - l.value.length, by
              have := y.isLt
              simp [value_binary] at this
              omega⟩ : Fin (r.value.length + 1)) <
            ⟨z.val - l.value.length, by
              have := z.isLt
              simp [value_binary] at this
              omega⟩ := by
            rw [Fin.lt_def]
            dsimp
            omega
          exact ihr.1 _ _ _ hxy_r hyz_r hrel_xy_r hrel_yz_r
    · intro x y u v hxy huv hrel_xy hrel_uv hrel_xu
      rcases splitRelation_binary_cases hxy hrel_xy with hy_lt | hx_gt
      · have hu_lt : u.val < l.value.length := by
          rcases lt_trichotomy x u with hxu | rxu | hux
          · rcases splitRelation_binary_cases hxu hrel_xu with hu_lt' | hx_gt'
            · exact hu_lt'
            · omega
          · rw [← rxu]
            omega
          · have hrel_ux : SplitRelation (treeToSplit (.binary l r)) u x := by
              rw [splitRelation_comm]
              exact hrel_xu
            rcases splitRelation_binary_cases hux hrel_ux with hx_lt' | hu_gt'
            · omega
            · omega
        rcases splitRelation_binary_cases huv hrel_uv with hv_lt | hu_gt
        · have h_wl_xy := wordLabeling_binary_left eval hmul l r x y hxy.le (by omega)
          have h_wl_uv := wordLabeling_binary_left eval hmul l r u v huv.le (by omega)
          rw [h_wl_xy, h_wl_uv]
          have hrel_xy_l := splitRelation_binary_left hxy hy_lt hrel_xy
          have hrel_uv_l := splitRelation_binary_left huv hv_lt hrel_uv
          have hrel_xu_l : SplitRelation (treeToSplit l) ⟨x.val, by omega⟩ ⟨u.val, by omega⟩ := by
            rcases lt_trichotomy x u with hxu | rxu | hux
            · exact splitRelation_binary_left hxu hu_lt hrel_xu
            · subst rxu
              exact splitRelation_refl _ _
            · have hrel_ux : SplitRelation (treeToSplit (.binary l r)) u x := by
                rw [splitRelation_comm]
                exact hrel_xu
              have := splitRelation_binary_left hux (by omega) hrel_ux
              rwa [splitRelation_comm]
          have hxy_l : (⟨x.val, by omega⟩ : Fin (l.value.length + 1)) < ⟨y.val, by omega⟩ := hxy
          have huv_l : (⟨u.val, by omega⟩ : Fin (l.value.length + 1)) < ⟨v.val, by omega⟩ := huv
          exact ihl.2 _ _ _ _ hxy_l huv_l hrel_xy_l hrel_uv_l hrel_xu_l
        · omega
      · have hu_gt : l.value.length < u.val := by
          rcases lt_trichotomy x u with hxu | rxu | hux
          · rcases splitRelation_binary_cases hxu hrel_xu with hu_lt' | hx_gt'
            · omega
            · omega
          · rw [← rxu]
            omega
          · have hrel_ux : SplitRelation (treeToSplit (.binary l r)) u x := by
              rw [splitRelation_comm]
              exact hrel_xu
            rcases splitRelation_binary_cases hux hrel_ux with hx_lt' | hu_gt'
            · omega
            · exact hu_gt'
        rcases splitRelation_binary_cases huv hrel_uv with hv_lt | hu_gt'
        · omega
        · have h_wl_xy := wordLabeling_binary_right eval hmul l r x y hx_gt.le hxy.le
          have h_wl_uv := wordLabeling_binary_right eval hmul l r u v hu_gt.le huv.le
          rw [h_wl_xy, h_wl_uv]
          have hrel_xy_r := splitRelation_binary_right hxy hx_gt hrel_xy
          have hrel_uv_r := splitRelation_binary_right huv hu_gt hrel_uv
          have hrel_xu_r : SplitRelation (treeToSplit r)
              ⟨x.val - l.value.length, by
                have := x.isLt
                simp [value_binary] at this
                omega⟩
              ⟨u.val - l.value.length, by
                have := u.isLt
                simp [value_binary] at this
                omega⟩ := by
            rcases lt_trichotomy x u with hxu | rxu | hux
            · exact splitRelation_binary_right hxu hx_gt hrel_xu
            · subst rxu
              exact splitRelation_refl _ _
            · have hrel_ux : SplitRelation (treeToSplit (.binary l r)) u x := by
                rw [splitRelation_comm]
                exact hrel_xu
              have := splitRelation_binary_right hux hu_gt hrel_ux
              rwa [splitRelation_comm]
          have hxy_r : (⟨x.val - l.value.length, by
              have := x.isLt
              simp [value_binary] at this
              omega⟩ : Fin (r.value.length + 1)) <
            ⟨y.val - l.value.length, by
              have := y.isLt
              simp [value_binary] at this
              omega⟩ := by
            rw [Fin.lt_def]
            dsimp
            omega
          have huv_r : (⟨u.val - l.value.length, by
              have := u.isLt
              simp [value_binary] at this
              omega⟩ : Fin (r.value.length + 1)) <
            ⟨v.val - l.value.length, by
              have := v.isLt
              simp [value_binary] at this
              omega⟩ := by
            rw [Fin.lt_def]
            dsimp
            omega
          exact ihr.2 _ _ _ _ hxy_r huv_r hrel_xy_r hrel_uv_r hrel_xu_r
  | h_idempotent children ih_children =>
    rw [isRamsey_idempotent] at ht
    rcases ht with ⟨hlen, hlist, e, he, he_eval⟩
    have h_ne : ∀ c ∈ children, c.value ≠ [] := fun c hc ↦
      tree_value_ne_nil c ((listIsRamsey_iff eval children).mp hlist c hc)
    have h_ramsey : ∀ c ∈ children, c.IsRamsey eval := (listIsRamsey_iff eval children).mp hlist
    have ih_all : ∀ c ∈ children, IsRamsey (wordLabeling eval hmul c.value) (treeToSplit c) :=
      fun c hc ↦ ih_children c hc eval hmul ((listIsRamsey_iff eval children).mp hlist c hc)
    have h_lt_cases := idempotent_of_lt eval hmul e he children he_eval h_ne h_ramsey ih_all
    refine ⟨?_, ?_⟩
    · intro x y z hxy hyz hrel_xy hrel_yz
      by_cases hx_ht : (treeToSplit (.idempotent children) x).val =
          (idempotent children).height
      · have h_sx_eq_sy : (treeToSplit (.idempotent children) x).val =
            (treeToSplit (.idempotent children) y).val :=
          congrArg Fin.val hrel_xy.1
        have hy_ht : (treeToSplit (.idempotent children) y).val =
            (idempotent children).height := by omega
        rw [treeToSplit_val] at hx_ht hy_ht
        have hx_none : locateCut children x.val = .inl none :=
          lcaHeightRaw_idempotent_eq_height.mp hx_ht
        have hy_none : locateCut children y.val = .inl none :=
          lcaHeightRaw_idempotent_eq_height.mp hy_ht
        have h_slice := eval_slice_of_locateCut_eq_none eval hmul e he children
          he_eval h_ne hxy hx_none hy_none
        have h_val := congrArg (fun w : List A ↦ eval ((w.drop x.val).take (y.val - x.val)))
          (value_idempotent children)
        have h_wl : (wordLabeling eval hmul (idempotent children).value).σ x y = e := by
          dsimp [wordLabeling]
          rw [h_val]
          exact h_slice
        rw [h_wl, he]
      · have hx_lt : (treeToSplit (.idempotent children) x).val <
            (idempotent children).height := by
          have h_le := lcaHeightRaw_le_height (.idempotent children) x.val
          rw [treeToSplit_val] at hx_ht ⊢
          omega
        exact h_lt_cases.1 x y z hxy hyz hx_lt hrel_xy hrel_yz
    · intro x y u v hxy huv hrel_xy hrel_uv hrel_xu
      by_cases hx_ht : (treeToSplit (.idempotent children) x).val =
          (idempotent children).height
      · have h_sx_eq_sy : (treeToSplit (.idempotent children) x).val =
            (treeToSplit (.idempotent children) y).val :=
          congrArg Fin.val hrel_xy.1
        have h_sx_eq_su : (treeToSplit (.idempotent children) x).val =
            (treeToSplit (.idempotent children) u).val :=
          congrArg Fin.val hrel_xu.1
        have h_su_eq_sv : (treeToSplit (.idempotent children) u).val =
            (treeToSplit (.idempotent children) v).val :=
          congrArg Fin.val hrel_uv.1
        have hy_ht : (treeToSplit (.idempotent children) y).val =
            (idempotent children).height := by omega
        have hu_ht : (treeToSplit (.idempotent children) u).val =
            (idempotent children).height := by omega
        have hv_ht : (treeToSplit (.idempotent children) v).val =
            (idempotent children).height := by omega
        rw [treeToSplit_val] at hx_ht hy_ht hu_ht hv_ht
        have hx_none : locateCut children x.val = .inl none :=
          lcaHeightRaw_idempotent_eq_height.mp hx_ht
        have hy_none : locateCut children y.val = .inl none :=
          lcaHeightRaw_idempotent_eq_height.mp hy_ht
        have hu_none : locateCut children u.val = .inl none :=
          lcaHeightRaw_idempotent_eq_height.mp hu_ht
        have hv_none : locateCut children v.val = .inl none :=
          lcaHeightRaw_idempotent_eq_height.mp hv_ht
        have h_slice_xy := eval_slice_of_locateCut_eq_none eval hmul e he children
          he_eval h_ne hxy hx_none hy_none
        have h_slice_uv := eval_slice_of_locateCut_eq_none eval hmul e he children
          he_eval h_ne huv hu_none hv_none
        have h_val_xy := congrArg (fun w : List A ↦ eval ((w.drop x.val).take (y.val - x.val)))
          (value_idempotent children)
        have h_wl_xy : (wordLabeling eval hmul (idempotent children).value).σ x y = e := by
          dsimp [wordLabeling]
          rw [h_val_xy]
          exact h_slice_xy
        have h_val_uv := congrArg (fun w : List A ↦ eval ((w.drop u.val).take (v.val - u.val)))
          (value_idempotent children)
        have h_wl_uv : (wordLabeling eval hmul (idempotent children).value).σ u v = e := by
          dsimp [wordLabeling]
          rw [h_val_uv]
          exact h_slice_uv
        rw [h_wl_xy, h_wl_uv]
      · have hx_lt : (treeToSplit (.idempotent children) x).val <
            (idempotent children).height := by
          have h_le := lcaHeightRaw_le_height (.idempotent children) x.val
          rw [treeToSplit_val] at hx_ht ⊢
          omega
        exact h_lt_cases.2 x y u v hxy huv hx_lt hrel_xy hrel_uv hrel_xu

/-- Lemma 3.5(a) for a semigroup morphism `ϕ : S →ₙ* T`. -/
theorem tree_to_split_isRamsey_mulHom {S T : Type*} [Semigroup S] [Semigroup T]
    [Nonempty T] (ϕ : S →ₙ* T) (t : FactorizationTree S)
    (ht : t.IsRamsey (fun w ↦ if hw : w = [] then Classical.arbitrary T else ϕ (listProdNE w hw))) :
    let eval_T : List S → T :=
      fun w ↦ if hw : w = [] then Classical.arbitrary T else ϕ (listProdNE w hw)
    have hmul_T : ∀ u v, u ≠ [] → v ≠ [] → eval_T (u ++ v) = eval_T u * eval_T v := by
      intro u v hu hv
      dsimp [eval_T]
      rw [dite_eq_right (by simp [hu, hv]), dite_eq_right hu, dite_eq_right hv,
        listProdNE_concat u v hu hv, ϕ.map_mul]
    IsRamsey (wordLabeling eval_T hmul_T t.value) (treeToSplit t) := by
  intro eval_T hmul_T
  exact tree_to_split_isRamsey eval_T hmul_T t ht

end TreeToSplit
