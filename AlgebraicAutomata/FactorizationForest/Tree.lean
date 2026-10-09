module

/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Max
public import AlgebraicAutomata.FactorizationForest.Split
public import AlgebraicAutomata.ForMathlib.Data.List.SemigroupProd
public import AlgebraicAutomata.ForMathlib.Data.List.Slice

@[expose] public section


/-!
# Simon's Factorization Forest Theorem (Tree Version)

Formalization of the tree version of Simon's Factorization Forest Theorem,
constructing a Ramsey factorization tree of height at most `3 * nS S - 1` from
a Ramsey split (`simon_word`).

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

open RamseySplit

/-- Factorization tree over alphabet `A`: leaf, binary concatenation, or idempotent node. -/
inductive FactorizationTree (A : Type*) where
  | leaf (a : A) : FactorizationTree A
  | binary (l r : FactorizationTree A) : FactorizationTree A
  | idempotent (children : List (FactorizationTree A)) : FactorizationTree A

namespace FactorizationTree

section TreeDefinitions

variable {A : Type*}

/-- Yields the list of leaves under `t` in left-to-right order. -/
def value (t : FactorizationTree A) : List A :=
  match t with
  | leaf a => [a]
  | binary l r => value l ++ value r
  | idempotent children =>
    (children.attach.map fun ⟨c, _⟩ => value c).flatten
termination_by t

/-- The yield of a leaf `leaf a` is `[a]`. -/
@[simp]
lemma value_leaf (a : A) : (leaf a).value = [a] := by
  unfold value
  rfl

/-- The yield of a binary node is the concatenation of the yields of its children. -/
@[simp]
lemma value_binary (l r : FactorizationTree A) : (binary l r).value = l.value ++ r.value := by
  rw [value]

/-- Yield of a list of factorization trees, concatenated left to right. -/
def listValue (ts : List (FactorizationTree A)) : List A :=
  (ts.map value).flatten

/-- Concatenation property for `listValue (t :: ts)`. -/
@[simp]
lemma listValue_cons (t : FactorizationTree A) (ts : List (FactorizationTree A)) :
    listValue (t :: ts) = value t ++ listValue ts := rfl

/-- The yield of an idempotent node equals the yield of its children. -/
@[simp]
lemma value_idempotent (children : List (FactorizationTree A)) :
    (idempotent children).value = listValue children := by
  unfold value listValue
  simp

/-- Height of a factorization tree. -/
def height (t : FactorizationTree A) : ℕ :=
  match t with
  | leaf _ => 0
  | binary l r => 1 + max (height l) (height r)
  | idempotent children =>
    1 + (children.attach.map fun ⟨c, _⟩ => height c).foldr max 0
termination_by t

/-- A leaf has height 0. -/
@[simp]
lemma height_leaf (a : A) : (leaf a).height = 0 := by rw [height]

/-- Height of a binary node is $1 + \max(l.height, r.height)$. -/
@[simp]
lemma height_binary (l r : FactorizationTree A) :
  (binary l r).height = 1 + max l.height r.height := by
  rw [height]

/-- Maximum height across a list of factorization trees. -/
def listHeight : List (FactorizationTree A) → ℕ
  | [] => 0
  | t :: ts => max (height t) (listHeight ts)

/-- Height of an idempotent node is $1 + \text{listHeight}(children)$. -/
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

/-- If every tree in `ts` has height $\le H$, then `listHeight ts \le H`. -/
lemma listHeight_le {H : ℕ} : ∀ (ts : List (FactorizationTree A)),
    (∀ t ∈ ts, height t ≤ H) → listHeight ts ≤ H
  | [], _ => Nat.zero_le H
  | t :: ts, h => max_le (h t (.head _)) (listHeight_le ts fun x hx ↦ h x (.tail _ hx))

/-- The height of any element of `ts` is bounded by `listHeight ts`. -/
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

/-- Induction principle for factorization trees. -/
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

/-- Predicate stating that `t` is a Ramsey factorization tree with respect to `eval`. -/
def IsRamsey (eval : List A → S) (t : FactorizationTree A) : Prop :=
  match t with
  | leaf _ => True
  | binary l r => IsRamsey eval l ∧ IsRamsey eval r
  | idempotent children =>
      2 ≤ children.length ∧
      (∀ c ∈ children, IsRamsey eval c) ∧
      ∃ e : S, e * e = e ∧ ∀ t ∈ children, eval (value t) = e
termination_by t

/-- A binary node is Ramsey iff both children are Ramsey. -/
@[simp]
lemma isRamsey_binary (eval : List A → S) (l r : FactorizationTree A) :
    (binary l r).IsRamsey eval ↔ l.IsRamsey eval ∧ r.IsRamsey eval := by rw [IsRamsey]

/-- Predicate stating that all trees in a list are Ramsey. -/
def listIsRamsey (eval : List A → S) : List (FactorizationTree A) → Prop
  | [] => True
  | t :: ts => IsRamsey eval t ∧ listIsRamsey eval ts

/-- Every leaf is trivially Ramsey. -/
lemma leaf_isRamsey (eval : List A → S) (a : A) : (leaf a).IsRamsey eval := by
  simp [IsRamsey]

/-- Constructs a Ramsey binary node from Ramsey children. -/
lemma binary_isRamsey (eval : List A → S) {l r : FactorizationTree A}
    (hl : l.IsRamsey eval) (hr : r.IsRamsey eval) :
    (binary l r).IsRamsey eval := (isRamsey_binary eval l r).mpr ⟨hl, hr⟩

/-- `listIsRamsey eval cs` holds iff every `c ∈ cs` is Ramsey. -/
lemma listIsRamsey_iff (eval : List A → S) :
    ∀ (ts : List (FactorizationTree A)), listIsRamsey eval ts ↔ ∀ t ∈ ts, t.IsRamsey eval
  | [] => by simp [listIsRamsey]
  | t :: ts => by simp [listIsRamsey, listIsRamsey_iff eval ts]

/-- An idempotent node is Ramsey iff all children are Ramsey and yield identical values. -/
@[simp]
lemma isRamsey_idempotent (eval : List A → S) (children : List (FactorizationTree A)) :
    (idempotent children).IsRamsey eval ↔
      2 ≤ children.length ∧
      listIsRamsey eval children ∧
      ∃ e : S, e * e = e ∧ ∀ t ∈ children, eval (value t) = e := by
  unfold IsRamsey
  rw [listIsRamsey_iff]

/-- Membership characterization for elements of `listValue cs`. -/
lemma mem_listValue {cs : List (FactorizationTree A)} {x : A}
    (h : x ∈ listValue cs) : ∃ c ∈ cs, x ∈ c.value := by
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
  exact ⟨c, hc, hx⟩

/-- A Ramsey factorization tree yields a non-empty word. -/
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


section SplitToTree

variable {A S : Type*} [Semigroup S]
variable (eval : List A → S)
variable (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
variable (u : List A)

/-- Constructs a factorization tree from an inner split step. -/
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
          by_contra
          have hx_mem : x ∈ S_cuts :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨hix, hxk.trans hkj, by omega⟩⟩
          have h_min := Finset.min'_le S_cuts x hx_mem
          omega
        obtain ⟨t_outer, ht_outer_val, ht_outer_ramsey, ht_outer_height⟩ := ih i k hik h_less
        have h_len : (j : ℕ) - (k : ℕ) < len := by omega
        obtain ⟨trees_inner, h_inner_ne, h_inner_val, h_inner_ramsey,
                h_inner_eval, h_inner_height, _⟩ :=
          ih_strong ((j : ℕ) - (k : ℕ)) h_len k j hkj rfl hsk hsj
            (fun x hkx hxj => h_between x (hik.trans hkx) hxj)
        have h_rel_ik : SplitRelation s i k := by
          apply splitRelation_of_le_between s hik (by grind)
          intro z hz1 hz2
          grind [h_between z hz1 (hz2.trans hkj)]
        have h_rel_kj : SplitRelation s k j := by
          apply splitRelation_of_le_between s hkj (by grind)
          intro z hz1 hz2
          grind [h_between z (hik.trans hz1) hz2]
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
        exact ⟨[t_outer], by simp, by simp [FactorizationTree.listValue, ht_outer_val],
          ⟨ht_outer_ramsey, trivial⟩, List.forall_mem_singleton.2 (ht_outer_val.symm ▸ rfl),
          List.forall_mem_singleton.2 ht_outer_height, fun hc ↦ (h_cut hc).elim⟩
  intro hij hsi hsj h_between
  exact H ((j : ℕ) - (i : ℕ)) i j hij rfl hsi hsj h_between

/-- Constructs a factorization tree from an outer split step. -/
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
    have hj_eq : (j : ℕ) = (i : ℕ) + 1 := by
      by_contra
      let x : Fin (u.length + 1) := ⟨i.val + 1, by omega⟩
      have := h_less x (by grind) (by grind)
      omega
    have hi_lt : (i : ℕ) < u.length := by
      have hj_lt := j.isLt
      omega
    let t := FactorizationTree.leaf u[i.val]
    have ht_val : t.value = (u.drop i).take (j - i) := by
      simp only [FactorizationTree.value_leaf, t]
      rw [hj_eq]
      have h_diff : (i : ℕ) + 1 - (i : ℕ) = 1 := by omega
      exact h_diff.symm ▸ (list_drop_take_one u i.val hi_lt).symm
    exact ⟨t, ht_val, FactorizationTree.leaf_isRamsey eval _, by simp [t]⟩
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
            have h_rel_12 : SplitRelation s k_1 k_2 := by
              apply splitRelation_of_le_between s hk12 (by grind)
              intro x hx1 hx2
              have := h_less x (hik1.trans hx1) (hx2.trans (hk2r.trans hkrj))
              grind
            have h_rel_2r : SplitRelation s k_2 k_r := by
              apply splitRelation_of_le_between s hk2r (by grind)
              intro x hx1 hx2
              have := h_less x ((hik1.trans hk12).trans hx1) (hx2.trans hkrj)
              grind
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
            use .idempotent trees
            constructor
            · rw [FactorizationTree.value_idempotent]
              exact h_trees_val
            constructor
            · rw [FactorizationTree.isRamsey_idempotent]
              exact ⟨h_len2, h_trees_ramsey, _, h_idem_1r, h_trees_eval⟩
            · rw [FactorizationTree.height_idempotent]
              have h_le := FactorizationTree.listHeight_le trees (fun t ht => h_trees_height t ht)
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

/-- Simon's Factorization Forest Theorem for finite semigroups with evaluation map. -/
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
            (fun x _ _ ↦ Fin.le_iff_val_le_val.2 (hk2_prop ▸ h_bound_all x))
        obtain ⟨-, -, -, h_idem_ir, -⟩ :=
          isRamsey_idem_step h_ramsey hik2 hk2r h_rel_i2 h_rel_2r
        have h_inner := split_to_tree_inner eval hmul u m hm_lt s h_ramsey
          (fun a b hab hless => split_to_tree_outer eval hmul u s h_ramsey m hm_lt.le a b hab hless)
          i k_r hikr hsi hskr (fun x _ _ => h_bound_all x)
        obtain ⟨trees, _, h_trees_val, h_trees_ramsey, h_trees_eval,
                h_trees_height, h_trees_len⟩ := h_inner
        have h_len2 : 2 ≤ trees.length := h_trees_len ⟨k_2, hik2, hk2r, hk2_prop⟩
        use .idempotent trees
        constructor
        · rw [FactorizationTree.value_idempotent]
          exact h_trees_val
        constructor
        · rw [FactorizationTree.isRamsey_idempotent]
          exact ⟨h_len2, h_trees_ramsey, _, h_idem_ir, h_trees_eval⟩
        · rw [FactorizationTree.height_idempotent]
          have h_le := FactorizationTree.listHeight_le trees (fun t ht => h_trees_height t ht)
          omega
    obtain ⟨t_mid, ht_mid_val, ht_mid_ramsey, _⟩ := h_mid
    have ht_val : (FactorizationTree.binary t_mid t_krj).value = u := by
      simp [ht_mid_val, ht_krj_val, list_drop_take_append u i.val k_r.val j.val hikr.le hkrj.le,
        h_u_val]
    exact ⟨.binary t_mid t_krj, ht_val,
      FactorizationTree.binary_isRamsey eval ht_mid_ramsey ht_krj_ramsey, by
        simp
        grind⟩

/-- Simon's Factorization Forest Theorem for semigroup homomorphisms. -/
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

/-- Classical height bound $3|S| - 1$ for factorization trees. -/
theorem factorization_forest_classical_bound {A S : Type*} [Semigroup S] [Fintype S]
    [Nonempty S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ t : FactorizationTree A,
      t.value = u ∧
      t.IsRamsey eval ∧
      t.height ≤ 3 * Fintype.card S - 1 := by
  grind [nS_le_card, factorization_forest_theorem eval hmul u hu]

/-- Classical height bound $3|S| - 1$ for semigroup homomorphisms. -/
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

/-- Locates the child containing index `i` in a list of trees. -/
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

/-- Raw lowest-common-ancestor height for cut index `i`. -/
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

/-- Bounded lowest-common-ancestor height in `Fin (t.height + 1)`. -/
def lcaHeight (t : FactorizationTree A) (i : ℕ) : Fin (t.height + 1) :=
  ⟨min (lcaHeightRaw t i) t.height, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- Constructs a split function from a factorization tree via LCA heights. -/
def treeToSplit (t : FactorizationTree A) : Split (Fin (t.value.length + 1)) (t.height + 1) :=
  fun i ↦ lcaHeight t i.val

/-- The raw LCA height at index `i` is at most the height of `t`. -/
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

/-- Evaluation of `treeToSplit t` at index `i`. -/
@[simp]
lemma treeToSplit_val (t : FactorizationTree A) (i : Fin (t.value.length + 1)) :
    (treeToSplit t i).val = lcaHeightRaw t i.val := by
  dsimp [treeToSplit]
  dsimp [lcaHeight]
  rw [min_eq_left (lcaHeightRaw_le_height t i)]

/-- LCA height in the left child of a binary node. -/
lemma lcaHeightRaw_binary_left (l r : FactorizationTree A) {i : ℕ} (hi : i < l.value.length) :
    lcaHeightRaw (.binary l r) i = lcaHeightRaw l i := by
  rw [lcaHeightRaw]
  split_ifs
  rfl

/-- LCA height in the right child of a binary node. -/
lemma lcaHeightRaw_binary_right (l r : FactorizationTree A) {i : ℕ} (hi : l.value.length < i) :
    lcaHeightRaw (.binary l r) i = lcaHeightRaw r (i - l.value.length) := by
  rw [lcaHeightRaw]
  grind

/-- LCA height of an index different from the split point is strictly less than node height. -/
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

/-- Symmetry of `SplitRelation`. -/
lemma splitRelation_comm {α : Type*} [LinearOrder α] {h : ℕ} (s : Split α h) (x y : α) :
    SplitRelation s x y ↔ SplitRelation s y x := by grind

/-- Reflexivity of `SplitRelation`. -/
lemma splitRelation_refl {α : Type*} [LinearOrder α] {h : ℕ} (s : Split α h) (x : α) :
    SplitRelation s x x := by grind

/-- Intermediate strictly smaller rank breaks `SplitRelation`. -/
lemma not_splitRelation_of_between_lt {α : Type*} [LinearOrder α] {h : ℕ} (s : Split α h)
    {x y z : α} (hxz : x ≤ z) (hzy : z ≤ y) (hlt : s x < s z) : ¬ SplitRelation s x y := by
  grind

/-- Cases for `SplitRelation` under binary tree concatenation. -/
lemma splitRelation_binary_cases {l r : FactorizationTree A}
    {x y : Fin ((binary l r).value.length + 1)} (hxy : x < y)
    (hrel : SplitRelation (treeToSplit (.binary l r)) x y) :
    y.val < l.value.length ∨ l.value.length < x.val := by
  by_contra! ⟨hy, hx⟩
  let mid : Fin ((binary l r).value.length + 1) := ⟨l.value.length, by omega⟩
  have h_mid : (treeToSplit (.binary l r) mid).val = (binary l r).height := by
    rw [treeToSplit_val, lcaHeightRaw]
    grind
  rcases lt_or_eq_of_le hx with hx_lt | hx_eq
  · have hlt : treeToSplit (.binary l r) x < treeToSplit (.binary l r) mid := by
      rw [Fin.lt_def, h_mid, treeToSplit_val]
      exact lcaHeightRaw_binary_lt l r (by omega)
    exact not_splitRelation_of_between_lt (treeToSplit (.binary l r))
      (by grind) (by grind) hlt hrel
  · have hy_ht : (treeToSplit (.binary l r) y).val < (binary l r).height := by
      rw [treeToSplit_val]
      exact lcaHeightRaw_binary_lt l r (by omega)
    have h_eq := congrArg Fin.val hrel.1
    rw [show x = mid from Fin.ext hx_eq, h_mid] at h_eq
    omega

/-- `SplitRelation` restricted to the left child of a binary node. -/
lemma splitRelation_binary_left {l r : FactorizationTree A}
    {x y : Fin ((binary l r).value.length + 1)} (hxy : x < y)
    (hy : y.val < l.value.length)
    (hrel : SplitRelation (treeToSplit (.binary l r)) x y) :
    SplitRelation (treeToSplit l)
      ⟨x.val, by omega⟩
      ⟨y.val, by omega⟩ := by
  apply splitRelation_of_le_between (treeToSplit l)
  · exact hxy
  · grind [hrel.1, treeToSplit_val, lcaHeightRaw_binary_left]
  · intro z _ _
    grind [hrel.2 ⟨z.val, by grind⟩, treeToSplit_val, lcaHeightRaw_binary_left]

/-- `SplitRelation` restricted to the right child of a binary node. -/
lemma splitRelation_binary_right {l r : FactorizationTree A}
    {x y : Fin ((binary l r).value.length + 1)} (hxy : x < y)
    (hx : l.value.length < x.val)
    (hrel : SplitRelation (treeToSplit (.binary l r)) x y) :
    SplitRelation (treeToSplit r)
      ⟨x.val - l.value.length, by grind [value_binary]⟩
      ⟨y.val - l.value.length, by grind [value_binary]⟩ := by
  apply splitRelation_of_le_between (treeToSplit r)
  · grind
  · grind [hrel.1, treeToSplit_val, lcaHeightRaw_binary_right]
  · intro z _ _
    grind [hrel.2 ⟨z.val + l.value.length, by grind⟩, treeToSplit_val, lcaHeightRaw_binary_right]

/-- Word labeling on the left component of a binary node. -/
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
  simp
  grind

/-- Word labeling on the right component of a binary node. -/
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
        grind [value_binary]⟩
      ⟨y.val - l.value.length, by
        grind [value_binary]⟩ := by
  grind only [locateCut, value_binary, list_drop_take_append_right _ _ _ _ hx]

/-- LCA height at child boundaries in an idempotent node equals node height. -/
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

/-- Locating a cut at the boundary between children. -/
lemma locateCut_cons_mid (c : FactorizationTree A) (cs : List (FactorizationTree A))
    (hcs : cs ≠ []) :
    locateCut (c :: cs) c.value.length = .inl none := by
  grind only [locateCut]

/-- Locating a cut strictly within the head child. -/
lemma locateCut_cons_left (c : FactorizationTree A) (cs : List (FactorizationTree A))
    {i : ℕ} (hi : i < c.value.length) :
    locateCut (c :: cs) i = .inl (some (⟨c, by simp⟩, i)) := by
  grind only [locateCut]

/-- LCA height within the head child in an idempotent node. -/
lemma lcaHeightRaw_idempotent_cons_left (c : FactorizationTree A) (cs : List (FactorizationTree A))
    {i : ℕ} (hi : i < c.value.length) :
    lcaHeightRaw (.idempotent (c :: cs)) i = lcaHeightRaw c i := by
  rw [lcaHeightRaw, locateCut_cons_left c cs hi]

/-- LCA height within head child is strictly less than idempotent node height. -/
lemma lcaHeightRaw_idempotent_cons_left_lt (c : FactorizationTree A)
    (cs : List (FactorizationTree A)) {i : ℕ} (hi : i < c.value.length) :
    lcaHeightRaw (.idempotent (c :: cs)) i < (idempotent (c :: cs)).height := by
  rw [lcaHeightRaw_idempotent_cons_left c cs hi, height_idempotent]
  have h1 := lcaHeightRaw_le_height c i
  have h2 : c.height ≤ listHeight (c :: cs) := height_le_listHeight (by simp)
  omega

/-- Locating cut at the end of a singleton child list. -/
lemma locateCut_singleton_length (c : FactorizationTree A) :
    locateCut [c] c.value.length = .inr () := by
  grind only [locateCut]

/-- LCA height at the end of a singleton child list. -/
lemma lcaHeightRaw_idempotent_singleton_length (c : FactorizationTree A) :
    lcaHeightRaw (.idempotent [c]) c.value.length = 0 := by
  rw [lcaHeightRaw, locateCut_singleton_length]

/-- Locating a cut within remaining children. -/
lemma locateCut_cons_right (c : FactorizationTree A) (cs : List (FactorizationTree A))
    {i : ℕ} (hi : c.value.length < i) :
    locateCut (c :: cs) i =
      match locateCut cs (i - c.value.length) with
      | .inr () => .inr ()
      | .inl none => .inl none
      | .inl (some (⟨c', hc'⟩, idx)) => .inl (some (⟨c', by simp [hc']⟩, idx)) := by
  cases cs <;> grind only [locateCut]

/-- Locating a cut at the yield length of a list of trees. -/
lemma locateCut_at_length (cs : List (FactorizationTree A))
    (h_ne : ∀ c ∈ cs, c.value ≠ []) :
    locateCut cs (listValue cs).length = .inr () := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil =>
      have : (listValue [c]).length = c.value.length := by simp [listValue]
      rw [this, locateCut_singleton_length]
    | cons c' cs' =>
      have h_gt : c.value.length < (listValue (c :: c' :: cs')).length := by
        have hc' := h_ne c' (by simp)
        cases h : c'.value
        · contradiction
        · simp [listValue_cons, h]
      have h_sub : (listValue (c :: c' :: cs')).length - c.value.length =
          (listValue (c' :: cs')).length := by
        simp [listValue_cons]
      rw [locateCut_cons_right c (c' :: cs') h_gt, h_sub,
        ih (fun d hd ↦ h_ne d (by simp [hd]))]

/-- LCA height at the right boundary of a tree. -/
lemma lcaHeightRaw_at_length {S : Type*} [Semigroup S] {eval : List A → S} (t : FactorizationTree A)
    (ht : t.IsRamsey eval) :
    lcaHeightRaw t t.value.length = 0 := by
  induction t using FactorizationTree.induction_on with
  | h_leaf a => rw [lcaHeightRaw]
  | h_binary l r ih_l ih_r =>
    rw [isRamsey_binary] at ht
    have hr : l.value.length < (binary l r).value.length := by
      cases h : r.value
      · exact nomatch (tree_value_ne_nil r ht.2 h)
      · rw [value_binary, List.length_append, h, List.length_cons]
        omega
    rw [lcaHeightRaw_binary_right l r hr]
    have h_sub : (binary l r).value.length - l.value.length = r.value.length := by
      rw [value_binary, List.length_append]
      omega
    rw [h_sub, ih_r ht.2]
  | h_idempotent children ih =>
    rw [isRamsey_idempotent] at ht
    have h_ne c hc := tree_value_ne_nil c ((listIsRamsey_iff eval children).mp ht.2.1 c hc)
    rw [lcaHeightRaw, value_idempotent, locateCut_at_length children h_ne]

/-- Cases for `SplitRelation` under idempotent nodes. -/
lemma splitRelation_idempotent_cases {c : FactorizationTree A} {cs : List (FactorizationTree A)}
    (hcs : cs ≠ [])
    {x y : Fin ((idempotent (c :: cs)).value.length + 1)} (_hxy : x < y)
    (hrel : SplitRelation (treeToSplit (.idempotent (c :: cs))) x y) :
    y.val < c.value.length ∨ c.value.length ≤ x.val := by
  by_contra! ⟨hy, hx⟩
  let mid : Fin ((idempotent (c :: cs)).value.length + 1) :=
    ⟨c.value.length, by omega⟩
  have h_mid : (treeToSplit (.idempotent (c :: cs)) mid).val = (idempotent (c :: cs)).height := by
    rw [treeToSplit_val, lcaHeightRaw, locateCut_cons_mid c cs hcs]
  have hlt : treeToSplit (.idempotent (c :: cs)) x < treeToSplit (.idempotent (c :: cs)) mid := by
    rw [Fin.lt_def, h_mid, treeToSplit_val]
    exact lcaHeightRaw_idempotent_cons_left_lt c cs hx
  exact not_splitRelation_of_between_lt (treeToSplit (.idempotent (c :: cs)))
    (by grind) (by grind) hlt hrel

/-- Word labeling within the head child of an idempotent node. -/
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
  simp only [value_idempotent, listValue_cons, list_drop_take_append_left _ _ _ _ hy]

/-- `SplitRelation` within the head child of an idempotent node. -/
lemma splitRelation_idempotent_left {c : FactorizationTree A}
    {cs : List (FactorizationTree A)}
    {x y : Fin ((idempotent (c :: cs)).value.length + 1)} (hxy : x < y)
    (hy : y.val < c.value.length)
    (hrel : SplitRelation (treeToSplit (.idempotent (c :: cs))) x y) :
    SplitRelation (treeToSplit c)
      ⟨x.val, by omega⟩
      ⟨y.val, by omega⟩ := by
  apply splitRelation_of_le_between (treeToSplit c)
  · exact hxy
  · grind [hrel.1, treeToSplit_val, lcaHeightRaw_idempotent_cons_left]
  · intro z _ _
    grind [hrel.2 ⟨z.val, by grind [value_idempotent, listValue]⟩, treeToSplit_val,
      lcaHeightRaw_idempotent_cons_left]

/-- LCA height for indices past the head child. -/
lemma lcaHeightRaw_idempotent_cons_right_of_lt (c : FactorizationTree A)
    (cs : List (FactorizationTree A)) {i : ℕ} (hi : c.value.length < i)
    (hlt : lcaHeightRaw (.idempotent (c :: cs)) i < (idempotent (c :: cs)).height) :
    lcaHeightRaw (.idempotent (c :: cs)) i =
    lcaHeightRaw (.idempotent cs) (i - c.value.length) := by
  rw [lcaHeightRaw, locateCut_cons_right c cs hi] at hlt ⊢
  rw [lcaHeightRaw]
  grind

/-- Length equation for cons in idempotent nodes. -/
lemma length_idempotent_cons (c : FactorizationTree A) (cs : List (FactorizationTree A)) :
    (idempotent (c :: cs)).value.length = c.value.length + (idempotent cs).value.length := by
  simp only [value_idempotent, listValue_cons, List.length_append]

/-- Word labeling for indices past the head child in an idempotent node. -/
lemma wordLabeling_idempotent_cons_right {S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (c : FactorizationTree A) (cs : List (FactorizationTree A))
    (x y : Fin ((idempotent (c :: cs)).value.length + 1))
    (hx : c.value.length ≤ x.val)
    (hxy : x.val ≤ y.val) :
    (wordLabeling eval hmul (idempotent (c :: cs)).value).σ x y =
    (wordLabeling eval hmul (idempotent cs).value).σ
      ⟨x.val - c.value.length, by grind [length_idempotent_cons]⟩
      ⟨y.val - c.value.length, by grind [length_idempotent_cons]⟩ := by
  simp only [value_idempotent, listValue_cons, list_drop_take_append_right _ _ _ _ hx,
    show y.val - c.value.length - (x.val - c.value.length) = y.val - x.val by omega]

/-- `SplitRelation` for indices past the head child in an idempotent node. -/
lemma splitRelation_idempotent_cons_right {c : FactorizationTree A}
    {cs : List (FactorizationTree A)}
    {x y : Fin ((idempotent (c :: cs)).value.length + 1)} (hxy : x < y)
    (hx : c.value.length < x.val)
    (hx_lt : (treeToSplit (.idempotent (c :: cs)) x).val < (idempotent (c :: cs)).height)
    (hrel : SplitRelation (treeToSplit (.idempotent (c :: cs))) x y) :
    SplitRelation (treeToSplit (.idempotent cs))
      ⟨x.val - c.value.length, by grind [length_idempotent_cons]⟩
      ⟨y.val - c.value.length, by grind [length_idempotent_cons]⟩ := by
  have hy : c.value.length < y.val := by omega
  have H_val (z : Fin ((idempotent (c :: cs)).value.length + 1))
      (hz : c.value.length < z.val)
      (hz_lt : (treeToSplit (.idempotent (c :: cs)) z).val < (idempotent (c :: cs)).height) :
      (treeToSplit (.idempotent (c :: cs)) z).val =
      (treeToSplit (.idempotent cs)
        ⟨z.val - c.value.length, by grind [length_idempotent_cons]⟩).val := by
    rw [treeToSplit_val, treeToSplit_val]
    rw [treeToSplit_val] at hz_lt
    exact lcaHeightRaw_idempotent_cons_right_of_lt c cs hz hz_lt
  have hy_lt : (treeToSplit (.idempotent (c :: cs)) y).val < (idempotent (c :: cs)).height :=
    (congrArg Fin.val hrel.1).symm ▸ hx_lt
  apply splitRelation_of_le_between (treeToSplit (.idempotent cs))
  · grind
  · ext
    rw [← H_val x hx hx_lt, ← H_val y hy hy_lt]
    exact congrArg Fin.val hrel.1
  · intro z _ _
    let z_idem : Fin ((idempotent (c :: cs)).value.length + 1) :=
      ⟨z.val + c.value.length, by grind [length_idempotent_cons]⟩
    have h_bet := hrel.2 z_idem (by grind) (by grind)
    rw [min_eq_left hxy.le] at h_bet
    have hz_idem_lt : (treeToSplit (.idempotent (c :: cs)) z_idem).val <
        (idempotent (c :: cs)).height :=
      (Fin.le_iff_val_le_val.mp h_bet).trans_lt hx_lt
    have h_gt : c.value.length < z_idem.val := by
      dsimp [z_idem]
      omega
    have h1 := H_val z_idem h_gt hz_idem_lt
    have h2 := H_val x hx hx_lt
    have hz_eq : (⟨z_idem.val - c.value.length, by grind [length_idempotent_cons]⟩ :
        Fin ((idempotent cs).value.length + 1)) = z := by
      ext
      dsimp [z_idem]
      omega
    rw [hz_eq] at h1
    have h_bet_val := Fin.le_iff_val_le_val.mp h_bet
    rw [h1, h2] at h_bet_val
    exact Fin.le_iff_val_le_val.mpr h_bet_val

/-- Singleton `locateCut` cannot return `none` on valid indices. -/
lemma locateCut_singleton_ne_inl_none (c : FactorizationTree A) (i : ℕ) :
    locateCut [c] i ≠ .inl none := by
  grind only [locateCut]

/-- Characterization of boundary cuts between consecutive children. -/
lemma locateCut_cons_cons_inl_none_iff (c c' : FactorizationTree A)
    (cs : List (FactorizationTree A)) (i : ℕ) :
    locateCut (c :: c' :: cs) i = .inl none ↔
    i = c.value.length ∨ (c.value.length < i ∧ locateCut (c' :: cs)
    (i - c.value.length) = .inl none) := by
  grind only [locateCut]

/-- `locateCut` on empty list yields `inr ()`. -/
lemma locateCut_nil (i : ℕ) : locateCut ([] : List (FactorizationTree A)) i = .inr () := rfl

/-- Evaluation of prefix up to a cut boundary equals child evaluations. -/
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
  | nil => cases hi
  | cons c cs' ih =>
    cases cs' with
    | nil => exact (locateCut_singleton_ne_inl_none c i hi).elim
    | cons c' cs'' =>
      rw [locateCut_cons_cons_inl_none_iff] at hi
      rw [listValue_cons]
      rcases hi with rfl | ⟨h_gt, _⟩
      · grind
      · grind [List.take_append, List.take_of_length_le h_gt.le]

/-- Evaluation of slice between cut boundaries equals child evaluation. -/
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
  | nil => cases hx
  | cons c cs' ih =>
    cases cs' with
    | nil => exact (locateCut_singleton_ne_inl_none c x hx).elim
    | cons c' cs'' =>
      rw [locateCut_cons_cons_inl_none_iff] at hx hy
      rcases hx with rfl | ⟨hx_gt, hx_tail⟩
      · rw [listValue_cons, List.drop_left]
        grind [eval_take_of_locateCut_eq_none eval hmul e he (c' :: cs'')]
      · rw [listValue_cons, list_drop_take_append_right _ _ _ _ hx_gt.le]
        have : y - x = (y - c.value.length) - (x - c.value.length) := by omega
        rw [this]
        exact ih (fun z hz ↦ h_eval z (.tail _ hz)) (fun z hz ↦ h_ne z (.tail _ hz))
          (by omega) hx_tail (hy.resolve_left (by omega)).2

/-- The split induced by a leaf is Ramsey. -/
lemma treeToSplit_leaf_isRamsey {S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (a : A) :
    IsRamsey (wordLabeling eval hmul (FactorizationTree.leaf a).value) (treeToSplit (.leaf a)) := by
  constructor
  · intro x y z _ _ _ _
    have := z.isLt
    grind [value_leaf]
  · intro x y u v _ _ _ _ _
    have := y.isLt
    have := v.isLt
    grind [value_leaf]

/-- Adjacent points of maximal rank evaluate to the same idempotent value. -/
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
  | nil => grind [value_idempotent, listValue]
  | cons c cs ih_cs =>
    intro h_eval h_ne h_ramsey ih_trees
    have hc_ramsey := h_ramsey c (.head _)
    have ih_c := ih_trees c (.head _)
    have ih_tail := ih_cs (fun d hd ↦ h_eval d (.tail _ hd))
      (fun d hd ↦ h_ne d (.tail _ hd))
      (fun d hd ↦ h_ramsey d (.tail _ hd))
      (fun d hd ↦ ih_trees d (.tail _ hd))
    have h_gt {w : Fin ((idempotent (c :: cs)).value.length + 1)}
        (hw_ge : c.value.length ≤ w.val)
        (hw_lt : (treeToSplit (.idempotent (c :: cs)) w).val < (idempotent (c :: cs)).height)
        (hcs_ne : cs ≠ []) : c.value.length < w.val := by
      by_contra!
      have hw_eq : w.val = c.value.length := by omega
      have h_ht : (treeToSplit (.idempotent (c :: cs)) w).val = (idempotent (c :: cs)).height := by
        rw [treeToSplit_val, hw_eq, lcaHeightRaw, locateCut_cons_mid c cs hcs_ne]
      omega
    have h_cs_lt {w : Fin ((idempotent (c :: cs)).value.length + 1)}
        (hw_gt : c.value.length < w.val)
        (hw_lt : (treeToSplit (.idempotent (c :: cs)) w).val < (idempotent (c :: cs)).height) :
        (treeToSplit (.idempotent cs) ⟨w.val - c.value.length, by
          have := w.isLt
          have := length_idempotent_cons c cs
          omega⟩).val < (idempotent cs).height := by
      rw [treeToSplit_val]
      have h1 : lcaHeightRaw (.idempotent cs) (w.val - c.value.length) =
          lcaHeightRaw (.idempotent (c :: cs)) w.val := by
        have := lcaHeightRaw_idempotent_cons_right_of_lt c cs hw_gt
        rw [treeToSplit_val] at hw_lt
        exact (this hw_lt).symm
      rw [h1]
      by_contra! h_ge
      have h_none : locateCut cs (w.val - c.value.length) = .inl none :=
        lcaHeightRaw_idempotent_eq_height.mp (by
          have := lcaHeightRaw_le_height (.idempotent cs) (w.val - c.value.length)
          omega)
      have h_top : lcaHeightRaw (.idempotent (c :: cs)) w.val = (idempotent (c :: cs)).height := by
        rw [lcaHeightRaw, locateCut_cons_right c cs hw_gt, h_none]
      rw [treeToSplit_val] at hw_lt
      omega
    by_cases hcs_emp : cs = []
    · subst hcs_emp
      let toC (w : Fin ((idempotent [c]).value.length + 1)) : Fin (c.value.length + 1) :=
        ⟨w.val, by
          have := w.isLt
          simp [value_idempotent, listValue] at this
          omega⟩
      have h_split_val (i : Fin ((idempotent [c]).value.length + 1)) :
          (treeToSplit (.idempotent [c]) i).val = (treeToSplit c (toC i)).val := by
        simp only [treeToSplit_val]
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ (toC i).isLt) with h | h
        · rw [lcaHeightRaw_idempotent_cons_left c [] h]
        · rw [h, lcaHeightRaw_idempotent_singleton_length, lcaHeightRaw_at_length c hc_ramsey]
      have h_rel_to_c {a b : Fin ((idempotent [c]).value.length + 1)}
          (hrel : SplitRelation (treeToSplit (.idempotent [c])) a b) :
          SplitRelation (treeToSplit c) (toC a) (toC b) := by
        constructor
        · exact Fin.ext (by rw [← h_split_val, ← h_split_val, congrArg Fin.val hrel.1])
        · intro z hz1 hz2
          have hz1_idem : min a b ≤ ⟨z.val, by simp [value_idempotent, listValue]⟩ := hz1
          have hz2_idem : ⟨z.val, by simp [value_idempotent, listValue]⟩ ≤ max a b := hz2
          have h_bet := hrel.2 _ hz1_idem hz2_idem
          have h_bet_val := Fin.le_def.mp h_bet
          have hz_eq : toC ⟨z.val, by simp [value_idempotent, listValue]⟩ = z := rfl
          rw [h_split_val ⟨z.val, _⟩, hz_eq] at h_bet_val
          grind
      constructor
      · intro x y z hxy hyz hx_lt hrel_xy hrel_yz
        rw [wordLabeling_idempotent_left eval hmul c [] x y hxy.le (Nat.le_of_lt_succ (toC y).isLt)]
        exact ih_c.1 _ _ _ hxy hyz (h_rel_to_c hrel_xy) (h_rel_to_c hrel_yz)
      · intro x y u v hxy huv hx_lt hrel_xy hrel_uv hrel_xu
        rw [wordLabeling_idempotent_left eval hmul c [] x y hxy.le (Nat.le_of_lt_succ (toC y).isLt),
            wordLabeling_idempotent_left eval hmul c [] u v huv.le
              (Nat.le_of_lt_succ (toC v).isLt)]
        exact ih_c.2 _ _ _ _ hxy huv (h_rel_to_c hrel_xy) (h_rel_to_c hrel_uv) (h_rel_to_c hrel_xu)
    · constructor
      · intro x y z hxy hyz hx_lt hrel_xy hrel_yz
        rcases splitRelation_idempotent_cases hcs_emp hxy hrel_xy with hy_lt | hx_ge
        · have hz_lt : z.val < c.value.length := by
            rcases splitRelation_idempotent_cases hcs_emp hyz hrel_yz with h | h <;> omega
          rw [wordLabeling_idempotent_left eval hmul c cs x y hxy.le hy_lt.le]
          exact ih_c.1 _ _ _ hxy hyz
            (splitRelation_idempotent_left hxy hy_lt hrel_xy)
            (splitRelation_idempotent_left hyz hz_lt hrel_yz)
        · have hx_gt := h_gt hx_ge hx_lt hcs_emp
          have hy_gt : c.value.length < y.val := by omega
          have hy_lt_ht :
            (treeToSplit (.idempotent (c :: cs)) y).val < (idempotent (c :: cs)).height :=
            (congrArg Fin.val hrel_xy.1).symm ▸ hx_lt
          rw [wordLabeling_idempotent_cons_right eval hmul c cs x y hx_ge hxy.le]
          exact ih_tail.1 _ _ _ (Fin.lt_def.2 (by grind)) (Fin.lt_def.2 (by grind))
            (h_cs_lt hx_gt hx_lt)
            (splitRelation_idempotent_cons_right hxy hx_gt hx_lt hrel_xy)
            (splitRelation_idempotent_cons_right hyz hy_gt hy_lt_ht hrel_yz)
      · intro x y u v hxy huv hx_lt hrel_xy hrel_uv hrel_xu
        rcases splitRelation_idempotent_cases hcs_emp hxy hrel_xy with hy_lt | hx_ge
        · have hu_lt : u.val < c.value.length := by
            by_cases h : x < u
            · rcases splitRelation_idempotent_cases hcs_emp h hrel_xu with h' | h' <;> omega
            · omega
          have hv_lt : v.val < c.value.length := by
            rcases splitRelation_idempotent_cases hcs_emp huv hrel_uv with h | h <;> omega
          have hrel_xu_c : SplitRelation (treeToSplit c) ⟨x.val, by omega⟩ ⟨u.val, by omega⟩ := by
            rcases lt_trichotomy x u with h | rfl | h
            · exact splitRelation_idempotent_left h hu_lt hrel_xu
            · exact splitRelation_refl _ _
            · have := splitRelation_idempotent_left h (by omega) (by rwa [splitRelation_comm])
              rwa [splitRelation_comm]
          rw [wordLabeling_idempotent_left eval hmul c cs x y hxy.le hy_lt.le,
              wordLabeling_idempotent_left eval hmul c cs u v huv.le hv_lt.le]
          exact ih_c.2 _ _ _ _ hxy huv
            (splitRelation_idempotent_left hxy hy_lt hrel_xy)
            (splitRelation_idempotent_left huv hv_lt hrel_uv)
            hrel_xu_c
        · have hx_gt := h_gt hx_ge hx_lt hcs_emp
          have hu_gt : c.value.length < u.val := by
            by_cases hux : u < x
            · have hrel_ux : SplitRelation (treeToSplit (.idempotent (c :: cs))) u x := by
                rwa [splitRelation_comm]
              rcases splitRelation_idempotent_cases hcs_emp hux hrel_ux with h | h
              · omega
              · have h_xu : (treeToSplit (.idempotent (c :: cs)) u).val <
                    (idempotent (c :: cs)).height :=
                  (congrArg Fin.val hrel_xu.1).symm ▸ hx_lt
                exact h_gt h h_xu hcs_emp
            · omega
          have hu_lt_ht :
            (treeToSplit (.idempotent (c :: cs)) u).val < (idempotent (c :: cs)).height :=
            (congrArg Fin.val hrel_xu.1).symm ▸ hx_lt
          have hrel_xu_cs : SplitRelation (treeToSplit (.idempotent cs))
              ⟨x.val - c.value.length, by grind [length_idempotent_cons]⟩
              ⟨u.val - c.value.length, by grind [length_idempotent_cons]⟩ := by
            rcases lt_trichotomy x u with h | rfl | h
            · exact splitRelation_idempotent_cons_right h hx_gt hx_lt hrel_xu
            · exact splitRelation_refl _ _
            · have :=
                splitRelation_idempotent_cons_right h hu_gt hu_lt_ht (by rwa [splitRelation_comm])
              rwa [splitRelation_comm]
          have hu_ge : c.value.length ≤ u.val := hu_gt.le
          rw [wordLabeling_idempotent_cons_right eval hmul c cs x y hx_ge hxy.le,
              wordLabeling_idempotent_cons_right eval hmul c cs u v hu_ge huv.le]
          exact ih_tail.2 _ _ _ _ (Fin.lt_def.2 (by grind)) (Fin.lt_def.2 (by grind))
            (h_cs_lt hx_gt hx_lt)
            (splitRelation_idempotent_cons_right hxy hx_gt hx_lt hrel_xy)
            (splitRelation_idempotent_cons_right huv hu_gt hu_lt_ht hrel_uv)
            hrel_xu_cs

/-- The split function constructed from a Ramsey tree is Ramsey. -/
theorem tree_to_split_isRamsey {S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (t : FactorizationTree A) (ht : t.IsRamsey eval) :
    IsRamsey (wordLabeling eval hmul t.value) (treeToSplit t) := by
  induction t using FactorizationTree.induction_on generalizing eval with
  | h_leaf a => exact treeToSplit_leaf_isRamsey eval hmul a
  | h_binary l r ih_l ih_r =>
    rw [isRamsey_binary] at ht
    have ihl := ih_l eval hmul ht.1
    have ihr := ih_r eval hmul ht.2
    constructor
    · intro x y z hxy hyz hrel_xy hrel_yz
      rcases splitRelation_binary_cases hxy hrel_xy with hy_lt | hx_gt
      · have hz_lt : z.val < l.value.length := by
          grind [splitRelation_binary_cases hyz hrel_yz]
        rw [wordLabeling_binary_left eval hmul l r x y hxy.le (by omega)]
        exact ihl.1 _ _ _ hxy hyz
          (splitRelation_binary_left hxy hy_lt hrel_xy)
          (splitRelation_binary_left hyz hz_lt hrel_yz)
      · rw [wordLabeling_binary_right eval hmul l r x y hx_gt.le hxy.le]
        exact ihr.1 _ _ _ (Fin.lt_def.2 (by grind)) (Fin.lt_def.2 (by grind))
          (splitRelation_binary_right hxy hx_gt hrel_xy)
          (splitRelation_binary_right hyz (by omega) hrel_yz)
    · intro x y u v hxy huv hrel_xy hrel_uv hrel_xu
      rcases splitRelation_binary_cases hxy hrel_xy with hy_lt | hx_gt
      · have hu_lt : u.val < l.value.length := by
          by_contra!
          have hxu : x < u := by omega
          grind [splitRelation_binary_cases hxu hrel_xu]
        have hv_lt : v.val < l.value.length := by
          by_contra!
          grind [splitRelation_binary_cases huv hrel_uv]
        rw [wordLabeling_binary_left eval hmul l r x y hxy.le (by omega),
            wordLabeling_binary_left eval hmul l r u v huv.le (by omega)]
        exact ihl.2 _ _ _ _ hxy huv
          (splitRelation_binary_left hxy hy_lt hrel_xy)
          (splitRelation_binary_left huv hv_lt hrel_uv)
          (by rcases lt_trichotomy x u with h | rfl | h
              · exact splitRelation_binary_left h hu_lt hrel_xu
              · exact splitRelation_refl _ _
              · grind [splitRelation_binary_left h (by omega) (by grind)])
      · have hu_gt : l.value.length < u.val := by
          by_contra!
          have hux : u < x := by omega
          have hrel_ux : SplitRelation (treeToSplit (.binary l r)) u x := by
            rwa [splitRelation_comm]
          grind [splitRelation_binary_cases hux hrel_ux]
        rw [wordLabeling_binary_right eval hmul l r x y hx_gt.le hxy.le,
            wordLabeling_binary_right eval hmul l r u v hu_gt.le huv.le]
        exact ihr.2 _ _ _ _ (Fin.lt_def.2 (by grind)) (Fin.lt_def.2 (by grind))
          (splitRelation_binary_right hxy hx_gt hrel_xy)
          (splitRelation_binary_right huv hu_gt hrel_uv)
          (by rcases lt_trichotomy x u with h | rfl | h
              · exact splitRelation_binary_right h hx_gt hrel_xu
              · exact splitRelation_refl _ _
              · grind [splitRelation_binary_right h hu_gt (by grind)])
  | h_idempotent children ih_children =>
    rw [isRamsey_idempotent] at ht
    rcases ht with ⟨hlen, hlist, e, he, he_eval⟩
    have h_ramsey := (listIsRamsey_iff eval children).mp hlist
    have h_ne c hc := tree_value_ne_nil c (h_ramsey c hc)
    have ih_all c hc := ih_children c hc eval hmul (h_ramsey c hc)
    have h_lt_cases := idempotent_of_lt eval hmul e he children he_eval h_ne h_ramsey ih_all
    have h_eval_e : ∀ {u v}, u < v → SplitRelation (treeToSplit (.idempotent children)) u v →
        (treeToSplit (.idempotent children) u).val = (idempotent children).height →
        (wordLabeling eval hmul (idempotent children).value).σ u v = e := by
      intro u v huv hrel hu_ht
      have hv_ht : (treeToSplit (.idempotent children) v).val = (idempotent children).height := by
        rw [← congrArg Fin.val hrel.1, hu_ht]
      simp only [treeToSplit_val] at hu_ht hv_ht
      grind [value_idempotent,
        eval_slice_of_locateCut_eq_none eval hmul e he children, lcaHeightRaw_idempotent_eq_height]
    have h_lt {w} (hw : (treeToSplit (.idempotent children) w).val ≠ (idempotent children).height) :
        (treeToSplit (.idempotent children) w).val < (idempotent children).height := by
      have := lcaHeightRaw_le_height (.idempotent children) w.val
      simp at *
      omega
    constructor
    · grind
    · intro x y u v hxy huv hrel_xy hrel_uv hrel_xu
      by_cases hx : (treeToSplit (.idempotent children) x).val = (idempotent children).height
      · have hu : (treeToSplit (.idempotent children) u).val = (idempotent children).height := by
          rw [← congrArg Fin.val hrel_xu.1, hx]
        rw [h_eval_e hxy hrel_xy hx, h_eval_e huv hrel_uv hu]
      · exact h_lt_cases.2 x y u v hxy huv (h_lt hx) hrel_xy hrel_uv hrel_xu

/-- The split constructed from a Ramsey tree under a homomorphism is Ramsey. -/
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
