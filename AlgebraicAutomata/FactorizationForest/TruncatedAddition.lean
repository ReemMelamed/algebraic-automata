/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Log
import AlgebraicAutomata.FactorizationForest.Tree

/-!
# Sub-linear Ramsey Factorization Trees: The Truncated Addition Semigroup

Construction of sub-linear height factorization trees over the truncated addition semigroup.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace Optimality

open FactorizationTree

section Log2Ceil

/-- Ceiling of the base-2 logarithm of `n`. -/
def log2Ceil (n : ℕ) : ℕ := Nat.clog 2 n

/-- Monotonicity of `log2Ceil`. -/
lemma log2Ceil_monotone {a b : ℕ} (h : a ≤ b) : log2Ceil a ≤ log2Ceil b :=
  Nat.clog_mono_right 2 h

/-- Recurrence relation for `log2Ceil` when `n ≥ 2`. -/
lemma log2Ceil_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    log2Ceil n = 1 + log2Ceil ((n + 1) / 2) := by
  grind [log2Ceil, Nat.clog_of_two_le Nat.one_lt_two hn]

end Log2Ceil

section BalancedTree

/-- Taking half the elements of a list of length at least 2 is non-empty. -/
lemma take_ne_nil {A : Type*} {l : List A} (hl : 2 ≤ l.length) :
    l.take (l.length / 2) ≠ [] := by
  grind [List.length_nil]

/-- Dropping half the elements of a list of length at least 2 is non-empty. -/
lemma drop_ne_nil {A : Type*} {l : List A} (hl : 2 ≤ l.length) :
    l.drop (l.length / 2) ≠ [] := by
  grind [List.length_nil]

/-- Constructs a balanced binary factorization tree for a word `v`. -/
def balancedTree {A : Type*} (d : A) (v : List A) : FactorizationTree A :=
  if h : v.length ≤ 1 then
    match v with
    | [] => FactorizationTree.leaf d
    | [a] => FactorizationTree.leaf a
    | _ => FactorizationTree.leaf d
  else
    FactorizationTree.binary
      (balancedTree d (v.take (v.length / 2)))
      (balancedTree d (v.drop (v.length / 2)))
termination_by v.length
decreasing_by all_goals grind [List.length_take, List.length_nil]

/-- Yield and height bound for `balancedTree`. -/
lemma balancedTree_val_height {A : Type*} (d : A) (v : List A) (hv : v ≠ []) :
    (balancedTree d v).value = v ∧ (balancedTree d v).height ≤ log2Ceil v.length := by
  generalize hlen : v.length = k
  induction k using Nat.strong_induction_on generalizing v with
  | h k ih =>
    rw [balancedTree]
    split_ifs with hle
    · cases v with
      | nil => contradiction
      | cons a rest =>
        cases rest with
        | nil =>
          subst hlen
          dsimp only
          constructor
          · exact value_leaf a
          · simp only [height_leaf, Nat.zero_le]
        | cons b rest' => grind
    · have hlen_ge : 2 ≤ v.length := by omega
      have h_take_lt : (v.take (v.length / 2)).length < k := by grind
      have h_drop_lt : (v.drop (v.length / 2)).length < k := by grind
      obtain ⟨ih_take_val, ih_take_ht⟩ := ih _ h_take_lt _ (take_ne_nil hlen_ge) rfl
      obtain ⟨ih_drop_val, ih_drop_ht⟩ := ih _ h_drop_lt _ (drop_ne_nil hlen_ge) rfl
      have h_take_len : (v.take (v.length / 2)).length ≤ (v.length + 1) / 2 := by grind
      have h_drop_len : (v.drop (v.length / 2)).length ≤ (v.length + 1) / 2 := by grind
      have hmax : max (balancedTree d (v.take (v.length / 2))).height
          (balancedTree d (v.drop (v.length / 2))).height ≤ log2Ceil ((v.length + 1) / 2) :=
        max_le (ih_take_ht.trans (log2Ceil_monotone h_take_len))
          (ih_drop_ht.trans (log2Ceil_monotone h_drop_len))
      grind [value_binary, List.take_append_drop, height_binary, log2Ceil_of_two_le hlen_ge]

/-- The yield of `balancedTree d v` is `v`. -/
lemma balancedTree_val {A : Type*} (d : A) (v : List A) (hv : v ≠ []) :
    (balancedTree d v).value = v :=
  (balancedTree_val_height d v hv).1

/-- The height of a balanced tree on `v` is at most `log2Ceil v.length`. -/
lemma balancedTree_height_le {A : Type*} (d : A) (v : List A) (hv : v ≠ []) :
    (balancedTree d v).height ≤ log2Ceil v.length :=
  (balancedTree_val_height d v hv).2

/-- The balanced tree is Ramsey for any evaluation map. -/
lemma balancedTree_isRamsey {A S : Type*} [Semigroup S] (eval : List A → S) (d : A)
    (v : List A) (hv : v ≠ []) : (balancedTree d v).IsRamsey eval := by
  generalize hlen : v.length = k
  induction k using Nat.strong_induction_on generalizing v with
  | h k ih =>
    rw [balancedTree]
    split_ifs with hle
    · cases v with
      | nil => contradiction
      | cons a rest => cases rest <;> [exact FactorizationTree.leaf_isRamsey eval a; grind]
    · have hlen_ge : 2 ≤ v.length := by omega
      have h_take_lt : (v.take (v.length / 2)).length < k := by
        simp only [← hlen, List.length_take]
        omega
      have h_drop_lt : (v.drop (v.length / 2)).length < k := by
        simp only [← hlen, List.length_drop]
        omega
      exact FactorizationTree.binary_isRamsey eval
        (ih _ h_take_lt _ (take_ne_nil hlen_ge) rfl)
        (ih _ h_drop_lt _ (drop_ne_nil hlen_ge) rfl)

end BalancedTree

section TruncatedAddSemigroup

/-- The truncated addition semigroup `S_n = {1, ..., n}` with operation `min (a + b) n`. -/
@[ext]
structure TruncatedAdd (n : ℕ) where
  val : ℕ
  pos : 0 < val
  le : val ≤ n
deriving DecidableEq

namespace TruncatedAdd

variable {n : ℕ}

noncomputable instance (n : ℕ) : Fintype (TruncatedAdd n) :=
  Fintype.ofInjective (fun x : TruncatedAdd n ↦ (⟨x.val, Nat.lt_succ_of_le x.le⟩ : Fin (n + 1)))
    fun _ _ h ↦ TruncatedAdd.ext (Fin.ext_iff.mp h)

instance : Mul (TruncatedAdd n) where
  mul a b := ⟨min (a.val + b.val) n,
    a.pos.trans_le (le_min (Nat.le_add_right _ _) a.le), min_le_right _ _⟩

/-- Product in `TruncatedAdd n` is given by truncated integer addition. -/
lemma mul_val (a b : TruncatedAdd n) : (a * b).val = min (a.val + b.val) n := rfl

instance : Semigroup (TruncatedAdd n) where
  mul_assoc a b c := by
    ext
    simp only [mul_val]
    omega

/-- The maximum element `n` in `TruncatedAdd n`. -/
def top (hn : 0 < n) : TruncatedAdd n := ⟨n, hn, le_rfl⟩

/-- Value of `top` is `n`. -/
lemma top_val (hn : 0 < n) : (top hn).val = n := rfl

/-- The top element is an idempotent: `top * top = top`. -/
lemma top_mul_self (hn : 0 < n) : top hn * top hn = top hn := by
  ext
  simp [mul_val, top_val]

/-- The length of a list in `TruncatedAdd n` is bounded by the sum of its values. -/
lemma length_le_sum_val (u : List (TruncatedAdd n)) :
    u.length ≤ (u.map TruncatedAdd.val).sum := by
  induction u with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha : 1 ≤ a.val := a.pos
    omega

/-- Evaluator mapping lists of elements to their truncated sum in `TruncatedAdd n`. -/
def evalTrunc (hn : 0 < n) (u : List (TruncatedAdd n)) : TruncatedAdd n :=
  ⟨if u = [] then n else min (u.map TruncatedAdd.val).sum n, by
    split_ifs with h
    · exact hn
    · have := length_le_sum_val u
      have : 1 ≤ u.length := List.length_pos_iff.mpr h
      omega,
   by grind⟩

/-- Value of `evalTrunc` on non-empty lists. -/
lemma evalTrunc_val (hn : 0 < n) {u : List (TruncatedAdd n)} (hu : u ≠ []) :
    (evalTrunc hn u).val = min (u.map TruncatedAdd.val).sum n :=
  ite_eq_right hu

/-- Any word of length at least `n` evaluates to the top idempotent element. -/
lemma evalTrunc_of_length_ge (hn : 0 < n) (u : List (TruncatedAdd n))
    (hlen : n ≤ u.length) :
    evalTrunc hn u = top hn := by
  ext
  grind [evalTrunc, top_val, length_le_sum_val]

/-- The unique idempotent in `TruncatedAdd n` is `top n`. -/
lemma idempotent_eq_top {n : ℕ} (hn : 0 < n)
    (x : TruncatedAdd n) (hx : x * x = x) : x = top hn := by
  grind [TruncatedAdd.ext_iff, mul_val, top_val, x.pos]

/-- Left-multiplication by `top n` returns `top n` for any element. -/
lemma top_mul_any {n : ℕ} (hn : 0 < n) (x : TruncatedAdd n) : top hn * x = top hn := by
  ext
  simp [mul_val, top_val]

/-- `TruncatedAdd n` has exactly `n` elements. -/
noncomputable def equivFin (n : ℕ) (_ : 0 < n) : TruncatedAdd n ≃ Fin n where
  toFun x   := ⟨x.val - 1, (Nat.sub_lt x.pos Nat.zero_lt_one).trans_le x.le⟩
  invFun j  := ⟨j.val + 1, by omega, by omega⟩
  left_inv x := TruncatedAdd.ext (Nat.sub_add_cancel x.pos)
  right_inv _ := Fin.ext (Nat.add_sub_cancel _ _)

/-- The cardinality of `TruncatedAdd n` is `n`. -/
lemma card_eq (n : ℕ) (hn : 0 < n) : Fintype.card (TruncatedAdd n) = n :=
  (Fintype.card_congr (equivFin n hn)).trans (Fintype.card_fin n)

/-- The `evalTrunc` function is a semigroup homomorphism
from non-empty lists under concatenation. -/
lemma evalTrunc_append (hn : 0 < n) (u v : List (TruncatedAdd n))
    (hu : u ≠ []) (hv : v ≠ []) :
    evalTrunc hn (u ++ v) = evalTrunc hn u * evalTrunc hn v := by
  ext
  have h_ne : u ++ v ≠ [] := by simp [hu]
  simp only [evalTrunc_val hn h_ne, mul_val, evalTrunc_val hn hu,
    evalTrunc_val hn hv, List.map_append, List.sum_append]
  omega

end TruncatedAdd

end TruncatedAddSemigroup

section Complexity

open GreensRelations RamseySplit TruncatedAdd

variable {n : ℕ}

/-- Divisibility relation in `TruncatedAdd n`: `b.val ≤ a.val`. -/
lemma isGreenJRel_val_le (a b : TruncatedAdd n) (h : IsGreenJRel a b) : b.val ≤ a.val := by
  have hb := b.le
  cases h with
  | of_eq h => rw [h]
  | mul_left u h =>
    have := congrArg TruncatedAdd.val h
    rw [mul_val] at this
    omega
  | mul_right v h =>
    have := congrArg TruncatedAdd.val h
    rw [mul_val] at this
    omega
  | mul_both u v h =>
    have := congrArg TruncatedAdd.val h
    rw [mul_assoc, mul_val, mul_val] at this
    omega

lemma isGreenJRel_of_val_le (a b : TruncatedAdd n) (h : b.val ≤ a.val) : IsGreenJRel a b := by
  rcases eq_or_lt_of_le h with heq | hlt
  · exact .of_eq (TruncatedAdd.ext heq.symm)
  · have h_pos : 0 < a.val - b.val := by omega
    have h_le : a.val - b.val ≤ n := by
      have := a.le
      omega
    let v : TruncatedAdd n := ⟨a.val - b.val, h_pos, h_le⟩
    have h_mul : b * v = a := by
      ext
      simp only [mul_val]
      change min (b.val + (a.val - b.val)) n = a.val
      have := a.le
      omega
    exact .mul_right v h_mul.symm

/-- In `TruncatedAdd n`, `a ≤_J b` (meaning `IsGreenJRel a b`) if and only if `b.val ≤ a.val`. -/
theorem isGreenJRel_iff_val_le (a b : TruncatedAdd n) : IsGreenJRel a b ↔ b.val ≤ a.val :=
  ⟨isGreenJRel_val_le a b, isGreenJRel_of_val_le a b⟩

/-- Green's J-relation on `TruncatedAdd n` is equality: each element forms its own J-class. -/
theorem isGreenJ_iff_eq (a b : TruncatedAdd n) : IsGreenJ a b ↔ a = b := by
  grind [isGreenJRel_iff_val_le, TruncatedAdd.ext_iff]

/-- In `TruncatedAdd n`, Green's D-relation is equality. -/
theorem isGreenD_iff_eq (a b : TruncatedAdd n) : IsGreenD a b ↔ a = b := by
  rw [isGreenD_eq_isGreenJ_of_finite]
  exact isGreenJ_iff_eq a b

/-- The D-class of `x` is the singleton `{x}`. -/
lemma isGreenD_eqvClass_eq (x : TruncatedAdd n) :
    IsGreenD.eqvClass x = {x} := by
  ext z
  simp [isGreenD_iff_eq]

/-- The J-order on `TruncatedAdd n` is the reverse of the natural value order. -/
theorem greenJClass_le_iff (a b : TruncatedAdd n) :
    GreenJClass.mk a ≤ GreenJClass.mk b ↔ b.val ≤ a.val :=
  isGreenJRel_iff_val_le a b

theorem greenJClass_lt_iff (a b : TruncatedAdd n) :
    GreenJClass.mk a < GreenJClass.mk b ↔ b.val < a.val := by
  change (GreenJClass.mk a ≤ GreenJClass.mk b ∧
    ¬(GreenJClass.mk b ≤ GreenJClass.mk a)) ↔ b.val < a.val
  grind [greenJClass_le_iff]


open Classical in
/-- Every D-class in `TruncatedAdd n` has complexity `nD = 1`. -/
theorem nD_truncatedAdd (x : TruncatedAdd n) : nD (IsGreenD.eqvClass x) = 1 := by
  grind [nD_pos (IsGreenD.eqvClass x) ⟨x, rfl⟩, nD_le_card_j_eq x,
    GreenJClass.mk_eq_mk_iff, isGreenJ_iff_eq, Finset.card_le_one_iff]

open Classical in
/-- The complexity bound `nSElement` of each element
`x` in `TruncatedAdd n` is exactly its value `x.val`. -/
theorem nSElement_truncatedAdd (x : TruncatedAdd n) : nSElement x = x.val := by
  induction hval : x.val using Nat.strong_induction_on generalizing x with
  | h k ih =>
    rw [nSElement]
    dsimp only
    rw [nD_truncatedAdd]
    set strictlyAbove := Finset.univ.filter (fun y ↦ GreenJClass.mk x < GreenJClass.mk y)
    by_cases hk : k = 1
    · have h_empty : strictlyAbove = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro y _
        rw [greenJClass_lt_iff, hval, hk]
        have := y.pos
        omega
      have h_sup : strictlyAbove.attach.sup (fun y ↦ nSElement y.1) = 0 := by
        simp [h_empty]
      rw [h_sup, hk]
    · have hk_ge : 2 ≤ k := by grind [x.pos]
      have h_pred_pos : 0 < k - 1 := by omega
      have h_pred_le : k - 1 ≤ n := by grind [x.le]
      let y_pred : TruncatedAdd n := ⟨k - 1, h_pred_pos, h_pred_le⟩
      have hy_pred_lt : GreenJClass.mk x < GreenJClass.mk y_pred := by
        grind [greenJClass_lt_iff]
      have hy_pred_mem : y_pred ∈ strictlyAbove :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy_pred_lt⟩
      have hy_pred_val : nSElement y_pred = k - 1 := by
        apply ih (k - 1) (by omega) y_pred rfl
      have h_le : strictlyAbove.attach.sup (fun y ↦ nSElement y.1) ≤ k - 1 := by
        apply Finset.sup_le
        rintro ⟨y, hy_mem⟩ -
        dsimp only
        have hy_lt : GreenJClass.mk x < GreenJClass.mk y :=
          (Finset.mem_filter.mp hy_mem).2
        rw [greenJClass_lt_iff, hval] at hy_lt
        have hy_val := ih y.val (by omega) y rfl
        omega
      have h_ge : k - 1 ≤ strictlyAbove.attach.sup (fun y ↦ nSElement y.1) := by
        have h_in : ⟨y_pred, hy_pred_mem⟩ ∈ strictlyAbove.attach := Finset.mem_attach _ _
        have h_le_sup := Finset.le_sup (f := fun y ↦ nSElement y.1) h_in
        dsimp only at h_le_sup
        omega
      grind [le_antisymm h_le h_ge]

open Classical in
/-- For the truncated addition semigroup `TruncatedAdd n`, the complexity bound `nS` is
exactly `n = |TruncatedAdd n|`. -/
theorem nS_truncatedAdd (n : ℕ) (hn : 0 < n) : nS (TruncatedAdd n) = n := by
  have instNonempty : Nonempty (TruncatedAdd n) := ⟨top hn⟩
  apply le_antisymm
  · have h_le := nS_le_card (S := TruncatedAdd n)
    rw [card_eq n hn] at h_le
    exact h_le
  · dsimp [nS]
    split_ifs with h
    · have h_top_mem : nSElement (top hn) ∈
          Finset.univ.image (fun (x : TruncatedAdd n) ↦ nSElement x) :=
        Finset.mem_image_of_mem _ (Finset.mem_univ _)
      have h_le := Finset.le_max' _ _ h_top_mem
      have h_val : nSElement (top hn) = n := by
        have := nSElement_truncatedAdd (top hn)
        rwa [top_val] at this
      exact le_trans (le_of_eq h_val.symm) h_le
    · exfalso
      apply h
      exact ⟨nSElement (top hn), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

open Classical in
/-- The complexity bound `nS` equals the cardinality of the semigroup:
`nS (TruncatedAdd n) = |TruncatedAdd n| = n`. -/
theorem nS_eq_card_truncatedAdd (n : ℕ) (hn : 0 < n) :
    nS (TruncatedAdd n) = Fintype.card (TruncatedAdd n) := by
  rw [nS_truncatedAdd n hn, card_eq n hn]

end Complexity

section RamseyTreeConstruction

open TruncatedAdd

/-- The yield of a list of trees equals the flattened list of yields. -/
lemma listValue_eq_flatten {A : Type*} :
    ∀ (ts : List (FactorizationTree A)), listValue ts = (ts.map FactorizationTree.value).flatten
  | [] => rfl
  | t :: ts => congrArg (t.value ++ ·) (listValue_eq_flatten ts)

/-- Partitioning a list into blocks of size `n` and concatenating yields the prefix. -/
lemma flatten_map_range_take_drop {A : Type*} (u : List A) (n : ℕ) :
    ∀ (q : ℕ), ((List.range q).map (fun i ↦ (u.drop (i * n)).take n)).flatten =
      u.take (q * n)
  | 0 => by simp
  | q + 1 => by
    simp only [List.range_succ, List.map_append, List.flatten_append,
      flatten_map_range_take_drop u n q, List.map_singleton, List.flatten_singleton,
      Nat.succ_mul, List.take_add]

/-- Every non-empty word in `TruncatedAdd n` admits a
Ramsey tree of height at most `log2Ceil n + 2`. -/
theorem truncatedAdd_tree_height (n : ℕ) (hn : 0 < n)
    (u : List (TruncatedAdd n)) (hu : u ≠ []) :
    ∃ t : FactorizationTree (TruncatedAdd n),
      t.value = u ∧
      t.IsRamsey (evalTrunc hn) ∧
      t.height ≤ log2Ceil n + 2 := by
  let d : TruncatedAdd n := top hn
  let eval := evalTrunc hn
  by_cases hle : u.length ≤ n
  · use balancedTree d u
    grind [balancedTree_val, balancedTree_isRamsey,
      (balancedTree_height_le d u hu).trans (log2Ceil_monotone hle)]
  · by_cases h_short : u.length < 2 * n
    · obtain ⟨htake_ne, hdrop_ne⟩ : u.take n ≠ [] ∧ u.drop n ≠ [] := by
        grind [List.length_take, List.length_drop, List.length_nil]
      have ht_h : (balancedTree d (u.take n)).height ≤ log2Ceil n ∧
          (balancedTree d (u.drop n)).height ≤ log2Ceil n :=
        ⟨(balancedTree_height_le d _ htake_ne).trans (log2Ceil_monotone (by grind)),
         (balancedTree_height_le d _ hdrop_ne).trans (log2Ceil_monotone (by grind))⟩
      use FactorizationTree.binary (balancedTree d (u.take n)) (balancedTree d (u.drop n))
      grind [value_binary, balancedTree_val, List.take_append_drop,
        FactorizationTree.binary_isRamsey, balancedTree_isRamsey, height_binary]
    · let q := u.length / n
      have h_block_len : ∀ i < q, ((u.drop (i * n)).take n).length = n := fun i hi ↦ by
        rw [List.length_take, List.length_drop]
        have h_in : i * n + n ≤ q * n :=
          Nat.succ_mul i n ▸ Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)
        have hqn : q * n ≤ u.length := Nat.div_mul_le_self u.length n
        omega
      have h_block_ne : ∀ i < q, (u.drop (i * n)).take n ≠ [] := by
        grind [List.length_nil]
      let trees : List (FactorizationTree (TruncatedAdd n)) :=
        (List.range q).map (fun i ↦ balancedTree d ((u.drop (i * n)).take n))
      have h_trees_ge : 2 ≤ trees.length := by
        simpa [trees] using (Nat.le_div_iff_mul_le hn).mpr (by omega)
      obtain ⟨h_trees_ramsey, h_trees_eval, h_trees_height⟩ :
          listIsRamsey eval trees ∧
          (∀ t ∈ trees, eval t.value = top hn) ∧
          (∀ t ∈ trees, t.height ≤ log2Ceil n) := by
        grind [listIsRamsey_iff, balancedTree_isRamsey, balancedTree_val,
          evalTrunc_of_length_ge, balancedTree_height_le]
      have h_idem_ramsey : (FactorizationTree.idempotent trees).IsRamsey eval :=
        (isRamsey_idempotent eval trees).mpr
          ⟨h_trees_ge, h_trees_ramsey, top hn, top_mul_self hn, h_trees_eval⟩
      obtain ⟨h_trees_val, h_idem_height⟩ :
          listValue trees = u.take (q * n) ∧
          (FactorizationTree.idempotent trees).height ≤ 1 + log2Ceil n := by
        grind [listValue_eq_flatten, List.map_congr_left, balancedTree_val,
          flatten_map_range_take_drop, height_idempotent, listHeight_le trees h_trees_height]
      by_cases hrem : u.drop (q * n) = []
      · grind [value_idempotent, List.take_append_drop]
      · let trem := balancedTree d (u.drop (q * n))
        have htrem_h : trem.height ≤ log2Ceil n :=
          (balancedTree_height_le d _ hrem).trans (log2Ceil_monotone (by
            grind [List.length_drop, Nat.mod_lt u.length hn, Nat.mod_add_div]))
        use FactorizationTree.binary (FactorizationTree.idempotent trees) trem
        grind [value_binary, value_idempotent, balancedTree_val, List.take_append_drop,
          FactorizationTree.binary_isRamsey, balancedTree_isRamsey, height_binary]

end RamseyTreeConstruction

end Optimality
