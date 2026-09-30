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
  simp only [log2Ceil, Nat.clog_of_two_le Nat.one_lt_two hn]
  grind

end Log2Ceil

section BalancedTree

/-- Taking half the elements of a list of length at least 2 is non-empty. -/
lemma take_ne_nil {A : Type*} {l : List A} (hl : 2 ≤ l.length) :
    l.take (l.length / 2) ≠ [] := fun h ↦ by
  have := congrArg List.length h; simp only [List.length_take, List.length_nil] at this; omega

/-- Dropping half the elements of a list of length at least 2 is non-empty. -/
lemma drop_ne_nil {A : Type*} {l : List A} (hl : 2 ≤ l.length) :
    l.drop (l.length / 2) ≠ [] := fun h ↦ by
  have := congrArg List.length h; simp only [List.length_drop, List.length_nil] at this; omega

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
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

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
          exact ⟨rfl, le_rfl⟩
        | cons b rest' => grind
    · have hlen_ge : 2 ≤ v.length := by omega
      have h1_lt : (v.take (v.length / 2)).length < k := by
        rw [← hlen, List.length_take]; omega
      have h2_lt : (v.drop (v.length / 2)).length < k := by
        rw [← hlen, List.length_drop]; omega
      obtain ⟨ih1_val, ih1_ht⟩ := ih _ h1_lt _ (take_ne_nil hlen_ge) rfl
      obtain ⟨ih2_val, ih2_ht⟩ := ih _ h2_lt _ (drop_ne_nil hlen_ge) rfl
      have h1_len : (v.take (v.length / 2)).length ≤ (v.length + 1) / 2 := by
        simp only [List.length_take]; omega
      have h2_len : (v.drop (v.length / 2)).length ≤ (v.length + 1) / 2 := by
        simp only [List.length_drop]; omega
      have hmax : max (balancedTree d (v.take (v.length / 2))).height
          (balancedTree d (v.drop (v.length / 2))).height ≤ log2Ceil ((v.length + 1) / 2) :=
        max_le (ih1_ht.trans (log2Ceil_monotone h1_len)) (ih2_ht.trans (log2Ceil_monotone h2_len))
      refine ⟨by simp only [FactorizationTree.value, ih1_val, ih2_val, List.take_append_drop],
              by dsimp [FactorizationTree.height]; rw [← hlen, log2Ceil_of_two_le hlen_ge]; omega⟩

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
      have h1_lt : (v.take (v.length / 2)).length < k := by
        simp only [← hlen, List.length_take]; omega
      have h2_lt : (v.drop (v.length / 2)).length < k := by
        simp only [← hlen, List.length_drop]; omega
      exact FactorizationTree.binary_isRamsey eval
        (ih _ h1_lt _ (take_ne_nil hlen_ge) rfl)
        (ih _ h2_lt _ (drop_ne_nil hlen_ge) rfl)

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
  mul_assoc a b c := by ext; simp only [mul_val]; omega

/-- The maximum element `n` in `TruncatedAdd n`. -/
def top (hn : 0 < n) : TruncatedAdd n := ⟨n, hn, le_rfl⟩

/-- Value of `top` is `n`. -/
lemma top_val (hn : 0 < n) : (top hn).val = n := rfl

/-- The top element is an idempotent: `top * top = top`. -/
lemma top_mul_self (hn : 0 < n) : top hn * top hn = top hn := by ext; simp [mul_val, top_val]

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
    · have := length_le_sum_val u; have : 1 ≤ u.length := List.length_pos_iff.mpr h; omega,
   by grind⟩

/-- Value of `evalTrunc` on non-empty lists. -/
lemma evalTrunc_val (hn : 0 < n) {u : List (TruncatedAdd n)} (hu : u ≠ []) :
    (evalTrunc hn u).val = min (u.map TruncatedAdd.val).sum n :=
  ite_eq_right hu

/-- Any word of length at least `n` evaluates to the top idempotent element. -/
lemma evalTrunc_of_length_ge (hn : 0 < n) (u : List (TruncatedAdd n))
    (hlen : n ≤ u.length) :
    evalTrunc hn u = top hn := by
  have hu : u ≠ [] := by grind
  have h_sum := length_le_sum_val u
  ext
  simp [evalTrunc_val hn hu, top_val]
  omega

/-- The unique idempotent in `TruncatedAdd n` is `top n`. -/
lemma idempotent_eq_top {n : ℕ} (hn : 0 < n)
    (x : TruncatedAdd n) (hx : x * x = x) : x = top hn := by
  have h := congrArg TruncatedAdd.val hx
  rw [mul_val] at h
  have := x.pos; have := x.le; ext; simp only [top_val]; omega

/-- Left-multiplication by `top n` returns `top n` for any element. -/
lemma top_mul_any {n : ℕ} (hn : 0 < n) (x : TruncatedAdd n) : top hn * x = top hn := by
  ext; simp [mul_val, top_val]

/-- `TruncatedAdd n` has exactly `n` elements. -/
noncomputable def equivFin (n : ℕ) (_ : 0 < n) : TruncatedAdd n ≃ Fin n where
  toFun x   := ⟨x.val - 1, (Nat.sub_lt x.pos Nat.zero_lt_one).trans_le x.le⟩
  invFun j  := ⟨j.val + 1, by omega, by omega⟩
  left_inv x := TruncatedAdd.ext (Nat.sub_add_cancel x.pos)
  right_inv _ := Fin.ext (Nat.add_sub_cancel _ _)

/-- The cardinality of `TruncatedAdd n` is `n`. -/
lemma card_eq (n : ℕ) (hn : 0 < n) : Fintype.card (TruncatedAdd n) = n :=
  (Fintype.card_congr (equivFin n hn)).trans (Fintype.card_fin n)

/-- The `evalTrunc` function is a semigroup homomorphism from non-empty lists. -/
lemma evalTrunc_hmul (hn : 0 < n) (u v : List (TruncatedAdd n))
    (hu : u ≠ []) (hv : v ≠ []) :
    evalTrunc hn (u ++ v) = evalTrunc hn u * evalTrunc hn v := by
  ext
  have h_ne : u ++ v ≠ [] := by simp [hu]
  simp only [evalTrunc_val hn h_ne, mul_val, evalTrunc_val hn hu,
    evalTrunc_val hn hv, List.map_append, List.sum_append]
  omega

end TruncatedAdd

end TruncatedAddSemigroup

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
theorem truncated_addition_tree_height (n : ℕ) (hn : 0 < n)
    (u : List (TruncatedAdd n)) (hu : u ≠ []) :
    ∃ t : FactorizationTree (TruncatedAdd n),
      t.value = u ∧
      t.IsRamsey (evalTrunc hn) ∧
      t.height ≤ log2Ceil n + 2 := by
  let d : TruncatedAdd n := top hn
  let eval := evalTrunc hn
  by_cases hle : u.length ≤ n
  · have h_h := (balancedTree_height_le d u hu).trans (log2Ceil_monotone hle)
    exact ⟨balancedTree d u, balancedTree_val d u hu, balancedTree_isRamsey eval d u hu, by omega⟩
  · push Not at hle
    by_cases h2n : u.length < 2 * n
    · have htake_ne : u.take n ≠ [] := fun h ↦ by
        have := congrArg List.length h; simp only [List.length_take, List.length_nil] at this; omega
      have hdrop_ne : u.drop n ≠ [] := fun h ↦ by
        have := congrArg List.length h; simp only [List.length_drop, List.length_nil] at this; omega
      let t1 := balancedTree d (u.take n)
      let t2 := balancedTree d (u.drop n)
      let t := FactorizationTree.binary t1 t2
      have ht_val : t.value = u := by
        dsimp [t, FactorizationTree.value]
        rw [balancedTree_val d (u.take n) htake_ne,
            balancedTree_val d (u.drop n) hdrop_ne,
            List.take_append_drop]
      have ht_ramsey : t.IsRamsey eval :=
        FactorizationTree.binary_isRamsey eval
          (balancedTree_isRamsey eval d _ htake_ne)
          (balancedTree_isRamsey eval d _ hdrop_ne)
      have ht_height : t.height ≤ log2Ceil n + 2 := by
        have ht1 := balancedTree_height_le d (u.take n) htake_ne
        have ht2 := balancedTree_height_le d (u.drop n) hdrop_ne
        rw [List.length_take] at ht1
        rw [List.length_drop] at ht2
        have ht1' := ht1.trans (log2Ceil_monotone (min_le_left _ _))
        have ht2' := ht2.trans (log2Ceil_monotone (show u.length - n ≤ n by omega))
        have h_max : max t1.height t2.height ≤ log2Ceil n := max_le ht1' ht2'
        dsimp [t, FactorizationTree.height]
        omega
      exact ⟨t, ht_val, ht_ramsey, ht_height⟩
    · push Not at h2n
      let q := u.length / n
      have hq2 : 2 ≤ q := Nat.le_div_iff_mul_le hn |>.mpr (by omega)
      have h_block_len : ∀ i < q, ((u.drop (i * n)).take n).length = n := by
        intro i hi
        rw [List.length_take, List.length_drop]
        have h_in : i * n + n ≤ q * n := by
          have h_mul := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)
          rw [Nat.succ_mul] at h_mul
          exact h_mul
        have hqn : q * n ≤ u.length := Nat.div_mul_le_self u.length n
        omega
      have h_block_ne : ∀ i < q, (u.drop (i * n)).take n ≠ [] := fun i hi h ↦ by
        have h_len := congrArg List.length h
        rw [h_block_len i hi, List.length_nil] at h_len
        omega
      let trees : List (FactorizationTree (TruncatedAdd n)) :=
        (List.range q).map (fun i ↦ balancedTree d ((u.drop (i * n)).take n))
      have h_trees_len : trees.length = q := by
        dsimp [trees]
        rw [List.length_map, List.length_range]
      have h_trees_ramsey : listIsRamsey eval trees := by
        rw [listIsRamsey_iff]
        intro t ht
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
        exact balancedTree_isRamsey eval d _ (h_block_ne i (List.mem_range.mp hi))
      have h_trees_eval : ∀ t ∈ trees, eval (FactorizationTree.value t) = top hn := fun t ht ↦ by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
        rw [balancedTree_val d _ (h_block_ne i (List.mem_range.mp hi))]
        exact evalTrunc_of_length_ge hn _ (h_block_len i (List.mem_range.mp hi)).ge
      have h_trees_height : ∀ t ∈ trees, t.height ≤ log2Ceil n := fun t ht ↦ by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
        have ht_h := balancedTree_height_le d _ (h_block_ne i (List.mem_range.mp hi))
        rwa [h_block_len i (List.mem_range.mp hi)] at ht_h
      have h_idem_ramsey : (FactorizationTree.idempotent trees).IsRamsey eval := by
        apply FactorizationTree.idempotent_isRamsey eval
        · exact h_trees_len.symm ▸ hq2
        · exact h_trees_ramsey
        · exact top_mul_self hn
        · exact h_trees_eval
      have h_trees_val : listValue trees = u.take (q * n) := by
        rw [listValue_eq_flatten]
        have h_map_val : trees.map FactorizationTree.value =
            (List.range q).map (fun i ↦ (u.drop (i * n)).take n) := by
          dsimp [trees]
          rw [List.map_map]
          apply List.map_congr_left
          intro i hi
          have hi' : i < q := List.mem_range.mp hi
          exact balancedTree_val d _ (h_block_ne i hi')
        rw [h_map_val]
        exact flatten_map_range_take_drop u n q
      have h_idem_height : (FactorizationTree.idempotent trees).height ≤ 1 + log2Ceil n := by
        dsimp [FactorizationTree.height]
        have h_lh := listHeight_le trees h_trees_height
        omega
      by_cases hrem : u.drop (q * n) = []
      · have hu_eq : u = u.take (q * n) := by
          have h_take_drop := List.take_append_drop (q * n) u
          rw [hrem, List.append_nil] at h_take_drop
          exact h_take_drop.symm
        have h_val : (FactorizationTree.idempotent trees).value = u := by
          dsimp [FactorizationTree.value]
          rw [h_trees_val, ← hu_eq]
        exact ⟨FactorizationTree.idempotent trees, h_val, h_idem_ramsey, by omega⟩
      · let trem := balancedTree d (u.drop (q * n))
        let t := FactorizationTree.binary (FactorizationTree.idempotent trees) trem
        have htrem_val := balancedTree_val d (u.drop (q * n)) hrem
        have htrem_ramsey := balancedTree_isRamsey eval d (u.drop (q * n)) hrem
        have hrem_len : (u.drop (q * n)).length ≤ n := by
          rw [List.length_drop]
          have h_div_mod := Nat.mod_add_div u.length n
          have h_mul_comm : q * n = n * (u.length / n) := Nat.mul_comm q n
          have h_mod_lt := Nat.mod_lt u.length hn
          omega
        have htrem_h' : trem.height ≤ log2Ceil n :=
          (balancedTree_height_le d (u.drop (q * n)) hrem).trans (log2Ceil_monotone hrem_len)
        have ht_val : t.value = u := by
          dsimp [t, FactorizationTree.value]
          rw [h_trees_val, htrem_val, List.take_append_drop]
        have ht_ramsey : t.IsRamsey eval :=
          FactorizationTree.binary_isRamsey eval h_idem_ramsey htrem_ramsey
        have ht_height : t.height ≤ log2Ceil n + 2 := by
          have h_height_def :
              t.height = 1 + max (FactorizationTree.idempotent trees).height trem.height := rfl
          rw [h_height_def]
          have h_trem_le : trem.height ≤ log2Ceil n := htrem_h'
          have h_tree_le : (FactorizationTree.idempotent trees).height ≤ 1 + log2Ceil n :=
            h_idem_height
          omega
        exact ⟨t, ht_val, ht_ramsey, ht_height⟩

end RamseyTreeConstruction

end Optimality
