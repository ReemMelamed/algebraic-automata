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
  have := congrArg List.length h
  simp only [List.length_take, List.length_nil] at this
  omega

/-- Dropping half the elements of a list of length at least 2 is non-empty. -/
lemma drop_ne_nil {A : Type*} {l : List A} (hl : 2 ≤ l.length) :
    l.drop (l.length / 2) ≠ [] := fun h ↦ by
  have := congrArg List.length h
  simp only [List.length_drop, List.length_nil] at this
  omega

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
          dsimp only
          constructor
          · exact value_leaf a
          · rw [height_leaf]
            exact Nat.zero_le _
        | cons b rest' => grind
    · have hlen_ge : 2 ≤ v.length := by omega
      have h_take_lt : (v.take (v.length / 2)).length < k := by
        rw [← hlen, List.length_take]
        omega
      have h_drop_lt : (v.drop (v.length / 2)).length < k := by
        rw [← hlen, List.length_drop]
        omega
      obtain ⟨ih_take_val, ih_take_ht⟩ := ih _ h_take_lt _ (take_ne_nil hlen_ge) rfl
      obtain ⟨ih_drop_val, ih_drop_ht⟩ := ih _ h_drop_lt _ (drop_ne_nil hlen_ge) rfl
      have h_take_len : (v.take (v.length / 2)).length ≤ (v.length + 1) / 2 := by
        simp only [List.length_take]
        omega
      have h_drop_len : (v.drop (v.length / 2)).length ≤ (v.length + 1) / 2 := by
        simp only [List.length_drop]
        omega
      have hmax : max (balancedTree d (v.take (v.length / 2))).height
          (balancedTree d (v.drop (v.length / 2))).height ≤ log2Ceil ((v.length + 1) / 2) :=
        max_le (ih_take_ht.trans (log2Ceil_monotone h_take_len)) (ih_drop_ht.trans (log2Ceil_monotone h_drop_len))
      refine ⟨by simp only [value_binary, ih_take_val, ih_drop_val, List.take_append_drop], ?_⟩
      rw [height_binary, ← hlen, log2Ceil_of_two_le hlen_ge]
      omega

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
  have := x.pos
  have := x.le
  ext
  simp only [top_val]
  omega

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

/-- The `evalTrunc` function is a semigroup homomorphism from non-empty lists under concatenation. -/
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
  rw [IsGreenJ, isGreenJRel_iff_val_le, isGreenJRel_iff_val_le]
  constructor
  · rintro ⟨h_le_left, h_le_right⟩
    exact TruncatedAdd.ext (by omega)
  · rintro rfl
    exact ⟨le_rfl, le_rfl⟩

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
  rw [greenJClass_le_iff, greenJClass_le_iff]
  omega

open Classical in
/-- Every D-class in `TruncatedAdd n` has complexity `nD = 1`. -/
theorem nD_truncatedAdd (x : TruncatedAdd n) : nD (IsGreenD.eqvClass x) = 1 := by
  have h_pos := nD_pos (IsGreenD.eqvClass x) ⟨x, rfl⟩
  have h_le := nD_le_card_j_eq x
  have h_sub : (Finset.univ.filter (fun z ↦ GreenJClass.mk z = GreenJClass.mk x)) ⊆ {x} := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    rw [GreenJClass.mk_eq_mk_iff, isGreenJ_iff_eq] at hz
    exact Finset.mem_singleton.mpr hz
  have h_card : (Finset.univ.filter (fun z ↦ GreenJClass.mk z = GreenJClass.mk x)).card ≤ 1 :=
    (Finset.card_le_card h_sub).trans_eq (Finset.card_singleton x)
  have h_le_one : nD (IsGreenD.eqvClass x) ≤ 1 := h_le.trans h_card
  omega

open Classical in
/-- The complexity bound `nSElement` of each element `x` in `TruncatedAdd n` is exactly its value `x.val`. -/
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
    · have hk_ge : 2 ≤ k := by
        have := x.pos
        omega
      have h_pred_pos : 0 < k - 1 := by omega
      have h_pred_le : k - 1 ≤ n := by
        have := x.le
        omega
      let y_pred : TruncatedAdd n := ⟨k - 1, h_pred_pos, h_pred_le⟩
      have hy_pred_lt : GreenJClass.mk x < GreenJClass.mk y_pred := by
        rw [greenJClass_lt_iff, hval]
        dsimp [y_pred]
        omega
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
      have h_sup_eq : strictlyAbove.attach.sup (fun y ↦ nSElement y.1) = k - 1 :=
        le_antisymm h_le h_ge
      rw [h_sup_eq]
      omega

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
/-- The complexity bound `nS` equals the cardinality of the semigroup: `nS (TruncatedAdd n) = |TruncatedAdd n| = n`. -/
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
  · have h_h := (balancedTree_height_le d u hu).trans (log2Ceil_monotone hle)
    exact ⟨balancedTree d u, balancedTree_val d u hu, balancedTree_isRamsey eval d u hu, by omega⟩
  · push Not at hle
    by_cases h_short : u.length < 2 * n
    · have htake_ne : u.take n ≠ [] := fun h ↦ by
        have := congrArg List.length h
        simp only [List.length_take, List.length_nil] at this
        omega
      have hdrop_ne : u.drop n ≠ [] := fun h ↦ by
        have := congrArg List.length h
        simp only [List.length_drop, List.length_nil] at this
        omega
      let treeTake := balancedTree d (u.take n)
      let treeDrop := balancedTree d (u.drop n)
      let t := FactorizationTree.binary treeTake treeDrop
      have ht_val : t.value = u := by
        rw [value_binary, balancedTree_val d (u.take n) htake_ne,
            balancedTree_val d (u.drop n) hdrop_ne, List.take_append_drop]
      have ht_ramsey : t.IsRamsey eval :=
        FactorizationTree.binary_isRamsey eval
          (balancedTree_isRamsey eval d _ htake_ne)
          (balancedTree_isRamsey eval d _ hdrop_ne)
      have ht_height : t.height ≤ log2Ceil n + 2 := by
        have h_take_ht := balancedTree_height_le d (u.take n) htake_ne
        have h_drop_ht := balancedTree_height_le d (u.drop n) hdrop_ne
        rw [List.length_take] at h_take_ht
        rw [List.length_drop] at h_drop_ht
        have h_take_ht' := h_take_ht.trans (log2Ceil_monotone (min_le_left _ _))
        have h_drop_ht' := h_drop_ht.trans (log2Ceil_monotone (show u.length - n ≤ n by omega))
        have h_max : max treeTake.height treeDrop.height ≤ log2Ceil n := max_le h_take_ht' h_drop_ht'
        rw [height_binary]
        omega
      exact ⟨t, ht_val, ht_ramsey, ht_height⟩
    · push Not at h_short
      let q := u.length / n
      have hq_ge : 2 ≤ q := Nat.le_div_iff_mul_le hn |>.mpr (by omega)
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
      have h_idem_ramsey : (FactorizationTree.idempotent trees).IsRamsey eval :=
        (isRamsey_idempotent eval trees).mpr
          ⟨h_trees_len.symm ▸ hq_ge, h_trees_ramsey, top hn, top_mul_self hn, h_trees_eval⟩
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
        rw [height_idempotent]
        have h_lh := listHeight_le trees h_trees_height
        omega
      by_cases hrem : u.drop (q * n) = []
      · have hu_eq : u = u.take (q * n) := by
          have h_take_drop := List.take_append_drop (q * n) u
          rw [hrem, List.append_nil] at h_take_drop
          exact h_take_drop.symm
        have h_val : (FactorizationTree.idempotent trees).value = u := by
          rw [value_idempotent, h_trees_val, ← hu_eq]
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
          rw [value_binary, value_idempotent, h_trees_val, htrem_val, List.take_append_drop]
        have ht_ramsey : t.IsRamsey eval :=
          FactorizationTree.binary_isRamsey eval h_idem_ramsey htrem_ramsey
        have ht_height : t.height ≤ log2Ceil n + 2 := by
          rw [height_binary]
          omega
        exact ⟨t, ht_val, ht_ramsey, ht_height⟩

end RamseyTreeConstruction

end Optimality
