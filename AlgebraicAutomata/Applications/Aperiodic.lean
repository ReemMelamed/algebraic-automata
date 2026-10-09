/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.List.Infix
public import AlgebraicAutomata.Applications.TruncatedAddition

/-!
# Aperiodic Semigroups and Height Bounds

Aperiodic (group-free) semigroups, aperiodicity of truncated addition,
and tightness of the 2|S| factorization forest height bound.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

@[expose] public section


universe u

/-- A semigroup is *aperiodic* if every subgroup of `S` is trivial:
whenever a group `G` embeds into `S` as a subsemigroup, `G` must be a subsingleton. -/
def IsAperiodic (S : Type u) [Semigroup S] : Prop :=
  ∀ {G : Type u} [Group G] (f : G → S),
    (∀ a b, f (a * b) = f a * f b) → Function.Injective f → Subsingleton G

namespace Aperiodic

open Optimality TruncatedAdd FactorizationTree

section TruncatedAddition

/-- The truncated addition semigroup `TruncatedAdd n` is aperiodic (group-free). -/
lemma truncatedAdd_isAperiodic (n : ℕ) (hn : 0 < n) : IsAperiodic (TruncatedAdd n) := by
  intro G instGroup f hf_mul hf_inj
  have h_f_one_top : f 1 = TruncatedAdd.top hn :=
    TruncatedAdd.idempotent_eq_top hn (f 1) (by rw [← hf_mul, one_mul])
  have h_all_top (g : G) : f g = TruncatedAdd.top hn := by
    rw [← one_mul g, hf_mul, h_f_one_top, TruncatedAdd.top_mul_any]
  exact ⟨fun a b ↦ hf_inj ((h_all_top a).trans (h_all_top b).symm)⟩

end TruncatedAddition

section Tightness

/-- The max semigroup on `Fin n`. -/
def MaxSemigroup (n : ℕ) := Fin n

instance (n : ℕ) : LinearOrder (MaxSemigroup n) :=
  inferInstanceAs (LinearOrder (Fin n))

instance (n : ℕ) : Semigroup (MaxSemigroup n) where
  mul a b := max a b
  mul_assoc a b c := max_assoc a b c

instance (n : ℕ) : Fintype (MaxSemigroup n) :=
  inferInstanceAs (Fintype (Fin n))

/-- The max semigroup on `Fin n` is aperiodic (group-free). -/
lemma maxSemigroup_isAperiodic (n : ℕ) : IsAperiodic (MaxSemigroup n) :=
  fun {G} [Group G] f hf_mul hf_inj ↦ ⟨fun a b ↦
    let h_le_one g : f 1 ≤ f g :=
      (mul_one g ▸ (hf_mul g 1).symm) ▸ le_max_right (f g) (f 1)
    let h_one_le g : f g ≤ f 1 :=
      (mul_inv_cancel g ▸ (hf_mul g g⁻¹).symm) ▸ le_max_left (f g) (f g⁻¹)
    let h_eq_one g : f g = f 1 := le_antisymm (h_one_le g) (h_le_one g)
    hf_inj ((h_eq_one a).trans (h_eq_one b).symm)⟩

/-- The bottom element of `MaxSemigroup n`. -/
def botEl (n : ℕ) (hn : 0 < n) : MaxSemigroup n := ⟨0, hn⟩

/-- Evaluator for `MaxSemigroup n`: maps a list to the maximum element (with default 0). -/
def evalMax (n : ℕ) (hn : 0 < n) (u : List (MaxSemigroup n)) : MaxSemigroup n :=
  u.foldl max (botEl n hn)

/-- The bottom element is bounded above by any element. -/
lemma botEl_le (n : ℕ) (hn : 0 < n) (x : MaxSemigroup n) : botEl n hn ≤ x :=
  Nat.zero_le x.val

/-- Taking max with the bottom element on the left is the identity. -/
lemma max_botEl_left (n : ℕ) (hn : 0 < n) (x : MaxSemigroup n) :
    max (botEl n hn) x = x :=
  max_eq_right (botEl_le n hn x)

/-- Left-folding `max` over a list with initial element `z` equals `max z (evalMax n hn u)`. -/
lemma foldl_max_eq_max (n : ℕ) (hn : 0 < n) (u : List (MaxSemigroup n)) (z : MaxSemigroup n) :
    u.foldl max z = max z (evalMax n hn u) := by
  induction u generalizing z with
  | nil => exact (max_eq_left (botEl_le n hn z)).symm
  | cons x xs ih =>
    simp only [List.foldl_cons, ih (max z x)]
    have : evalMax n hn (x :: xs) = max x (evalMax n hn xs) := by
      change xs.foldl max (max (botEl n hn) x) = max x (evalMax n hn xs)
      rw [max_botEl_left, ih]
    rw [this, max_assoc]

/-- The evaluation map `evalMax` distributes over list concatenation. -/
lemma evalMax_append (n : ℕ) (hn : 0 < n) (u v : List (MaxSemigroup n)) :
    evalMax n hn (u ++ v) = evalMax n hn u * evalMax n hn v :=
  (List.foldl_append ..).trans (foldl_max_eq_max n hn v (evalMax n hn u))

/-- Evaluating `cons` takes the max with the head element. -/
@[simp] lemma evalMax_cons (n : ℕ) (hn : 0 < n) (x : MaxSemigroup n) (xs : List (MaxSemigroup n)) :
    evalMax n hn (x :: xs) = max x (evalMax n hn xs) := by
  rw [evalMax, List.foldl_cons, max_botEl_left, foldl_max_eq_max]

/-- Any element in a list is bounded by the maximum evaluation of the list. -/
lemma evalMax_ge_of_mem (n : ℕ) (hn : 0 < n) {x : MaxSemigroup n} {u : List (MaxSemigroup n)}
    (hx : x ∈ u) : x ≤ evalMax n hn u := by
  induction u with
  | nil => contradiction
  | cons y ys ih =>
    rw [evalMax_cons]
    grind

/-- If a non-bottom element `k` is bounded by the evaluation of a list,
some element in the list is at least `k`. -/
lemma exists_mem_ge_of_evalMax_ge (n : ℕ) (hn : 0 < n) {k : MaxSemigroup n}
    {u : List (MaxSemigroup n)} (hk : botEl n hn < k) (h : k ≤ evalMax n hn u) :
    ∃ x ∈ u, k ≤ x := by
  induction u with
  | nil => exact (not_le_of_gt hk h).elim
  | cons y ys ih => grind [evalMax_cons]

/-- Each tree in a list of Ramsey trees is itself a Ramsey tree. -/
lemma isRamsey_of_mem_listIsRamsey {A S : Type*} [Semigroup S] {eval : List A → S}
    {cs : List (FactorizationTree A)} (hcs : listIsRamsey eval cs) {c : FactorizationTree A}
    (hc : c ∈ cs) : c.IsRamsey eval :=
  (listIsRamsey_iff eval cs).mp hcs c hc

/-- In an idempotent node of a Ramsey tree, if one child contains an element `≥ k`,
then every child contains an element `≥ k`. -/
lemma idempotent_children_mem_ge {n : ℕ} (hn : 0 < n)
    {cs : List (FactorizationTree (MaxSemigroup n))}
    (_ : listIsRamsey (evalMax n hn) cs)
    (e : MaxSemigroup n) (he_eval : ∀ t ∈ cs, evalMax n hn (value t) = e)
    (k : MaxSemigroup n) (hk_pos : botEl n hn < k)
    (t : FactorizationTree (MaxSemigroup n)) (ht : t ∈ cs)
    (x : MaxSemigroup n) (hx : x ∈ value t) (hkx : k ≤ x) :
    ∀ c ∈ cs, ∃ y ∈ value c, k ≤ y := by
  have h_ev : k ≤ e := (he_eval t ht) ▸ hkx.trans (evalMax_ge_of_mem n hn hx)
  intro c hc
  exact exists_mem_ge_of_evalMax_ge n hn hk_pos ((he_eval c hc).symm ▸ h_ev)

/-- No child of an idempotent node can have its yield contained in a word
whose elements are all strictly less than `k`. -/
lemma no_child_infix_of_all_lt {n : ℕ} (hn : 0 < n)
    {cs : List (FactorizationTree (MaxSemigroup n))}
    (h_ramsey : listIsRamsey (evalMax n hn) cs)
    (e : MaxSemigroup n) (he_eval : ∀ t ∈ cs, evalMax n hn (value t) = e)
    (k : MaxSemigroup n) (hk_pos : botEl n hn < k)
    (t : FactorizationTree (MaxSemigroup n)) (ht : t ∈ cs)
    (x : MaxSemigroup n) (hx : x ∈ value t) (hkx : k ≤ x)
    (v : List (MaxSemigroup n)) (hv : ∀ y ∈ v, y < k)
    (c : FactorizationTree (MaxSemigroup n)) (hc : c ∈ cs) :
    ¬ (value c <:+: v) := fun h_inf ↦ by
  obtain ⟨y, hy_mem, hky⟩ :=
    idempotent_children_mem_ge hn h_ramsey e he_eval k hk_pos t ht x hx hkx c hc
  exact not_le_of_gt (hv y (h_inf.subset hy_mem)) hky

/-- Triple repetition of a list `l ++ l ++ l`, representing `l³`.
Three copies force any binary node splitting
the word to contain an entire copy of `l` in one of its subtrees. -/
def repeatThree {α : Type*} (l : List α) : List α :=
  l ++ l ++ l

/-- Nine-fold repetition `repeatThree (repeatThree l)`, representing `l⁹ = (l³)³`.
Forces idempotent nodes to contain a three-fold repetition in at least one child. -/
def repeatNine {α : Type*} (l : List α) : List α :=
  repeatThree (repeatThree l)

/-- 27-fold repetition `repeatThree (repeatNine l)`, representing `l²⁷ = ((l³)³)³`.
Forces tree height to decrease by at least 2 levels across grandparent and grandchild nodes. -/
def repeatTwentySeven {α : Type*} (l : List α) : List α :=
  repeatThree (repeatNine l)

/-- `repeatThree l` is non-empty if `l` is non-empty. -/
lemma repeatThree_ne_nil {α : Type*} {l : List α} (hl : l ≠ []) : repeatThree l ≠ [] :=
  fun h ↦ hl (List.append_eq_nil_iff.mp h).right

/-- `repeatNine l` is non-empty if `l` is non-empty. -/
lemma repeatNine_ne_nil {α : Type*} {l : List α} (hl : l ≠ []) : repeatNine l ≠ [] :=
  repeatThree_ne_nil (repeatThree_ne_nil hl)

/-- `repeatTwentySeven l` is non-empty if `l` is non-empty. -/
lemma repeatTwentySeven_ne_nil {α : Type*} {l : List α} (hl : l ≠ []) : repeatTwentySeven l ≠ [] :=
  repeatThree_ne_nil (repeatNine_ne_nil hl)

/-- Elements of `repeatThree l` belong to `l`. -/
lemma mem_repeatThree {α : Type*} {l : List α} {x : α} (hx : x ∈ repeatThree l) : x ∈ l := by
  grind [repeatThree]

/-- Elements of `repeatNine l` belong to `l`. -/
lemma mem_repeatNine {α : Type*} {l : List α} {x : α} (hx : x ∈ repeatNine l) : x ∈ l :=
  mem_repeatThree (mem_repeatThree hx)

/-- Elements of `repeatTwentySeven l` belong to `l`. -/
lemma mem_repeatTwentySeven {α : Type*} {l : List α} {x : α}
    (hx : x ∈ repeatTwentySeven l) : x ∈ l :=
  mem_repeatNine (mem_repeatThree hx)

/-- If `X ++ Y = Z ++ W` and `|Z| ≤ |X|`, then `Z` is a prefix of `X`. -/
lemma prefix_of_append_eq_append_left {α : Type*} (X Y Z W : List α)
    (h : X ++ Y = Z ++ W) (hle : Z.length ≤ X.length) :
    Z <+: X := by
  grind [congrArg (List.take Z.length) h]

/-- If a triple repetition `l ++ l ++ l` occurs in an append `A ++ B`,
then `l` is an infix of `A` or an infix of `B`. -/
lemma repeatThree_append_cases {α : Type*} (l : List α) (_ : l ≠ [])
    (A B : List α) (s t : List α) (h : A ++ B = s ++ (l ++ l ++ l) ++ t) :
    l <:+: A ∨ l <:+: B := by
  by_cases hA : s.length + l.length ≤ A.length
  · left
    have h_pref := prefix_of_append_eq_append_left A B (s ++ l) (l ++ l ++ t)
      (h.trans (by simp [List.append_assoc])) (by simpa using hA)
    exact List.IsInfix.trans ⟨s, [], by simp⟩ h_pref.isInfix
  · right
    have hB_drop : B = (A ++ B).drop A.length := by simp
    grind

/-- `l` is an infix of `repeatThree l`. -/
lemma infix_repeatThree_of_self {α : Type*} (l : List α) : l <:+: repeatThree l :=
  ⟨[], l ++ l, by simp [repeatThree]⟩

/-- `repeatThree l` is an infix of `repeatNine l`. -/
lemma repeatThree_isInfix_repeatNine {α : Type*} (l : List α) : repeatThree l <:+: repeatNine l :=
  infix_repeatThree_of_self (repeatThree l)

/-- `repeatNine l` is an infix of `repeatTwentySeven l`. -/
lemma repeatNine_isInfix_repeatTwentySeven {α : Type*} (l : List α) :
    repeatNine l <:+: repeatTwentySeven l := infix_repeatThree_of_self (repeatNine l)

/-- `l` is an infix of `repeatNine l`. -/
lemma infix_repeatNine_of_self {α : Type*} (l : List α) : l <:+: repeatNine l :=
  (infix_repeatThree_of_self l).trans (repeatThree_isInfix_repeatNine l)

/-- `l` is an infix of `repeatTwentySeven l`. -/
lemma infix_repeatTwentySeven_of_self {α : Type*} (l : List α) : l <:+: repeatTwentySeven l :=
  (infix_repeatNine_of_self l).trans (repeatNine_isInfix_repeatTwentySeven l)

/-- If `repeatThree l` is an infix of `A ++ B`, then `l` is an infix of `A` or an infix of `B`. -/
lemma repeatThree_isInfix_append {α : Type*} (l : List α) (hl : l ≠ [])
    (A B : List α) : repeatThree l <:+: A ++ B → l <:+: A ∨ l <:+: B
  | ⟨s, t, hst⟩ => repeatThree_append_cases l hl A B s t hst.symm

/-- If `repeatNine l` is an infix of `A ++ B`, then `repeatThree l` is an infix of `A` or `B`. -/
lemma repeatNine_isInfix_append {α : Type*} (l : List α) (hl : l ≠ [])
    (A B : List α) (h : repeatNine l <:+: A ++ B) :
    repeatThree l <:+: A ∨ repeatThree l <:+: B :=
  repeatThree_isInfix_append (repeatThree l) (repeatThree_ne_nil hl) A B h

/-- If `repeatTwentySeven l` is an infix of `A ++ B`,
then `repeatNine l` is an infix of `A` or `B`. -/
lemma repeatTwentySeven_isInfix_append {α : Type*} (l : List α) (hl : l ≠ [])
    (A B : List α) (h : repeatTwentySeven l <:+: A ++ B) :
    repeatNine l <:+: A ∨ repeatNine l <:+: B :=
  repeatThree_isInfix_append (repeatNine l) (repeatNine_ne_nil hl) A B h

/-- If a non-empty word `u` is an infix of `listValue cs` and no single child has `u` as an infix,
then `u` is an infix of at most two consecutive children. -/
lemma infix_listValue_cases {α : Type*} (cs : List (FactorizationTree α))
    (u : List α) (hu : u ≠ [])
    (h_no : ∀ c ∈ cs, ¬ (value c <:+: u))
    (h_inf : u <:+: listValue cs) :
    (∃ c ∈ cs, u <:+: value c) ∨
    (∃ c_left ∈ cs, ∃ c_right ∈ cs, u <:+: value c_left ++ value c_right) := by
  induction cs with
  | nil =>
    have h_len := h_inf.length_le
    simp only [listValue, List.map_nil, List.flatten_nil, List.length_nil] at h_len
    cases u with
    | nil => contradiction
    | cons head tail =>
      simp only [List.length_cons] at h_len
      omega
  | cons c cs' ih =>
    obtain ⟨s, t, hst⟩ := h_inf
    have h_app : c.value ++ listValue cs' = s ++ u ++ t := hst.symm
    by_cases h_take_le : (s ++ u).length ≤ (value c).length
    · left
      have h_pref := prefix_of_append_eq_append_left (value c) (listValue cs') (s ++ u) t
        (by rw [h_app, List.append_assoc]) (by simpa using h_take_le)
      exact ⟨c, .head _, (show u <:+: s ++ u from ⟨s, [], by simp⟩).trans h_pref.isInfix⟩
    · by_cases h_drop_le : (value c).length ≤ s.length
      · have h_drop : listValue cs' = s.drop (value c).length ++ u ++ t := by
          have h_d := congrArg (List.drop (value c).length) h_app
          rw [List.drop_left] at h_d
          have h_split : s ++ u ++ t = s ++ (u ++ t) := by simp only [List.append_assoc]
          rw [h_split, List.drop_append] at h_d
          have h_sub : (value c).length - s.length = 0 := by omega
          rw [h_sub, List.drop_zero] at h_d
          rw [← List.append_assoc] at h_d
          exact h_d
        have h_inf_cs' : u <:+: listValue cs' := by
          use s.drop (value c).length, t
          exact h_drop.symm
        have h_no_cs' : ∀ d ∈ cs', ¬ (value d <:+: u) := fun d hd =>
          h_no d (.tail c hd)
        grind
      · right
        simp only [List.length_append] at h_take_le
        have h_len_lt_su : (value c).length < s.length + u.length := by omega
        have h_s_lt_len : s.length < (value c).length := by omega
        let k := (value c).length - s.length
        have hk_pos : 0 < k := by omega
        have hk_lt : k < u.length := by omega
        have h_split : s ++ u ++ t = (s ++ u.take k) ++ (u.drop k ++ t) := by
          have h_take_drop := List.take_append_drop k u
          nth_rw 1 [← h_take_drop]
          simp only [List.append_assoc]
        have h_take_c : value c = s ++ u.take k := by
          have h_t := congrArg (List.take (value c).length) h_app
          rw [List.take_left] at h_t
          rw [h_split, List.take_append] at h_t
          have h_diff_zero : (value c).length - (s ++ u.take k).length = 0 := by
            simp only [List.length_append, List.length_take]
            omega
          rw [h_diff_zero, List.take_zero, List.append_nil] at h_t
          have h_len_take : (s ++ u.take k).length ≤ (value c).length := by
            simp only [List.length_append, List.length_take]
            omega
          rw [List.take_of_length_le h_len_take] at h_t
          exact h_t
        have h_drop_cs' : c.value ++ listValue cs' = (s ++ u.take k) ++ (u.drop k ++ t) := by
          rw [h_app, h_split]
        have h_drop_cs'' : listValue cs' = u.drop k ++ t := by
          rw [h_take_c] at h_drop_cs'
          exact List.append_cancel_left h_drop_cs'
        cases cs' with
        | nil =>
          grind [congrArg List.length h_drop_cs'', listValue, List.flatten_nil, List.length_nil,
            List.length_append, List.length_drop]
        | cons c' cs'' =>
          dsimp [listValue] at h_drop_cs''
          by_cases h_drop_le_c' : (u.drop k).length ≤ (value c').length
          · have h_pref := prefix_of_append_eq_append_left (value c') (listValue cs'')
              (u.drop k) t h_drop_cs'' h_drop_le_c'
            obtain ⟨w, hw⟩ := h_pref
            grind [List.append_assoc, List.take_append_drop]
          · have h_c'_le_drop : (value c').length ≤ (u.drop k).length := by omega
            have h_pref := prefix_of_append_eq_append_left (u.drop k) t (value c')
              (listValue cs'') h_drop_cs''.symm h_c'_le_drop
            grind [prefix_of_append_eq_append_left, List.take_append_drop k u, h_pref.isInfix.trans]

/-- A tree that is not a leaf has height at least 1. -/
lemma height_pos_of_not_leaf {α : Type*} (t : FactorizationTree α)
    (h : ∀ a, t ≠ FactorizationTree.leaf a) : 1 ≤ t.height := by
  cases t <;> first | exact (h _ rfl).elim | simp [height_binary, height_idempotent]

/-- The height of any tree in a list is bounded by `listHeight`. -/
lemma mem_listHeight_le {α : Type*} {c : FactorizationTree α} {cs : List (FactorizationTree α)}
    (hc : c ∈ cs) : c.height ≤ FactorizationTree.listHeight cs := by
  induction cs with
  | nil => contradiction
  | cons head tail ih =>
    cases hc with
    | head => exact le_max_left _ _
    | tail _ h => exact (ih h).trans (le_max_right _ _)

/-- The height of an idempotent tree is strictly greater than the height of each of its children. -/
lemma height_ge_child_of_idempotent {α : Type*} {cs : List (FactorizationTree α)}
    {c : FactorizationTree α} (hc : c ∈ cs) :
    c.height + 1 ≤ (FactorizationTree.idempotent cs).height := by
  grind [height_idempotent, mem_listHeight_le hc]

/-- The height of a binary tree is strictly greater than the height of its left subtree. -/
lemma height_ge_child_of_binary_left {α : Type*} (l r : FactorizationTree α) :
    l.height + 1 ≤ (FactorizationTree.binary l r).height := by grind [height_binary]

/-- The height of a binary tree is strictly greater than the height of its right subtree. -/
lemma height_ge_child_of_binary_right {α : Type*} (l r : FactorizationTree α) :
    r.height + 1 ≤ (FactorizationTree.binary l r).height := by grind [height_binary]

/-- Inductive sequence of hard words `w_k`: constructed inductively by
taking 27 copies of the previous word and appending the next letter `k+1`. -/
def w (n : ℕ) (hn : 0 < n) : ℕ → List (MaxSemigroup n)
  | 0 => repeatTwentySeven [botEl n hn]
  | k + 1 =>
    if h : k + 1 < n then
      repeatTwentySeven (repeatTwentySeven (w n hn k) ++ [⟨k + 1, h⟩])
    else
      repeatTwentySeven (w n hn k)

/-- The word `w_k` is non-empty for all `k`. -/
lemma w_ne_nil (n : ℕ) (hn : 0 < n) : ∀ k : ℕ, w n hn k ≠ []
  | 0 => repeatTwentySeven_ne_nil (by simp)
  | k + 1 => by
    dsimp [w]
    split_ifs <;> exact repeatTwentySeven_ne_nil (by simp [w_ne_nil n hn k])

/-- Every element in `w_k` is at most `k`. -/
lemma w_mem_le (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n)
    (x : MaxSemigroup n) (hx : x ∈ w n hn k) : x.val ≤ k := by
  induction k generalizing x with
  | zero =>
    have := mem_repeatTwentySeven hx
    cases this with | head => rfl | tail _ h => contradiction
  | succ k' ih =>
    dsimp [w] at hx
    rw [dite_eq_left hk] at hx
    rcases List.mem_append.mp (mem_repeatTwentySeven hx) with h | h
    · exact (ih (by omega) x (mem_repeatTwentySeven h)).trans (Nat.le_succ _)
    · cases h with | head => rfl | tail _ h => contradiction

/-- Every element in `w_k` is strictly less than `k+1`. -/
lemma w_mem_lt (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (x : MaxSemigroup n) (hx : x ∈ w n hn k) : x < ⟨k + 1, hk⟩ :=
  Nat.lt_succ_of_le (w_mem_le n hn k (by omega) x hx)

/-- The 9-fold repetition of a non-empty list has length at least 9. -/
lemma repeatNine_length_ge {α : Type*} (l : List α) (hl : l ≠ []) : 9 ≤ (repeatNine l).length := by
  grind [List.length_pos_iff, repeatNine, repeatThree]

/-- The 27-fold repetition of a non-empty list has length at least 27. -/
lemma repeatTwentySeven_length_ge {α : Type*} (l : List α) (hl : l ≠ []) :
    27 ≤ (repeatTwentySeven l).length := by
  grind [List.length_pos_iff, repeatTwentySeven, repeatNine, repeatThree]

/-- If a 9-fold repetition of `w_k` occurs in a tree that also contains a large element,
a child tree contains `w_k`. -/
lemma exists_child_w_of_repeatNine_w {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (C : FactorizationTree (MaxSemigroup n))
    (hC_ramsey : C.IsRamsey (evalMax n hn))
    (h_inf : repeatNine (w n hn k) <:+: C.value)
    (h_ge : ∃ y ∈ C.value, ⟨k + 1, hk⟩ ≤ y) :
    ∃ g : FactorizationTree (MaxSemigroup n),
      g.IsRamsey (evalMax n hn) ∧ g.height + 1 ≤ C.height ∧ w n hn k <:+: g.value := by
  have hw_ne := w_ne_nil n hn k
  cases C with
  | leaf a =>
    grind [value_leaf, repeatNine_length_ge (w n hn k) hw_ne]
  | binary l r =>
    rw [isRamsey_binary] at hC_ramsey
    obtain ⟨hC_l, hC_r⟩ := hC_ramsey
    rw [value_binary] at h_inf
    rcases repeatNine_isInfix_append (w n hn k) hw_ne l.value r.value h_inf with h | h
    · exact ⟨l, hC_l, height_ge_child_of_binary_left l r,
        (infix_repeatThree_of_self _).trans h⟩
    · exact ⟨r, hC_r, height_ge_child_of_binary_right l r,
        (infix_repeatThree_of_self _).trans h⟩
  | idempotent gs =>
    rw [value_idempotent] at h_inf h_ge
    rw [isRamsey_idempotent] at hC_ramsey
    obtain ⟨hlen, hgs_ramsey, e, he_idem, he_eval⟩ := hC_ramsey
    obtain ⟨y, hy_val, hky⟩ := h_ge
    obtain ⟨t_wit, ht_wit_mem, hyt_wit⟩ := mem_listValue hy_val
    have h_bot_lt : botEl n hn < ⟨k + 1, hk⟩ := Nat.succ_pos k
    let v := repeatNine (w n hn k)
    have hv_ne : v ≠ [] := repeatNine_ne_nil hw_ne
    have hv_lt : ∀ z ∈ v, z < ⟨k + 1, hk⟩ := fun z hz =>
      w_mem_lt n hn k hk z (mem_repeatNine hz)
    have h_no_child : ∀ g ∈ gs, ¬ (g.value <:+: v) := fun g hg =>
      no_child_infix_of_all_lt hn hgs_ramsey e he_eval ⟨k + 1, hk⟩ h_bot_lt
        t_wit ht_wit_mem y hyt_wit hky v hv_lt g hg
    rcases infix_listValue_cases gs v hv_ne h_no_child h_inf with
      ⟨g, hg, hgv⟩ | ⟨g_left, hg_left, g_right, hg_right, hg_append⟩
    · exact ⟨g, isRamsey_of_mem_listIsRamsey hgs_ramsey hg, height_ge_child_of_idempotent hg,
        (infix_repeatNine_of_self _).trans hgv⟩
    · rcases repeatNine_isInfix_append (w n hn k)
        hw_ne g_left.value g_right.value hg_append with h | h
      · exact ⟨g_left, isRamsey_of_mem_listIsRamsey hgs_ramsey hg_left,
          height_ge_child_of_idempotent hg_left, (infix_repeatThree_of_self _).trans h⟩
      · exact ⟨g_right, isRamsey_of_mem_listIsRamsey hgs_ramsey hg_right,
          height_ge_child_of_idempotent hg_right, (infix_repeatThree_of_self _).trans h⟩

/-- If a 9-fold repetition occurs in a tree,
there exists a child tree of strictly smaller height containing `w_k`. -/
lemma exists_child_w_of_repeatNine_step {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (C : FactorizationTree (MaxSemigroup n))
    (hC_ramsey : C.IsRamsey (evalMax n hn))
    (h_inf : repeatNine (repeatTwentySeven (w n hn k) ++ [⟨k + 1, hk⟩]) <:+: C.value) :
    ∃ g : FactorizationTree (MaxSemigroup n),
      g.IsRamsey (evalMax n hn) ∧ g.height + 1 ≤ C.height ∧ w n hn k <:+: g.value := by
  let X := repeatTwentySeven (w n hn k) ++ [⟨k + 1, hk⟩]
  have hw_inf : repeatNine (w n hn k) <:+: C.value :=
    (repeatNine_isInfix_repeatTwentySeven (w n hn k)).trans
      ((List.IsInfix.trans ⟨[], [⟨k + 1, hk⟩], by simp [X]⟩ (infix_repeatNine_of_self X)).trans
        h_inf)
  have h_mem_X : ⟨k + 1, hk⟩ ∈ X := List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have h_ge : ∃ y ∈ C.value, ⟨k + 1, hk⟩ ≤ y :=
    ⟨⟨k + 1, hk⟩, h_inf.subset ((infix_repeatNine_of_self X).subset h_mem_X), le_rfl⟩
  exact exists_child_w_of_repeatNine_w hn k hk C hC_ramsey hw_inf h_ge

/-- If `w_{k+1}` occurs in a Ramsey tree,
there exists a descendant at distance at least 2 containing `w_k`. -/
lemma grandchild_has_w_of_w_succ {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (t : FactorizationTree (MaxSemigroup n))
    (ht_ramsey : t.IsRamsey (evalMax n hn))
    (h_inf : w n hn (k + 1) <:+: t.value) :
    ∃ g : FactorizationTree (MaxSemigroup n),
      g.IsRamsey (evalMax n hn) ∧ g.height + 2 ≤ t.height ∧ w n hn k <:+: g.value := by
  let X := repeatTwentySeven (w n hn k) ++ [⟨k + 1, hk⟩]
  have hw_succ : w n hn (k + 1) = repeatTwentySeven X := by
    dsimp [w]
    rw [dite_eq_left hk]
  rw [hw_succ] at h_inf
  have hX_ne : X ≠ [] := by simp [X]
  cases t with
  | leaf a =>
    grind [value_leaf, repeatTwentySeven_length_ge]
  | binary l r =>
    rw [isRamsey_binary] at ht_ramsey
    obtain ⟨ht_l, ht_r⟩ := ht_ramsey
    rw [value_binary] at h_inf
    rcases repeatTwentySeven_isInfix_append X hX_ne l.value r.value h_inf with h | h
    · obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ := exists_child_w_of_repeatNine_step hn k hk l ht_l h
      have := height_ge_child_of_binary_left l r
      exact ⟨g, hg_ram, by omega, hg_inf⟩
    · obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ := exists_child_w_of_repeatNine_step hn k hk r ht_r h
      have := height_ge_child_of_binary_right l r
      exact ⟨g, hg_ram, by omega, hg_inf⟩
  | idempotent cs =>
    rw [value_idempotent] at h_inf
    rw [isRamsey_idempotent] at ht_ramsey
    obtain ⟨hlen, hcs_ramsey, e, he_idem, he_eval⟩ := ht_ramsey
    have ha_in_list : ⟨k + 1, hk⟩ ∈ listValue cs :=
      h_inf.subset ((infix_repeatTwentySeven_of_self X).subset
        (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
    obtain ⟨t_wit, ht_wit_mem, hat_wit⟩ := mem_listValue ha_in_list
    have h_bot_lt : botEl n hn < ⟨k + 1, hk⟩ := Nat.succ_pos k
    have h_all_ge : ∀ c ∈ cs, ∃ y ∈ c.value, ⟨k + 1, hk⟩ ≤ y := fun c hc =>
      idempotent_children_mem_ge hn hcs_ramsey e he_eval
        ⟨k + 1, hk⟩ h_bot_lt t_wit ht_wit_mem ⟨k + 1, hk⟩ hat_wit le_rfl c hc
    let v := repeatTwentySeven (w n hn k)
    have hv_ne : v ≠ [] := repeatTwentySeven_ne_nil (w_ne_nil n hn k)
    have hv_lt : ∀ y ∈ v, y < ⟨k + 1, hk⟩ := fun y hy =>
      w_mem_lt n hn k hk y (mem_repeatTwentySeven hy)
    have h_no_child : ∀ c ∈ cs, ¬ (c.value <:+: v) := fun c hc =>
      no_child_infix_of_all_lt hn hcs_ramsey e he_eval
        ⟨k + 1, hk⟩ h_bot_lt t_wit ht_wit_mem ⟨k + 1, hk⟩ hat_wit le_rfl v hv_lt c hc
    have hw_X : v <:+: X := ⟨[], [⟨k + 1, hk⟩], by simp [X, v]⟩
    have hv_inf : v <:+: listValue cs :=
      hw_X.trans ((infix_repeatTwentySeven_of_self X).trans h_inf)
    have step (c : FactorizationTree (MaxSemigroup n)) (hc : c ∈ cs)
        (h : repeatNine (w n hn k) <:+: c.value) :
        ∃ g : FactorizationTree (MaxSemigroup n),
          g.IsRamsey (evalMax n hn) ∧ g.height + 2 ≤ (FactorizationTree.idempotent cs).height ∧
          w n hn k <:+: g.value := by
      obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ := exists_child_w_of_repeatNine_w hn k hk c
        (isRamsey_of_mem_listIsRamsey hcs_ramsey hc) h (h_all_ge c hc)
      have h_ht_c := height_ge_child_of_idempotent hc
      exact ⟨g, hg_ram, by omega, hg_inf⟩
    rcases infix_listValue_cases cs v hv_ne h_no_child hv_inf with
      ⟨c, hc, hcv⟩ | ⟨c_left, hc_left, c_right, hc_right, hc_append⟩
    · exact step c hc ((repeatNine_isInfix_repeatTwentySeven _).trans hcv)
    · rcases repeatTwentySeven_isInfix_append (w n hn k) (w_ne_nil n hn k)
          c_left.value c_right.value hc_append with h | h <;> grind

/-- Any Ramsey tree whose yield contains `w_k` as an infix must have height at least `2k+1`. -/
lemma height_ge_of_w_infix {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n)
    (t : FactorizationTree (MaxSemigroup n))
    (ht : t.IsRamsey (evalMax n hn))
    (h : w n hn k <:+: t.value) :
    2 * k + 1 ≤ t.height := by
  induction k generalizing t with
  | zero =>
    have h_not_leaf (a : MaxSemigroup n) : t ≠ FactorizationTree.leaf a := by
      grind [h.length_le, repeatTwentySeven_length_ge [botEl n hn] (by simp), w, value_leaf]
    grind [height_pos_of_not_leaf t h_not_leaf]
  | succ k' ih => grind [grandchild_has_w_of_w_succ]

/-- Tightness: for each `n ≥ 2`, there exists an aperiodic finite semigroup `S`
of size `n` and a word where **all** Ramsey trees have height at least `2 * n - 1`.
We use the semilattice `MaxSemigroup n = Fin n` with `max` multiplication. -/
theorem aperiodic_bound_tight (n : ℕ) (hn : 2 ≤ n) :
    ∃ (S : Type) (_ : Semigroup S) (_ : Fintype S) (_ : IsAperiodic S),
      Fintype.card S = n ∧
      ∃ (eval : List S → S)
        (_ : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
        (u : List S) (_ : u ≠ []),
        ∀ t : FactorizationTree S,
          t.value = u →
          t.IsRamsey eval →
          2 * n - 1 ≤ t.height := by
  have hn' : 0 < n := by omega
  have h_bound (t : FactorizationTree (MaxSemigroup n))
      (ht_val : t.value = w n hn' (n - 1)) (ht_ramsey : IsRamsey (evalMax n hn') t) :
      2 * n - 1 ≤ t.height := by
    grind [height_ge_of_w_infix hn' (n - 1) (by omega) t ht_ramsey (ht_val ▸ List.infix_refl _)]
  exact ⟨MaxSemigroup n, inferInstance, inferInstance, maxSemigroup_isAperiodic n,
    Fintype.card_fin n, evalMax n hn', fun u v _ _ => evalMax_append n hn' u v,
    w n hn' (n - 1), w_ne_nil n hn' (n - 1), h_bound⟩

end Tightness

section GreenHCharacterization

open GreensRelations

/-- A semigroup in which Green's `H`-relation is trivial (`a H b → a = b`) is aperiodic. -/
theorem isAperiodic_of_isGreenH_trivial {S : Type u} [Semigroup S]
    (h_Htriv : ∀ a b : S, IsGreenH a b → a = b) : IsAperiodic S := by
  intro G instGroup f hf_mul hf_inj
  have h_H (g : G) : IsGreenH (f g) (f 1) :=
    ⟨⟨.inr ⟨f g, by simp [← hf_mul]⟩, .inr ⟨f g⁻¹, by simp [← hf_mul]⟩⟩,
     ⟨.inr ⟨f g, by simp [← hf_mul]⟩, .inr ⟨f g⁻¹, by simp [← hf_mul]⟩⟩⟩
  exact ⟨fun a b ↦ hf_inj ((h_Htriv _ _ (h_H a)).trans (h_Htriv _ _ (h_H b)).symm)⟩

/-- In an aperiodic semigroup, every `H`-class that forms a group is a subsingleton. -/
theorem isGreenH_subsingleton_of_isGroup {S : Type u} [Semigroup S] (hAper : IsAperiodic S)
    {H : Set S} (h : IsGroup H) : Subsingleton H :=
  @hAper H h.group Subtype.val (fun _ _ ↦ rfl) Subtype.val_injective

/-- In an aperiodic finite semigroup, every `H`-class containing an idempotent is a singleton. -/
theorem isGreenH_eqvClass_subsingleton_of_idempotent {S : Type u} [Semigroup S] [Finite S]
    (hAper : IsAperiodic S) {a e : S} (he : e ∈ IsGreenH.eqvClass a)
    (he_idem : e * e = e) :
    ∀ x ∈ IsGreenH.eqvClass a, x = a :=
  have instSubsingleton := isGreenH_subsingleton_of_isGroup hAper
    (isGreenH_eqvClass_isGroup_of_idempotent ⟨a, rfl⟩ he he_idem)
  fun x hx ↦ Subtype.ext_iff.mp (@Subsingleton.elim _ instSubsingleton ⟨x, hx⟩ ⟨a, .refl a⟩)

end GreenHCharacterization

section AperiodicUpperBound

open RamseySplit GreensRelations

/-- In an aperiodic finite semigroup, the elements in the `H`-class of some idempotent
are precisely the idempotents themselves, because all subgroups are trivial. -/
lemma aperiodic_regular_dclass_elements_eq_idempotents {S : Type*} [Semigroup S] [Finite S]
    (hAper : IsAperiodic S) (D : Set S) :
    {x | x ∈ D ∧ ∃ e ∈ D, e * e = e ∧ IsGreenH x e} = {e | e ∈ D ∧ e * e = e} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hxD, e, heD, he_idem, hHxe⟩
    have he_in_H : e ∈ IsGreenH.eqvClass x := hHxe.symm
    have h_eq := isGreenH_eqvClass_subsingleton_of_idempotent hAper he_in_H he_idem e he_in_H
    subst h_eq
    exact ⟨heD, he_idem⟩
  · rintro ⟨hxD, hx_idem⟩
    exact ⟨hxD, x, hxD, hx_idem, IsGreenH.refl x⟩

open Classical in
/-- In an aperiodic finite semigroup, for any regular D-class `D`, `nD D` is the number
of idempotents in `D`. When `D` contains at most one idempotent, `nD D = 1`. -/
lemma nD_eq_card_idempotents_of_isAperiodic {S : Type*} [Semigroup S] [Fintype S]
    (hAper : IsAperiodic S) (D : Set S) (hD_reg : IsRegularDClass D) :
    nD D = (Finset.univ.filter (fun e ↦ e ∈ D ∧ e * e = e)).card := by
  dsimp [nD]
  rw [ite_eq_left hD_reg]
  congr 1
  ext x
  grind [congr_arg (fun s ↦ x ∈ s) (aperiodic_regular_dclass_elements_eq_idempotents hAper D)]

open Classical in
/-- If an aperiodic regular D-class has at most one idempotent, its complexity `nD D` is 1. -/
lemma nD_eq_one_of_isAperiodic_unique_idempotent {S : Type*} [Semigroup S] [Fintype S]
    (hAper : IsAperiodic S) (D : Set S) (hD_reg : IsRegularDClass D)
    (h_one : (Finset.univ.filter (fun e ↦ e ∈ D ∧ e * e = e)).card = 1) :
    nD D = 1 := by rw [nD_eq_card_idempotents_of_isAperiodic hAper D hD_reg, h_one]

/-- For any finite aperiodic semigroup `S`, every non-empty word admits a Ramsey
factorization tree of height at most `3 * |S| - 1`.
In an aperiodic semigroup, all groups are trivial, so each regular D-class satisfies `nD D = 1`,
and `nS S ≤ |S|`. -/
theorem aperiodic_factorization_forest_upper_bound {A S : Type*} [Semigroup S] [Fintype S]
    [Nonempty S] (_hAper : IsAperiodic S)
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ t : FactorizationTree A,
      t.value = u ∧
      t.IsRamsey eval ∧
      t.height ≤ 3 * Fintype.card S - 1 := by
  exact factorization_forest_classical_bound eval hmul u hu

/-- Upper bound for a semigroup homomorphism `ϕ : S →ₙ* T` into an aperiodic
finite semigroup `T`. -/
theorem aperiodic_factorization_forest_upper_bound_mulHom {S T : Type*} [Semigroup S] [Semigroup T]
    [Fintype T] [Nonempty T] (hAper : IsAperiodic T) (ϕ : S →ₙ* T) (u : List S) (hu : u ≠ []) :
    let eval_T : List S → T :=
      fun w ↦ if hw : w = [] then Classical.arbitrary T else ϕ (listProdNE w hw)
    ∃ t : FactorizationTree S,
      t.value = u ∧ t.IsRamsey eval_T ∧ t.height ≤ 3 * Fintype.card T - 1 := by
  intro eval_T
  have hmul_T (v w : List S) (hv : v ≠ []) (hw : w ≠ []) :
      eval_T (v ++ w) = eval_T v * eval_T w := by
    simp only [eval_T]
    rw [dite_eq_right (by simp [hv, hw]), dite_eq_right hv, dite_eq_right hw,
      listProdNE_concat v w hv hw, ϕ.map_mul]
  exact aperiodic_factorization_forest_upper_bound hAper eval_T hmul_T u hu

end AperiodicUpperBound

end Aperiodic
