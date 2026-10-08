/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.List.Basic

/-!
# Slice operations on lists (drop and take combinations)

Lemmas concerning taking slices of lists using `(u.drop i).take (j - i)`,
including concatenations and behavior with append.
-/

variable {A : Type*}

-- TODO: Upstream to Mathlib.Data.List.Basic
lemma list_drop_take_append (u : List A) (i k j : ℕ) (hik : i ≤ k) (hkj : k ≤ j) :
    (u.drop i).take (k - i) ++ (u.drop k).take (j - k) = (u.drop i).take (j - i) := by
  have h_drop : u.drop k = (u.drop i).drop (k - i) := by
    rw [List.drop_drop, Nat.add_sub_cancel' hik]
  rw [h_drop]
  have h_take_drop (l : List A) (a b : ℕ) : l.take a ++ (l.drop a).take b = l.take (a + b) := by
    grind
  grind

-- TODO: Upstream to Mathlib.Data.List.Basic
lemma list_drop_take_one (u : List A) (i : ℕ) (hi : i < u.length) :
    (u.drop i).take 1 = [u[i]] :=
  congrArg (List.take 1) (List.drop_eq_getElem_cons hi)

-- TODO: Upstream to Mathlib.Data.List.Basic
lemma list_drop_take_append_left (u v : List A) (i j : ℕ) (hj : j ≤ u.length) :
    ((u ++ v).drop i).take (j - i) = (u.drop i).take (j - i) := by
  by_cases hij : i ≤ j
  · simpa [List.drop_take] using congrArg (List.drop i) (List.take_append_of_le_length hj)
  · simp [show j - i = 0 by omega]

-- TODO: Upstream to Mathlib.Data.List.Basic
lemma list_drop_take_append_right (u v : List A) (i j : ℕ) (hi : u.length ≤ i) :
    ((u ++ v).drop i).take (j - i) = (v.drop (i - u.length)).take (j - i) := by
  rw [List.drop_append, List.drop_eq_nil_of_le hi, List.nil_append]
