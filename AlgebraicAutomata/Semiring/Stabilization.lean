/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import AlgebraicAutomata.Semiring.Stability

/-!
# Leung's Stabilization Operator and Closure

Leung's stabilization operator `M♯` on idempotent matrices over `𝕋₁`
and the finite stabilization closure `⟨Z⟩♯`.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

variable {n : ℕ}

/-- Leung's stabilization operation `M♯` on a matrix `M` over `𝕋₁`:
entries that grow unboundedly under iteration are set to `∞`. -/
def stabilize (M : Matrix (Fin n) (Fin n) Trop1) : Matrix (Fin n) (Fin n) Trop1 :=
  fun i j ↦
    if M i j = Trop1.zero then Trop1.zero
    else if M i j = Trop1.one ∧
        (∃ k, M i k ≠ Trop1.infty ∧ M k k = Trop1.zero ∧ M k j ≠ Trop1.infty) then Trop1.one
    else Trop1.infty

postfix:max "♯" => stabilize

lemma stabilize_zero {M : Matrix (Fin n) (Fin n) Trop1} {i j : Fin n}
    (h : M i j = Trop1.zero) : (M♯) i j = Trop1.zero := ite_eq_left h

lemma stabilize_le (M : Matrix (Fin n) (Fin n) Trop1) (i j : Fin n) :
    M i j ≤ (M♯) i j := by
  dsimp [stabilize]
  split_ifs with h1 h2
  · rw [h1]
  · rw [h2.1]
  · exact Trop1.le_infty (M i j)

lemma stabilize_eq_of_isStable {M : Matrix (Fin n) (Fin n) Trop1}
    (h : IsStableTrop1 M) : M♯ = M := by
  ext i j
  dsimp [stabilize]
  split_ifs with h0 h1
  · exact h0.symm
  · exact h1.1.symm
  · by_cases h_inf : M i j = Trop1.infty
    · exact h_inf.symm
    · obtain ⟨k, hik, hkk, hkj⟩ := h i j h_inf
      rcases h_val : M i j with _ | _ | _
      · exact (h0 h_val).elim
      · exact (h1 ⟨h_val, k, hik, hkk, hkj⟩).elim
      · exact (h_inf h_val).elim

lemma isStable_of_stabilize_eq {M : Matrix (Fin n) (Fin n) Trop1}
    (h_zero_diag : ∀ i j, M i j = Trop1.zero →
      ∃ k, M i k ≠ Trop1.infty ∧ M k k = Trop1.zero ∧ M k j ≠ Trop1.infty)
    (h : M♯ = M) : IsStableTrop1 M := by
  intro i j hij
  cases h_val : M i j with
  | zero => exact h_zero_diag i j h_val
  | one =>
    have h_sharp : (M♯) i j = Trop1.one := by rw [h, h_val]
    unfold stabilize at h_sharp
    split_ifs at h_sharp with h0 h1
    exact h1.2
  | infty => contradiction

/-- The stabilization closure `⟨Z⟩♯` of a set of matrices `Z ⊆ 𝕋₁^{n × n}`:
closed under matrix product and stabilization of idempotent matrices. -/
inductive StabilizationClosure (Z : Set (Matrix (Fin n) (Fin n) Trop1)) :
    Set (Matrix (Fin n) (Fin n) Trop1) where
  | of (M : Matrix (Fin n) (Fin n) Trop1) (h : M ∈ Z) :
      StabilizationClosure Z M
  | mul (M N : Matrix (Fin n) (Fin n) Trop1)
      (hM : StabilizationClosure Z M) (hN : StabilizationClosure Z N) :
      StabilizationClosure Z (M * N)
  | sharp (M : Matrix (Fin n) (Fin n) Trop1)
      (hM : StabilizationClosure Z M) (hidem : M * M = M) :
      StabilizationClosure Z (M♯)

/-- The stabilization closure is always finite because `𝕋₁^{n × n}` is a finite type. -/
instance (Z : Set (Matrix (Fin n) (Fin n) Trop1)) :
    Finite (StabilizationClosure Z) :=
  Set.toFinite (StabilizationClosure Z)

lemma subset_stabilizationClosure (Z : Set (Matrix (Fin n) (Fin n) Trop1)) :
    Z ⊆ StabilizationClosure Z :=
  fun _ h ↦ StabilizationClosure.of _ h
