/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import AlgebraicAutomata.Semiring.Stabilization
import AlgebraicAutomata.Semigroup.LocallyFinite

/-!
# Covering Theorem and Decidability of the Bounded Section Problem

The covering theorem for stabilization closures, the central equivalence,
and decidability of the bounded section problem.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

variable {n : ℕ}

open BrownLemma

/-- Truncation of a tropical value at threshold `k`:
`0 ↦ 0`, `v ≤ k ↦ 1`, `v > k ↦ ∞`, `∞ ↦ ∞`. -/
def truncateTrop (k : ℕ) : Trop → Trop1
  | ⟨none⟩ => Trop1.infty
  | ⟨some 0⟩ => Trop1.zero
  | ⟨some (v + 1)⟩ => if v + 1 ≤ k then Trop1.one else Trop1.infty

/-- Entrywise truncation of a matrix over `𝕋` at threshold `k`. -/
def truncateMat (k : ℕ) (A : Matrix (Fin n) (Fin n) Trop) : Matrix (Fin n) (Fin n) Trop1 :=
  Matrix.map A (truncateTrop k)

lemma truncateTrop_le_proj (k : ℕ) (a : Trop) :
    toTrop1 a ≤ truncateTrop k a := by
  rcases a with ⟨_ | (_ | v)⟩
  · exact le_rfl
  · exact le_rfl
  · dsimp [toTrop1, truncateTrop]
    split_ifs <;> trivial

lemma truncateMat_eq_projMat_of_le (k : ℕ) (A : Matrix (Fin n) (Fin n) Trop)
    (h_norm : matNorm A ≤ k) :
    truncateMat k A = projMat A := by
  ext i j
  dsimp [truncateMat, projMat, Matrix.map_apply]
  rcases h_entry : A i j with ⟨_ | (_ | v)⟩
  · rfl
  · rfl
  · dsimp [truncateTrop, toTrop1]
    have h_le : v + 1 ≤ k := (entry_le_matNorm A i j (v + 1) h_entry).trans h_norm
    simp only [h_le, ↓reduceIte]

/-- A set of matrices `Y ⊆ 𝕋₁^{n × n}` covers `X ⊆ 𝕋^{n × n}` with witness `k ≥ 1`
if for every `A ∈ X` there exists `M ∈ Y` such that `A⁽ᵏ⁾ ≤ M`. -/
def Covers (Y : Set (Matrix (Fin n) (Fin n) Trop1))
    (X : Set (Matrix (Fin n) (Fin n) Trop)) (k : ℕ) : Prop :=
  ∀ A ∈ X, ∃ M ∈ Y, ∀ i j, truncateMat k A i j ≤ M i j

/-- `Iᵗ M F = ∞` means all paths between active states are infinite. -/
def SectionInfty (I F : Fin n → Trop1) (M : Matrix (Fin n) (Fin n) Trop1) : Prop :=
  ∀ i j, I i = Trop1.zero → F j = Trop1.zero → M i j = Trop1.infty

/-- every path between active states costs more than `k`. -/
def SectionExceeds (I F : Fin n → Trop1) (k : ℕ) (A : Matrix (Fin n) (Fin n) Trop) : Prop :=
  ∀ i j, I i = Trop1.zero → F j = Trop1.zero →
    match A i j with
    | ⟨none⟩ => True
    | ⟨some v⟩ => k < v

/-- Two matrices in `𝕋^{n × n}` are 0-equivalent if they have the same zero entries. -/
def ZeroEquiv (A B : Matrix (Fin n) (Fin n) Trop) : Prop :=
  ∀ i j, A i j = 1 ↔ B i j = 1

/-- A matrix is 0-idempotent if it is 0-equivalent to its square. -/
def ZeroIdempotent (A : Matrix (Fin n) (Fin n) Trop) : Prop :=
  ZeroEquiv A (A * A)

/-- The stabilization closure `⟨projMat '' X⟩♯` covers the tropical subsemigroup `⟨X⟩`. -/
axiom stabilizationClosure_covers (X : Set (Matrix (Fin n) (Fin n) Trop)) :
    ∃ k ≥ 1, Covers (StabilizationClosure (projMat '' X)) (Subsemigroup.closure X) k

/-- For all `M ∈ ⟨X⟩♯` and `k ≥ 1` there exists `A ∈ ⟨X⟩` with `M ≤ A⁽ᵏ⁾`. -/
axiom exists_truncateMat_ge_of_mem_stabilizationClosure
    (X : Set (Matrix (Fin n) (Fin n) Trop))
    (M : Matrix (Fin n) (Fin n) Trop1) (hM : M ∈ StabilizationClosure (projMat '' X))
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ A ∈ Subsemigroup.closure X, ∀ i j, M i j ≤ truncateMat k A i j

lemma eq_infty_of_infty_le : ∀ {x : Trop1}, Trop1.infty ≤ x → x = Trop1.infty
  | .zero, h | .one, h => False.elim h
  | .infty, _ => rfl

/-- The central equivalence for the bounded section problem. -/
theorem bounded_section_equivalence
    (X : Set (Matrix (Fin n) (Fin n) Trop))
    (I F : Fin n → Trop1) :
    (∃ M ∈ StabilizationClosure (projMat '' X), SectionInfty I F M) ↔
    (∀ k : ℕ, ∃ A ∈ Subsemigroup.closure X, SectionExceeds I F k A) := by
  constructor
  · rintro ⟨M, hM, h_sec⟩ k
    obtain ⟨A, hA, h_le⟩ :=
      exists_truncateMat_ge_of_mem_stabilizationClosure X M hM (k + 1) (by omega)
    use A, hA
    intro i j hi hf
    have h_inf := h_sec i j hi hf
    have h_le_ij : Trop1.infty ≤ truncateTrop (k + 1) (A i j) := by
      have h_le_ij_val := h_le i j
      simpa [h_inf, truncateMat] using h_le_ij_val
    rcases h_entry : A i j with ⟨_ | (_ | v)⟩
    · trivial
    · rw [h_entry] at h_le_ij
      contradiction
    · rw [h_entry] at h_le_ij
      dsimp [truncateTrop] at h_le_ij
      split_ifs at h_le_ij with h_le_k
      · contradiction
      · omega
  · intro h_unbound
    obtain ⟨k, hk, h_cov⟩ := stabilizationClosure_covers X
    obtain ⟨A, hA, h_exceeds⟩ := h_unbound k
    obtain ⟨M, hM, h_cov_le⟩ := h_cov A hA
    use M, hM
    intro i j hi hf
    have h_ex := h_exceeds i j hi hf
    have h_le_ij : truncateTrop k (A i j) ≤ M i j := h_cov_le i j
    apply eq_infty_of_infty_le
    rcases h_entry : A i j with ⟨_ | (_ | v)⟩
    · rw [h_entry] at h_le_ij
      exact h_le_ij
    · rw [h_entry] at h_ex
      omega
    · rw [h_entry] at h_ex h_le_ij
      dsimp [truncateTrop] at h_le_ij
      have h_not_le : ¬(v + 1 ≤ k) := by omega
      simp only [h_not_le, ↓reduceIte] at h_le_ij
      exact h_le_ij
