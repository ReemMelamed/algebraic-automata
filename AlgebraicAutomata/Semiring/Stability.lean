/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import AlgebraicAutomata.Semiring.Tropical
import AlgebraicAutomata.Semigroup.LocallyFinite

/-!
# Matrix Stability and the Finite Closure Property

Stability of idempotent matrices over `𝕋₁`, Leung's path condition,
and decidability of the finite closure property via Brown's Lemma.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

variable {n : ℕ}

open BrownLemma

/-- Stability of an idempotent matrix `M` over `𝕋₁`:
for every non-infinity entry `(i, j)`, there is an intermediate state `k` with `M k k = 0`. -/
def IsStableTrop1 (M : Matrix (Fin n) (Fin n) Trop1) : Prop :=
  ∀ i j, M i j ≠ Trop1.infty →
    ∃ k, M i k ≠ Trop1.infty ∧ M k k = Trop1.zero ∧ M k j ≠ Trop1.infty

/-- Leung's combinatorial condition on a matrix `A` over `𝕋`:
each finite entry is bridged through a zero diagonal entry. -/
def LeungCondition (A : Matrix (Fin n) (Fin n) Trop) : Prop :=
  ∀ i j, A i j ≠ 0 →
    ∃ k, A i k ≠ 0 ∧ A k k = 1 ∧ A k j ≠ 0

lemma leungCondition_iff_isStableTrop1 (A : Matrix (Fin n) (Fin n) Trop) :
    LeungCondition A ↔ IsStableTrop1 (projMat A) := by
  dsimp [LeungCondition, IsStableTrop1, projMat, Matrix.map_apply]
  simp only [toTrop1.toTrop1_eq_infty_iff, toTrop1.toTrop1_eq_zero_iff]

/-- An idempotent matrix `A` over `𝕋` is stable if it generates a finite subsemigroup. -/
def IsStableTrop (A : Matrix (Fin n) (Fin n) Trop) : Prop :=
  (Subsemigroup.closure {A} : Set (Matrix (Fin n) (Fin n) Trop)).Finite

/-- A matrix `A` is projectively idempotent if its projection in `𝕋₁` is idempotent. -/
def IsProjIdempotent (A : Matrix (Fin n) (Fin n) Trop) : Prop :=
  projMat A * projMat A = projMat A

/-- Canonical projection of a subsemigroup of `𝕋^{n × n}` into `𝕋₁^{n × n}`. -/
def projMatSubsemigroup (S : Subsemigroup (Matrix (Fin n) (Fin n) Trop)) :
    S →ₙ* Matrix (Fin n) (Fin n) Trop1 where
  toFun A := projMat A.1
  map_mul' A B := projMat_mul A.1 B.1

/-- Application of Brown's Lemma to matrix semigroups over the tropical semiring:
if all idempotent fibers under the projection `toTrop1` are locally finite,
then the tropical matrix subsemigroup is locally finite. -/
theorem isLocallyFinite_of_idempotent_fibers
    (S : Subsemigroup (Matrix (Fin n) (Fin n) Trop))
    (h_fibers : ∀ (e : Matrix (Fin n) (Fin n) Trop1) (he : e * e = e),
      IsLocallyFinite (fiberSubsemigroup (projMatSubsemigroup S) e he)) :
    IsLocallyFinite S :=
  brown_lemma (projMatSubsemigroup S) (fun _ _ ↦ Set.toFinite _) h_fibers
