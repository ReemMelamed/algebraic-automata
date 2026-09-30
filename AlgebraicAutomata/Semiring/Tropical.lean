/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Tropical Semirings and Matrix Semigroups

The tropical semirings `𝕋` and `𝕋₁`, the canonical projection homomorphism,
and matrix norms over `𝕋`.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

/-- The tropical semiring `𝕋 = (ℕ ∪ {∞}, min, +)` wrapping `WithTop ℕ`,
with algebraic structure transferred directly from Mathlib's `MinTropical (WithTop ℕ)`.
Additive operation is `min` with zero `∞`.
Multiplicative operation is `+` with unit `0`. -/
@[ext]
structure Trop where
  toWithTop : WithTop ℕ
deriving DecidableEq, Inhabited

namespace Trop

/-- Equivalence between `Trop` and Mathlib's `MinTropical (WithTop ℕ)`. -/
def toMinTropicalEquiv : Trop ≃ MinTropical (WithTop ℕ) where
  toFun x := MinTropical.trop x.toWithTop
  invFun x := ⟨MinTropical.untrop x⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- CommSemiring instance transferred directly from Mathlib's `MinTropical (WithTop ℕ)`. -/
instance : CommSemiring Trop := Trop.toMinTropicalEquiv.commSemiring

/-- Canonical semiring isomorphism between `Trop` and Mathlib's `MinTropical (WithTop ℕ)`. -/
def toMinTropical : Trop ≃+* MinTropical (WithTop ℕ) :=
  Trop.toMinTropicalEquiv.ringEquiv

instance : Preorder Trop := Preorder.lift Trop.toWithTop

@[simp] lemma zero_toWithTop : (0 : Trop).toWithTop = ⊤ := rfl
@[simp] lemma one_toWithTop : (1 : Trop).toWithTop = 0 := rfl
@[simp] lemma add_toWithTop (a b : Trop) : (a + b).toWithTop = min a.toWithTop b.toWithTop := rfl
@[simp] lemma mul_toWithTop (a b : Trop) : (a * b).toWithTop = a.toWithTop + b.toWithTop := rfl

end Trop

/-- The reduced tropical semiring `𝕋₁ = ({0, 1, ∞}, min, +)`. -/
inductive Trop1
  | zero
  | one
  | infty
deriving DecidableEq, Inhabited

namespace Trop1

instance : Fintype Trop1 where
  elems := {Trop1.zero, Trop1.one, Trop1.infty}
  complete x := by cases x <;> simp

instance : Zero Trop1 where zero := infty
instance : One Trop1 where one := zero

def addOp : Trop1 → Trop1 → Trop1
  | infty, x => x
  | x, infty => x
  | zero, _ => zero
  | _, zero => zero
  | one, one => one

def mulOp : Trop1 → Trop1 → Trop1
  | infty, _ => infty
  | _, infty => infty
  | zero, x => x
  | x, zero => x
  | one, one => one

instance : Add Trop1 where add := addOp
instance : Mul Trop1 where mul := mulOp

instance : CommSemiring Trop1 where
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl
  zero_mul a := by cases a <;> rfl
  mul_zero a := by cases a <;> rfl
  nsmul n x := if n = 0 then 0 else x
  nsmul_zero x := rfl
  nsmul_succ n x := by cases n <;> cases x <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl

/-- Partial order on `𝕋₁`: `0 ≤ 1 ≤ ∞`. -/
instance : PartialOrder Trop1 where
  le a b := match a, b with
    | zero, _ => True
    | one, zero => False
    | one, one | one, infty => True
    | infty, infty => True
    | infty, _ => False
  le_refl a := by cases a <;> trivial
  le_trans a b c := by cases a <;> cases b <;> cases c <;> trivial
  le_antisymm a b h1 h2 := by
    cases a <;> cases b <;> first | rfl | contradiction

@[simp] lemma zero_le (a : Trop1) : (1 : Trop1) ≤ a := by cases a <;> trivial
@[simp] lemma le_infty (a : Trop1) : a ≤ 0 := by cases a <;> trivial

end Trop1

/-- Canonical projection homomorphism `toTrop1 : 𝕋 → 𝕋₁`. -/
def toTrop1 : Trop → Trop1
  | ⟨some 0⟩ => Trop1.zero
  | ⟨some (_ + 1)⟩ => Trop1.one
  | ⟨none⟩ => Trop1.infty

namespace toTrop1

lemma map_zero : toTrop1 0 = 0 := rfl
lemma map_one : toTrop1 1 = 1 := rfl

lemma map_add (a b : Trop) : toTrop1 (a + b) = toTrop1 a + toTrop1 b := by
  rcases a with ⟨_ | (_ | a)⟩ <;> rcases b with ⟨_ | (_ | b)⟩ <;> try rfl
  change toTrop1 ⟨some (min (a + 1) (b + 1))⟩ = Trop1.one + Trop1.one
  rw [Nat.succ_min_succ]
  rfl

lemma map_mul (a b : Trop) : toTrop1 (a * b) = toTrop1 a * toTrop1 b := by
  rcases a with ⟨_ | (_ | a)⟩ <;> rcases b with ⟨_ | (_ | b)⟩ <;> rfl

/-- `toTrop1` as a semiring homomorphism. -/
def hom : Trop →+* Trop1 where
  toFun := toTrop1
  map_zero' := map_zero
  map_one' := map_one
  map_add' := map_add
  map_mul' := map_mul

lemma toTrop1_eq_infty_iff (a : Trop) : toTrop1 a = Trop1.infty ↔ a = 0 := by
  cases a with | mk v => cases v with
  | top => simp [toTrop1]; rfl
  | coe m => cases m <;> simp [toTrop1, Trop.ext_iff]

lemma toTrop1_eq_zero_iff (a : Trop) : toTrop1 a = Trop1.zero ↔ a = 1 := by
  cases a with | mk v => cases v with
  | top => simp [toTrop1, Trop.ext_iff]
  | coe m => cases m <;> simp [toTrop1, Trop.ext_iff]

end toTrop1

section MatrixTrop

variable {n : ℕ}

/-- Projection of a matrix over `𝕋` to a matrix over `𝕋₁`. -/
def projMat (A : Matrix (Fin n) (Fin n) Trop) : Matrix (Fin n) (Fin n) Trop1 :=
  Matrix.map A toTrop1

lemma projMat_mul (A B : Matrix (Fin n) (Fin n) Trop) :
    projMat (A * B) = projMat A * projMat B := by
  ext i j
  dsimp [projMat, Matrix.mul_apply, Matrix.map_apply]
  exact (map_sum toTrop1.hom _ _).trans (by simp only [map_mul]; rfl)

/-- `projMat` as a multiplicative semigroup homomorphism. -/
def projMatHom (n : ℕ) :
    Matrix (Fin n) (Fin n) Trop →ₙ* Matrix (Fin n) (Fin n) Trop1 where
  toFun := projMat
  map_mul' := projMat_mul

/-- The finite entries of a matrix over `𝕋`. -/
def finiteEntries (A : Matrix (Fin n) (Fin n) Trop) : Finset ℕ :=
  Finset.univ.biUnion fun i ↦ Finset.univ.biUnion fun j ↦
    match A i j with
    | ⟨some v⟩ => {v}
    | ⟨none⟩ => ∅

/-- The norm `‖A‖` of a matrix over `𝕋`: maximum finite entry (or 1 if none). -/
def matNorm (A : Matrix (Fin n) (Fin n) Trop) : ℕ :=
  ({1} ∪ finiteEntries A).max' (by simp)

lemma one_le_matNorm (A : Matrix (Fin n) (Fin n) Trop) : 1 ≤ matNorm A :=
  Finset.le_max' _ 1 (Finset.mem_union_left _ (Finset.mem_singleton_self 1))

lemma entry_le_matNorm (A : Matrix (Fin n) (Fin n) Trop) (i j : Fin n) (v : ℕ)
    (h : A i j = ⟨some v⟩) : v ≤ matNorm A := by
  have hv_mem : v ∈ {1} ∪ finiteEntries A := by
    apply Finset.mem_union_right
    simp only [finiteEntries, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, j, by simp [h]⟩
  exact Finset.le_max' _ v hv_mem

/-- Scaling an element of `𝕋₁` by `k ∈ ℕ`: `0 ↦ 0`, `1 ↦ k`, `∞ ↦ ∞`. -/
def scaleTrop1 (k : ℕ) : Trop1 → Trop
  | Trop1.zero => ⟨some 0⟩
  | Trop1.one => ⟨some k⟩
  | Trop1.infty => ⟨none⟩

/-- Scaling a matrix over `𝕋₁` by `k ∈ ℕ`. -/
def scaleMat (k : ℕ) (M : Matrix (Fin n) (Fin n) Trop1) : Matrix (Fin n) (Fin n) Trop :=
  Matrix.map M (scaleTrop1 k)

lemma le_scaleMat_of_proj (A : Matrix (Fin n) (Fin n) Trop) :
    ∀ i j, A i j ≤ scaleMat (matNorm A) (projMat A) i j := by
  intro i j
  dsimp [scaleMat, projMat, Matrix.map_apply]
  rcases hA : A i j with ⟨_ | v⟩
  · exact le_rfl
  · rcases v with _ | v
    · exact le_rfl
    · dsimp [toTrop1, scaleTrop1]
      exact WithTop.coe_le_coe.mpr (entry_le_matNorm A i j (v + 1) hA)

end MatrixTrop
