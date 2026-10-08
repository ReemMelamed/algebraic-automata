/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Quotient
import AlgebraicAutomata.GreensRelations.Finite

/-!
# Green's Relations Partial Orders

Partial orders on the quotient types `GreenLClass`, `GreenRClass`, `GreenJClass`,
and `GreenDClass`.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace GreensRelations

variable {S : Type*} [Semigroup S]

namespace GreenLClass

/-- Green's `L`-relation induces a natural left-multiplication order on `L`-classes.
`[a] ≤ [b]` iff `a` is a left multiple of `b`. -/
instance : LE (GreenLClass S) where
  le := Quotient.lift₂ IsGreenLeftDvd fun _ _ _ _ ha hb =>
    propext ⟨fun h => ha.right.trans (h.trans hb.left),
            fun h => ha.left.trans (h.trans hb.right)⟩

/-- The partial order on `L`-classes. -/
instance : PartialOrder (GreenLClass S) where
  le_refl := Quot.ind IsGreenLeftDvd.refl
  le_trans := Quot.ind fun a ↦ Quot.ind fun b ↦ Quot.ind fun c hab hbc ↦
    IsGreenLeftDvd.trans hab hbc
  le_antisymm := Quot.ind fun a ↦ Quot.ind fun b hab hba ↦
    mk_eq_mk_iff.mpr ⟨hab, hba⟩

end GreenLClass

namespace GreenRClass

/-- Green's `R`-relation induces a natural right-multiplication order on `R`-classes.
`[a] ≤ [b]` iff `a` is a right multiple of `b`. -/
instance : LE (GreenRClass S) where
  le := Quotient.lift₂ IsGreenRightDvd fun _ _ _ _ ha hb =>
    propext ⟨fun h => ha.right.trans (h.trans hb.left),
            fun h => ha.left.trans (h.trans hb.right)⟩

/-- The partial order on `R`-classes. -/
instance : PartialOrder (GreenRClass S) where
  le_refl := Quot.ind IsGreenRightDvd.refl
  le_trans := Quot.ind fun a ↦ Quot.ind fun b ↦ Quot.ind fun c hab hbc ↦
    IsGreenRightDvd.trans hab hbc
  le_antisymm := Quot.ind fun a ↦ Quot.ind fun b hab hba ↦
    mk_eq_mk_iff.mpr ⟨hab, hba⟩

end GreenRClass

namespace GreenJClass

/-- Green's `J`-relation induces a natural two-sided order on `J`-classes.
`[a] ≤ [b]` iff `a` is a two-sided multiple of `b`. -/
instance : LE (GreenJClass S) where
  le := Quotient.lift₂ IsGreenJRel fun _ _ _ _ ha hb =>
    propext ⟨fun h => ha.right.trans (h.trans hb.left),
            fun h => ha.left.trans (h.trans hb.right)⟩

/-- The partial order on `J`-classes. -/
instance : PartialOrder (GreenJClass S) where
  le_refl := Quot.ind IsGreenJRel.refl
  le_trans := Quot.ind fun a ↦ Quot.ind fun b ↦ Quot.ind fun c hab hbc ↦
    IsGreenJRel.trans hab hbc
  le_antisymm := Quot.ind fun a ↦ Quot.ind fun b hab hba ↦
    mk_eq_mk_iff.mpr ⟨hab, hba⟩

open Classical in
/-- In a finite semigroup, the quotient of Green's `J`-classes is finite. -/
noncomputable instance [Fintype S] : Fintype (GreenJClass S) :=
  Quotient.fintype (IsGreenJ.setoid S)

end GreenJClass

namespace GreenDClass

/-- In a finite semigroup, equivalence of D and J relations yields an equivalence
between `GreenDClass S` and `GreenJClass S`. -/
noncomputable def equivGreenJClass [Finite S] : GreenDClass S ≃ GreenJClass S where
  toFun := Quotient.map id (fun _ _ h => isGreenJ_of_isGreenD h)
  invFun := Quotient.map id (fun _ _ h => isGreenD_of_isGreenJ h)
  left_inv := Quot.ind fun _ ↦ rfl
  right_inv := Quot.ind fun _ ↦ rfl

/-- Green's `D`-relation induces an order on `D`-classes in a finite semigroup via `D` = `J`. -/
noncomputable instance [Finite S] : LE (GreenDClass S) where
  le x y := equivGreenJClass x ≤ equivGreenJClass y

/-- The partial order on `D`-classes in a finite semigroup. -/
noncomputable instance [Finite S] : PartialOrder (GreenDClass S) where
  le_refl x := le_refl (equivGreenJClass x)
  le_trans x y z hxy hyz := le_trans (α := GreenJClass S) hxy hyz
  le_antisymm x y hxy hyx := equivGreenJClass.injective (le_antisymm (α := GreenJClass S) hxy hyx)

end GreenDClass

end GreensRelations
