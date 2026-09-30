/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import AlgebraicAutomata.Semiring.Covering

/-!
# Distance Automata and Decidability of the Boundedness Problem

Distance automata, tropical matrix representations, and decidability of the
boundedness problem.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008], Sections 4.3–4.4
-/

open BigOperators

variable {Q α : Type*} [Fintype Q] [DecidableEq Q]

/-- A distance automaton with states `Q`, alphabet `α`, initial states,
final states, and tropical transition weights. -/
structure DistanceAutomaton (Q α : Type*) [Fintype Q] [DecidableEq Q] where
  initial : Finset Q
  final : Finset Q
  weight : Q → α → Q → Trop

namespace DistanceAutomaton

variable (DA : DistanceAutomaton Q α)

/-- Canonical bijection between `Q` and `Fin |Q|`. -/
noncomputable def equivFin : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q

/-- Transition matrix for a symbol `a : α`. -/
noncomputable def transMat (a : α) : Matrix (Fin (Fintype.card Q)) (Fin (Fintype.card Q)) Trop :=
  fun i j => DA.weight (equivFin.symm i) a (equivFin.symm j)

/-- Transition matrix for a word `w : List α`. -/
noncomputable def wordMat : List α → Matrix (Fin (Fintype.card Q)) (Fin (Fintype.card Q)) Trop
  | [] => 1
  | a :: rest => DA.transMat a * wordMat rest

@[simp] lemma wordMat_nil : DA.wordMat [] = 1 := rfl

lemma wordMat_cons (a : α) (w : List α) :
    DA.wordMat (a :: w) = DA.transMat a * DA.wordMat w := rfl

lemma wordMat_append : ∀ (w₁ w₂ : List α),
    DA.wordMat (w₁ ++ w₂) = DA.wordMat w₁ * DA.wordMat w₂
  | [], w₂ => (one_mul (DA.wordMat w₂)).symm
  | a :: rest, w₂ =>
    (congrArg (DA.transMat a * ·) (wordMat_append rest w₂)).trans
      (mul_assoc (DA.transMat a) (DA.wordMat rest) (DA.wordMat w₂)).symm

/-- Initial state characteristic vector in `𝕋₁`. -/
noncomputable def I : Fin (Fintype.card Q) → Trop1 :=
  fun i => if equivFin.symm i ∈ DA.initial then Trop1.zero else Trop1.infty

/-- Final state characteristic vector in `𝕋₁`. -/
noncomputable def F : Fin (Fintype.card Q) → Trop1 :=
  fun j => if equivFin.symm j ∈ DA.final then Trop1.zero else Trop1.infty

/-- The set of generator matrices `{M_a : a ∈ α}`. -/
noncomputable def genSet : Set (Matrix (Fin (Fintype.card Q)) (Fin (Fintype.card Q)) Trop) :=
  Set.range DA.transMat

/-- The finite set of generator matrices when `α` is finite. -/
noncomputable def genFinset [Fintype α] :
    Finset (Matrix (Fin (Fintype.card Q)) (Fin (Fintype.card Q)) Trop) :=
  Finset.univ.image DA.transMat

lemma coe_genFinset [Fintype α] :
    (DA.genFinset : Set (Matrix (Fin (Fintype.card Q)) (Fin (Fintype.card Q)) Trop)) =
    DA.genSet := by
  ext M
  simp [genFinset, genSet]

lemma wordMat_mem_closure {w : List α} (hw : w ≠ []) :
    DA.wordMat w ∈ Subsemigroup.closure DA.genSet := by
  induction w with
  | nil => contradiction
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [wordMat_cons, wordMat_nil, mul_one]
      exact Subsemigroup.subset_closure ⟨a, rfl⟩
    | cons b rest' =>
      rw [wordMat_cons]
      exact Subsemigroup.mul_mem _ (Subsemigroup.subset_closure ⟨a, rfl⟩) (ih (by simp))

/-- An accepting run starts in an initial state and ends in a final state. -/
def isAcceptingRun {w : List α} (ρ : Fin (w.length + 1) → Q) : Prop :=
  ρ 0 ∈ DA.initial ∧ ρ (Fin.last w.length) ∈ DA.final

instance {w : List α} (ρ : Fin (w.length + 1) → Q) :
    Decidable (DA.isAcceptingRun ρ) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The tropical cost of a run along a word `w`. -/
def runCost : (w : List α) → (Fin (w.length + 1) → Q) → Trop
  | [], _ => 1
  | a :: rest, ρ =>
    DA.weight (ρ 0) a (ρ 1) *
    runCost rest (fun i => ρ i.succ)

/-- Word value `f(w)`: the tropical sum (i.e. minimum) over all accepting runs. -/
def wordValue (w : List α) : Trop :=
  ∑ ρ : Fin (w.length + 1) → Q,
    if DA.isAcceptingRun ρ then DA.runCost w ρ else 0

/-- Tropical section value of a matrix with respect to initial and final states. -/
noncomputable def sectionVal
    (M : Matrix (Fin (Fintype.card Q)) (Fin (Fintype.card Q)) Trop) : Trop :=
  ∑ i, ∑ j, if equivFin.symm i ∈ DA.initial ∧ equivFin.symm j ∈ DA.final
    then M i j else 0

/-- A distance automaton is bounded if there is no element in the stabilization closure
with an infinite section. By Lemma 4.11 (`bounded_section_equivalence`), this is
equivalent to the transition values between initial and final states being bounded. -/
def IsBounded : Prop :=
  ¬(∃ M ∈ StabilizationClosure (projMat '' DA.genSet), SectionInfty DA.I DA.F M)

/-- Characterization of boundedness via subsemigroup sections:
an automaton is bounded if and only if its section values do not exceed all thresholds `k`. -/
theorem isBounded_iff_not_unbounded :
    DA.IsBounded ↔
    ¬(∀ k : ℕ, ∃ A ∈ Subsemigroup.closure DA.genSet, SectionExceeds DA.I DA.F k A) :=
  not_congr (bounded_section_equivalence DA.genSet DA.I DA.F)

end DistanceAutomaton
