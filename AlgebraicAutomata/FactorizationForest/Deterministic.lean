/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import AlgebraicAutomata.Semigroup.GreensRelations.Order
import AlgebraicAutomata.Semigroup.GreensRelations.Finite
import AlgebraicAutomata.FactorizationForest.Basic
import AlgebraicAutomata.Mathlib.Data.List.SemigroupProd

/-!
# Deterministic Factorization Forests and Forward Ramsey Splits

Deterministic finite-state transducer producing forward Ramsey splits from left to right.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008], Section 5
-/

namespace RamseySplit

open GreensRelations

variable {S α : Type*} [Semigroup S] [LinearOrder α]

section ForwardRamsey

/-- A split `s` over a multiplicative labeling `L` is forward Ramsey if,
for all `x < y` and `x' < y'` that are split-related (and cross-related),
`L.σ x y * L.σ x' y' = L.σ x y`. -/
def IsForwardRamsey {h : ℕ} (L : MultiplicativeLabeling S α) (s : Split α h) : Prop :=
  ∀ x y x' y' : α, x < y → x' < y' →
    SplitRelation s x y → SplitRelation s x' y' → SplitRelation s x x' →
    L.σ x y * L.σ x' y' = L.σ x y

/-- A forward Ramsey split satisfies `σ(x, z) = σ(x, y)` for all `x < y < z` with
`x ∼_s y ∼_s z` (Colcombet line 1340). -/
lemma forwardRamsey_three_points {h : ℕ} {L : MultiplicativeLabeling S α} {s : Split α h}
    (hf : IsForwardRamsey L s) {x y z : α} (hxy : x < y) (hyz : y < z)
    (hrel_xy : SplitRelation s x y) (hrel_yz : SplitRelation s y z) :
    L.σ x z = L.σ x y :=
  (L.prop x y z hxy hyz).symm.trans (hf x y y z hxy hyz hrel_xy hrel_yz hrel_xy)

/-- Remark 5.1 (Colcombet 2008): A split with uniform idempotent values on split-related
pairs is forward Ramsey. -/
lemma isForwardRamsey_of_idempotent_uniform {h : ℕ} (L : MultiplicativeLabeling S α) (s : Split α h)
    (h_idem : ∀ x y : α, x < y → SplitRelation s x y → L.σ x y * L.σ x y = L.σ x y)
    (h_unif : ∀ x y x' y' : α, x < y → x' < y' →
      SplitRelation s x y → SplitRelation s x' y' → SplitRelation s x x' →
      L.σ x y = L.σ x' y') :
    IsForwardRamsey L s := by
  intro x y x' y' hxy hx'y' h_rel_xy h_rel_x'y' h_rel_xx'
  have h_eq := h_unif x y x' y' hxy hx'y' h_rel_xy h_rel_x'y' h_rel_xx'
  rw [← h_eq, h_idem x y hxy h_rel_xy]

/-- Lemma 5.3 (Colcombet 2008): Let `a, b, c ∈ S` be such that `a * b = a`, `a * c = a`,
and `a 𝒥 b` in a finite semigroup `S`. Then `b * c = b`. -/
lemma lemma_5_3 [Finite S] {a b c : S} (hab : a * b = a) (hac : a * c = a)
    (hj : IsGreenJ a b) : b * c = b := by
  have hj_ab : IsGreenJ (a * b) b := hab.symm ▸ hj
  have hD : IsGreenD b (a * b) := (isGreenD_of_isGreenJ hj_ab).symm
  have hL : IsGreenL b (a * b) := isGreenL_sl_of_isGreenD_sl hD
  rw [hab] at hL
  rcases hL.left with rfl | ⟨d, rfl⟩
  · exact hac
  · calc
      (d * a) * c = d * (a * c) := mul_assoc d a c
      _ = d * a := by rw [hac]

end ForwardRamsey

section Configurations

/-- Condition (1) of a valid configuration: every subsegment product from `i` to `j`
is `J`-related to `aᵢ`. -/
def ConfigJRel (c : List S) : Prop :=
  ∀ (i j : ℕ) (hi : i < c.length) (hj : j < c.length), i ≤ j →
    have h_sub_ne : (c.drop i).take (j - i + 1) ≠ [] := by
      simp [List.take_eq_nil_iff]
      omega
    IsGreenJ (listProdNE ((c.drop i).take (j - i + 1)) h_sub_ne) (c.get ⟨i, hi⟩)

/-- Condition (2) of a valid configuration: elements form a strictly ascending
chain in the Green `J`-order (`[aᵢ] < [aⱼ]` for all `i < j`). -/
def ConfigJChain (c : List S) : Prop :=
  ∀ (i j : ℕ) (hi : i < c.length) (hj : j < c.length), i < j →
    GreenJClass.mk (c.get ⟨i, hi⟩) < GreenJClass.mk (c.get ⟨j, hj⟩)

/-- A configuration is *valid* (Colcombet Definition 5.1) if:
1. `c ≠ []`
2. `aᵢ ··· aⱼ 𝒥 aᵢ` for all `i ≤ j`
3. `aᵢ <_𝒥 aⱼ` for all `i < j`. -/
structure IsValidConfig (c : List S) : Prop where
  nonempty : c ≠ []
  j_rel : ConfigJRel c
  j_chain : ConfigJChain c

/-- A single-element list `[a]` is always a valid configuration. -/
theorem isValidConfig_singleton (a : S) : IsValidConfig [a] where
  nonempty := by simp
  j_rel := by
    intro i j hi hj _hij
    have h_idx : i = 0 ∧ j = 0 := by grind
    rcases h_idx with ⟨rfl, rfl⟩
    exact IsGreenJ.refl a
  j_chain := fun i j hi hj hij ↦ by grind

/-- Candidate configuration formed by keeping the first `k` elements and condensing the suffix
with the new input `b`. -/
def candidateConfig (c : List S) (b : S) (k : ℕ) : List S :=
  if hk : k < c.length then
    have h_drop_ne : c.drop k ≠ [] := by
      simp [List.drop_eq_nil_iff]
      omega
    c.take k ++ [listProdNE (c.drop k) h_drop_ne * b]
  else
    c ++ [b]

/-- The candidate configuration for `k = 0` is a singleton, which is always valid. -/
theorem candidateConfig_zero_isValid : ∀ (c : List S), c ≠ [] → ∀ b : S,
    IsValidConfig (candidateConfig c b 0)
  | [], hc, _ => False.elim (hc rfl)
  | _ :: _, _, _ => isValidConfig_singleton _

/-- The type of valid configurations in `S`. -/
def ValidConfig (S : Type*) [Semigroup S] :=
  { c : List S // IsValidConfig c }

instance [Inhabited S] : Inhabited (ValidConfig S) :=
  ⟨⟨[default], isValidConfig_singleton default⟩⟩

/-- The sequence of `J`-classes in a valid configuration has no duplicate elements. -/
theorem ConfigJChain.nodup_map (c : List S) (h : ConfigJChain c) :
    (c.map GreenJClass.mk).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro ⟨i, hi⟩ ⟨j, hj⟩ hij
  simp only [List.length_map] at hi hj
  have hij' : GreenJClass.mk (c.get ⟨i, hi⟩) = GreenJClass.mk (c.get ⟨j, hj⟩) := by
    simpa using hij
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact False.elim (lt_irrefl _ (hij' ▸ h i j hi hj hlt))
  · rfl
  · exact False.elim (lt_irrefl _ (hij'.symm ▸ h j i hj hi hgt))

/-- In a finite semigroup, the length of any valid configuration is bounded by the
number of Green's `J`-classes (Colcombet line 1332). -/
theorem IsValidConfig.length_le [Fintype S] (c : List S) (h : IsValidConfig c) :
    c.length ≤ Fintype.card (GreenJClass S) :=
  (c.length_map GreenJClass.mk).symm ▸ (h.j_chain.nodup_map c).length_le_card

open Classical in
/-- In a finite semigroup, the set of valid configurations is finite.
Hence Colcombet's transducer is a deterministic *finite-state* automaton. -/
noncomputable instance [Fintype S] : Fintype (ValidConfig S) := by
  let f : ValidConfig S → (Fin (Fintype.card (GreenJClass S)) → Option S) :=
    fun c i ↦ c.val[i.val]?
  have hf : Function.Injective f := by
    intro c₁ c₂ h
    apply Subtype.ext
    apply List.ext_getElem?
    intro n
    by_cases hn : n < Fintype.card (GreenJClass S)
    · exact congr_fun h ⟨n, hn⟩
    · push Not at hn
      have h1 := c₁.property.length_le
      have h2 := c₂.property.length_le
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  exact Fintype.ofInjective f hf

/-- Ranking function on configurations (Colcombet line 1366):
Given an injection `h₀ : S → ℕ` reversing the `J`-order, returns `h₀(aₙ)` of the last element. -/
def rankConfig (h₀ : S → ℕ) : List S → ℕ
  | [] => 0
  | [a] => h₀ a
  | _ :: rest => rankConfig h₀ rest

end Configurations

section Transducer

/-- The last element of a valid configuration. -/
def ValidConfig.last (c : ValidConfig S) : S :=
  c.val.getLast c.property.nonempty

open Classical in
/-- The maximal index `k` such that `candidateConfig c b k` is a valid configuration. -/
noncomputable def maxValidK (c : ValidConfig S) (b : S) : ℕ :=
  let s_k := (Finset.range (c.val.length + 1)).filter
    (fun k ↦ IsValidConfig (candidateConfig c.val b k))
  have h_ne : s_k.Nonempty := ⟨0, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), candidateConfig_zero_isValid c.val c.property.nonempty b⟩⟩
  s_k.max' h_ne

open Classical in
/-- `maxValidK` produces a valid configuration. -/
theorem maxValidK_isValid (c : ValidConfig S) (b : S) :
    IsValidConfig (candidateConfig c.val b (maxValidK c b)) := by
  dsimp [maxValidK]
  have h_ne : ((Finset.range (c.val.length + 1)).filter
    (fun k ↦ IsValidConfig (candidateConfig c.val b k))).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      candidateConfig_zero_isValid c.val c.property.nonempty b⟩⟩
  exact (Finset.mem_filter.mp (Finset.max'_mem _ h_ne)).2

/-- The transition function of Colcombet's deterministic transducer (line 1364). -/
noncomputable def stepConfig (c : ValidConfig S) (b : S) : ValidConfig S :=
  ⟨candidateConfig c.val b (maxValidK c b), maxValidK_isValid c b⟩

/-- The sequence of states traversed by the automaton on input word `u`,
starting from initial state `q₀`. -/
noncomputable def runAutomaton (q₀ : ValidConfig S) (u : List S) : List (ValidConfig S) :=
  u.scanl stepConfig q₀

/-- The length of the run is `u.length + 1`. -/
@[simp]
lemma length_runAutomaton (q₀ : ValidConfig S) (u : List S) :
    (runAutomaton q₀ u).length = u.length + 1 :=
  List.length_scanl

/-- The split produced by Colcombet's deterministic transducer on word `u` (Theorem 5.2). -/
noncomputable def deterministicSplit {h : ℕ} (h₀ : S → Fin h)
    (q₀ : ValidConfig S) (u : List S) : Split (Fin (u.length + 1)) h :=
  fun i ↦
    let state := (runAutomaton q₀ u).get ⟨i.val, by rw [length_runAutomaton]; exact i.isLt⟩
    h₀ state.last

@[simp]
lemma runAutomaton_nil (q₀ : ValidConfig S) :
    runAutomaton q₀ [] = [q₀] := rfl

@[simp]
lemma runAutomaton_cons (q₀ : ValidConfig S) (a : S) (u : List S) :
    runAutomaton q₀ (a :: u) = q₀ :: runAutomaton (stepConfig q₀ a) u := by
  simp [runAutomaton]

lemma runAutomaton_get_zero (q₀ : ValidConfig S) : ∀ (u : List S),
    (runAutomaton q₀ u).get ⟨0, by rw [length_runAutomaton]; omega⟩ = q₀
  | [] => rfl
  | _ :: _ => by simp [runAutomaton]

@[simp]
lemma deterministicSplit_apply {h : ℕ} (h₀ : S → Fin h)
    (q₀ : ValidConfig S) (u : List S) (i : Fin (u.length + 1)) :
    deterministicSplit h₀ q₀ u i =
      h₀ ((runAutomaton q₀ u).get ⟨i.val, by rw [length_runAutomaton]; exact i.isLt⟩).last :=
  rfl

end Transducer

section DeterministicRamsey

/-- A ranking function `h₀ : S → Fin h` is order-reversing with respect to Green's `J`-order:
if `[a] <_𝒥 [b]`, then `h₀ b < h₀ a`. -/
def IsOrderReversingRank {h : ℕ} (h₀ : S → Fin h) : Prop :=
  ∀ a b : S, GreenJClass.mk a < GreenJClass.mk b → h₀ b < h₀ a

/-- Transition property for the deterministic transducer (Colcombet 2008, Lemma 5.4):
Along any run of the transducer, when positions `x < y` are split-related under
`s = deterministicSplit h₀ q₀ u` with injective `h₀`, the evaluated slice
`L.σ x y` between them satisfies `a * L.σ x y = a` and `a 𝒥 L.σ x y`, where `a` is the
last element of the configuration at position `x`. -/
lemma deterministic_transducer_transition_lemma [Finite S] {h : ℕ} (h₀ : S → Fin h)
    (h_inj : Function.Injective h₀) (q₀ : ValidConfig S) (u : List S)
    (L : MultiplicativeLabeling S (Fin (u.length + 1)))
    (x y : Fin (u.length + 1)) (hxy : x < y)
    (h_rel : SplitRelation (deterministicSplit h₀ q₀ u) x y) :
    let state_x := (runAutomaton q₀ u).get ⟨x.val, by rw [length_runAutomaton]; exact x.isLt⟩
    state_x.last * L.σ x y = state_x.last ∧ IsGreenJ state_x.last (L.σ x y) := by
  simp only [List.get_eq_getElem]
  sorry

/-- The deterministic split produced by Colcombet's transducer on any word `u` is a forward
Ramsey split for the multiplicative labeling `L`. -/
theorem deterministicSplit_isForwardRamsey [Finite S] {h : ℕ} (h₀ : S → Fin h)
    (h_inj : Function.Injective h₀) (q₀ : ValidConfig S) (u : List S)
    (L : MultiplicativeLabeling S (Fin (u.length + 1))) :
    IsForwardRamsey L (deterministicSplit h₀ q₀ u) := by
  intro x y x' y' hxy hx'y' hrel_xy hrel_x'y' hrel_xx'
  set s := deterministicSplit h₀ q₀ u
  have h_last_xx' :
      ((runAutomaton q₀ u).get ⟨x.val, by rw [length_runAutomaton]; exact x.isLt⟩).last =
      ((runAutomaton q₀ u).get ⟨x'.val, by rw [length_runAutomaton]; exact x'.isLt⟩).last := by
    have h_rank := hrel_xx'.1
    dsimp [s, deterministicSplit] at h_rank
    exact h_inj h_rank
  obtain ⟨h_ab, h_j⟩ :=
    deterministic_transducer_transition_lemma h₀ h_inj q₀ u L x y hxy hrel_xy
  obtain ⟨h_ac', _⟩ :=
    deterministic_transducer_transition_lemma h₀ h_inj q₀ u L x' y' hx'y' hrel_x'y'
  rw [← h_last_xx'] at h_ac'
  exact lemma_5_3 h_ab h_ac' h_j

/-- For any finite semigroup `S`, there exists a deterministic automaton producing a forward
Ramsey split on every input word. -/
theorem colcombet_transducer_theorem [Finite S] {h : ℕ} (h₀ : S → Fin h)
    (h_inj : Function.Injective h₀) (q₀ : ValidConfig S) (u : List S)
    (L : MultiplicativeLabeling S (Fin (u.length + 1))) :
    IsForwardRamsey L (deterministicSplit h₀ q₀ u) :=
  deterministicSplit_isForwardRamsey h₀ h_inj q₀ u L

end DeterministicRamsey

end RamseySplit
