/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import BrownianMotion.Auxiliary.WithTop
public import BrownianMotion.StochasticIntegral.Predictable
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Process.LocalProperty

/-! # Localizing sequences of stopping times

-/

@[expose] public section

open MeasureTheory Filter Filtration
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

end LinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

lemma isLocalizingSequence_of_isPreLocalizingSequence
    {τ : ℕ → Ω → WithTop ι} (h𝓕 : IsRightContinuous 𝓕) (hτ : IsPreLocalizingSequence 𝓕 τ P) :
    IsLocalizingSequence 𝓕 (fun i ω ↦ ⨅ j ≥ i, τ j ω) P := by
  exact IsPreLocalizingSequence.isLocalizingSequence_biInf hτ

section

omit [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
variable [SecondCountableTopology ι] [IsFiniteMeasure P]

lemma isPreLocalizingSequence_of_isLocalizingSequence
    [NoMaxOrder ι] {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, StrictMono nk
      ∧ IsPreLocalizingSequence 𝓕 (fun i ω ↦ (τ i ω) ⊓ (σ i (nk i) ω)) P := by
  exact IsLocalizingSequence.isPrelocalizingSequence_inf_extraction hτ hσ

end

end ConditionallyCompleteLinearOrderBot

section cadlag

section LinearOrder

variable [LinearOrder ι] [OrderBot ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p : (ι → Ω → E) → Prop}

open Classical in
/-- Given a property on paths which holds almost surely for a stochastic process, we construct a
localizing sequence by setting the stopping time to be ∞ whenever the property holds. -/
noncomputable
def LocalizingSequenceOfProp (X : ι → Ω → E) (p : (ι → E) → Prop) : ℕ → Ω → WithTop ι :=
  Function.const _ <| fun ω ↦ if p (X · ω) then ⊤ else ⊥

omit [OrderBot ι] in
lemma isStoppingTime_ae_const [IsComplete 𝓕 P] (τ : Ω → WithTop ι) (c : WithTop ι)
    (hτ : τ =ᵐ[P] Function.const _ c) :
    IsStoppingTime 𝓕 τ := by
  intros i
  suffices P {ω | τ ω ≤ i} = 0 ∨ P {ω | τ ω ≤ ↑i}ᶜ = 0 by
    obtain h | h := this
    · exact IsComplete.measurableSet_of_null h i
    · exact (IsComplete.measurableSet_of_null h i).of_compl
  obtain hle | hgt := le_or_gt c i
  · refine Or.inr <| ae_iff.1 ?_
    filter_upwards [hτ] with ω rfl using hle
  · refine Or.inl ?_
    rw [← compl_compl {ω | τ ω ≤ i}]
    refine ae_iff.1 ?_
    filter_upwards [hτ] with ω hω
    simp [hω, hgt]

variable [TopologicalSpace ι] [OrderTopology ι]

lemma isLocalizingSequence_localizingSequenceOfProp [IsComplete 𝓕 P] {p : (ι → E) → Prop}
    (hpX : ∀ᵐ ω ∂P, p (X · ω)) :
    IsLocalizingSequence 𝓕 (LocalizingSequenceOfProp X p) P where
  isStoppingTime n := by
    refine isStoppingTime_ae_const (P := P) _ ⊤ ?_
    filter_upwards [hpX] with ω hω
    rw [LocalizingSequenceOfProp, Function.const_apply, Function.const_apply, if_pos hω]
  mono := ae_of_all _ <| fun ω i j hij ↦ by simp [LocalizingSequenceOfProp]
  tendsto_top := by
    filter_upwards [hpX] with ω hω
    simp [LocalizingSequenceOfProp, if_pos hω]

variable [Zero E]

end LinearOrder

end cadlag

end ProbabilityTheory
