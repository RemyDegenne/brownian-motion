/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Martingale
import BrownianMotion.StochasticIntegral.Locally
import BrownianMotion.StochasticIntegral.OptionalSampling

/-! # Local (sub)martingales

-/

open MeasureTheory Filter TopologicalSpace Function
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

/-- A stochastic process is a local martingale if it satisfies the martingale property locally. -/
def IsLocalMartingale (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω := by volume_tac) :
    Prop :=
  Locally (fun X ↦ Martingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) 𝓕 X P

/-- A stochastic process is a local submartingale if it satisfies the submartingale property
locally. -/
def IsLocalSubmartingale [LE E] (X : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω := by volume_tac) : Prop :=
  Locally (fun X ↦ Submartingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) 𝓕 X P

lemma Martingale.IsLocalMartingale (hX : Martingale X 𝓕 P) (hC : ∀ ω, IsCadlag (X · ω)) :
    IsLocalMartingale X 𝓕 P :=
  locally_of_prop ⟨hX, hC⟩

lemma Submartingale.IsLocalSubmartingale [LE E]
    (hX : Submartingale X 𝓕 P) (hC : ∀ ω, IsCadlag (X · ω)) :
    IsLocalSubmartingale X 𝓕 P :=
  locally_of_prop ⟨hX, hC⟩

variable [SecondCountableTopology ι] [MeasurableSpace ι] [BorelSpace ι]

lemma IsLocalMartingale.locally_progMeasurable (hX : IsLocalMartingale X 𝓕 P) :
    Locally (ProgMeasurable 𝓕) 𝓕 X P :=
  Locally.mono (fun _ ⟨hX, hC⟩ ↦ hX.stronglyAdapted.progMeasurable_of_rightContinuous
    (fun ω ↦ (hC ω).right_continuous)) hX

lemma IsLocalSubmartingale.locally_progMeasurable [LE E] (hX : IsLocalSubmartingale X 𝓕 P) :
    Locally (ProgMeasurable 𝓕) 𝓕 X P :=
  Locally.mono (fun _ ⟨hX, hC⟩ ↦ hX.stronglyAdapted.progMeasurable_of_rightContinuous
    (fun ω ↦ (hC ω).right_continuous)) hX

variable [PseudoMetrizableSpace ι]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma _root_.MeasureTheory.StronglyAdapted.stoppedProcess_indicator
    (hX : StronglyAdapted 𝓕 X) (hC : ∀ ω, RightContinuous (X · ω))
    {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    StronglyAdapted 𝓕 (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ) :=
  (isStable_progMeasurable X (hX.progMeasurable_of_rightContinuous hC) τ hτ).stronglyAdapted

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [IsFiniteMeasure P]
  [Approximable 𝓕 P]

lemma _root_.MeasureTheory.Martingale.stoppedProcess_indicator
    (hX : Martingale X 𝓕 P) (hC : ∀ ω, RightContinuous (X · ω))
    {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    Martingale (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ) 𝓕 P := by
  refine ⟨hX.stronglyAdapted.stoppedProcess_indicator hC hτ, fun i j hij ↦ ?_⟩
  have : Martingale (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) 𝓕 P :=
    hX.indicator (hτ.measurableSet_gt _)
  conv_rhs => rw [← stoppedProcess_min_eq_stoppedProcess _ τ hij]
  refine EventuallyEq.trans ?_ (Martingale.condExp_stoppedValue_ae_eq_stoppedProcess
    (μ := P) (n := j) this (fun ω ↦ ?_) ((isStoppingTime_const 𝓕 j).min hτ)
    (fun ω ↦ min_le_left _ _) i)
  · rw [stoppedProcess_eq_stoppedValue]
  · exact rightContinuous_indicator (fun ω ↦ hC ω) {ω | ⊥ < τ ω} ω

/-- Càdlàg martingales are a stable class. -/
lemma isStable_martingale :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ Martingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) :=
  fun X ⟨hX, hC⟩ τ hτ ↦ ⟨hX.stoppedProcess_indicator (fun ω ↦ (hC ω).right_continuous) hτ,
    isStable_isCadlag X hC τ hτ⟩

/-- Càdlàg submartingales are a stable class. -/
lemma isStable_submartingale [LE E] :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ Submartingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) := by
  sorry

end ProbabilityTheory
