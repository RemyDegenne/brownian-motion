/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.StochasticIntegral.Locally
import BrownianMotion.StochasticIntegral.OptionalSampling
import Mathlib.Probability.Martingale.Basic

/-! # Local (sub)martingales

-/

open MeasureTheory Filter Filtration TopologicalSpace
open scoped ENNReal Topology

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

variable [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι] [PseudoMetrizableSpace ι]
  [Approximable 𝓕 P]

/-- Martingales are a stable class. -/
lemma isStable_martingale :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ Martingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) := by
  intro X ⟨hX, hC⟩ τ hτ
  refine ⟨⟨ProgMeasurable.adapted_stoppedProcess ?_ hτ, fun i j hij ↦ ?_⟩,
    isStable_isCadlag X hC τ hτ⟩
  · refine Adapted.progMeasurable_of_rightContinuous
      (fun i ↦ (hX.adapted i).indicator <| 𝓕.mono bot_le _ <| hτ.measurableSet_gt _)
      (fun ω ↦ ?_) -- Make separate lemma `(fun ω ↦ (hC ω).right_continuous)`
    sorry
  · sorry

/-- Submartingales are a stable class. -/
lemma isStable_submartingale :
    IsStable 𝓕 (fun (X : ι → Ω → ℝ) ↦ Submartingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) := by
  sorry

end ProbabilityTheory
