/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.StochasticIntegral.Locally
import BrownianMotion.StochasticIntegral.Cadlag
import Mathlib.Probability.Martingale.Basic

/-! # Local (sub)martingales

-/

open MeasureTheory Filter Filtration
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

/-- Martingales are a stable class. -/
lemma isStable_martingale :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ Martingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) := by
  sorry

/-- Submartingales are a stable class. -/
lemma isStable_submartingale :
    IsStable 𝓕 (fun (X : ι → Ω → ℝ) ↦ Submartingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) := by
  sorry

end ProbabilityTheory
