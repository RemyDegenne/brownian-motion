/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.StochasticIntegral.Locally

/-! # Local (sub)martingales

-/

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [LinearOrder ι] [OrderBot ι]
  {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

/-- A stochastic process is a local martingale if it satisfies the martingale property locally. -/
def IsLocalMartingale (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω := by volume_tac) :
    Prop :=
  Locally (Martingale · 𝓕 P) 𝓕 X P

/-- A stochastic process is a local submartingale if it satisfies the submartingale property
locally. -/
def IsLocalSubmartingale [LE E] (X : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω := by volume_tac) : Prop :=
  Locally (Submartingale · 𝓕 P) 𝓕 X P

lemma Martingale.IsLocalMartingale (hX : Martingale X 𝓕 P) : IsLocalMartingale X 𝓕 P :=
  locally_of_prop hX

lemma Submartingale.IsLocalSubmartingale [LE E] (hX : Submartingale X 𝓕 P) :
    IsLocalSubmartingale X 𝓕 P :=
  locally_of_prop hX

/-- Martingales are a stable class. -/
lemma isStable_martingale : IsStable (fun X : ι → Ω → E ↦ Martingale X 𝓕 P) 𝓕 := by
  sorry

end ProbabilityTheory
