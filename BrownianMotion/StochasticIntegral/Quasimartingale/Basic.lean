/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.SimpleProcess
public import Mathlib.Probability.Notation

/-! # Real quasimartingales -/

@[expose] public section

open MeasureTheory
open scoped ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ}

/-! ### Almost-sure regularity along countable time sets -/

-- todo: to be superceded by a more general `IsQuasimartingale`
/-- A real quasimartingale is a real-valued stochastic process that is adapted, integrable,
and has bounded variation. -/
structure IsRealQuasimartingale (𝓕 : Filtration ι mΩ) (X : ι → Ω → ℝ) (μ : Measure Ω) : Prop where
  adapted : Adapted 𝓕 X
  integrable : ∀ t, Integrable (X t) μ
  boundedVariation :
    ∀ t, ∃ C, ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C

/-- The minimal bound on the variation of the process. -/
noncomputable
def variationBound (X : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (μ : Measure Ω) (t : ι) : ℝ :=
  ⨆ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t]

lemma IsRealQuasimartingale.integral_indicator_le_variationBound (hX : IsRealQuasimartingale 𝓕 X μ)
    (t : ι) (S : ElementaryPredictableSet 𝓕) :
    μ[(S.indicator (1 : ℝ) ● X) t] ≤ variationBound X 𝓕 μ t := by
  unfold variationBound
  refine le_ciSup (f := fun S ↦ ∫ x, (S.indicator 1 ● X) t x ∂μ) ?_ S
  obtain ⟨C, hC⟩ := hX.boundedVariation t
  exact ⟨C, by simp [mem_upperBounds, hC]⟩

lemma IsRealQuasimartingale.stronglyAdapted (hX : IsRealQuasimartingale 𝓕 X μ) :
    StronglyAdapted 𝓕 X := hX.adapted.stronglyAdapted

lemma IsRealQuasimartingale.measurable (hX : IsRealQuasimartingale 𝓕 X μ) (t : ι) :
    Measurable (X t) := (hX.adapted t).mono (𝓕.le t) le_rfl

end ProbabilityTheory
