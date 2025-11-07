/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import BrownianMotion.StochasticIntegral.Locally
import BrownianMotion.StochasticIntegral.UniformIntegrable
import Mathlib.Probability.Martingale.OptionalSampling

open scoped NNReal ENNReal

namespace MeasureTheory

variable {ι Ω E : Type*} [Nonempty ι] [TopologicalSpace ι] [TopologicalSpace E]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → ℝ}



def rightContinuous [PartialOrder ι] (X : ι → Ω → E) (μ : Measure Ω := by volume_tac) :=
    ∀ᵐ ω ∂μ, ∀ a, ContinuousWithinAt (X · ω) (Set.Ioi a) a

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ}

theorem stoppedValue_min_ae_eq_condExp' [SigmaFiniteFiltration μ 𝓕]
    (h : Martingale X 𝓕 μ) (hX : rightContinuous X μ)
    {τ σ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι}
    (hτ_le : ∀ x, τ x ≤ n)
    [h_sf_min : SigmaFinite (μ.trim (hτ.min hσ).measurableSpace_le)] :
    (stoppedValue X fun x ↦ min (σ x) (τ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] := by
  sorry

end MeasureTheory
