/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Martingale.OptionalSampling

/-!
# Uniform integrability

-/

open scoped NNReal ENNReal

namespace MeasureTheory

variable {ι Ω E : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {X : ι → Ω → ℝ}

-- todo: `X` takes values in `ℝ` because
-- `MeasureTheory.Integrable.uniformIntegrable_condExp` is written only for `ℝ`. Investigate why.
lemma UniformIntegrable.condExp (hX : UniformIntegrable X 1 μ) {𝓕 : ι → MeasurableSpace Ω}
    (h𝓕 : ∀ i, 𝓕 i ≤ mΩ) :
    UniformIntegrable (fun i ↦ μ[X i | 𝓕 i]) 1 μ := by
  sorry

lemma Martingale.uniformIntegrable_stoppedValue {X : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ}
    (hX : Martingale X 𝓕 μ) (τ : ℕ → Ω → ℕ∞) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ℕ} (hτ_le : ∀ i ω, τ i ω ≤ n) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ := by
  sorry

end MeasureTheory
