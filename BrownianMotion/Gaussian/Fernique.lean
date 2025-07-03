/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Distributions.Gaussian.Basic


/-!
# Gaussian distributions in Banach spaces: Fernique's theorem
-/

open MeasureTheory Real NormedSpace
open scoped ENNReal

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopology E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsGaussian μ]

/-- A Gaussian measure has moments of all orders.
That is, the identity is in Lp for all finite `p`. -/
lemma IsGaussian.memLp_id (μ : Measure E) [IsGaussian μ] (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp id p μ := by
  sorry -- Mathlib PR #26291

lemma IsGaussian.memLp_two_id {μ : Measure E} [IsGaussian μ] :
    MemLp id 2 μ := IsGaussian.memLp_id μ 2 (by norm_num)

lemma IsGaussian.integrable_id {μ : Measure E} [IsGaussian μ] :
    Integrable id μ := memLp_one_iff_integrable.1 <| IsGaussian.memLp_id μ 1 (by norm_num)

lemma IsGaussian.integrable_fun_id {μ : Measure E} [IsGaussian μ] :
    Integrable (fun x ↦ x) μ := IsGaussian.integrable_id

-- Mathlib PR #26291
lemma IsGaussian.integral_dual (L : Dual ℝ E) : μ[L] = L (∫ x, x ∂μ) :=
  L.integral_comp_comm IsGaussian.integrable_id

end ProbabilityTheory
