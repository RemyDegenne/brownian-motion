/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Covariance bilinear form

-/

open MeasureTheory InnerProductSpace NormedSpace
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

section NormedSpace

variable [NormedSpace ℝ E]

lemma covarianceBilin_comm [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = covarianceBilin μ L₂ L₁ := by
  have h' : MemLp id 2 (Measure.map (fun x ↦ x - ∫ (x : E), x ∂μ) μ) :=
    (measurableEmbedding_subRight _).memLp_map_measure_iff.mpr <| h.sub (memLp_const _)
  simp_rw [covarianceBilin, uncenteredCovarianceBilin_apply h', mul_comm (L₁ _)]

lemma covarianceBilin_apply' [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ)
    (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = ∫ x, L₁ (x - μ[id]) * L₂ (x - μ[id]) ∂μ := by
  rw [covarianceBilin_apply h]
  have hL (L : Dual ℝ E) : μ[L] = L (∫ x, x ∂μ) := L.integral_comp_comm (h.integrable (by simp))
  simp [← hL]

lemma covarianceBilin_apply'' [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ)
    (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = cov[L₁, L₂; μ] := by
  rw [covarianceBilin_apply h, covariance]

@[simp]
lemma covarianceBilin_zero : covarianceBilin (0 : Measure E) = 0 := by
  ext
  rw [covarianceBilin, uncenteredCovarianceBilin, Measure.map_zero]
  have : Subsingleton (Lp ℝ 2 (0 : Measure E)) :=
    ⟨fun x y ↦ Lp.ext_iff.2 rfl⟩
  rw [Subsingleton.eq_zero (Dual.toLp 0 2)]
  simp

end NormedSpace

end ProbabilityTheory
