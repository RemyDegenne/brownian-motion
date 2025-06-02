/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Init
import BrownianMotion.Gaussian.Fernique

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

end NormedSpace

section InnerProductSpace
variable [InnerProductSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma covarianceBilin_map_toDualMap [CompleteSpace E] [CompleteSpace F] [IsFiniteMeasure μ]
    (h : MemLp id 2 μ) (L : E →L[ℝ] F) (u v : F) :
    covarianceBilin (μ.map L) (toDualMap ℝ F u) (toDualMap ℝ F v) =
      covarianceBilin μ (toDualMap ℝ E (L.adjoint u)) (toDualMap ℝ E (L.adjoint v)) := by
  sorry

end InnerProductSpace

end ProbabilityTheory
