/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.ContinuousBilinForm
import BrownianMotion.Gaussian.Fernique
import Mathlib.Probability.Moments.Covariance

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

noncomputable def covarianceBilin (μ : Measure E) :
    ContinuousBilinForm ℝ (Dual ℝ E) := sorry

lemma covarianceBilin_apply [NormedSpace ℝ E] [IsFiniteMeasure μ] [CompleteSpace E]
    (h : MeasureTheory.MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    ((covarianceBilin μ) L₁) L₂ =
    ∫ (x : E), (L₁ x - ∫ (x : E), L₁ x ∂μ) * (L₂ x - ∫ (x : E), L₂ x ∂μ) ∂μ := sorry

lemma covarianceBilin_comm [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = covarianceBilin μ L₂ L₁ := by
  sorry
  -- have h' : MemLp id 2 (Measure.map (fun x ↦ x - ∫ (x : E), x ∂μ) μ) :=
  --   (measurableEmbedding_subRight _).memLp_map_measure_iff.mpr <| h.sub (memLp_const _)
  -- simp_rw [covarianceBilin, uncenteredCovarianceBilin_apply h', mul_comm (L₁ _)]

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
  sorry
  -- ext
  -- rw [covarianceBilin, uncenteredCovarianceBilin, Measure.map_zero]
  -- have : Subsingleton (Lp ℝ 2 (0 : Measure E)) :=
  --   ⟨fun x y ↦ Lp.ext_iff.2 rfl⟩
  -- rw [Subsingleton.eq_zero (Dual.toLp 0 2)]
  -- simp

lemma covarianceBilin_same_eq_variance {E : Type*} [NormedAddCommGroup E] {mE : MeasurableSpace E}
  {μ : Measure E} [NormedSpace ℝ E] [BorelSpace E] [IsFiniteMeasure μ] [CompleteSpace E]
  (h : MeasureTheory.MemLp id 2 μ) (L : NormedSpace.Dual ℝ E) :
  ((covarianceBilin μ) L) L = variance (⇑L) μ := sorry

lemma isPosSemidef_covarianceBilin [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) :
    (covarianceBilin μ).IsPosSemidef where
  map_symm := covarianceBilin_comm h
  nonneg_re_apply_self L := by
    rw [covarianceBilin_same_eq_variance h]
    simp [variance_nonneg]

nonrec
lemma IsGaussian.isPosSemidef_covarianceBilin [SecondCountableTopology E] [CompleteSpace E]
    [IsGaussian μ] : (covarianceBilin μ).IsPosSemidef :=
  isPosSemidef_covarianceBilin IsGaussian.memLp_two_id

lemma covarianceBilin_self_nonneg (L : Dual ℝ E) : 0 ≤ covarianceBilin μ L L := sorry

end NormedSpace

end ProbabilityTheory
