/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Gaussian.CovarianceBilin

/-!
# Covariance matrix

-/

open MeasureTheory InnerProductSpace NormedSpace
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- Covariance matrix of a measure on a finite dimensional inner product space. -/
noncomputable
def covMatrix (μ : Measure E) : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j ↦ covarianceBilin μ (toDualMap ℝ E (stdOrthonormalBasis ℝ E i))
    (toDualMap ℝ E (stdOrthonormalBasis ℝ E j))

lemma covMatrix_mulVec (x : Fin (Module.finrank ℝ E) → ℝ) :
    (covMatrix μ).mulVec x =
      fun i ↦ covarianceBilin μ (toDualMap ℝ E (stdOrthonormalBasis ℝ E i))
        (toDualMap ℝ E (∑ j, x j • stdOrthonormalBasis ℝ E j)) := by
  simp only [covMatrix, Matrix.mulVec_eq_sum, op_smul_eq_smul, map_sum, map_smul, smul_eq_mul]
  ext
  simp

lemma dotProduct_covMatrix_mulVec (x y : Fin (Module.finrank ℝ E) → ℝ) :
    x ⬝ᵥ (covMatrix μ).mulVec y =
      covarianceBilin μ (toDualMap ℝ E (∑ j, x j • stdOrthonormalBasis ℝ E j))
        (toDualMap ℝ E (∑ j, y j • stdOrthonormalBasis ℝ E j)) := by
  rw [covMatrix_mulVec, dotProduct]
  simp only [map_sum, map_smul, smul_eq_mul, ContinuousLinearMap.coe_sum',
    ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr with i
  congr with j
  simp_rw [← mul_assoc]
  rw [mul_comm (x j)]

lemma posSemidef_covMatrix [IsGaussian μ] : (covMatrix μ).PosSemidef := by
  constructor
  · simp only [Matrix.IsHermitian, covMatrix, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [covarianceBilin_comm]
    exact IsGaussian.memLp_id μ 2 (by simp)
  · intro x
    rw [star_trivial, dotProduct_covMatrix_mulVec,
      covarianceBilin_same_eq_variance (IsGaussian.memLp_id μ 2 (by simp))]
    exact variance_nonneg _ μ

end ProbabilityTheory
