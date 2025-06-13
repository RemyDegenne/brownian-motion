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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- Covariance of a measure on an inner product space, as a continuous bilinear form. -/
noncomputable
def covInnerBilin (μ : Measure E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (covarianceBilin μ)
    (toDualMap ℝ E).toContinuousLinearMap (toDualMap ℝ E).toContinuousLinearMap

lemma covInnerBilin_eq_covarianceBilin (x y : E) :
    covInnerBilin μ x y = covarianceBilin μ (toDualMap ℝ E x) (toDualMap ℝ E y) := rfl

lemma covInnerBilin_apply [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : E) :
    covInnerBilin μ x y = ∫ z, ⟪x, z - μ[id]⟫_ℝ * ⟪y, z - μ[id]⟫_ℝ ∂μ := by
  simp_rw [covInnerBilin, ContinuousLinearMap.bilinearComp_apply, covarianceBilin_apply' h]
  simp only [LinearIsometry.coe_toContinuousLinearMap, id_eq, toDualMap_apply]

nonrec
lemma IsGaussian.covInnerBilin_apply [IsGaussian μ] [SecondCountableTopology E] [CompleteSpace E]
    (x y : E) :
    covInnerBilin μ x y = ∫ z, ⟪x, z - μ[id]⟫_ℝ * ⟪y, z - μ[id]⟫_ℝ ∂μ :=
  covInnerBilin_apply (IsGaussian.memLp_id μ 2 (by simp)) x y

lemma covInnerBilin_comm [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : E) :
    covInnerBilin μ x y = covInnerBilin μ y x := by
  rw [covInnerBilin_eq_covarianceBilin, covarianceBilin_comm h, covInnerBilin_eq_covarianceBilin]

lemma covInnerBilin_self [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x : E) :
    covInnerBilin μ x x = Var[fun u ↦ ⟪x, u⟫_ℝ; μ] := by
  rw [covInnerBilin_eq_covarianceBilin, covarianceBilin_same_eq_variance h]
  congr

lemma covInnerBilin_self_nonneg [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x : E) :
    0 ≤ covInnerBilin μ x x := by
  rw [covInnerBilin_self h]
  exact variance_nonneg _ μ

variable [FiniteDimensional ℝ E]

lemma covInnerBilin_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace E] [CompleteSpace F] [IsFiniteMeasure μ]
    (h : MemLp id 2 μ) (L : E →L[ℝ] F) (u v : F) :
    covInnerBilin (μ.map L) u v = covInnerBilin μ (L.adjoint u) (L.adjoint v) := by
  sorry

/-- Covariance matrix of a measure on a finite dimensional inner product space. -/
noncomputable
def covMatrix (μ : Measure E) : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j ↦ covInnerBilin μ (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)

lemma covMatrix_mulVec (x : Fin (Module.finrank ℝ E) → ℝ) :
    (covMatrix μ).mulVec x = fun i ↦
      covInnerBilin μ (stdOrthonormalBasis ℝ E i) (∑ j, x j • stdOrthonormalBasis ℝ E j) := by
  ext
  simp [covMatrix, Matrix.mulVec_eq_sum]

lemma dotProduct_covMatrix_mulVec (x y : Fin (Module.finrank ℝ E) → ℝ) :
    x ⬝ᵥ (covMatrix μ).mulVec y =
      covInnerBilin μ (∑ j, x j • stdOrthonormalBasis ℝ E j)
        (∑ j, y j • stdOrthonormalBasis ℝ E j) := by
  rw [covMatrix_mulVec, dotProduct]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, ContinuousLinearMap.coe_sum',
    ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_comm]
  congr with i
  congr with j
  simp_rw [← mul_assoc]
  rw [mul_comm (x j)]

lemma covMatrix_toBilin (x y : E) :
    (covMatrix μ).toBilin (stdOrthonormalBasis ℝ E).toBasis x y =
    covInnerBilin μ x y := by
  simp only [Matrix.toBilin_apply, OrthonormalBasis.coe_toBasis_repr_apply]
  nth_rw 2 [← (stdOrthonormalBasis ℝ E).sum_repr x, ← (stdOrthonormalBasis ℝ E).sum_repr y]
  simp_rw [covMatrix]
  simp only [Matrix.of_apply, map_sum, map_smul, ContinuousLinearMap.coe_sum',
    ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  conv_lhs => enter [2]; intro i; enter [2]; intro j; rw [mul_comm]
  rw [Finset.sum_comm]

lemma covMatrix_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ F]
    [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L : E →L[ℝ] F) (i j : Fin (Module.finrank ℝ F)) :
    covMatrix (μ.map L) i j =
    (covMatrix μ).toBilin (stdOrthonormalBasis ℝ E).toBasis
      (L.adjoint (stdOrthonormalBasis ℝ F i))
      (L.adjoint (stdOrthonormalBasis ℝ F j)) := by
  rw [covMatrix_toBilin, covMatrix, Matrix.of_apply, covInnerBilin_map h]

lemma posSemidef_covMatrix [IsGaussian μ] : (covMatrix μ).PosSemidef := by
  constructor
  · simp only [Matrix.IsHermitian, covMatrix, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [covInnerBilin_comm]
    exact IsGaussian.memLp_id μ 2 (by simp)
  · intro x
    rw [star_trivial, dotProduct_covMatrix_mulVec]
    exact covInnerBilin_self_nonneg (IsGaussian.memLp_id μ 2 (by simp)) _

end ProbabilityTheory
