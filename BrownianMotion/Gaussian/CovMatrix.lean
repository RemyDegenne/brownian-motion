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

section toBilin

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (f : E →L[𝕜] E →L[𝕜] 𝕜)

def _root_.ContinuousLinearMap.toBilin : LinearMap.BilinForm 𝕜 E where
  toFun x := (f x).toLinearMap
  map_add' x y := by simp
  map_smul' m x := by simp

@[simp]
lemma _root_.ContinuousLinearMap.toBilin_apply (x y : E) : f.toBilin x y = f x y := rfl

lemma _root_.ContinuousLinearMap.toBilin_apply' (x : E) : f.toBilin x = (f x).toLinearMap := rfl

end toBilin

lemma covMatrix_toBilin :
    (covMatrix μ).toBilin (stdOrthonormalBasis ℝ E).toBasis = (covInnerBilin μ).toBilin := by
  apply LinearMap.BilinForm.ext_basis (stdOrthonormalBasis ℝ E).toBasis
  simp [covMatrix]

lemma _root_.OrthonormalBasis.inner_eq_ite {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) {i j : ι} :
    ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 := by
  split_ifs with h
  · simp [h, inner_self_eq_norm_sq_to_K]
  · simp [h]

lemma _root_.OrthonormalBasis.toBilin_apply_eq_dotProduct {n E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype n] [DecidableEq n] (b : OrthonormalBasis n ℝ E) (x y : E)
    (A : Matrix n n ℝ) : A.toBilin b.toBasis x y = ⟪x, A.toLin b.toBasis b.toBasis y⟫_ℝ := by
  let f : LinearMap.BilinForm ℝ E :=
    { toFun x :=
        { toFun y := ⟪x, A.toLin b.toBasis b.toBasis y⟫_ℝ
          map_add' y z := by simp [inner_add_right]
          map_smul' m y := by simp [inner_smul_right] }
      map_add' x y := by
        ext z
        simp [inner_add_left]
      map_smul' m x := by
        ext z
        simp [inner_smul_left] }
  change _ = f x y
  revert x y
  refine LinearMap.BilinForm.ext_iff.1 <| LinearMap.BilinForm.ext_basis b.toBasis ?_
  simp [f, Matrix.toLin_apply, Matrix.mulVec, dotProduct, inner_sum, inner_smul_right,
    OrthonormalBasis.inner_eq_ite]

lemma covMatrix_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ F]
    [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L : E →L[ℝ] F) (i j : Fin (Module.finrank ℝ F)) :
    covMatrix (μ.map L) i j =
    ⟪(L.adjoint (stdOrthonormalBasis ℝ F i)),
    (covMatrix μ).toLin (stdOrthonormalBasis ℝ E).toBasis (stdOrthonormalBasis ℝ E).toBasis
    (L.adjoint (stdOrthonormalBasis ℝ F j))⟫_ℝ := by
  rw [← OrthonormalBasis.toBilin_apply_eq_dotProduct, covMatrix_toBilin,
    ContinuousLinearMap.toBilin_apply, covMatrix, Matrix.of_apply, covInnerBilin_map h]

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
