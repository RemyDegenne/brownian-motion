/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.ContinuousBilinForm
import BrownianMotion.Gaussian.CovarianceBilin
import BrownianMotion.Auxiliary.MeasureTheory

/-!
# Covariance matrix

-/

open MeasureTheory InnerProductSpace NormedSpace
open scoped ENNReal NNReal Matrix

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- Covariance of a measure on an inner product space, as a continuous bilinear form. -/
noncomputable
def covInnerBilin (μ : Measure E) : ContinuousBilinForm ℝ E :=
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
  covInnerBilin_apply (IsGaussian.memLp_two_id μ) x y

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

lemma isPosSemidef_covInnerBilin [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) :
    (covInnerBilin μ).IsPosSemidef where
  map_symm := covInnerBilin_comm h
  nonneg_re_apply_self := covInnerBilin_self_nonneg h

nonrec lemma IsGaussian.isPosSemidef_covInnerBilin [SecondCountableTopology E] [CompleteSpace E]
    [IsGaussian μ] : (covInnerBilin μ).IsPosSemidef :=
  isPosSemidef_covInnerBilin (IsGaussian.memLp_two_id μ)

lemma covInnerBilin_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace E] [FiniteDimensional ℝ F]
    [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L : E →L[ℝ] F) (u v : F) :
    covInnerBilin (μ.map L) u v = covInnerBilin μ (L.adjoint u) (L.adjoint v) := by
  rw [covInnerBilin_apply, covInnerBilin_apply h]
  · simp_rw [L.integral_id_map (h.integrable (by simp)), id]
    rw [integral_map]
    · simp_rw [← map_sub, ← L.adjoint_inner_left]
    all_goals fun_prop
  · exact memLp_map_measure_iff (by fun_prop) (by fun_prop) |>.2 (L.comp_memLp' h)

lemma covInnerBilin_map_const_add [CompleteSpace E] [IsProbabilityMeasure μ]
    (c : E) (h : MemLp id 2 μ) :
    covInnerBilin (μ.map (fun x ↦ c + x)) = covInnerBilin μ := by
  ext x y
  have h_Lp : MemLp id 2 (μ.map (fun x ↦ c + x)) :=
    (measurableEmbedding_addLeft _).memLp_map_measure_iff.mpr <| (memLp_const c).add h
  rw [covInnerBilin_apply h_Lp, covInnerBilin_apply h, integral_map (by fun_prop) (by fun_prop)]
  congr with z
  rw [integral_map (by fun_prop) h_Lp.1]
  simp only [id_eq]
  rw [integral_add (integrable_const _)]
  · simp
  · exact h.integrable (by simp)

variable [FiniteDimensional ℝ E]

/-- Covariance matrix of a measure on a finite dimensional inner product space. -/
noncomputable
def covMatrix (μ : Measure E) : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (covInnerBilin μ).toMatrix (stdOrthonormalBasis ℝ E).toBasis

lemma covMatrix_apply (μ : Measure E) (i j : Fin (Module.finrank ℝ E)) :
    covMatrix μ i j = covInnerBilin μ (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) := by
  rw [covMatrix, ContinuousBilinForm.toMatrix_apply, OrthonormalBasis.coe_toBasis]

lemma covMatrix_mulVec (x : Fin (Module.finrank ℝ E) → ℝ) :
    (covMatrix μ).mulVec x = fun i ↦
      covInnerBilin μ (stdOrthonormalBasis ℝ E i) (∑ j, x j • stdOrthonormalBasis ℝ E j) := by
  ext
  simp [covMatrix, Matrix.mulVec_eq_sum]

lemma dotProduct_covMatrix_mulVec (x y : Fin (Module.finrank ℝ E) → ℝ) :
    x ⬝ᵥ (covMatrix μ).mulVec y =
      covInnerBilin μ (∑ j, x j • stdOrthonormalBasis ℝ E j)
        (∑ j, y j • stdOrthonormalBasis ℝ E j) := by
  simp_rw [covMatrix, ContinuousBilinForm.dotProduct_toMatrix_mulVec,
    Basis.equivFun_symm_apply, OrthonormalBasis.coe_toBasis]

lemma covInnerBilin_eq_dotProduct_covMatrix_mulVec (x y : E) :
    covInnerBilin μ x y =
      ((stdOrthonormalBasis ℝ E).repr x) ⬝ᵥ
        ((covMatrix μ).mulVec ((stdOrthonormalBasis ℝ E).repr y)) := by
  rw [ContinuousBilinForm.apply_eq_dotProduct_toMatrix_mulVec _ (stdOrthonormalBasis ℝ E).toBasis]
  rfl

lemma covMatrix_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L : E →L[ℝ] F) (i j : Fin (Module.finrank ℝ F)) :
    covMatrix (μ.map L) i j =
      (stdOrthonormalBasis ℝ E).repr (L.adjoint (stdOrthonormalBasis ℝ F i)) ⬝ᵥ ((covMatrix μ) *ᵥ
        (stdOrthonormalBasis ℝ E).repr (L.adjoint (stdOrthonormalBasis ℝ F j))) := by
  rw [covMatrix_apply, covInnerBilin_map h, covInnerBilin_eq_dotProduct_covMatrix_mulVec]

lemma posSemidef_covMatrix [IsGaussian μ] : (covMatrix μ).PosSemidef :=
    (ContinuousBilinForm.isPosSemidef_iff_posSemidef_toMatrix _).1
      IsGaussian.isPosSemidef_covInnerBilin

end ProbabilityTheory
