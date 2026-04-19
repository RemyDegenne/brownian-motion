/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.WithLp
public import BrownianMotion.Gaussian.CovMatrix
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Multivariate Gaussian distributions
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Matrix NormedSpace WithLp
open scoped ENNReal NNReal Topology RealInnerProductSpace MatrixOrder

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  {d : ℕ}

variable [BorelSpace E]

set_option backward.isDefEq.respectTransparency false in
lemma covMatrix_stdGaussian : covMatrix (stdGaussian E) = 1 := by
  rw [covMatrix, covarianceBilin_stdGaussian] --  ContinuousBilinForm.inner_toMatrix_eq_one
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    ContinuousLinearMap.toBilinForm_apply, one_apply]
  rw [innerSL_apply_apply, (stdOrthonormalBasis ℝ E).inner_eq]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {μ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} {hS : S.PosSemidef}

set_option backward.isDefEq.respectTransparency false in
lemma inner_toEuclideanCLM (x y : EuclideanSpace ℝ ι) :
    ⟪x, toEuclideanCLM (𝕜 := ℝ) S y⟫
      = (EuclideanSpace.basisFun ι ℝ).toBasis.repr x ⬝ᵥ S
        *ᵥ (EuclideanSpace.basisFun ι ℝ).toBasis.repr y := by
  simp only [toEuclideanCLM, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearEquiv.invFun_eq_symm, LinearMap.coe_toContinuousLinearMap_symm, StarAlgEquiv.trans_apply,
    LinearMap.toMatrixOrthonormal_symm_apply, LinearMap.toMatrix_symm, StarAlgEquiv.coe_mk,
    StarRingEquiv.coe_mk, RingEquiv.coe_mk, Equiv.coe_fn_mk, LinearMap.coe_toContinuousLinearMap',
    toLin_apply, mulVec_eq_sum, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply,
    smul_eq_mul, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, dotProduct]
  congr with i
  rw [mul_comm (x.ofLp i)]
  simp [Pi.single_apply]

lemma hasLaw_eval_multivariateGaussian (hS : S.PosSemidef) {i : ι} :
    HasLaw (fun x ↦ x i) (gaussianReal (μ i) (S i i).toNNReal) (multivariateGaussian μ S) where
  aemeasurable := Measurable.aemeasurable (by fun_prop)
  map_eq := by
    rw [← EuclideanSpace.coe_proj ℝ, IsGaussian.map_eq_gaussianReal,
      ContinuousLinearMap.integral_comp_id_comm, integral_id_multivariateGaussian,
      EuclideanSpace.proj_apply, EuclideanSpace.coe_proj, variance_eval_multivariateGaussian hS]
    exact IsGaussian.integrable_id

end ProbabilityTheory
