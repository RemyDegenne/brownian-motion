/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Gaussian.Gaussian


/-!
# Multivariate Gaussian distributions
-/

open MeasureTheory ProbabilityTheory Filter Matrix NormedSpace
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  {d : ℕ}

variable (E) in
/-- Standard Gaussian distribution on `E`. -/
noncomputable
def stdGaussian : Measure E :=
  (Measure.pi (fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 1)).map
    (fun x ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i)

variable [BorelSpace E]

instance isProbabilityMeasure_stdGaussian : IsProbabilityMeasure (stdGaussian E) :=
    isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

-- TODO: generalize to `f` taking values in a Banach space
lemma integrable_eval_pi {ι 𝕜 : Type*} [Fintype ι] [NormedCommRing 𝕜] {X : ι → Type*} {i : ι}
    {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}
    [∀ i, IsFiniteMeasure (μ i)] {f : X i → 𝕜} (hf : Integrable f (μ i)) :
    Integrable (fun x ↦ f (x i)) (Measure.pi μ) := by
  classical
  let g : Π i, X i → 𝕜 := fun j ↦ if h : j = i then h ▸ f else 1
  have : (fun x ↦ ∏ j, g j (x j)) = fun (x : Π i, X i) ↦ f (x i) := by
    ext x
    rw [show f (x i) = g i (x i) by simp [g]]
    exact Finset.prod_eq_single_of_mem i (by simp) (fun j _ hj ↦ by simp [g, hj])
  rw [← this]
  refine Integrable.fintype_prod_dep fun j ↦ ?_
  by_cases h : j = i
  · cases h; simpa [g]
  · simpa [g, h] using integrable_const 1

-- TODO: generalize to `f` taking values in a Banach space
lemma integral_eval_pi {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜] {X : ι → Type*} {i : ι}
    {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}
    [∀ i, IsProbabilityMeasure (μ i)] {f : X i → 𝕜} :
    ∫ (x : Π i, X i), f (x i) ∂Measure.pi μ = ∫ x, f x ∂μ i := by
  classical
  let g : Π i, X i → 𝕜 := fun j ↦ if h : j = i then h ▸ f else 1
  have : (fun x ↦ ∏ j, g j (x j)) = fun (x : Π i, X i) ↦ f (x i) := by
    ext x
    rw [show f (x i) = g i (x i) by simp [g]]
    exact Finset.prod_eq_single_of_mem i (by simp) (fun j _ hj ↦ by simp [g, hj])
  rw [← this, integral_fintype_prod_eq_prod, show ∫ x, f x ∂μ i = ∫ x, g i x ∂μ i by simp [g]]
  exact Finset.prod_eq_single_of_mem i (by simp) (fun j _ hj ↦ by simp [g, hj])

@[simp]
lemma integral_id_stdGaussian : ∫ x, x ∂(stdGaussian E) = 0 := by
  rw [stdGaussian, integral_map _ (by fun_prop)]
  swap; · exact (Finset.measurable_sum _ (by fun_prop)).aemeasurable -- todo: add fun_prop tag
  rw [integral_finset_sum]
  swap
  · refine fun i _ ↦ Integrable.smul_const ?_ _
    convert integrable_eval_pi (i := i) (f := id) ?_
    · infer_instance
    · rw [← memLp_one_iff_integrable]
      exact memLp_id_gaussianReal 1
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have : (∫ (a : Fin (Module.finrank ℝ E) → ℝ), a i ∂Measure.pi fun x ↦ gaussianReal 0 1)
      = ∫ x, x ∂gaussianReal 0 1 := by
    convert integral_eval_pi (i := i)
    · rfl
    · infer_instance
  simp [integral_smul_const, this]

lemma isCentered_stdGaussian : ∀ L : Dual ℝ E, (stdGaussian E)[L] = 0 := by
  intro L
  rw [L.integral_comp_id_comm, integral_id_stdGaussian, map_zero]
  rw [stdGaussian, integrable_map_measure]
  · rw [Function.id_comp]
    exact integrable_finset_sum _ fun i _ ↦ Integrable.smul_const
      (integrable_eval_pi (f := id) (IsGaussian.integrable_id _)) _
  · exact aestronglyMeasurable_id
  · exact Measurable.aemeasurable (by fun_prop)

lemma variance_dual_stdGaussian (L : Dual ℝ E) : Var[L; stdGaussian E] = ‖L‖ ^ 2 := by
  rw [stdGaussian, variance_map]
  · have : L ∘ (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i) =
        ∑ i, (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ L (stdOrthonormalBasis ℝ E i) * x i) := by
      ext x; simp [mul_comm]
    rw [this, variance_pi]
    · change ∑ i, Var[fun x ↦ _ * (id x); gaussianReal 0 1] = _
      simp_rw [variance_mul, variance_id_gaussianReal, (stdOrthonormalBasis ℝ E).norm_dual]
      simp
    · exact fun i ↦ ((isGaussian_gaussianReal 0 1).memLp_two_id _).const_mul _
  · exact L.continuous.aemeasurable
  · exact Measurable.aemeasurable (by fun_prop)

lemma charFun_stdGaussian (t : E) : charFun (stdGaussian E) t = Complex.exp (- ‖t‖ ^ 2 / 2) := by
  rw [charFun_apply, stdGaussian, integral_map]
  · simp_rw [sum_inner, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum,
      integral_fintype_prod_eq_prod
        (f := fun i x ↦ Complex.exp (⟪x • stdOrthonormalBasis ℝ E i, t⟫ * Complex.I)),
      real_inner_smul_left, mul_comm _ (⟪_, _⟫), Complex.ofReal_mul, ← charFun_apply_real,
      charFun_gaussianReal]
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one, one_mul,
      zero_sub]
    simp_rw [← Complex.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, ← Complex.ofReal_pow,
      ← Complex.ofReal_sum, ← (stdOrthonormalBasis ℝ E).norm_sq_eq_sum_sq_inner_right, neg_div]
  · exact Measurable.aemeasurable (by fun_prop)
  · exact Measurable.aestronglyMeasurable (by fun_prop)

instance isGaussian_stdGaussian : IsGaussian (stdGaussian E) := by
  refine isGaussian_iff_gaussian_charFun.2 ?_
  use 0, ContinuousBilinForm.inner E, ContinuousBilinForm.isPosSemidef_inner
  simp [charFun_stdGaussian, real_inner_self_eq_norm_sq, neg_div]

lemma charFunDual_stdGaussian (L : Dual ℝ E) :
    charFunDual (stdGaussian E) L = Complex.exp (- ‖L‖ ^ 2 / 2) := by
  rw [IsGaussian.charFunDual_eq, integral_complex_ofReal, isCentered_stdGaussian,
    variance_dual_stdGaussian]
  simp [neg_div]

lemma covInnerBilin_stdGaussian :
    covInnerBilin (stdGaussian E) = ContinuousBilinForm.inner E := by
  refine gaussian_charFun_congr 0 _ ContinuousBilinForm.isPosSemidef_inner (fun t ↦ ?_) |>.2.symm
  simp [charFun_stdGaussian, real_inner_self_eq_norm_sq, neg_div]

lemma covMatrix_stdGaussian : covMatrix (stdGaussian E) = 1 := by
  rw [covMatrix, covInnerBilin_stdGaussian, ContinuousBilinForm.inner_toMatrix_eq_one]

lemma stdGaussian_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] (f : E ≃ₗᵢ[ℝ] F) :
    haveI := f.finiteDimensional; (stdGaussian E).map f = stdGaussian F := by
  have := f.finiteDimensional
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [← f.coe_coe_eq_coe, charFunDual_map, charFunDual_stdGaussian,
    L.opNorm_comp_linearIsometryEquiv]

lemma pi_eq_stdGaussian {n : Type*} [Fintype n] :
    Measure.pi (fun _ ↦ gaussianReal 0 1) = stdGaussian (EuclideanSpace ℝ n) := by
  -- This instance is not found automatically, probably a defeq issue between
  -- `n → ℝ` and `EuclideanSpace ℝ n`.
  have : IsFiniteMeasure (Measure.pi fun _ : n ↦ gaussianReal 0 1) := inferInstance
  apply Measure.ext_of_charFun (E := EuclideanSpace ℝ n)
  ext t
  simp_rw [charFun_stdGaussian, charFun_pi, charFun_gaussianReal, ← Complex.exp_sum,
    ← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq]
  simp [Finset.sum_div, neg_div]

lemma stdGaussian_eq_pi_map_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    stdGaussian E = (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map
      (fun x ↦ ∑ i, x i • b i) := by
  have : (fun (x : ι → ℝ) ↦ ∑ i, x i • b i) =
      ⇑((EuclideanSpace.basisFun ι ℝ).equiv b (Equiv.refl ι)) := by
    simp_rw [← b.equiv_apply_euclideanSpace]
  rw [this, pi_eq_stdGaussian, stdGaussian_map (f := (EuclideanSpace.basisFun ι ℝ).equiv _ _)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable
def multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (hS : S.PosSemidef) :
    Measure (EuclideanSpace ℝ ι) :=
  (stdGaussian (EuclideanSpace ℝ ι)).map (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) hS.sqrt x)

variable {μ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} {hS : S.PosSemidef}

instance isGaussian_multivariateGaussian : IsGaussian (multivariateGaussian μ S hS) := by
  have h : (fun x ↦ μ + x) ∘ ((toEuclideanCLM (𝕜 := ℝ) hS.sqrt)) =
    (fun x ↦ μ + (toEuclideanCLM (𝕜 := ℝ) hS.sqrt) x) := rfl
  simp only [multivariateGaussian]
  rw [← h, ← Measure.map_map (measurable_const_add μ) (by measurability)]
  infer_instance

@[simp]
lemma integral_id_multivariateGaussian : ∫ x, x ∂(multivariateGaussian μ S hS) = μ := by
  rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop),
    integral_add (integrable_const _), integral_const]
  · simp [ContinuousLinearMap.integral_comp_comm _ (IsGaussian.integrable_fun_id _)]
  · have h_id : Integrable id ((stdGaussian (EuclideanSpace ℝ ι)).map
      (toEuclideanCLM (𝕜 := ℝ) hS.sqrt)) := IsGaussian.integrable_id _
    exact h_id.comp_measurable (by fun_prop)

lemma inner_toEuclideanCLM (x y : EuclideanSpace ℝ ι) :
    ⟪x, toEuclideanCLM (𝕜 := ℝ) S y⟫
      = (EuclideanSpace.basisFun ι ℝ).toBasis.repr x ⬝ᵥ S
        *ᵥ (EuclideanSpace.basisFun ι ℝ).toBasis.repr y := by
  simp only [toEuclideanCLM, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearEquiv.invFun_eq_symm, LinearMap.coe_toContinuousLinearMap_symm, StarAlgEquiv.trans_apply,
    LinearMap.toMatrixOrthonormal_symm_apply, LinearMap.toMatrix_symm, StarAlgEquiv.coe_mk,
    RingEquiv.coe_mk, Equiv.coe_fn_mk, LinearMap.coe_toContinuousLinearMap', toLin_apply,
    mulVec_eq_sum, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, dotProduct]
  congr with i
  rw [mul_comm]
  congr
  rw [Finset.sum_apply]
  simp

lemma covInnerBilin_multivariateGaussian :
    covInnerBilin (multivariateGaussian μ S hS)
      = ContinuousBilinForm.ofMatrix S (EuclideanSpace.basisFun ι ℝ).toBasis := by
  have h : (fun x ↦ μ + x) ∘ ((toEuclideanCLM (𝕜 := ℝ) hS.sqrt)) =
    (fun x ↦ μ + (toEuclideanCLM (𝕜 := ℝ) hS.sqrt) x) := rfl
  simp only [multivariateGaussian]
  rw [← h, ← Measure.map_map (measurable_const_add μ) (by fun_prop)]
  rw [covInnerBilin_map_const_add]
  swap; · exact IsGaussian.memLp_two_id _
  ext x y
  rw [covInnerBilin_map, covInnerBilin_stdGaussian]
  swap; · exact IsGaussian.memLp_two_id _
  rw [ContinuousBilinForm.inner_apply, ContinuousBilinForm.ofMatrix_apply,
    ContinuousLinearMap.adjoint_inner_left]
  rw [IsSelfAdjoint.adjoint_eq]
  swap
  · unfold _root_.IsSelfAdjoint
    rw [← map_star, EmbeddingLike.apply_eq_iff_eq]
    exact hS.posSemidef_sqrt.isHermitian
  calc ⟪x, (toEuclideanCLM (𝕜 := ℝ) hS.sqrt) (toEuclideanCLM (𝕜 := ℝ) hS.sqrt y)⟫
  _ = ⟪x, toEuclideanCLM (𝕜 := ℝ) S y⟫ := by
    congr 1
    have : (toEuclideanCLM (𝕜 := ℝ) hS.sqrt).comp (toEuclideanCLM (𝕜 := ℝ) hS.sqrt)
        = toEuclideanCLM (𝕜 := ℝ) (hS.sqrt * hS.sqrt) := by
      rw [map_mul]
      rfl
    rw [PosSemidef.sqrt_mul_self, ContinuousLinearMap.ext_iff] at this
    rw [← this y]
    simp
  _ = ((EuclideanSpace.basisFun ι ℝ).toBasis.repr x) ⬝ᵥ
      S *ᵥ ((EuclideanSpace.basisFun ι ℝ).toBasis.repr y) := inner_toEuclideanCLM _ _

lemma charFun_multivariateGaussian (x : EuclideanSpace ℝ ι) :
    charFun (multivariateGaussian μ S hS) x =
      Complex.exp (⟪x, μ⟫ * Complex.I
        - ContinuousBilinForm.ofMatrix S (EuclideanSpace.basisFun ι ℝ).toBasis x x / 2) := by
  rw [IsGaussian.charFun_eq]
  congr
  · exact integral_id_multivariateGaussian
  · exact covInnerBilin_multivariateGaussian

end ProbabilityTheory
