/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Gaussian.Gaussian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular



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

lemma integrable_eval_pi {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] {X : ι → Type*} {i : ι}
    {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}
    [∀ i, IsFiniteMeasure (μ i)] {f : X i → E} (hf : Integrable f (μ i)) :
    Integrable (fun x ↦ f (x i)) (Measure.pi μ) := by
  simp_rw [← Function.eval_apply (x := i)]
  refine Integrable.comp_measurable ?_ (by fun_prop)
  classical
  rw [Measure.pi_map_eval]
  exact hf.smul_measure <| ENNReal.prod_ne_top (fun _ _ ↦ measure_ne_top _ _)

lemma integral_eval_pi {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {X : ι → Type*}
    {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}
    [∀ i, IsProbabilityMeasure (μ i)] {i : ι} {f : X i → E} (hf : AEStronglyMeasurable f (μ i)) :
    ∫ (x : Π i, X i), f (x i) ∂Measure.pi μ = ∫ x, f x ∂μ i := by
  simp_rw [← Function.eval_apply (β := X) (x := i)]
  rw [← integral_map, (measurePreserving_eval i).map_eq]
  · exact Measurable.aemeasurable (by fun_prop)
  · rwa [(measurePreserving_eval i).map_eq]

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
    convert integral_eval_pi (i := i) aestronglyMeasurable_id
    all_goals infer_instance
  simp [integral_smul_const, this]

lemma isCentered_stdGaussian : ∀ L : StrongDual ℝ E, (stdGaussian E)[L] = 0 := by
  intro L
  rw [L.integral_comp_id_comm, integral_id_stdGaussian, map_zero]
  rw [stdGaussian, integrable_map_measure]
  · rw [Function.id_comp]
    exact integrable_finset_sum _ fun i _ ↦ Integrable.smul_const
      (integrable_eval_pi (f := id) IsGaussian.integrable_id) _
  · exact aestronglyMeasurable_id
  · exact Measurable.aemeasurable (by fun_prop)

lemma variance_dual_stdGaussian (L : StrongDual ℝ E) : Var[L; stdGaussian E] = ‖L‖ ^ 2 := by
  rw [stdGaussian, variance_map]
  · have : L ∘ (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i) =
        ∑ i, (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ L (stdOrthonormalBasis ℝ E i) * x i) := by
      ext x; simp [mul_comm]
    rw [this, variance_pi]
    · change ∑ i, Var[fun x ↦ _ * (id x); gaussianReal 0 1] = _
      simp_rw [variance_mul, variance_id_gaussianReal, (stdOrthonormalBasis ℝ E).norm_dual]
      simp
    · exact fun i ↦ IsGaussian.memLp_two_id.const_mul _
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

lemma charFunDual_stdGaussian (L : StrongDual ℝ E) :
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

/-- Multivariate Gaussian measure on `EuclideanSpace ℝ ι` with mean `μ` and covariance
matrix `S`. -/
noncomputable
def multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (hS : S.PosSemidef) :
    Measure (EuclideanSpace ℝ ι) :=
  (stdGaussian (EuclideanSpace ℝ ι)).map (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) hS.sqrt x)

/-- Because `multivariateGaussian` carries a proof that `S` is positive semidefinite,
`rw [h]` will not solve the goal below. This is what this lemma is used for. -/
lemma multivariateGaussian_congr_matrix {μ : EuclideanSpace ℝ ι} {S S' : Matrix ι ι ℝ}
    {hS : S.PosSemidef} (h : S = S') :
    multivariateGaussian μ S hS = multivariateGaussian μ S' (h ▸ hS) := by
  cases h; rfl

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
  · simp [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id]
  · exact IsGaussian.integrable_id.comp_measurable (by fun_prop)

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
  swap; · exact IsGaussian.memLp_two_id
  ext x y
  rw [covInnerBilin_map, covInnerBilin_stdGaussian]
  swap; · exact IsGaussian.memLp_two_id
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

lemma covariance_eval_multivariateGaussian (i j : ι) :
    cov[fun x ↦ x i, fun x ↦ x j; multivariateGaussian μ S hS] = S i j := by
  have (i : ι) : (fun x : EuclideanSpace ℝ ι ↦ x i) =
      fun x ↦ ⟪EuclideanSpace.basisFun ι ℝ i, x⟫ := by ext; simp [PiLp.inner_apply]
  rw [this, this, ← covInnerBilin_apply_eq, covInnerBilin_multivariateGaussian,
    ContinuousBilinForm.ofMatrix_orthonormalBasis]
  exact IsGaussian.memLp_two_id

lemma variance_eval_multivariateGaussian (i : ι) :
    Var[fun x ↦ x i; multivariateGaussian μ S hS] = S i i := by
  rw [← covariance_self, covariance_eval_multivariateGaussian]
  exact Measurable.aemeasurable <| by fun_prop

lemma hasLaw_eval_multivariateGaussian {i : ι} :
    HasLaw (fun x ↦ x i) (gaussianReal (μ i) (S i i).toNNReal) (multivariateGaussian μ S hS) where
  aemeasurable := Measurable.aemeasurable (by fun_prop)
  map_eq := by
    rw [← EuclideanSpace.coe_proj ℝ, IsGaussian.map_eq_gaussianReal,
      ContinuousLinearMap.integral_comp_id_comm, integral_id_multivariateGaussian,
      EuclideanSpace.proj_apply, EuclideanSpace.coe_proj, variance_eval_multivariateGaussian]
    exact IsGaussian.integrable_id

lemma charFun_multivariateGaussian (x : EuclideanSpace ℝ ι) :
    charFun (multivariateGaussian μ S hS) x =
      Complex.exp (⟪x, μ⟫ * Complex.I
        - ContinuousBilinForm.ofMatrix S (EuclideanSpace.basisFun ι ℝ).toBasis x x / 2) := by
  rw [IsGaussian.charFun_eq]
  congr
  · exact integral_id_multivariateGaussian
  · exact covInnerBilin_multivariateGaussian

/-- `Finset.restrict₂` as a continuous linear map. -/
def _root_.Finset.restrict₂CLM {ι : Type*} (R : Type*) {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)]
    {I J : Finset ι} (hIJ : I ⊆ J) :
    (Π i : J, M i) →L[R] Π i : I, M i where
  toFun := Finset.restrict₂ hIJ
  map_add' x y := by ext; simp
  map_smul' m x := by ext; simp
  cont := by fun_prop

lemma _root_.Finset.coe_restrict₂CLM {ι R : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)] {I J : Finset ι}
    (hIJ : I ⊆ J) :
    ⇑(Finset.restrict₂CLM (R := R) (M := M) hIJ) = Finset.restrict₂ hIJ := rfl

@[simp]
lemma _root_.Finset.restrict₂CLM_apply {ι R : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)] {I J : Finset ι}
    (hIJ : I ⊆ J) (x : Π i : J, M i) (i : I) :
    Finset.restrict₂CLM (R := R) hIJ x i = x ⟨i.1, hIJ i.2⟩ := rfl

/-- The restriction from `EuclideanSpace 𝕜 J` to `EuclideanSpace κ I` when `I ⊆ J`. -/
def _root_.EuclideanSpace.restrict₂ {ι 𝕜 : Type*} [RCLike 𝕜] {I J : Finset ι} (hIJ : I ⊆ J) :
    EuclideanSpace 𝕜 J →L[𝕜] EuclideanSpace 𝕜 I :=
  (EuclideanSpace.equiv I 𝕜).symm.toContinuousLinearMap ∘L
    (Finset.restrict₂CLM 𝕜 (M := fun _ ↦ 𝕜) hIJ) ∘L
      (EuclideanSpace.equiv J 𝕜).toContinuousLinearMap

-- lemma _root_.EuclideanSpace.coe_restrict₂
--     {ι 𝕜 : Type*} [RCLike 𝕜] {I J : Finset ι} (hIJ : I ⊆ J) :
--     ⇑(@EuclideanSpace.restrict₂ ι 𝕜 _ I J hIJ) = EuclideanSpace.restrict₂ hIJ := rfl

@[simp]
lemma _root_.EuclideanSpace.restrict₂_apply {ι 𝕜 : Type*} [RCLike 𝕜] {I J : Finset ι}
    (hIJ : I ⊆ J) (x : EuclideanSpace 𝕜 J) (i : I) :
    EuclideanSpace.restrict₂ hIJ x i = x ⟨i.1, hIJ i.2⟩ := rfl

variable {ι : Type*} [DecidableEq ι] {I J : Finset ι}

variable {μ : EuclideanSpace ℝ I} {S : Matrix I I ℝ} {hS : S.PosSemidef}

lemma measurePreserving_restrict_multivariateGaussian (hJI : J ⊆ I) :
    MeasurePreserving (EuclideanSpace.restrict₂ hJI) (multivariateGaussian μ S hS)
      (multivariateGaussian (μ.restrict₂ hJI)
      (S.submatrix (fun i : J ↦ ⟨i.1, hJI i.2⟩) (fun i : J ↦ ⟨i.1, hJI i.2⟩))
      (hS.submatrix _)) where
  measurable := by fun_prop
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
      exact IsGaussian.integrable_id
    apply ContinuousBilinForm.ext_basis (EuclideanSpace.basisFun J ℝ).toBasis
    intro i j
    rw [covInnerBilin_apply_eq, covariance_map]
    · have (i : J) : (fun u ↦ ⟪(EuclideanSpace.basisFun J ℝ).toBasis i, u⟫) ∘
          EuclideanSpace.restrict₂ hJI = fun u ↦ u ⟨i.1, hJI i.2⟩ := by ext; simp [PiLp.inner_apply]
      simp_rw [this, covariance_eval_multivariateGaussian, covInnerBilin_multivariateGaussian,
        ContinuousBilinForm.ofMatrix_basis, S.submatrix_apply]
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

open scoped ComplexOrder in
@[simp]
lemma _root_.Matrix.PosSemidef.sqrt_one {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜] [DecidableEq n]
    (h : Matrix.PosSemidef (1 : Matrix n n 𝕜)) : h.sqrt = 1 := h.sqrt_eq_one_iff.2 rfl

lemma multivariateGaussian_zero_one [Fintype ι] :
    multivariateGaussian 0 (1 : Matrix ι ι ℝ) Matrix.PosSemidef.one =
      stdGaussian (EuclideanSpace ℝ ι) := by
  simp [multivariateGaussian]

end ProbabilityTheory
