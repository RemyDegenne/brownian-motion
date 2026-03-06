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
import Mathlib.Analysis.Matrix.Order



/-!
# Multivariate Gaussian distributions
-/

open MeasureTheory ProbabilityTheory Filter Matrix NormedSpace WithLp
open scoped ENNReal NNReal Topology RealInnerProductSpace MatrixOrder

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
    Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

@[simp]
lemma integral_id_stdGaussian : ∫ x, x ∂(stdGaussian E) = 0 := by
  rw [stdGaussian, integral_map _ (by fun_prop)]
  swap; · exact (Finset.measurable_sum _ (by fun_prop)).aemeasurable -- todo: add fun_prop tag
  rw [integral_finset_sum]
  swap
  · refine fun i _ ↦ Integrable.smul_const ?_ _
    convert integrable_comp_eval (i := i) (f := id) ?_
    · infer_instance
    · rw [← memLp_one_iff_integrable]
      exact memLp_id_gaussianReal 1
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have : (∫ (a : Fin (Module.finrank ℝ E) → ℝ), a i ∂Measure.pi fun x ↦ gaussianReal 0 1)
      = ∫ x, x ∂gaussianReal 0 1 := by
    convert integral_comp_eval (i := i) aestronglyMeasurable_id
    all_goals infer_instance
  simp [integral_smul_const, this]

lemma isCentered_stdGaussian : ∀ L : StrongDual ℝ E, (stdGaussian E)[L] = 0 := by
  intro L
  rw [L.integral_comp_id_comm, integral_id_stdGaussian, map_zero]
  rw [stdGaussian, integrable_map_measure]
  · rw [Function.id_comp]
    exact integrable_finset_sum _ fun i _ ↦ Integrable.smul_const
      (integrable_comp_eval (f := id) IsGaussian.integrable_id) _
  · exact aestronglyMeasurable_id
  · exact Measurable.aemeasurable (by fun_prop)

lemma variance_dual_stdGaussian (L : StrongDual ℝ E) : Var[L; stdGaussian E] = ‖L‖ ^ 2 := by
  rw [stdGaussian, variance_map]
  · have : L ∘ (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i) =
        ∑ i, (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ L (stdOrthonormalBasis ℝ E i) * x i) := by
      ext x; simp [mul_comm]
    rw [this, variance_pi]
    · change ∑ i, Var[fun x ↦ _ * (id x); gaussianReal 0 1] = _
      simp_rw [variance_const_mul, variance_id_gaussianReal, (stdOrthonormalBasis ℝ E).norm_dual]
      simp
    · exact fun i ↦ IsGaussian.memLp_two_id.const_mul _
  · exact L.continuous.aemeasurable
  · exact Measurable.aemeasurable (by fun_prop)

set_option backward.isDefEq.respectTransparency false in
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
  refine isGaussian_iff_gaussian_charFun.2 ⟨0, ContinuousBilinForm.inner E, ?_, ?_⟩
  · rw [← ContinuousBilinForm.toBilinForm_eq,
      ← ContinuousBilinForm.isPosSemidef_iff_bilinForm]
    exact ContinuousBilinForm.isPosSemidef_inner
  · simp [charFun_stdGaussian, neg_div]

set_option backward.isDefEq.respectTransparency false in
lemma charFunDual_stdGaussian (L : StrongDual ℝ E) :
    charFunDual (stdGaussian E) L = Complex.exp (- ‖L‖ ^ 2 / 2) := by
  rw [IsGaussian.charFunDual_eq, integral_complex_ofReal, isCentered_stdGaussian,
    variance_dual_stdGaussian]
  simp [neg_div]

lemma covarianceBilin_stdGaussian :
    covarianceBilin (stdGaussian E) = ContinuousBilinForm.inner E := by
  refine gaussian_charFun_congr 0 _ ?_ (fun t ↦ ?_) |>.2.symm
  · rw [← ContinuousBilinForm.toBilinForm_eq,
      ← ContinuousBilinForm.isPosSemidef_iff_bilinForm]
    exact ContinuousBilinForm.isPosSemidef_inner
  · simp [charFun_stdGaussian, neg_div]

lemma covMatrix_stdGaussian : covMatrix (stdGaussian E) = 1 := by
  rw [covMatrix, covarianceBilin_stdGaussian] --  ContinuousBilinForm.inner_toMatrix_eq_one
  ext i j
  simp [(stdOrthonormalBasis ℝ E).inner_eq, Matrix.one_apply]

lemma stdGaussian_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] (f : E ≃ₗᵢ[ℝ] F) :
    haveI := f.finiteDimensional; (stdGaussian E).map f = stdGaussian F := by
  have := f.finiteDimensional
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [← f.coe_coe_eq_coe, charFunDual_map, charFunDual_stdGaussian,
    L.opNorm_comp_linearIsometryEquiv]

lemma pi_eq_stdGaussian {n : Type*} [Fintype n] :
    (Measure.pi (fun _ ↦ gaussianReal 0 1)).map (toLp 2) = stdGaussian (EuclideanSpace ℝ n) := by
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
      ⇑((EuclideanSpace.basisFun ι ℝ).equiv b (Equiv.refl ι)) ∘ (toLp 2) := by
    simp_rw [← b.equiv_apply_euclideanSpace]
    rfl
  rw [this, ← Measure.map_map, pi_eq_stdGaussian, stdGaussian_map]
  all_goals fun_prop

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
/-- Multivariate Gaussian measure on `EuclideanSpace ℝ ι` with mean `μ` and covariance
matrix `S`. -/
noncomputable
def multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  (stdGaussian (EuclideanSpace ℝ ι)).map (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)

variable {μ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} {hS : S.PosSemidef}

set_option backward.isDefEq.respectTransparency false in
instance isGaussian_multivariateGaussian : IsGaussian (multivariateGaussian μ S) := by
  have h : (fun x ↦ μ + x) ∘ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))) =
    (fun x ↦ μ + (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) x) := rfl
  simp only [multivariateGaussian]
  rw [← h, ← Measure.map_map (measurable_const_add μ) (by measurability)]
  infer_instance

@[simp]
lemma integral_id_multivariateGaussian : ∫ x, x ∂(multivariateGaussian μ S) = μ := by
  rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop),
    integral_add (integrable_const _), integral_const]
  · simp [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id]
  · exact IsGaussian.integrable_id.comp_measurable (by fun_prop)

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

set_option backward.isDefEq.respectTransparency false in
lemma covarianceBilin_multivariateGaussian (hS : S.PosSemidef) :
    covarianceBilin (multivariateGaussian μ S)
      = ContinuousBilinForm.ofMatrix S (EuclideanSpace.basisFun ι ℝ).toBasis := by
  have h : (fun x ↦ μ + x) ∘ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))) =
    (fun x ↦ μ + (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) x) := rfl
  simp only [multivariateGaussian]
  rw [← h, ← Measure.map_map (measurable_const_add μ) (by fun_prop)]
  rw [covarianceBilin_map_const_add]
  ext x y
  rw [covarianceBilin_map, covarianceBilin_stdGaussian]
  swap; · exact IsGaussian.memLp_two_id
  rw [ContinuousBilinForm.inner_apply, ContinuousBilinForm.ofMatrix_apply,
    ContinuousLinearMap.adjoint_inner_left]
  rw [IsSelfAdjoint.adjoint_eq]
  swap
  · unfold _root_.IsSelfAdjoint
    rw [← map_star, EmbeddingLike.apply_eq_iff_eq]
    simpa using (CFC.sqrt_nonneg S).isHermitian
  calc ⟪x, (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) y)⟫
  _ = ⟪x, toEuclideanCLM (𝕜 := ℝ) S y⟫ := by
    congr 1
    have : (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).comp (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))
        = toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt S) * (CFC.sqrt S)) := by
      rw [map_mul]
      rfl
    rw [CFC.sqrt_mul_sqrt_self _ hS.nonneg, ContinuousLinearMap.ext_iff] at this
    rw [← this y]
    simp
  _ = ((EuclideanSpace.basisFun ι ℝ).toBasis.repr x) ⬝ᵥ
      S *ᵥ ((EuclideanSpace.basisFun ι ℝ).toBasis.repr y) := inner_toEuclideanCLM _ _

set_option backward.isDefEq.respectTransparency false in
lemma covariance_eval_multivariateGaussian (hS : S.PosSemidef) (i j : ι) :
    cov[fun x ↦ x i, fun x ↦ x j; multivariateGaussian μ S] = S i j := by
  have (i : ι) : (fun x : EuclideanSpace ℝ ι ↦ x i) =
      fun x ↦ ⟪EuclideanSpace.basisFun ι ℝ i, x⟫ := by ext; simp [PiLp.inner_apply]
  rw [this, this, ← covarianceBilin_apply_eq_cov, covarianceBilin_multivariateGaussian hS,
    ContinuousBilinForm.ofMatrix_orthonormalBasis]
  exact IsGaussian.memLp_two_id

lemma variance_eval_multivariateGaussian (hS : S.PosSemidef) (i : ι) :
    Var[fun x ↦ x i; multivariateGaussian μ S] = S i i := by
  rw [← covariance_self, covariance_eval_multivariateGaussian hS]
  exact Measurable.aemeasurable <| by fun_prop

lemma hasLaw_eval_multivariateGaussian (hS : S.PosSemidef) {i : ι} :
    HasLaw (fun x ↦ x i) (gaussianReal (μ i) (S i i).toNNReal) (multivariateGaussian μ S) where
  aemeasurable := Measurable.aemeasurable (by fun_prop)
  map_eq := by
    rw [← EuclideanSpace.coe_proj ℝ, IsGaussian.map_eq_gaussianReal,
      ContinuousLinearMap.integral_comp_id_comm, integral_id_multivariateGaussian,
      EuclideanSpace.proj_apply, EuclideanSpace.coe_proj, variance_eval_multivariateGaussian hS]
    exact IsGaussian.integrable_id

lemma charFun_multivariateGaussian (hS : S.PosSemidef) (x : EuclideanSpace ℝ ι) :
    charFun (multivariateGaussian μ S) x =
      Complex.exp (⟪x, μ⟫ * Complex.I
        - ContinuousBilinForm.ofMatrix S (EuclideanSpace.basisFun ι ℝ).toBasis x x / 2) := by
  rw [IsGaussian.charFun_eq']
  congr
  · exact integral_id_multivariateGaussian
  · exact covarianceBilin_multivariateGaussian hS

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
noncomputable
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

set_option backward.isDefEq.respectTransparency false in
lemma measurePreserving_restrict_multivariateGaussian (hS : S.PosSemidef) (hJI : J ⊆ I) :
    MeasurePreserving (EuclideanSpace.restrict₂ hJI) (multivariateGaussian μ S)
      (multivariateGaussian (μ.restrict₂ hJI)
      (S.submatrix (fun i : J ↦ ⟨i.1, hJI i.2⟩) (fun i : J ↦ ⟨i.1, hJI i.2⟩))) where
  measurable := by fun_prop
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
      exact IsGaussian.integrable_id
    apply ContinuousBilinForm.ext_basis (EuclideanSpace.basisFun J ℝ).toBasis
    intro i j
    rw [covarianceBilin_apply_eq_cov, covariance_map]
    · have (i : J) : (fun u ↦ ⟪(EuclideanSpace.basisFun J ℝ).toBasis i, u⟫) ∘
          EuclideanSpace.restrict₂ hJI = fun u ↦ u ⟨i.1, hJI i.2⟩ := by ext; simp [PiLp.inner_apply]
      simp_rw [this, covariance_eval_multivariateGaussian hS,
        covarianceBilin_multivariateGaussian (hS.submatrix _),
        ContinuousBilinForm.ofMatrix_basis, S.submatrix_apply]
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

set_option backward.isDefEq.respectTransparency false in
open scoped ComplexOrder in
lemma _root_.Matrix.PosSemidef.sqrt_one {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜] [DecidableEq n] :
    CFC.sqrt (1 : Matrix n n 𝕜) = 1 := by simp

set_option backward.isDefEq.respectTransparency false in
lemma multivariateGaussian_zero_one [Fintype ι] :
    multivariateGaussian 0 (1 : Matrix ι ι ℝ) = stdGaussian (EuclideanSpace ℝ ι) := by
  simp [multivariateGaussian]

end ProbabilityTheory
