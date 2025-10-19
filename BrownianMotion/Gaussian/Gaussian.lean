import BrownianMotion.Gaussian.CovMatrix
import BrownianMotion.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilinDual

/-!
# Facts about Gaussian characteristic function
-/

open Complex MeasureTheory WithLp NormedSpace

open scoped Matrix NNReal Real InnerProductSpace ProbabilityTheory

namespace ProbabilityTheory

/-- A Gaussian measure is a probability measure. -/
instance IsGaussian.isProbabilityMeasure {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module ℝ E] {mE : MeasurableSpace E} (μ : Measure E) [IsGaussian μ] :
    IsProbabilityMeasure μ where
  measure_univ := by simp

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

lemma isGaussian_iff_gaussian_charFunDual [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∃ (m : E) (f : ContinuousBilinForm ℝ (StrongDual ℝ E)),
      f.IsPosSemidef ∧ ∀ L, charFunDual μ L = exp (L m * I - f L L / 2) := by
  refine ⟨fun h ↦ ⟨μ[id], covarianceBilinDual μ, isPosSemidef_covarianceBilinDual, fun L ↦ ?_⟩,
    fun ⟨m, f, hf, h⟩ ↦ ⟨fun L ↦ ?_⟩⟩
  · rw [h.charFunDual_eq, covarianceBilinDual_self_eq_variance]
    · congr
      rw [← L.integral_comp_id_comm', integral_complex_ofReal]
      exact IsGaussian.integrable_id
    exact IsGaussian.memLp_two_id
  have : μ.map L = gaussianReal (L m) (f L L).toNNReal := by
    apply Measure.ext_of_charFun
    ext t
    simp_rw [charFun_map_eq_charFunDual_smul, h, charFun_gaussianReal,
      ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    congr
    · norm_cast
    rw [Real.coe_toNNReal]
    · norm_cast
      ring
    exact hf.nonneg_apply_self L
  rw [eq_gaussianReal_integral_variance this, integral_map (by fun_prop) (by fun_prop),
    variance_map aemeasurable_id (by fun_prop)]
  simp

attribute [simp] ContinuousLinearMap.coe_zero'

lemma gaussian_charFunDual_congr [IsFiniteMeasure μ] {m : E}
    {f : ContinuousBilinForm ℝ (StrongDual ℝ E)}
    (hf : f.IsPosSemidef) (h : ∀ L, charFunDual μ L = exp (L m * I - f L L / 2)) :
    m = ∫ x, x ∂μ ∧ f = covarianceBilinDual μ := by
  have h' := isGaussian_iff_gaussian_charFunDual.2 ⟨m, f, hf, h⟩
  simp_rw [h'.charFunDual_eq, Complex.exp_eq_exp_iff_exists_int, integral_complex_ofReal,
    ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id] at h
  choose n hn using h
  have h L : (n L : ℂ) = (L (∫ x, x ∂μ) * I - Var[L; μ] / 2 - L m * I + f L L / 2) /
      (2 * π * I) := by
    rw [hn L]
    have : 2 * π * I ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
    ring
  have : Continuous n := by
    rw [← Complex.isometry_intCast.comp_continuous_iff]
    change Continuous (fun L ↦ (n L : ℂ))
    simp_rw [h, ← covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id]
    fun_prop
  rw [← IsLocallyConstant.iff_continuous] at this
  apply IsLocallyConstant.eq_const at this
  have this L : n L = 0 := by
    rw [this 0, ← Int.cast_inj (α := ℂ)]
    simp [h]
  simp only [this, Int.cast_zero, zero_mul, add_zero, Complex.ext_iff, sub_re, mul_re, ofReal_re,
    I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, div_ofNat_re, zero_sub, neg_inj, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj', sub_im, mul_im, div_ofNat_im, zero_div,
    sub_zero] at hn
  constructor
  · rw [eq_iff_forall_dual_eq ℝ]
    simp [hn]
  · apply ContinuousBilinForm.ext_of_isSymm hf.isSymm isPosSemidef_covarianceBilinDual.isSymm
    intro x
    rw [covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id]
    exact (hn x).1.symm

/-- Two Gaussian measures are equal if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_covarianceBilinDual {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covarianceBilinDual μ = covarianceBilinDual ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [IsGaussian.charFunDual_eq, integral_complex_ofReal,
    L.integral_comp_id_comm' IsGaussian.integrable_id, hm,
    ← covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_iff_covarianceBilinDual {ν : Measure E} [IsGaussian μ]
    [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilinDual μ = covarianceBilinDual ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext_covarianceBilinDual h.1 h.2

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

lemma isGaussian_iff_charFun_eq [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∀ t, charFun μ t = exp (μ[fun x ↦ ⟪t, x⟫_ℝ] * I - Var[fun x ↦ ⟪t, x⟫_ℝ; μ] / 2) := by
  rw [isGaussian_iff_charFunDual_eq]
  constructor
  · intro h t
    convert h (InnerProductSpace.toDualMap ℝ E t)
    exact charFun_eq_charFunDual_toDualMap t
  · intro h L
    simpa using h ((InnerProductSpace.toDual ℝ E).symm L)

variable [SecondCountableTopology E]

lemma IsGaussian.charFun_eq [IsGaussian μ] (t : E) :
    charFun μ t = exp (⟪t, μ[id]⟫_ℝ * I - covInnerBilin μ t t / 2) := by
  rw [isGaussian_iff_charFun_eq.1 inferInstance]
  congr
  · simp_rw [integral_complex_ofReal, ← integral_inner IsGaussian.integrable_id, id]
  · rw [covInnerBilin_self IsGaussian.memLp_two_id]

lemma HasGaussianLaw.charFun_toLp {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {X : ι → Ω → ℝ} [hX : HasGaussianLaw (fun ω ↦ (X · ω)) P]
    (ξ : EuclideanSpace ℝ ι) :
    charFun (P.map (fun ω ↦ toLp 2 (X · ω))) ξ =
      exp (∑ i, ξ i * P[X i] * I - ∑ i, ∑ j, (ξ i : ℂ) * ξ j * (cov[X i, X j; P] / 2)) := by
  nth_rw 1 [IsGaussian.charFun_eq, covInnerBilin_apply_pi, EuclideanSpace.real_inner_eq]
  · simp_rw [ofReal_sum, Finset.sum_mul, ← mul_div_assoc, Finset.sum_div,
      integral_complex_ofReal, ← ofReal_mul]
    congrm exp (∑ i, Complex.ofReal (_ * ?_) * I - _)
    rw [integral_map, eval_integral_piLp]
    · simp
    · simp only [id_eq, PiLp.toLp_apply]
      exact fun i ↦ HasGaussianLaw.integrable
    · have := hX.aemeasurable
      fun_prop
    · exact aestronglyMeasurable_id
  · exact fun i ↦ HasGaussianLaw.memLp_two

lemma isGaussian_iff_gaussian_charFun [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∃ (m : E) (f : ContinuousBilinForm ℝ E),
      f.IsPosSemidef ∧ ∀ t, charFun μ t = exp (⟪t, m⟫_ℝ * I - f t t / 2) := by
  rw [isGaussian_iff_gaussian_charFunDual]
  refine ⟨fun ⟨m, f, hf, h⟩ ↦ ⟨m,
    f.bilinearComp (InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap
      (InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap,
    ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩, ?_⟩,
    fun ⟨m, f, hf, h⟩ ↦ ⟨m,
      f.bilinearComp (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
        (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap,
    ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩, ?_⟩⟩
  · simp [hf.isSymm.map_symm]
  · simp [hf.isPos.nonneg_apply_self]
  · simp [charFun_eq_charFunDual_toDualMap, h]
  · simp [hf.isSymm.map_symm]
  · simp [hf.isPos.nonneg_apply_self]
  · simp [← charFun_toDual_symm_eq_charFunDual, h]

/-- If the characteristic function of `μ` takes the form of a gaussian characteristic function,
then the parameters have to be the expectation and the covariance bilinear form. -/
lemma gaussian_charFun_congr [IsFiniteMeasure μ] (m : E) (f : ContinuousBilinForm ℝ E)
    (hf : f.IsPosSemidef) (h : ∀ t, charFun μ t = exp (⟪t, m⟫_ℝ * I - f t t / 2)) :
    m = ∫ x, x ∂μ ∧ f = covInnerBilin μ := by
  let g : ContinuousBilinForm ℝ (StrongDual ℝ E) :=
    f.bilinearComp (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
      (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
  have : ∀ L : StrongDual ℝ E, charFunDual μ L = exp (L m * I - g L L / 2) := by
    simp [← charFun_toDual_symm_eq_charFunDual, h, g]
  have hg : g.IsPosSemidef := by
    refine ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩
    · simp [g, hf.isSymm.map_symm]
    · simp [g, hf.isPos.nonneg_apply_self]
  have := gaussian_charFunDual_congr hg this
  refine ⟨this.1, ?_⟩
  ext
  simp [covInnerBilin, ← this.2, g, ← InnerProductSpace.toDual_apply_eq_toDualMap_apply]

/-- Two Gaussian measures are equal if they have same mean and same covariance. This is
`IsGaussian.ext_covarianceBilinDual` specialized to Hilbert spaces. -/
protected lemma IsGaussian.ext {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covInnerBilin μ = covInnerBilin ν) : μ = ν := by
  apply Measure.ext_of_charFun
  ext t
  simp_rw [IsGaussian.charFun_eq, hm, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. This is
`IsGaussian.ext_iff_covarianceBilinDual` specialized to Hilbert spaces. -/
protected lemma IsGaussian.ext_iff {ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covInnerBilin μ = covInnerBilin ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext h.1 h.2

end InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

lemma IsGaussian.eq_gaussianReal (μ : Measure ℝ) [IsGaussian μ] :
    μ = gaussianReal (∫ x, x ∂μ) Var[id; μ].toNNReal := by
  nth_rw 1 [← Measure.map_id (μ := μ), ← ContinuousLinearMap.coe_id' (R₁ := ℝ),
    map_eq_gaussianReal]
  rfl

end ProbabilityTheory
