import BrownianMotion.Auxiliary.HasLaw
import BrownianMotion.Gaussian.CovMatrix
import BrownianMotion.Gaussian.Fernique

/-!
# Facts about Gaussian characteristic function
-/

open Complex MeasureTheory WithLp

open scoped Matrix NNReal Real InnerProductSpace ProbabilityTheory

namespace ProbabilityTheory

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
  refine ⟨fun h ↦ ⟨μ[id], covInnerBilin μ, h.isPosSemidef_covInnerBilin, IsGaussian.charFun_eq⟩,
    fun ⟨m, f, hf, h⟩ ↦ ⟨fun L ↦ ?_⟩⟩
  have : μ.map L = gaussianReal (L m)
      (f ((InnerProductSpace.toDual ℝ E).symm L)
        ((InnerProductSpace.toDual ℝ E).symm L)).toNNReal := by
    apply Measure.ext_of_charFun
    ext t
    rw [charFun_map_eq_charFunDual_smul, ← charFun_toDual_symm_eq_charFunDual,
      charFun_gaussianReal, h, InnerProductSpace.toDual_symm_apply]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, ofReal_mul, map_smul]
    rw [← mul_assoc, pow_two, mul_comm (t * t : ℂ), Real.coe_toNNReal]
    exact hf.nonneg_re_apply_self _
  rw [eq_gaussianReal_integral_variance this, integral_map (by fun_prop) (by fun_prop),
    variance_map aemeasurable_id (by fun_prop)]
  simp

/-- If the characteristic function of `μ` takes the form of a gaussian characteristic function,
then the parameters have to be the expectation and the covariance bilinear form. -/
lemma gaussian_charFun_congr [IsFiniteMeasure μ] (m : E) (f : ContinuousBilinForm ℝ E)
    (hf : f.IsPosSemidef) (h : ∀ t, charFun μ t = exp (⟪t, m⟫_ℝ * I - f t t / 2)) :
    m = μ[id] ∧ f = covInnerBilin μ := by
  have h' := isGaussian_iff_gaussian_charFun.2 ⟨m, f, hf, h⟩
  simp_rw [h'.charFun_eq, Complex.exp_eq_exp_iff_exists_int] at h
  choose n hn using h
  have h t : (n t : ℂ) = (⟪t, μ[id]⟫_ℝ * I - covInnerBilin μ t t / 2 - ⟪t, m⟫_ℝ * I + f t t / 2) /
      (2 * π * I) := by
    rw [hn]
    have : 2 * π * I ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
    ring
  have : Continuous n := by
    rw [← Complex.isometry_intCast.comp_continuous_iff]
    change Continuous (fun t ↦ (n t : ℂ))
    simp_rw [h]
    fun_prop
  rw [← IsLocallyConstant.iff_continuous] at this
  apply IsLocallyConstant.eq_const at this
  have this t : n t = 0 := by
    rw [this 0, ← Int.cast_inj (α := ℂ)]
    simp [h]
  simp [Complex.ext_iff, this] at hn
  constructor
  · apply ext_inner_left ℝ
    simp [hn]
  · apply ContinuousBilinForm.ext_of_isSymm hf.isSymm h'.isPosSemidef_covInnerBilin.isSymm
    grind

/-- Two Gaussian measures are equal if they have same mean and same covariance. This is
`IsGaussian.ext_covarianceBilin` specialized to Hilbert spaces. -/
protected lemma IsGaussian.ext {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covInnerBilin μ = covInnerBilin ν) : μ = ν := by
  apply Measure.ext_of_charFun
  ext t
  simp_rw [IsGaussian.charFun_eq, hm, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. This is
`IsGaussian.ext_iff_covarianceBilin` specialized to Hilbert spaces. -/
protected lemma IsGaussian.ext_iff {ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covInnerBilin μ = covInnerBilin ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext h.1 h.2

end InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- Two Gaussian measures are equal if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_covarianceBilin {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covarianceBilinDual μ = covarianceBilinDual ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [IsGaussian.charFunDual_eq, integral_complex_ofReal,
    L.integral_comp_id_comm' IsGaussian.integrable_id, hm,
    ← covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_iff_covarianceBilin {ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilinDual μ = covarianceBilinDual ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext_covarianceBilin h.1 h.2

lemma IsGaussian.eq_gaussianReal (μ : Measure ℝ) [IsGaussian μ] :
    μ = gaussianReal μ[id] Var[id; μ].toNNReal := by
  nth_rw 1 [← Measure.map_id (μ := μ), ← ContinuousLinearMap.coe_id' (R₁ := ℝ),
    map_eq_gaussianReal]
  rfl

lemma HasGaussianLaw.map_eq_gaussianReal {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} [HasGaussianLaw X P] :
    P.map X = gaussianReal P[X] Var[X; P].toNNReal := by
  rw [IsGaussian.eq_gaussianReal (.map _ _), integral_map, variance_map]
  · rfl
  any_goals fun_prop

lemma HasGaussianLaw.charFun_map_real {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} [HasGaussianLaw X P] (t : ℝ) :
    charFun (P.map X) t = exp (t * P[X] * I - t ^ 2 * Var[X; P] / 2) := by
  rw [HasGaussianLaw.map_eq_gaussianReal, IsGaussian.charFun_eq, covInnerBilin_real_self]
  · simp [variance_nonneg, integral_complex_ofReal, mul_comm]
  exact IsGaussian.memLp_two_id

end ProbabilityTheory
