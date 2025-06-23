import BrownianMotion.Gaussian.CovMatrix

/-!
# Facts about Gaussian characteristic function
-/

open Complex MeasureTheory

open scoped Matrix NNReal Real InnerProductSpace ProbabilityTheory

namespace ProbabilityTheory

section InnerProductSpace

protected lemma IsGaussian.ne_zero {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {mE : MeasurableSpace E} (μ : Measure E) [hμ : IsGaussian μ] : μ ≠ 0 := by
  by_contra h
  let L : E →L[ℝ] ℝ := Classical.ofNonempty
  have := hμ.map_eq_gaussianReal L
  rw [h, Measure.map_zero] at this
  have : IsProbabilityMeasure (0 : Measure ℝ) := this ▸ inferInstance
  have := this.ne_zero
  contradiction

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
  · simp_rw [integral_complex_ofReal, ← integral_inner (IsGaussian.integrable_id μ), id]
  · rw [covInnerBilin_self (IsGaussian.memLp_two_id μ)]

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
    intro x
    linear_combination 2 * (hn x).1.symm

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
    (hm : μ[id] = ν[id]) (hv : covarianceBilin μ = covarianceBilin ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [IsGaussian.charFunDual_eq, integral_complex_ofReal,
    L.integral_comp_id_comm' (IsGaussian.integrable_id _), hm,
    ← covarianceBilin_same_eq_variance (IsGaussian.memLp_two_id _), hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_iff_covarianceBilin {ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilin μ = covarianceBilin ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext_covarianceBilin h.1 h.2

end ProbabilityTheory
