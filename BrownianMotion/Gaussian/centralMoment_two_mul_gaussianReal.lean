import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic


lemma centralMoment_two_mul_gaussianReal
  (μ : ℝ) (σ : NNReal) (n : ℕ) :
  ProbabilityTheory.centralMoment id (2 * n) (ProbabilityTheory.gaussianReal μ σ)
  = (σ : ℝ)^(2 * n) * Nat.doubleFactorial (2 * n - 1)
  := by
    unfold ProbabilityTheory.centralMoment
    unfold ProbabilityTheory.gaussianReal
    by_cases hσ : σ = 0
    .
      by_cases hn : n = 0
        <;> simp_all only [↓reduceIte, id_eq, MeasureTheory.integral_dirac,
                            mul_zero, Pi.pow_apply, Pi.sub_apply, pow_zero,
                            MeasureTheory.integral_const,
                            MeasureTheory.measureReal_univ_eq_one, smul_eq_mul,
                            mul_one, NNReal.coe_zero, zero_tsub,
                            Nat.doubleFactorial.eq_1, Nat.cast_one, ↓reduceIte,
                            id_eq, MeasureTheory.integral_dirac, Pi.pow_apply,
                            Pi.sub_apply, sub_self, ne_eq, mul_eq_zero,
                            OfNat.ofNat_ne_zero, or_self, not_false_eq_true,
                            zero_pow, NNReal.coe_zero, zero_mul]
    .
      -- 1) ∫ (x - μ)^(2n) dP(x) = ∫ (x - μ)^(2n) (1 / (σ * sqrt(2 * π))) *
      -- exp(-((x - μ)^2) / (2 * σ^2)) dx
      simp_all only [↓reduceIte, Nat.cast_prod, Nat.cast_add, Nat.cast_mul,
                    Nat.cast_ofNat, Nat.cast_one]
      rw [integral_withDensity_eq_integral_toReal_smul]
      rotate_left
      simp only [ProbabilityTheory.measurable_gaussianPDF]
      simp only [ProbabilityTheory.gaussianPDF_lt_top, Filter.eventually_true]
      simp only [ProbabilityTheory.toReal_gaussianPDF, smul_eq_mul]
      rw [ProbabilityTheory.gaussianPDFReal_def]
      simp_all only [NNReal.zero_le_coe, Real.sqrt_mul', Nat.ofNat_nonneg,
                    Real.sqrt_mul, mul_inv_rev, ENNReal.toReal_ofReal', smul_eq_mul]
      -- 2) Change of variable y = sqrt(2(x - μ) / σ) using parity to end up with
      -- an integral over 0 to +∞.
      -- 3) Relate the integral to the gamma function and end the proof with
      -- simple algebra.
      sorry
