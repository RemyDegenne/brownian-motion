import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic


lemma centralMoment_two_mul_gaussianReal
  (μ : ℝ) (σ : NNReal) (n : ℕ) :
  ProbabilityTheory.centralMoment id (2 * n) (ProbabilityTheory.gaussianReal μ (σ^2))
  = σ ^ (2 * n) * Nat.doubleFactorial (2 * n - 1)
  := by
    -- 1. E[(X - E[X])^(2n)] = ∫ x^(2n) dP(x) with P = N(0, σ^2)
    unfold ProbabilityTheory.centralMoment
    simp_all
    rw [show μ = 0 + μ by ring_nf]
    rw [<-ProbabilityTheory.gaussianReal_map_add_const]
    simp_all
    rw [MeasurableEmbedding.integral_map]
    simp_all
    rotate_left
    sorry
    -- 2. Prove the case σ = 0 and proceed with σ ≠ 0
    by_cases hσ : σ = 0
    .
      by_cases hn : n = 0
        <;> simp_all
    .
      -- 3. ∫ x^(2n) dP(x) = ∫ x^(2n) / √(2πσ²) e^(- x² / 2σ^2) dx
      simp_all [ProbabilityTheory.integral_gaussianReal_eq_integral_smul,
                ProbabilityTheory.gaussianPDFReal_def]
      -- 4. ∫ x^(2n) / √(2πσ²) e^(- x² / 2σ^2) dx = 2 ∫_(0, ∞) x^(2n) / √(2πσ²) e^(- x² / 2σ^2) dx
      conv =>
        lhs
        rhs
        ext x
        rw [show (↑σ)⁻¹ * ((√Real.pi)⁻¹ * (√2)⁻¹) *
  Real.exp (-x ^ 2 / (2 * ↑σ^2)) * x ^ (2 * n) = (fun x => (↑σ)⁻¹ * ((√Real.pi)⁻¹ * (√2)⁻¹) *
              Real.exp (-x ^ 2 / (2 * ↑σ^2)) * x ^ (2 * n)) |x| by sorry]
      rw [integral_comp_abs (f := (fun x => (↑σ)⁻¹ * ((√Real.pi)⁻¹ * (√2)⁻¹) *
              Real.exp (-x ^ 2 / (2 * ↑σ^2)) * x ^ (2 * n)))]
      -- 5. 2 ∫_(0, ∞) x^(2n) / √(2πσ²) e^(- x² / 2σ^2) dx
      --        = 2 ∫_(0, ∞) φ(x)^(2n) / √(2πσ²) e^(- φ(x)² / 2σ^2) |φ'(x)| dx
      -- where φ(x) = σ √(2x) and φ'(x) = σ / (√2 * √x), i.e.,
      -- u sub with y = x^2 / (2σ²) or x = σ √(2y).
      let φ x := σ * Real.sqrt (2 * x)
      let φ' x := σ / (Real.sqrt 2 * Real.sqrt x)
      rw [show Set.Ioi 0 = φ '' Set.Ioi 0 by sorry]
      rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul (f' := φ')]
      rotate_left
      measurability
      sorry
      sorry
      -- 6. 2 ∫_(0, ∞) φ(x)^(2n) / √(2πσ²) e^(- φ(x)² / 2σ^2) |φ'(x)| dx = σ^(2n) 2^n / √π Γ(n + 1/2)
      unfold φ φ'
      simp_all
      simp [abs_div, abs_mul, abs_of_pos]
      sorry
