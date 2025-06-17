import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open scoped NNReal

namespace ProbabilityTheory

lemma centralMoment_two_mul_gaussianReal (μ : ℝ) (σ : ℝ≥0) (n : ℕ) :
  centralMoment id (2 * n) (gaussianReal μ (σ^2))
  = σ ^ (2 * n) * Nat.doubleFactorial (2 * n - 1) := by
    -- 1. Prove the case n = 0 and proceed with n ≠ 0
    by_cases hn : n = 0
    · subst n
      unfold centralMoment
      simp
    -- 2. Prove the case σ = 0 and proceed with σ ≠ 0
    by_cases hσ : σ = 0
    · subst σ
      unfold centralMoment
      simp_all
    let φ x := σ * Real.sqrt (2 * x) -- used for u sub later
    calc centralMoment id (2 * n) (gaussianReal μ (σ^2))
      -- 3. E_{X ∼ N(μ, σ²)}[(X - E[X])^(2n)] = ∫ x^(2n) dP(x) with P = N(0, σ^2)
      _ = ∫ x, x^(2 * n) ∂gaussianReal 0 (σ^2) := by
        unfold centralMoment
        simp_all only [id_eq, integral_id_gaussianReal,
                        Pi.pow_apply, Pi.sub_apply]
        rw [show μ = 0 + μ by ring_nf,
            ←gaussianReal_map_add_const,
            MeasurableEmbedding.integral_map]
        · simp
        · apply MeasurableEmbedding.of_measurable_inverse (g := fun x => x - μ)
            <;> try fun_prop
          · rw [Function.Surjective.range_eq (by apply add_right_surjective)]
            measurability
          simp [Function.LeftInverse]
      -- 4. ... = ∫ x^(2n) / √(2πσ²) e^(- x² / 2σ^2) dx
      _ = ∫ x, x^(2 * n) / (Real.sqrt (2 * Real.pi * σ ^ 2))
                * Real.exp (-x ^ 2 / (2 * σ ^ 2)) := by
        simp_all [integral_gaussianReal_eq_integral_smul,
                  gaussianPDFReal_def]
        ring_nf
    -- 5. ... = 2 ∫_(0, ∞) x^(2n) / √(2πσ²) e^(- x² / 2σ^2) dx
      _ = 2 * ∫ x in Set.Ioi 0, x^(2 * n) / (Real.sqrt (2 * Real.pi * σ ^ 2))
                                * Real.exp (-x ^ 2 / (2 * σ ^ 2)) := by
        conv =>
          lhs
          rhs
          ext x
          rw [show x ^ (2 * n) / √(2 * Real.pi * ↑σ ^ 2) * Real.exp (-x ^ 2
              / (2 * ↑σ ^ 2)) = (fun u => u ^ (2 * n) / √(2 * Real.pi * ↑σ ^ 2)
              * Real.exp (-u ^ 2 / (2 * ↑σ ^ 2))) |x| by
                simp only [NNReal.zero_le_coe, pow_nonneg,
                                Real.sqrt_mul', Nat.ofNat_nonneg, Real.sqrt_mul,
                                Real.sqrt_sq, sq_abs, mul_eq_mul_right_iff,
                                Real.exp_ne_zero, or_false]
                rw [pow_mul, ←sq_abs]
                ring_nf]
        rw [integral_comp_abs (f := (fun u => u ^ (2 * n) / √(2 * Real.pi *
                              ↑σ ^ 2) * Real.exp (-u ^ 2 / (2 * ↑σ ^ 2))))]
    -- 6. ... = 2 ∫_(0, ∞) φ(x)^(2n) / √(2πσ²) e^(- φ(x)² / 2σ^2) |φ'(x)| dx
    -- where φ(x) = σ √(2x) and φ'(x) = σ / (√2 * √x), i.e.,
    -- u sub with y = x^2 / (2σ²) or x = σ √(2y).
      _ = 2 * ∫ x in Set.Ioi 0,
          φ x ^ (2 * n) / (Real.sqrt (2 * Real.pi * σ ^ 2))
            * Real.exp (-φ x ^ 2 / (2 * σ ^ 2)) * |deriv φ x| := by
        conv =>
          lhs
          rw [show Set.Ioi 0 = φ '' Set.Ioi 0 by
            subst φ
            apply Set.eq_of_subset_of_subset
              <;> rw [Set.subset_def]
            · intros x hx
              rw [Set.mem_Ioi] at hx
              rw [Set.mem_image]
              exists x^2 / (2 * σ ^ 2)
              split_ands
              · rw [Set.mem_Ioi]
                positivity
              · field_simp
                group
            · intros x hx
              rw [Set.mem_image] at hx
              rw [Set.mem_Ioi]
              rcases hx with ⟨y, ⟨hy, hxy⟩⟩
              subst x
              rw [Set.mem_Ioi] at hy
              positivity]
        rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul (f' := deriv φ)
                                                                    (by measurability)]
        · congr
          funext x
          simp only [NNReal.zero_le_coe, pow_nonneg, Real.sqrt_mul',
                      Nat.ofNat_nonneg, Real.sqrt_mul, Real.sqrt_sq, smul_eq_mul]
          group
        · intros x hx
          apply HasDerivAt.hasDerivWithinAt
          apply DifferentiableAt.hasDerivAt
          subst φ
          simp_all only [Set.mem_Ioi]
          fun_prop (disch:=(apply ne_of_gt; positivity))
        · subst φ
          rw [Set.InjOn.eq_1]
          intros x1 hx1 x2 hx2 hx1x2
          replace hx1x2 := mul_left_cancel₀ (a := (σ: ℝ)) (by positivity) hx1x2
          rw [Set.mem_Ioi] at *
          rw [Real.sqrt_inj (by positivity) (by positivity)] at hx1x2
          simp_all
      -- 7. ... = σ^(2n) 2^n / √π Γ(n + 1/2)
      _ = σ^(2 * n) * 2^n / √ Real.pi * Real.Gamma (n + 1/2) := by
        rw [Real.Gamma_eq_integral (by positivity)]
        simp only [←MeasureTheory.integral_mul_const, ←MeasureTheory.integral_const_mul]
        apply MeasureTheory.setIntegral_congr_fun (by measurability)
        intros x hx
        subst φ
        simp_all only [Set.mem_Ioi, Nat.ofNat_nonneg, Real.sqrt_mul,
                        NNReal.zero_le_coe, pow_nonneg, Real.sqrt_mul', Real.sqrt_sq,
                        differentiableAt_const, deriv_const_mul_field', one_div]
        rw [show deriv Real.sqrt x = 1 / (2 * Real.sqrt x) by
          have hd := deriv_sqrt (f := id) (x := x) (by fun_prop) (by positivity)
          simp at hd
          rw [hd]
          simp]
        simp
        rw [show -(↑σ * (√2 * √x)) ^ 2 / (2 * ↑σ ^ 2) = - x by (ring_nf; field_simp; group) ]
        ring_nf
        field_simp
        group
        simp only [Int.reduceNeg, zpow_neg, zpow_one, one_div, abs_mul,
                    NNReal.abs_eq, zpow_natCast]
        ring_nf
        field_simp
        group
        rw [←Set.InjOn.eq_iff (f := Real.log) (s := Set.Ioi 0) Real.log_injOn_pos]
          <;> try { rw [Set.mem_Ioi]; positivity }
        repeat rw [Real.log_mul (by apply ne_of_gt; positivity)
                    (by apply ne_of_gt; positivity)]
        simp [Real.log_mul (by apply ne_of_gt; positivity)
                (by apply ne_of_gt; positivity)]
        ring_nf
        rw [←sub_eq_zero]
        ring_nf
        repeat rw [Real.log_sqrt (by positivity)]
        repeat rw [Real.log_rpow (by positivity)]
        ring_nf
      -- 8. ... = σ^(2n) (2n - 1)!!
      _ = σ ^ (2 * n) * Nat.doubleFactorial (2 * n - 1) := by
        clear hn
        rw [Real.Gamma_nat_add_half]
        rw [←sub_eq_zero]
        ring_nf
        field_simp

end ProbabilityTheory
