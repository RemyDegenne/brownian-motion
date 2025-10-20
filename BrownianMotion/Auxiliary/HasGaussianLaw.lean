import BrownianMotion.Gaussian.Gaussian
import Mathlib.Probability.Independence.CharacteristicFunction

open MeasureTheory ProbabilityTheory Finset WithLp Complex

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section charFun

lemma HasGaussianLaw.charFun_toLp_pi {X : ι → Ω → ℝ} [hX : HasGaussianLaw (fun ω ↦ (X · ω)) P]
    (ξ : EuclideanSpace ℝ ι) :
    charFun (P.map (fun ω ↦ toLp 2 (X · ω))) ξ =
      exp (∑ i, ξ i * P[X i] * I - ∑ i, ∑ j, (ξ i : ℂ) * ξ j * (cov[X i, X j; P] / 2)) := by
  have := hX.isProbabilityMeasure
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

lemma HasGaussianLaw.charFun_toLp_prodMk {X Y : Ω → ℝ} [hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P]
    (ξ : WithLp 2 (ℝ × ℝ)) :
    charFun (P.map (fun ω ↦ toLp 2 (X ω, Y ω))) ξ =
      exp ((ξ.1 * P[X] + ξ.2 * P[Y]) * I -
        (ξ.1 ^ 2 * Var[X; P] + 2 * ξ.1 * ξ.2 * cov[X, Y; P] + ξ.2 ^ 2 * Var[Y; P]) / 2) := by
  have := hXY.isProbabilityMeasure
  nth_rw 1 [IsGaussian.charFun_eq, covInnerBilin_apply_prod]
  · simp only [id_eq, prod_inner_apply, ofLp_fst, RCLike.inner_apply, conj_trivial, ofLp_snd,
      ofReal_add, ofReal_mul, add_mul, add_div, integral_complex_ofReal, pow_two, mul_comm]
    congrm exp (I * (_ * ?_ + _ * ?_) - ?_)
    · rw [integral_map, fst_integral_withLp]
      · simp
      · exact HasGaussianLaw.integrable
      · fun_prop
      · exact aestronglyMeasurable_id
    · rw [integral_map, snd_integral_withLp]
      · simp
      · exact HasGaussianLaw.integrable
      · fun_prop
      · exact aestronglyMeasurable_id
    · ring
  · exact hXY.fst.memLp_two
  · exact hXY.snd.memLp_two

end charFun

lemma HasGaussianLaw.iIndepFun_of_covariance_eq_zero {X : ι → Ω → ℝ}
    [h1 : HasGaussianLaw (fun ω ↦ (X · ω)) P] (h2 : ∀ i j : ι, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P := by
  have := h1.isProbabilityMeasure
  refine iIndepFun_iff_charFun_pi h1.aemeasurable.eval |>.2 fun ξ ↦ ?_
  simp_rw [HasGaussianLaw.charFun_toLp_pi, ← sum_sub_distrib, Complex.exp_sum,
    HasGaussianLaw.charFun_map_real]
  congrm ∏ i, Complex.exp (_ - ?_)
  rw [Fintype.sum_eq_single i]
  · simp [covariance_self, h1.aemeasurable.eval, pow_two, mul_div_assoc]
  · exact fun j hj ↦ by simp [h2 i j hj.symm]

lemma HasGaussianLaw.indepFun_of_covariance_eq_zero {X Y : Ω → ℝ}
    [h1 : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] (h2 : cov[X, Y; P] = 0) :
    IndepFun X Y P := by
  have := h1.isProbabilityMeasure
  refine indepFun_iff_charFun_prod h1.aemeasurable.fst h1.aemeasurable.snd |>.2 fun ξ ↦ ?_
  simp_rw [HasGaussianLaw.charFun_toLp_prodMk, h1.fst.charFun_map_real,
    h1.snd.charFun_map_real, ← Complex.exp_add, h2, Complex.ofReal_zero, mul_zero,
    WithLp.ofLp_fst, WithLp.ofLp_snd]
  congr
  ring

open ContinuousLinearMap in
lemma iIndepFun.hasGaussianLaw {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {X : Π i, Ω → (E i)} [∀ i, HasGaussianLaw (X i) P] (hX : iIndepFun X P) :
    HasGaussianLaw (fun ω ↦ (X · ω)) P where
  isGaussian_map := by
    have := hX.isProbabilityMeasure
    obtain hι | hι := isEmpty_or_nonempty ι
    · have : P.map (fun ω ↦ fun x ↦ X x ω) = .dirac hι.elim := by
        ext s -
        apply Subsingleton.set_cases (p := fun s ↦ Measure.map _ _ s = _)
        · simp
        simp only [measure_univ]
        exact @measure_univ _ _ _ (Measure.isProbabilityMeasure_map (by fun_prop))
      rw [this]
      infer_instance
    classical
    rw [isGaussian_iff_gaussian_charFunDual]
    refine ⟨fun i ↦ ∫ ω, X i ω ∂P, .diagonalStrongDual (fun i ↦ covarianceBilinDual (P.map (X i))),
      ContinuousBilinForm.isPosSemidef_diagonalStrongDual
        (fun i ↦ isPosSemidef_covarianceBilinDual), fun L ↦ ?_⟩
    rw [(iIndepFun_iff_charFunDual_pi _).1 hX]
    · simp only [← sum_single_apply E (fun i ↦ ∫ ω, X i ω ∂P), map_sum, ofReal_sum, sum_mul,
      ContinuousBilinForm.diagonalStrongDual_apply, sum_div, ← sum_sub_distrib, exp_sum]
      congr with i
      rw [IsGaussian.charFunDual_eq, integral_complex_ofReal,
        ContinuousLinearMap.integral_comp_id_comm, covarianceBilinDual_self_eq_variance,
        integral_map]
      · simp
      · exact HasGaussianLaw.aemeasurable
      · exact aestronglyMeasurable_id
      · exact IsGaussian.memLp_two_id
      · exact IsGaussian.integrable_id
    · exact fun i ↦ HasGaussianLaw.aemeasurable

end ProbabilityTheory
