import BrownianMotion.Gaussian.Gaussian
import Mathlib.Probability.Independence.CharacteristicFunction

open MeasureTheory ProbabilityTheory Finset

namespace ProbabilityTheory

lemma HasGaussianLaw.iIndepFun_of_covariance_eq_zero {ι Ω : Type*} [Fintype ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → ℝ}
    [h1 : HasGaussianLaw (fun ω ↦ (X · ω)) P] (h2 : ∀ i j : ι, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P := by
  refine iIndepFun_iff_charFun_pi h1.aemeasurable.eval |>.2 fun ξ ↦ ?_
  simp_rw [HasGaussianLaw.charFun_toLp, ← sum_sub_distrib, Complex.exp_sum,
    HasGaussianLaw.charFun_map_real]
  congrm ∏ i, Complex.exp (_ - ?_)
  rw [Fintype.sum_eq_single i]
  · simp [covariance_self, h1.aemeasurable.eval, pow_two, mul_div_assoc]
  · exact fun j hj ↦ by simp [h2 i j hj.symm]

lemma HasGaussianLaw.indepFun_of_covariance_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    [h1 : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] (h2 : cov[X, Y; P] = 0) :
    IndepFun X Y P := by
  refine indepFun_iff_charFun_prod h1.aemeasurable.fst h1.aemeasurable.snd |>.2 fun ξ ↦ ?_
  simp_rw [HasGaussianLaw.charFun_toLp', h1.fst.charFun_map_real,
    h1.snd.charFun_map_real, ← Complex.exp_add, h2, Complex.ofReal_zero, mul_zero,
    WithLp.ofLp_fst, WithLp.ofLp_snd]
  congr
  ring

open ContinuousLinearMap in
lemma iIndepFun.hasGaussianLaw {ι Ω : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Π i, Ω → (E i)}
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] [∀ i, HasGaussianLaw (X i) μ] (hX : iIndepFun X μ) :
    HasGaussianLaw (fun ω ↦ (X · ω)) μ where
  isGaussian_map := by
    classical
    rw [isGaussian_iff_gaussian_charFunDual]
    refine ⟨fun i ↦ ∫ ω, X i ω ∂μ, .diagonalStrongDual (fun i ↦ covarianceBilinDual (μ.map (X i))),
      ContinuousBilinForm.isPosSemidef_diagonalStrongDual
        (fun i ↦ isPosSemidef_covarianceBilinDual), fun L ↦ ?_⟩
    rw [(iIndepFun_iff_charFunDual_pi _).1 hX]
    · simp only [← sum_single_apply E (fun i ↦ ∫ ω, X i ω ∂μ), map_sum, Complex.ofReal_sum,
      sum_mul, ContinuousBilinForm.diagonalStrongDual, LinearMap.mkContinuous₂_apply,
      LinearMap.mk₂_apply,
      sum_div, ← sum_sub_distrib, Complex.exp_sum]
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
