import BrownianMotion.Gaussian.Gaussian
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Probability.Independence.CharacteristicFunction

open MeasureTheory ProbabilityTheory Finset WithLp Complex
open scoped NNReal

namespace ProbabilityTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section charFun

variable [Fintype ι]

lemma HasGaussianLaw.charFun_toLp_pi {X : ι → Ω → ℝ} (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P)
    (ξ : EuclideanSpace ℝ ι) :
    charFun (P.map (fun ω ↦ toLp 2 (X · ω))) ξ =
      exp (∑ i, ξ i * P[X i] * I - ∑ i, ∑ j, (ξ i : ℂ) * ξ j * (cov[X i, X j; P] / 2)) := by
  -- sorry
  have := hX.isProbabilityMeasure
  nth_rw 1 [(hX.toLp_pi 2).isGaussian_map.charFun_eq', covarianceBilin_apply_pi,
    EuclideanSpace.real_inner_eq]
  · simp_rw [ofReal_sum, Finset.sum_mul, ← mul_div_assoc, Finset.sum_div,
      integral_complex_ofReal, ← ofReal_mul]
    congrm exp (∑ i, Complex.ofReal (_ * ?_) * I - _)
    rw [integral_map, eval_integral_piLp]
    · simp
    · simp only [id_eq, PiLp.toLp_apply]
      exact fun i ↦ (hX.eval i).integrable
    · exact (measurable_toLp 2 _).comp_aemeasurable hX.aemeasurable
    · exact aestronglyMeasurable_id
  · exact fun i ↦ (hX.eval i).memLp_two

lemma HasGaussianLaw.charFun_toLp_prodMk {X Y : Ω → ℝ} (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    charFun (P.map (fun ω ↦ toLp 2 (X ω, Y ω))) ξ =
      exp ((ξ.fst * P[X] + ξ.snd * P[Y]) * I -
        (ξ.fst ^ 2 * Var[X; P] +
          2 * ξ.fst * ξ.snd * cov[X, Y; P] + ξ.snd ^ 2 * Var[Y; P]) / 2) := by
  have := hXY.isProbabilityMeasure
  nth_rw 1 [(hXY.toLp_prodMk 2).isGaussian_map.charFun_eq', covarianceBilin_apply_prod]
  · simp only [id_eq, prod_inner_apply, ofLp_fst, RCLike.inner_apply, conj_trivial, mul_comm,
    ofLp_snd, ofReal_add, ofReal_mul, add_div, integral_complex_ofReal, pow_two]
    rw [mul_comm (ξ.fst : ℂ), mul_comm (ξ.snd : ℂ)]
    congrm exp (I * (?_ * _ + ?_ * _) - ?_)
    · rw [integral_map, fst_integral_withLp]
      · simp
      · exact (hXY.toLp_prodMk 2).integrable
      · fun_prop
      · exact aestronglyMeasurable_id
    · rw [integral_map, snd_integral_withLp]
      · simp
      · exact (hXY.toLp_prodMk 2).integrable
      · fun_prop
      · exact aestronglyMeasurable_id
    · ring
  · exact hXY.fst.memLp_two
  · exact hXY.snd.memLp_two

end charFun

variable [Finite ι]

open ContinuousLinearMap in
lemma HasGaussianLaw.iIndepFun_of_cov {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {X : Π i, Ω → (E i)} (h : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h' : ∀ i j, i ≠ j → ∀ (L₁ : StrongDual ℝ (E i)) (L₂ : StrongDual ℝ (E j)),
      cov[L₁ ∘ (X i), L₂ ∘ (X j); P] = 0) :
    iIndepFun X P := by
  exact iIndepFun_of_covariance_strongDual h h'

open ContinuousLinearMap in
lemma HasGaussianLaw.indepFun_of_cov {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [CompleteSpace F] [BorelSpace F] [SecondCountableTopology F]
    {X : Ω → E} {Y : Ω → F} (h : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h' : ∀ (L₁ : StrongDual ℝ E) (L₂ : StrongDual ℝ F), cov[L₁ ∘ X, L₂ ∘ Y; P] = 0) :
    IndepFun X Y P := by
  exact indepFun_of_covariance_strongDual h h'

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.iIndepFun_of_cov' {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {X : Π i, Ω → (E i)} (h : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h' : ∀ i j, i ≠ j → ∀ (x : E i) (y : E j),
      cov[fun ω ↦ ⟪x, X i ω⟫, fun ω ↦ ⟪y, X j ω⟫; P] = 0) :
    iIndepFun X P :=
  iIndepFun_of_covariance_inner h h'

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.indepFun_of_cov' {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [CompleteSpace F] [BorelSpace F] [SecondCountableTopology F]
    {X : Ω → E} {Y : Ω → F} (h : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h' : ∀ x y, cov[fun ω ↦ ⟪x, X ω⟫, fun ω ↦ ⟪y, Y ω⟫; P] = 0) :
    IndepFun X Y P := by
  exact indepFun_of_covariance_inner h h'

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.iIndepFun_of_cov'' {κ : ι → Type*} [∀ i, Finite (κ i)]
    {X : (i : ι) → κ i → Ω → ℝ} (h : HasGaussianLaw (fun ω i j ↦ X i j ω) P)
    (h' : ∀ i j, i ≠ j → ∀ k l, cov[X i k, X j l; P] = 0) :
    iIndepFun (fun i ω j ↦ X i j ω) P := by
  exact iIndepFun_of_covariance_eval h h'

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.indepFun_of_cov'' {κ : Type*} [Finite κ]
    {X : ι → Ω → ℝ} {Y : κ → Ω → ℝ} (h : HasGaussianLaw (fun ω ↦ (fun i ↦ X i ω, fun j ↦ Y j ω)) P)
    (h' : ∀ i j, cov[X i, Y j; P] = 0) :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P := by
  exact indepFun_of_covariance_eval h h'

variable {X Y : Ω → ℝ} {μX μY : ℝ} {vX vY : ℝ≥0}

lemma IndepFun.hasLaw_sub_of_gaussian
    (hX : HasLaw X (gaussianReal μX vX) P) (hY : HasLaw Y (gaussianReal μY vY) P)
    (h1 : IndepFun X (Y - X) P) (h2 : vX ≤ vY) :
    HasLaw (Y - X) (gaussianReal (μY - μX) (vY - vX)) P where
  map_eq := by
    have : IsProbabilityMeasure P := hX.hasGaussianLaw.isProbabilityMeasure
    refine Measure.ext_of_charFun <| funext fun t ↦ ?_
    apply mul_left_cancel₀ (a := charFun (P.map X) t)
    · rw [hX.map_eq, charFun_gaussianReal]
      exact Complex.exp_ne_zero _
    · rw [← Pi.mul_apply, ← h1.charFun_map_add_eq_mul, add_sub_cancel, hY.map_eq, hX.map_eq,
        charFun_gaussianReal, charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add,
        NNReal.coe_sub h2, Complex.ofReal_sub]
      · congr
        field_simp
        push_cast
        ring
      all_goals fun_prop

lemma IndepFun.hasLaw_gaussianReal_of_add
    (hX : HasLaw X (gaussianReal μX vX) P) (hY : HasLaw (X + Y) (gaussianReal μY vY) P)
    (h : IndepFun X Y P) :
    HasLaw Y (gaussianReal (μY - μX) (vY - vX)) P := by
  have h' := h
  rw [show Y = X + Y - X by simp] at h' ⊢
  apply h'.hasLaw_sub_of_gaussian hX hY
  rw [← @Real.toNNReal_coe vY, ← @variance_id_gaussianReal μY vY, ← hY.variance_eq,
    h.variance_add, hX.variance_eq, variance_id_gaussianReal, Real.toNNReal_add,
    Real.toNNReal_coe]
  any_goals simp
  · exact variance_nonneg _ _
  · exact hX.hasGaussianLaw.memLp_two
  · convert hY.hasGaussianLaw.memLp_two.sub hX.hasGaussianLaw.memLp_two
    simp

lemma IndepFun.hasGaussianLaw_of_add_real
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw (X + Y) P) (h : IndepFun X Y P) :
    HasGaussianLaw Y P where
  isGaussian_map := by
    have h1 : HasLaw X (gaussianReal _ _) P := ⟨hX.aemeasurable, hX.map_eq_gaussianReal⟩
    have h2 : HasLaw (X + Y) (gaussianReal _ _) P := ⟨hY.aemeasurable, hY.map_eq_gaussianReal⟩
    have := h.hasLaw_gaussianReal_of_add h1 h2
    exact this.hasGaussianLaw.isGaussian_map

lemma IndepFun.hasGaussianLaw_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {X Y : Ω → E} (hX : HasGaussianLaw X P)
    (hY : HasGaussianLaw Y P) (h : IndepFun X (Y - X) P) :
    HasGaussianLaw (Y - X) P := by
  exact hasGaussianLaw_sub_of_sub hX hY h

end ProbabilityTheory
