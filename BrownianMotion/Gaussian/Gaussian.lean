module

public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

@[expose] public section

/-!
# Facts about Gaussian characteristic function
-/

open Complex MeasureTheory WithLp NormedSpace

open scoped Matrix NNReal Real InnerProductSpace ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

lemma HasGaussianLaw.map_eq_gaussianReal {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (h : HasGaussianLaw X P) :
    P.map X = gaussianReal P[X] Var[X; P].toNNReal := by
  rw [IsGaussian.eq_gaussianReal (.map _ _), integral_map, variance_map]
  · rfl
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · exact h.isGaussian_map

set_option backward.isDefEq.respectTransparency false in
lemma HasGaussianLaw.charFun_map_real {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (h : HasGaussianLaw X P) (t : ℝ) :
    charFun (P.map X) t = cexp (t * P[X] * I - t ^ 2 * Var[X; P] / 2) := by
  rw [h.map_eq_gaussianReal, IsGaussian.charFun_eq', covarianceBilin_real_self]
  simp [variance_nonneg, integral_complex_ofReal, mul_comm]

end ProbabilityTheory
