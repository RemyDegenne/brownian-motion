import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# General lemmas to be upstreamed to Mathlib
-/

open MeasureTheory

open scoped NNReal ProbabilityTheory

namespace ProbabilityTheory

@[simp]
lemma charFunDual_eq_charFun_toDual_symm {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [InnerProductSpace ℝ E] {mE : MeasurableSpace E} {μ : Measure E} (L : NormedSpace.Dual ℝ E) :
    charFun μ ((InnerProductSpace.toDual ℝ E).symm L) = charFunDual μ L := by
  rw [charFun_eq_charFunDual_toDualMap]
  congr with x
  simp

@[simp]
lemma inner_toDual_symm_eq_self {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (L : NormedSpace.Dual 𝕜 E) :
  inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm L) = L := by ext; simp

lemma eq_gaussianReal_integral_variance {μ : Measure ℝ} {m : ℝ} {v : ℝ≥0}
    (h : μ = gaussianReal m v) : μ = gaussianReal μ[id] Var[id; μ].toNNReal := by
  simp [h]

end ProbabilityTheory

nonrec lemma _root_.ContinuousLinearMap.integral_id_map {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F] [MeasurableSpace E]
    [OpensMeasurableSpace E] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {μ : Measure E} (h : Integrable id μ) (L : E →L[𝕜] F) : (μ.map L)[id] = L μ[id] := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  change ∫ x, L (id x) ∂μ = _
  rw [L.integral_comp_comm h]
