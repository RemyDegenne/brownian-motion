/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.HasLaw
import Mathlib.Probability.Distributions.Gaussian.Fernique


/-!
# Gaussian distributions in Banach spaces: Fernique's theorem
-/

open MeasureTheory Real NormedSpace
open scoped ENNReal

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopology E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsGaussian μ]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → E}

/-- A Gaussian random variable has moments of all orders. -/
lemma HasGaussianLaw.memLp [hX : HasGaussianLaw X P] {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp X p P := by
  rw [← Function.id_comp X, ← memLp_map_measure_iff]
  · exact IsGaussian.memLp_id _ p hp
  · exact aestronglyMeasurable_id
  · exact hX.aemeasurable

lemma HasGaussianLaw.memLp_two [HasGaussianLaw X P] :
    MemLp X 2 P := HasGaussianLaw.memLp (by norm_num)

lemma HasGaussianLaw.integrable [HasGaussianLaw X P] :
    Integrable X P := memLp_one_iff_integrable.1 <| HasGaussianLaw.memLp (by norm_num)

end ProbabilityTheory
