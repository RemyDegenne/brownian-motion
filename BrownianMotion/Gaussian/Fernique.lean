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

end ProbabilityTheory
