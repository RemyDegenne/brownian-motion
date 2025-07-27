/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Covariance bilinear form

-/

open MeasureTheory InnerProductSpace NormedSpace
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

section NormedSpace

variable [NormedSpace ℝ E]

end NormedSpace

end ProbabilityTheory
