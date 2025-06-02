/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Gaussian.MultivariateGaussian
import BrownianMotion.Init

/-!
# Gaussian processes

-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}

/-- A stochastic process is a Gaussian process if all its finite dimensional distributions are
Gaussian. -/
def IsGaussianProcess [MeasurableSpace E] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ I : Finset T, IsGaussian ((P.map (fun ω t ↦ X t ω)).map I.restrict)

end ProbabilityTheory
