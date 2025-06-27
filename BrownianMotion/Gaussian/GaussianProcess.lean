/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Gaussian.StochasticProcesses
import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Gaussian processes

-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : T → Ω → E}

section Basic

variable [MeasurableSpace E] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-- A stochastic process is a Gaussian process if all its finite dimensional distributions are
Gaussian. -/
def IsGaussianProcess (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ I : Finset T, IsGaussian (P.map (fun ω ↦ I.restrict (X · ω)))

lemma IsGaussianProcess.modification (hX : IsGaussianProcess X P) (hXY : ∀ t, X t =ᵐ[P] Y t) :
    IsGaussianProcess Y P := by
  intro I
  rw [finite_distributions_eq fun t ↦ (hXY t).symm]
  exact hX I

end Basic

end ProbabilityTheory
