/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Gaussian.MultivariateGaussian
import BrownianMotion.Gaussian.StochasticProcesses
import BrownianMotion.Init

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
  ∀ I : Finset T, IsGaussian ((P.map (fun ω t ↦ X t ω)).map I.restrict)

lemma IsGaussianProcess.aemeasurable (hX : IsGaussianProcess X P) :
    AEMeasurable (fun ω t ↦ X t ω) P := by
  by_contra h
  by_cases hT : IsEmpty T
  · have : (fun ω t ↦ X t ω) = fun ω ↦ hT.elim := by ext ω t; exact hT.elim t
    rw [this] at h
    exact h aemeasurable_const
  let t := Classical.choice (not_isEmpty_iff.1 hT)
  have := hX {t}
  rw [Measure.map_of_not_aemeasurable h, Measure.map_zero] at this
  have := this.isProbabilityMeasure.ne_zero
  contradiction

lemma IsGaussianProcess.modification (hX : IsGaussianProcess X P)
    (hY : AEMeasurable (fun ω t ↦ Y t ω) P) (hXY : ∀ t, X t =ᵐ[P] Y t) :
    IsGaussianProcess Y P := by
  intro I
  convert hX I using 1
  rw [AEMeasurable.map_map_of_aemeasurable, AEMeasurable.map_map_of_aemeasurable]
  · exact finite_distributions_eq fun t ↦ (hXY t).symm
  any_goals fun_prop
  · exact hX.aemeasurable
  · exact hY

end Basic

end ProbabilityTheory
