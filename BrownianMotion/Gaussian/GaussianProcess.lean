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
  ∀ I : Finset T, IsGaussian (P.map (fun ω ↦ I.restrict (X · ω)))

lemma IsGaussianProcess.modification (hX : IsGaussianProcess X P) (hXY : ∀ t, X t =ᵐ[P] Y t) :
    IsGaussianProcess Y P := by
  intro I
  rw [finite_distributions_eq fun t ↦ (hXY t).symm]
  exact hX I

end Basic

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma IsGaussianProcess.isGaussian_eval (hX : IsGaussianProcess X P) (t : T)
    (hX' : AEMeasurable (X t) P) : IsGaussian (P.map (X t)) := by
  have : BorelSpace (({t} : Finset T) → E) := by
    constructor
    apply le_antisymm
    · exact pi_le_borel_pi
    rw [borel]
    apply MeasurableSpace.generateFrom_le
    intro s hs
    rw [Pi.topologicalSpace] at hs
    simp at hs
    rw [isOpen_induced_eq] at hs
    rw [MeasurableSpace.measurableSet_iSup]
    apply MeasurableSpace.GenerateMeasurable.basic
    use ⟨t, by simp⟩
    rw [MeasurableSpace.measurableSet_comap]
    obtain ⟨t, ht, rfl⟩ := hs
    use t, ht.measurableSet
    rfl
  let L : (({t} : Finset T) → E) →L[ℝ] E := ContinuousLinearMap.proj ⟨t, by simp⟩
  have : X t = L ∘ (fun ω ↦ ({t} : Finset T).restrict (X · ω)) := by ext; simp [L]
  rw [this, ← AEMeasurable.map_map_of_aemeasurable]
  · have : BorelSpace (({t} : Finset T) → E) := by
      constructor
      apply le_antisymm
      · exact pi_le_borel_pi
      rw [borel]
      apply MeasurableSpace.generateFrom_le
      intro s hs
      rw [Pi.topologicalSpace] at hs
      simp at hs
      rw [isOpen_induced_eq] at hs
      rw [MeasurableSpace.measurableSet_iSup]
      apply MeasurableSpace.GenerateMeasurable.basic
      use ⟨t, by simp⟩
      rw [MeasurableSpace.measurableSet_comap]
      obtain ⟨t, ht, rfl⟩ := hs
      use t, ht.measurableSet
      rfl
    have := hX {t}
    exact @isGaussian_map _ _ _ _ _ _ _ _ _ _ _ (hX {t}) L
  · exact L.continuous.aemeasurable
  rw [aemeasurable_pi_iff]
  simpa

end ProbabilityTheory
