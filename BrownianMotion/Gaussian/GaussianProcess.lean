/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Gaussian.Fernique
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

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

instance {E ι : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [Subsingleton ι] :
    BorelSpace (ι → E) := by
  refine ⟨le_antisymm pi_le_borel_pi ?_⟩
  obtain h | h := isEmpty_or_nonempty ι
  · exact fun s _ ↦ Subsingleton.set_cases .empty .univ s
  have := @Unique.mk' ι ⟨Classical.choice h⟩ inferInstance
  rw [borel]
  refine MeasurableSpace.generateFrom_le fun s hs ↦ ?_
  simp only [Pi.topologicalSpace, ciInf_unique, isOpen_induced_eq, Set.mem_image,
    Set.mem_setOf_eq] at hs
  simp_rw [MeasurableSpace.measurableSet_iSup, MeasurableSpace.measurableSet_comap]
  refine MeasurableSpace.GenerateMeasurable.basic _ ⟨Classical.choice h, ?_⟩
  obtain ⟨t, ht, rfl⟩ := hs
  exact ⟨t, ht.measurableSet, by rw [Subsingleton.elim (Classical.choice h) default]⟩

lemma IsGaussianProcess.isGaussian_eval (hX : IsGaussianProcess X P) {t : T}
    (hX' : AEMeasurable (X t) P) : IsGaussian (P.map (X t)) := by
  let L : (({t} : Finset T) → E) →L[ℝ] E := ContinuousLinearMap.proj ⟨t, by simp⟩
  have : X t = L ∘ (fun ω ↦ ({t} : Finset T).restrict (X · ω)) := by ext; simp [L]
  rw [this, ← AEMeasurable.map_map_of_aemeasurable]
  · have := hX {t}
    exact isGaussian_map L
  · exact L.continuous.aemeasurable
  rw [aemeasurable_pi_iff]
  simpa

lemma IsGaussianProcess.memLp_eval [SecondCountableTopology E] [CompleteSpace E]
    (hX : IsGaussianProcess X P) {t : T}
    (hX' : AEMeasurable (X t) P) {p : ℝ≥0∞} (hp : p ≠ ∞) : MemLp (X t) p P := by
  rw [← Function.id_comp (X t)]
  apply MemLp.comp_of_map
  · exact hX.isGaussian_eval hX' |>.memLp_id _ p hp
  · exact hX'

end ProbabilityTheory
