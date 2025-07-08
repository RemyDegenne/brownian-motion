/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.HasLaw
import BrownianMotion.Gaussian.StochasticProcesses

/-!
# Gaussian processes

-/

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T → Ω → E}

section Basic

variable [MeasurableSpace E] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-- A stochastic process is a Gaussian process if all its finite dimensional distributions are
Gaussian. -/
class IsGaussianProcess (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop where
  hasGaussianLaw : ∀ I : Finset T, HasGaussianLaw (fun ω ↦ I.restrict (X · ω)) P

attribute [instance] IsGaussianProcess.hasGaussianLaw

lemma IsGaussianProcess.aemeasurable [hX : IsGaussianProcess X P] (t : T) :
    AEMeasurable (X t) P := by
  by_contra h
  have := (hX.hasGaussianLaw {t}).isGaussian_map
  rw [Measure.map_of_not_aemeasurable] at this
  · exact this.toIsProbabilityMeasure.ne_zero _ rfl
  · rw [aemeasurable_pi_iff]
    push_neg
    exact ⟨⟨t, by simp⟩, h⟩

lemma IsGaussianProcess.modification [IsGaussianProcess X P] (hXY : ∀ t, X t =ᵐ[P] Y t) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    constructor
    rw [finite_distributions_eq fun t ↦ (hXY t).symm]
    infer_instance

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

instance IsGaussianProcess.hasGaussianLaw_eval [IsGaussianProcess X P] {t : T} :
    HasGaussianLaw (X t) P where
  isGaussian_map := by
    have : X t = (ContinuousLinearMap.proj (R := ℝ) ⟨t, by simp⟩) ∘
      (fun ω ↦ ({t} : Finset T).restrict (X · ω)) := by ext; simp
    rw [this]
    infer_instance

instance IsGaussianProcess.hasGaussianLaw_sub [SecondCountableTopology E] [IsGaussianProcess X P]
    {s t : T} : HasGaussianLaw (X s - X t) P where
  isGaussian_map := by
    classical
    have : X s - X t =
        (ContinuousLinearMap.proj (R := ℝ) (ι := ({s, t} : Finset T))
          (φ := fun _ ↦ E) ⟨s, by simp⟩ -
        ContinuousLinearMap.proj (R := ℝ) (ι := ({s, t} : Finset T))
          (φ := fun _ ↦ E) ⟨t, by simp⟩) ∘
      (fun ω ↦ ({s, t} : Finset T).restrict (X · ω)) := by ext; simp
    rw [this]
    infer_instance

end ProbabilityTheory
