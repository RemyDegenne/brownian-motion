/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.HasLaw
import BrownianMotion.Gaussian.StochasticProcesses
import Mathlib.Probability.Process.FiniteDimensionalLaws

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

lemma IsGaussianProcess.isProbabilityMeasure [hX : IsGaussianProcess X P] :
    IsProbabilityMeasure P :=
  hX.hasGaussianLaw Classical.ofNonempty |>.isProbabilityMeasure

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
    rw [map_restrict_eq_of_forall_ae_eq fun t ↦ (hXY t).symm]
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
    HasGaussianLaw (X t) P := by
  have : X t = (ContinuousLinearMap.proj (R := ℝ) ⟨t, by simp⟩) ∘
    (fun ω ↦ ({t} : Finset T).restrict (X · ω)) := by ext; simp
  rw [this]
  infer_instance

instance IsGaussianProcess.hasGaussianLaw_sub [SecondCountableTopology E] [IsGaussianProcess X P]
    {s t : T} : HasGaussianLaw (X s - X t) P := by
  classical
  have : X s - X t =
      (ContinuousLinearMap.proj (R := ℝ) (ι := ({s, t} : Finset T))
        (φ := fun _ ↦ E) ⟨s, by simp⟩ -
      ContinuousLinearMap.proj (R := ℝ) (ι := ({s, t} : Finset T))
        (φ := fun _ ↦ E) ⟨t, by simp⟩) ∘
    (fun ω ↦ Finset.restrict {s, t} (X · ω)) := by ext; simp
  rw [this]
  infer_instance

instance IsGaussianProcess.hasGaussianLaw_fun_sub [SecondCountableTopology E]
    [IsGaussianProcess X P] {s t : T} : HasGaussianLaw (fun ω ↦ X s ω - X t ω) P :=
  IsGaussianProcess.hasGaussianLaw_sub

instance IsGaussianProcess.hasGaussianLaw_increments [SecondCountableTopology E]
    [IsGaussianProcess X P] {n : ℕ} {t : Fin (n + 1) → T} :
    HasGaussianLaw (fun ω (i : Fin n) ↦ X (t i.succ) ω - X (t i.castSucc) ω) P := by
  classical
  let L : ((Finset.univ.image t) → E) →L[ℝ] Fin n → E :=
    { toFun x i := x ⟨t i.succ, by simp⟩ - x ⟨t i.castSucc, by simp⟩
      map_add' x y := by ext; simp; abel
      map_smul' m x := by ext; simp; module
      cont := by fun_prop }
  have : (fun ω i ↦ X (t i.succ) ω - X (t i.castSucc) ω) =
      L ∘ fun ω ↦ (Finset.univ.image t).restrict (X · ω) := by ext; simp [L]
  rw [this]
  infer_instance

end ProbabilityTheory
