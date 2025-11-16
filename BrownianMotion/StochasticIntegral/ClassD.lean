/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Martingale
import BrownianMotion.StochasticIntegral.ApproxSeq
import BrownianMotion.StochasticIntegral.Locally
import Mathlib.Probability.Process.HittingTime

/-! # Locally integrable, class D, class DL

-/

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ι → Ω → E}

/-- A stochastic process has locally integrable supremum if it satisfies locally the property that
for all `t`, the random variable `ω ↦ sup_{s ≤ t} ‖X s ω‖` is integrable. -/
def HasLocallyIntegrableSup [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    (X : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω := by volume_tac) : Prop :=
  Locally (fun Y ↦ ∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖Y s ω‖) P) 𝓕 X P

section Defs

variable [Preorder ι] [Nonempty ι]

/-- A stochastic process $(X_t)$ is of class D (or in the Doob-Meyer class) if it is adapted
and the set $\{X_\tau \mid \tau \text{ is a finite stopping time}\}$ is uniformly integrable. -/
structure ClassD (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    Prop where
  adapted : Adapted 𝓕 X
  uniformIntegrable : UniformIntegrable
    (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}) ↦ stoppedValue X τ.1) 1 P

/-- A stochastic process $(X_t)$ is of class DL if it is adapted and for all $t$, the set
$\{X_\tau \mid \tau \text{ is a stopping time with } \tau \le t\}$ is uniformly integrable. -/
structure ClassDL (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    Prop where
  adapted : Adapted 𝓕 X
  uniformIntegrable (t : ι) : UniformIntegrable
    (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ t}) ↦ stoppedValue X τ.1) 1 P

lemma ClassD.classDL {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} (hX : ClassD X 𝓕 P) :
    ClassDL X 𝓕 P := by
  sorry

end Defs

section PartialOrder

variable [PartialOrder ι] [Nonempty ι] {𝓕 : Filtration ι mΩ}

section RightContinuous

variable [TopologicalSpace ι]

section Order

variable [PartialOrder E] [OrderClosedTopology E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]

lemma _root_.MeasureTheory.Submartingale.classDL (hX1 : Submartingale X 𝓕 P)
    (hX2 : RightContinuous X) (hX3 : 0 ≤ X) :
    ClassDL X 𝓕 P := sorry

lemma _root_.MeasureTheory.Submartingale.classD_iff_uniformIntegrable (hX1 : Submartingale X 𝓕 P)
    (hX2 : RightContinuous X) (hX3 : 0 ≤ X) :
    ClassD X 𝓕 P ↔ UniformIntegrable X 1 P := sorry

end Order

lemma _root_.MeasureTheory.Martingale.classDL (hX1 : Martingale X 𝓕 P) (hX2 : RightContinuous X) :
    ClassDL X 𝓕 P := sorry

lemma _root_.MeasureTheory.Martingale.classD_iff_uniformIntegrable (hX1 : Martingale X 𝓕 P)
    (hX2 : RightContinuous X) :
    ClassD X 𝓕 P ↔ UniformIntegrable X 1 P := sorry

end RightContinuous

end PartialOrder

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ}

lemma isStable_classD [OrderBot ι] : IsStable 𝓕 (ClassD (E := E) · 𝓕 P) := by
  sorry

lemma isStable_classDL [OrderBot ι] : IsStable 𝓕 (ClassDL (E := E) · 𝓕 P) := by
  sorry

lemma Integrable.classDL [Nonempty ι] (hX : ∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖X t ω‖) P) :
    (ClassDL X 𝓕 P) := by
  sorry

lemma HasLocallyIntegrableSup.locally_classDL [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    (hX1 : HasLocallyIntegrableSup X 𝓕 P) (hX2 : Adapted 𝓕 X) :
    Locally (ClassDL · 𝓕 P) 𝓕 X P := by
  sorry

lemma ClassDL.locally_classD [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    (hX : ClassDL X 𝓕 P) :
    Locally (ClassD · 𝓕 P) 𝓕 X P := by
  sorry

lemma locally_classD_of_locally_classDL [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    (hX : Locally (ClassDL · 𝓕 P) 𝓕 X P) :
    Locally (ClassD · 𝓕 P) 𝓕 X P := by
  sorry

-- TODO: The assumptions should be refined with those of Début theorem.
lemma isLocalizingSequence_hittingAfter_Ici {ι : Type*} [PartialOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [InfSet ι] [Bot ι] (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι)
    {X : ι → Ω → ℝ} (hX1 : Adapted 𝓕 X) (hX2 : RightContinuous X) (h𝓕 : 𝓕.IsRightContinuous) :
    IsLocalizingSequence 𝓕 (fun n ↦ hittingAfter X (Set.Ici n) ⊥) P := sorry

-- TODO: The assumptions should be refined with those of Début theorem.
lemma sup_stoppedProcess_hittingAfter_Ici_le {ι : Type*} [LinearOrder ι] [InfSet ι] [Bot ι]
    {X : ι → Ω → ℝ} (t : ι) (K : ℝ) (ω : Ω) :
    ⨆ s ≤ t, |stoppedProcess X (hittingAfter X (Set.Ici K) ⊥) s ω| ≤
    K + Set.indicator {ω | hittingAfter X (Set.Ici K) ⊥ ω ≤ t}
      (fun ω ↦ |stoppedValue X (hittingAfter X (Set.Ici K) ⊥) ω|) ω := sorry

lemma ClassD.HasLocallyIntegrableSup [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    (hX1 : RightContinuous X) (hX2 : ClassD X 𝓕 P) :
    HasLocallyIntegrableSup X 𝓕 P := by
  sorry

lemma hasLocallyIntegrableSup_of_locally_classD [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    (hX1 : RightContinuous X) (hX2 : Locally (ClassD · 𝓕 P) 𝓕 X P) :
    HasLocallyIntegrableSup X 𝓕 P := by
  sorry

end LinearOrder

end ProbabilityTheory
