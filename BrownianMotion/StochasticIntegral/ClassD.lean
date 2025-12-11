/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Martingale
import BrownianMotion.Auxiliary.Adapted
import BrownianMotion.StochasticIntegral.ApproxSeq
import BrownianMotion.StochasticIntegral.Locally
import Mathlib.Probability.Process.HittingTime

/-! # Locally integrable, class D, class DL

-/

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [NormedAddCommGroup E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
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
  let f (t : ι) : {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≤ t} →
      {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≠ ⊤} :=
    fun τ => ⟨τ, τ.2.1, fun ω => ne_of_lt
      (lt_of_le_of_lt (τ.2.2 ω) (WithTop.coe_lt_top t))⟩
  exact ⟨hX.1, fun t => hX.2.comp (f t)⟩

end Defs

section PartialOrder

variable [NormedSpace ℝ E] [CompleteSpace E] [LinearOrder ι] [Nonempty ι] {𝓕 : Filtration ι mΩ}

section RightContinuous

variable [TopologicalSpace ι]

section Order

variable [PartialOrder E] [OrderClosedTopology E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]

lemma _root_.MeasureTheory.Submartingale.classDL (hX1 : Submartingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) (hX3 : 0 ≤ X) :
    ClassDL X 𝓕 P := sorry

lemma _root_.MeasureTheory.Submartingale.classD_iff_uniformIntegrable (hX1 : Submartingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) (hX3 : 0 ≤ X) :
    ClassD X 𝓕 P ↔ UniformIntegrable X 1 P := sorry

end Order

#check Martingale.submartingale_convex_comp
#check MeasureTheory.uniformIntegrable_iff_norm

lemma _root_.MeasureTheory.Martingale.classDL [SecondCountableTopology ι] [MetrizableSpace ι]
  [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] [SigmaFinite P]
  (hX1 : Martingale X 𝓕 P) (hX2 : ∀ ω, RightContinuous (X · ω)) :
    ClassDL X 𝓕 P := by
    constructor
    · exact hX1.1
    · intro t
      refine (uniformIntegrable_iff_norm (le_refl _) ?_).mpr ?_
      · intro τ
        apply StronglyMeasurable.aestronglyMeasurable
        have h := hX1.adapted.progMeasurable_of_rightContinuous hX2
        have h' := stronglyMeasurable_stoppedValue_of_le h τ.2.1 τ.2.2
        exact h'.mono (𝓕.le t)
      have : UniformIntegrable (fun (t_1 : {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≤ ↑t}) ω ↦ ‖stoppedValue X (↑t_1) ω‖) 1 P
        ↔ UniformIntegrable (fun (t_1 : {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≤ ↑t}) ω ↦ stoppedValue (fun t ω_1 ↦ ‖X t ω_1‖) (↑t_1) ω) 1 P
        := by aesop
      apply this.2
      apply (Submartingale.classDL ?_ ?_ ?_).2
      · exact hX1.submartingale_norm
      · intro ω
        specialize hX2 ω
        unfold RightContinuous at *
        intro a
        specialize hX2 a
        apply ContinuousAt.comp_continuousWithinAt _ hX2
        fun_prop
      intro t ω
      positivity

lemma _root_.MeasureTheory.Martingale.classD_iff_uniformIntegrable (hX1 : Martingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) :
    ClassD X 𝓕 P ↔ UniformIntegrable X 1 P := sorry

end RightContinuous

end PartialOrder

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ}

lemma isStable_hasLocallyIntegrableSup [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] :
    IsStable 𝓕 (HasLocallyIntegrableSup (E := E) · 𝓕 P) := by
  sorry

lemma isStable_classD [OrderBot ι] : IsStable 𝓕 (ClassD (E := E) · 𝓕 P) := by
  sorry

lemma isStable_classDL [OrderBot ι] : IsStable 𝓕 (ClassDL (E := E) · 𝓕 P) := by
  sorry

lemma _root_.MeasureTheory.Integrable.classDL [Nonempty ι]
    (hX : ∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖X t ω‖) P) :
    ClassDL X 𝓕 P := by
  sorry

lemma HasLocallyIntegrableSup.locally_classDL [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    (hX1 : HasLocallyIntegrableSup X 𝓕 P) (hX2 : Adapted 𝓕 X) (h𝓕 : 𝓕.IsRightContinuous) :
    Locally (ClassDL · 𝓕 P) 𝓕 X P := by
  sorry

lemma ClassDL.locally_classD [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    (hX : ClassDL X 𝓕 P) :
    Locally (ClassD · 𝓕 P) 𝓕 X P := by
  sorry

lemma locally_classD_of_locally_classDL [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    (hX : Locally (ClassDL · 𝓕 P) 𝓕 X P) (h𝓕 : 𝓕.IsRightContinuous) :
    Locally (ClassD · 𝓕 P) 𝓕 X P := by
  sorry

-- TODO: The assumptions should be refined with those of Début theorem.
lemma isLocalizingSequence_hittingAfter_Ici {ι : Type*} [PartialOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [FirstCountableTopology ι] [InfSet ι] [Bot ι] [CompactIccSpace ι]
    (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι) {X : ι → Ω → ℝ} (hX1 : Adapted 𝓕 X)
    (hX2 : ∀ ω, RightContinuous (X · ω)) (h𝓕 : 𝓕.IsRightContinuous) :
    IsLocalizingSequence 𝓕 (fun n ↦ hittingAfter X (Set.Ici n) ⊥) P := sorry

lemma sup_stoppedProcess_hittingAfter_Ici_le {E : Type*} [NormedAddCommGroup E] [InfSet ι] [Bot ι]
    {X : ι → Ω → E} (t : ι) (K : ℝ) (ω : Ω) :
    ⨆ s ≤ t, ‖stoppedProcess X (hittingAfter (fun t ω ↦ ‖X t ω‖) (Set.Ici K) ⊥) s ω‖ ≤
    K + Set.indicator {ω | hittingAfter (fun t ω ↦ ‖X t ω‖) (Set.Ici K) ⊥ ω ≤ t}
      (fun ω ↦ ‖stoppedValue X (hittingAfter (fun t ω ↦ ‖X t ω‖) (Set.Ici K) ⊥) ω‖) ω := sorry

lemma ClassDL.hasLocallyIntegrableSup [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] [InfSet ι] [CompactIccSpace ι] [OrderBot ι]
    (hX1 : ∀ᵐ ω ∂P, IsCadlag (X · ω)) (hX2 : ClassDL X 𝓕 P)
    (h𝓕 : 𝓕.IsRightContinuous) :
    HasLocallyIntegrableSup X 𝓕 P := by
  sorry

lemma hasLocallyIntegrableSup_of_locally_classDL [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] [InfSet ι] [CompactIccSpace ι] [OrderBot ι]
    (hX1 : ∀ᵐ ω ∂P, IsCadlag (X · ω)) (hX2 : Locally (ClassDL · 𝓕 P) 𝓕 X P)
    (h𝓕 : 𝓕.IsRightContinuous) :
    HasLocallyIntegrableSup X 𝓕 P := by
  sorry

end LinearOrder

end ProbabilityTheory
