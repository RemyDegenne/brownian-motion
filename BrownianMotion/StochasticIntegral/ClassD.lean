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

variable {ι Ω E : Type*} [NormedAddCommGroup E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ι → Ω → E}


/-- A stochastic process has integrable supremum if the function `(t, ω) ↦ sup_{s ≤ t} ‖X s ω‖`
is strongly measurable and if for all `t`, the random variable `ω ↦ sup_{s ≤ t} ‖X s ω‖`
is integrable. -/
def HasIntegrableSup [LinearOrder ι] [MeasurableSpace ι] (X : ι → Ω → E)
    (P : Measure Ω := by volume_tac) : Prop :=
  (StronglyMeasurable (fun (tω : ι × Ω) ↦ ⨆ s ≤ tω.1, ‖X s tω.2‖ₑ)) ∧
     (∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖X s ω‖ₑ) P)

/-- A stochastic process has locally integrable supremum if it satisfies locally the property that
for all `t`, the random variable `ω ↦ sup_{s ≤ t} ‖X s ω‖` is integrable. -/
def HasLocallyIntegrableSup [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [MeasurableSpace ι] (X : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω := by volume_tac) : Prop :=
  Locally (HasIntegrableSup · P) 𝓕 X P

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

variable [NormedSpace ℝ E] [CompleteSpace E] [PartialOrder ι] [Nonempty ι] {𝓕 : Filtration ι mΩ}

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

lemma _root_.MeasureTheory.Martingale.classDL (hX1 : Martingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) :
    ClassDL X 𝓕 P := sorry

lemma _root_.MeasureTheory.Martingale.classD_iff_uniformIntegrable (hX1 : Martingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) :
    ClassD X 𝓕 P ↔ UniformIntegrable X 1 P := sorry

end RightContinuous

end PartialOrder

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ}

lemma isStable_hasIntegrableSup [OrderBot ι] [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] :
    IsStable 𝓕 (HasIntegrableSup (E := E) · P) := by
  intro X hX τ hτ
  let M : ι × Ω → ι × Ω := fun p ↦ ((min ↑p.1 (τ p.2)).untopA, p.2)
  have hM : Measurable M := (WithTop.measurable_coe.comp measurable_fst).min
      (hτ.measurable'.comp measurable_snd) |>.untopA.prodMk measurable_snd
  have key_eq : (fun p : ι × Ω ↦ ⨆ s ≤ p.1, ‖stoppedProcess
          (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ s p.2‖ₑ) =
      {p | ⊥ < τ p.2}.indicator (fun p ↦ ⨆ s ≤ (M p).1, ‖X s (M p).2‖ₑ) := by
    ext ⟨t, ω⟩; simp only [M, stoppedProcess, Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : ⊥ < τ ω <;> simp only [h, ↓reduceIte, enorm_zero, ENNReal.iSup_zero,
      ciSup_const]; apply le_antisymm
    · apply iSup₂_le
      intro s hst
      apply le_iSup₂_of_le (min ↑s (τ ω)).untopA ?_
      · simp only [le_refl]
      · rw [WithTop.le_untopA_iff, WithTop.untopA_eq_untop, WithTop.coe_untop]
        · exact min_le_min (WithTop.coe_le_coe.mpr hst) le_rfl
        · exact ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top s))
        · exact ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top t))
    · apply iSup₂_le
      intro u hu
      apply le_iSup₂_of_le (α := ℝ≥0∞) u ?_
      · rw [min_eq_left]
        · exact le_rfl
        · rw [WithTop.le_untopA_iff] at hu
          · exact le_trans hu (min_le_right _ _)
          · simp only [ne_eq, inf_eq_top_iff, WithTop.coe_ne_top, false_and, not_false_eq_true]
      · rw [WithTop.le_untopA_iff] at hu
        · exact WithTop.coe_le_coe.mp (le_trans hu (min_le_left _ _))
        · simp only [ne_eq, inf_eq_top_iff, WithTop.coe_ne_top, false_and, not_false_eq_true]
  constructor
  · rw [key_eq]
    exact StronglyMeasurable.indicator (hX.1.comp_measurable hM)
      (measurableSet_lt measurable_const (hτ.measurable'.comp measurable_snd))
  · intro t
    constructor
    · rw [show (fun ω ↦ ⨆ s ≤ t, ‖stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ s ω‖ₑ) =
            (fun ω ↦ {p | ⊥ < τ p.2}.indicator (fun p ↦ ⨆ s ≤ (M p).1, ‖X s (M p).2‖ₑ) (t, ω)) by
            ext ω; exact congr_fun key_eq (t, ω)]
      exact (StronglyMeasurable.indicator (hX.1.comp_measurable hM)
        (measurableSet_lt measurable_const (hτ.measurable'.comp measurable_snd))).comp_measurable
        (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable
    · have h_bound := (hX.2 t).hasFiniteIntegral
      rw [hasFiniteIntegral_def] at h_bound ⊢; simp only [enorm_eq_self] at h_bound ⊢
      refine lt_of_le_of_lt (lintegral_mono fun ω ↦ ?_) h_bound
      rw [show (⨆ s ≤ t, ‖stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ s ω‖ₑ) =
            {p | ⊥ < τ p.2}.indicator (fun p ↦ ⨆ s ≤ (M p).1, ‖X s (M p).2‖ₑ) (t, ω) by
            exact congr_fun key_eq (t, ω)]
      simp only [M, Set.indicator_apply, Set.mem_setOf_eq]
      by_cases h : ⊥ < τ ω
      · simp only [h, ↓reduceIte, iSup_le_iff]
        intro i hi
        apply le_iSup₂_of_le (min ↑i (τ ω)).untopA ?_
        · rw [min_eq_left]
          · simp only [WithTop.untopD_coe, le_refl]
          · rw [WithTop.le_untopA_iff] at hi
            · exact le_trans hi (min_le_right _ _)
            · exact ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top t))
        · rw [WithTop.untopA_eq_untop, WithTop.untop_le_iff]
          · rw [WithTop.le_untopA_iff] at hi
            · exact le_trans (min_le_left _ _) (le_trans hi (min_le_left _ _))
            · exact ne_of_lt (lt_of_le_of_lt (min_le_left (↑t) (τ ω)) (WithTop.coe_lt_top t))
          · exact ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top _))
      · simp only [h, ↓reduceIte, zero_le]


lemma isStable_hasLocallyIntegrableSup [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι]:
    IsStable 𝓕 (HasLocallyIntegrableSup (E := E) · 𝓕 P) :=
  IsStable.isStable_locally isStable_hasIntegrableSup

lemma isStable_classD [OrderBot ι] : IsStable 𝓕 (ClassD (E := E) · 𝓕 P) := by
  sorry

lemma isStable_classDL [OrderBot ι] : IsStable 𝓕 (ClassDL (E := E) · 𝓕 P) := by
  sorry

lemma _root_.MeasureTheory.Integrable.classDL [Nonempty ι]
    (hX : ∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖X t ω‖ₑ) P) :
    ClassDL X 𝓕 P := by
  sorry

lemma HasLocallyIntegrableSup.locally_classDL [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [MeasurableSpace ι]
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
    [FirstCountableTopology ι] [InfSet ι] [CompactIccSpace ι] [OrderBot ι] [MeasurableSpace ι]
    (hX1 : ∀ ω, IsCadlag (X · ω)) (hX2 : ClassDL X 𝓕 P)
    (h𝓕 : 𝓕.IsRightContinuous) :
    HasLocallyIntegrableSup X 𝓕 P := by
  sorry

end LinearOrder

section ConditionallyCompleteLinearOrderBot


variable [ConditionallyCompleteLinearOrderBot ι] {𝓕 : Filtration ι mΩ}
  [Filtration.HasUsualConditions 𝓕 P] [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι]
    [SecondCountableTopology ι] [DenselyOrdered ι] [NoMaxOrder ι] [BorelSpace ι]
    [IsFiniteMeasure P] [CompleteSpace E] [NormedSpace ℝ E]

lemma hasLocallyIntegrableSup_of_locally_classDL (hX1 : ∀ᵐ (ω : Ω) ∂P, IsCadlag (X · ω))
    (hX2 : Locally (ClassDL · 𝓕 P) 𝓕 X P) (h𝓕 : 𝓕.IsRightContinuous) :
    HasLocallyIntegrableSup X 𝓕 P :=
  locally_induction h𝓕  (fun _ ⟨hDL, hCad⟩ ↦ ClassDL.hasLocallyIntegrableSup hCad hDL h𝓕)
    isStable_hasIntegrableSup
    ((locally_and isStable_classDL isStable_isCadlag).mpr ⟨hX2, locally_isCadlag_iff.mpr hX1⟩)

end ConditionallyCompleteLinearOrderBot

end ProbabilityTheory
