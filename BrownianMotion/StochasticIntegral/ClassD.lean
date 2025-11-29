/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Martingale
import BrownianMotion.StochasticIntegral.ApproxSeq
import BrownianMotion.StochasticIntegral.Locally
import BrownianMotion.Auxiliary.Adapted
import BrownianMotion.StochasticIntegral.OptionalSampling
import Mathlib.Probability.Process.HittingTime

/-! # Locally integrable, class D, class DL

-/

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [NormedAddCommGroup E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ι → Ω → E}

/-- The condition that the running supremum process `(t, ω) ↦ sup_{s ≤ t} ‖X s ω‖` is strongly
measurable as a function on the product. -/
def HasStronglyMeasurableSupProcess [LinearOrder ι] [MeasurableSpace ι] (X : ι → Ω → E) : Prop :=
  (StronglyMeasurable (fun (tω : ι × Ω) ↦ ⨆ s ≤ tω.1, ‖X s tω.2‖ₑ))

/-- A stochastic process has integrable supremum if the function `(t, ω) ↦ sup_{s ≤ t} ‖X s ω‖`
is strongly measurable and if for all `t`, the random variable `ω ↦ sup_{s ≤ t} ‖X s ω‖`
is integrable. -/
def HasIntegrableSup [LinearOrder ι] [MeasurableSpace ι] (X : ι → Ω → E)
    (P : Measure Ω := by volume_tac) : Prop :=
  (HasStronglyMeasurableSupProcess (mΩ:= mΩ) X) ∧
     (∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖X s ω‖ₑ) P)

/-- A stochastic process has locally integrable supremum if it satisfies locally the property that
for all `t`, the random variable `ω ↦ sup_{s ≤ t} ‖X s ω‖` is integrable. -/
def HasLocallyIntegrableSup [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [MeasurableSpace ι] (X : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω := by volume_tac) : Prop :=
  Locally (HasIntegrableSup · P) 𝓕 X P

section Defs

variable [Preorder ι] [Nonempty ι] [MeasurableSpace ι]

/-- A stochastic process $(X_t)$ is of class D (or in the Doob-Meyer class) if it is adapted
and the set $\{X_\tau \mid \tau \text{ is a finite stopping time}\}$ is uniformly integrable. -/
structure ClassD (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    Prop where
  progMeasurable : ProgMeasurable 𝓕 X
  uniformIntegrable : UniformIntegrable
    (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}) ↦ stoppedValue X τ.1) 1 P

/-- A stochastic process $(X_t)$ is of class DL if it is adapted and for all $t$, the set
$\{X_\tau \mid \tau \text{ is a stopping time with } \tau \le t\}$ is uniformly integrable. -/
structure ClassDL (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    Prop where
  progMeasurable : ProgMeasurable 𝓕 X
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

variable [NormedSpace ℝ E] [CompleteSpace E] [LinearOrder ι] {𝓕 : Filtration ι mΩ}

section RightContinuous

variable [TopologicalSpace ι] [OrderTopology ι] [OrderBot ι] [MeasurableSpace ι]
  [SecondCountableTopology ι] [BorelSpace ι] [MetrizableSpace ι]

section Order

variable [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [IsFiniteMeasure P]

lemma _root_.MeasureTheory.Submartingale.classDL (hX1 : Submartingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) (hX3 : 0 ≤ X) :
    ClassDL X 𝓕 P := by
  refine ⟨Adapted.progMeasurable_of_rightContinuous hX1.1 hX2, fun t => ?_⟩
  have := (hX1.2.2 t).uniformIntegrable_condExp' (fun T :
    {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≤ t} => IsStoppingTime.measurableSpace_le T.2.1)
  refine uniformIntegrable_of_dominated le_rfl this (fun T => ?_) (fun T => ⟨T, ?_⟩)
  · exact ((stronglyMeasurable_stoppedValue_of_le (Adapted.progMeasurable_of_rightContinuous
      hX1.1 hX2) T.2.1 T.2.2).mono (𝓕.le' t)).aestronglyMeasurable
  · have : stoppedValue X T.1 ≤ᵐ[P] P[stoppedValue X (fun ω => t)|T.2.1.measurableSpace] := by
      suffices lem : stoppedValue X ((fun ω => t) ⊓ T.1) ≤ᵐ[P]
        P[stoppedValue X (fun ω => t)|T.2.1.measurableSpace] from by
        have : T.1 ⊓ (fun ω => t) = T.1 := by simpa [inf_eq_left] using T.2.2
        simpa [inf_comm, this] using lem
      exact hX1.stoppedValue_min_ae_le_condExp 𝓕 hX2
        (Eventually.of_forall (fun ω => le_rfl)) T.2.1 (isStoppingTime_const 𝓕 t)
    simp only [stoppedValue_const] at this
    filter_upwards [this] with ω hω
    have p1 : 0 ≤ stoppedValue X T.1 ω := by simpa [stoppedValue] using (hX3 (T.1 ω).untopA ω)
    have p2 := abs_of_nonneg (le_trans p1 hω)
    rw [← abs_of_nonneg p1, ← p2] at hω
    exact norm_le_norm_of_abs_le_abs hω

lemma _root_.MeasureTheory.Submartingale.classD_iff_uniformIntegrable
    [IsFiniteMeasure P] (hX1 : Submartingale X 𝓕 P)
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

lemma isStable_hasStronglyMeasurableSupProcess [OrderBot ι] [TopologicalSpace ι]
    [SecondCountableTopology ι] [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] :
    IsStable 𝓕 (HasStronglyMeasurableSupProcess (E := E) (mΩ := mΩ) · ) := by
  intro X hX τ hτ
  unfold HasStronglyMeasurableSupProcess at hX ⊢
  let M : ι × Ω → ι × Ω := fun p ↦ ((min ↑p.1 (τ p.2)).untopA, p.2)
  have hM : Measurable M := (WithTop.measurable_coe.comp measurable_fst).min
      (hτ.measurable'.comp measurable_snd) |>.untopA.prodMk measurable_snd
  have key_eq : (fun p : ι × Ω ↦ ⨆ s ≤ p.1, ‖stoppedProcess
          (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ s p.2‖ₑ) =
      {p | ⊥ < τ p.2}.indicator (fun p ↦ ⨆ s ≤ (M p).1, ‖X s (M p).2‖ₑ) := by
    ext ⟨t, ω⟩; simp only [M, stoppedProcess, Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs with h
    · apply le_antisymm
      · apply iSup₂_le
        intro s hst
        apply le_iSup₂_of_le (min ↑s (τ ω)).untopA ?_
        · simp only [le_refl]
        · rw [WithTop.le_untopA_iff, WithTop.untopA_eq_untop, WithTop.coe_untop]
          · exact min_le_min (WithTop.coe_le_coe.mpr hst) le_rfl
          all_goals simp
      · apply iSup₂_le
        intro u hu
        rw [WithTop.le_untopA_iff (by simp)] at hu
        · apply le_iSup₂_of_le (α := ℝ≥0∞) u ?_
          · rw [min_eq_left]
            · exact le_rfl
            · exact le_trans hu (min_le_right _ _)
          · exact WithTop.coe_le_coe.mp (le_trans hu (min_le_left _ _))
    · simp
  rw [key_eq]
  exact StronglyMeasurable.indicator (hX.comp_measurable hM)
    (measurableSet_lt measurable_const (hτ.measurable'.comp measurable_snd))

lemma isStable_hasIntegrableSup [OrderBot ι] [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] :
    IsStable 𝓕 (HasIntegrableSup (E := E) · P) := by
  refine (fun X hX τ hτ ↦ ⟨isStable_hasStronglyMeasurableSupProcess X hX.1 τ hτ, ?_⟩)
  refine fun t ↦ ⟨ (isStable_hasStronglyMeasurableSupProcess X hX.1 τ hτ).comp_measurable
      (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable, ?_ ⟩
  have h_bound := (hX.2 t).hasFiniteIntegral
  simp_rw  [hasFiniteIntegral_def, enorm_eq_self] at h_bound ⊢
  refine lt_of_le_of_lt (lintegral_mono fun ω ↦ ?_) h_bound
  apply iSup₂_le
  intro s hs
  simp only [stoppedProcess, Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs with h_bot
  · refine le_iSup₂_of_le (min ↑s (τ ω)).untopA ?_ (le_refl _)
    · rw [WithTop.untopA_le_iff]
      · exact le_trans (min_le_left _ _) (WithTop.coe_le_coe.mpr hs)
      · exact ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top s))
  · simp only [enorm_zero, zero_le]

lemma isStable_hasLocallyIntegrableSup [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι] :
    IsStable 𝓕 (HasLocallyIntegrableSup (E := E) · 𝓕 P) :=
  IsStable.isStable_locally isStable_hasIntegrableSup

lemma isStable_classD [OrderBot ι] [MeasurableSpace ι] : IsStable 𝓕 (ClassD (E := E) · 𝓕 P) := by
  sorry

lemma isStable_classDL [OrderBot ι] [MeasurableSpace ι] : IsStable 𝓕 (ClassDL (E := E) · 𝓕 P) := by
  sorry

lemma _root_.MeasureTheory.Integrable.classDL [Nonempty ι] [MeasurableSpace ι]
    (hX : ∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖X t ω‖ₑ) P) :
    ClassDL X 𝓕 P := by
  sorry

lemma HasLocallyIntegrableSup.locally_classDL [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [MeasurableSpace ι]
    (hX1 : HasLocallyIntegrableSup X 𝓕 P) (hX2 : Adapted 𝓕 X) (h𝓕 : 𝓕.IsRightContinuous) :
    Locally (ClassDL · 𝓕 P) 𝓕 X P := by
  sorry

omit [LinearOrder ι] in
lemma ClassDL.classD [Preorder ι] {𝓕 : Filtration ι mΩ} [OrderTop ι] [MeasurableSpace ι]
    (hX : ClassDL X 𝓕 P) :
    ClassD X 𝓕 P := by
  let A := {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}
  let B := {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ (⊤ : ι)}
  let f : A → B := fun T => ⟨T, ⟨T.2.1, fun ω => ?_⟩⟩
  · have : (fun T : A ↦ stoppedValue X T.1) = (fun T ↦ stoppedValue X T.1) ∘ f := by ext; simp [f]
    refine ⟨hX.1, ?_⟩
    rw [this]
    exact UniformIntegrable.comp (hX.2 (⊤ : ι)) f
  · have := T.2.2 ω
    simp only [ne_eq, WithTop.ne_top_iff_exists] at this
    obtain ⟨a, ha⟩ := this
    exact ha ▸ WithTop.coe_le_coe.mpr (le_top (a := a))

lemma ClassDL.locally_classD [OrderBot ι] [TopologicalSpace ι] [SecondCountableTopology ι]
    [MeasurableSpace ι] [BorelSpace ι] [PseudoMetrizableSpace ι] [OrderTopology ι]
    (hX : ClassDL X 𝓕 P) :
    Locally (ClassD · 𝓕 P) 𝓕 X P := by
  rcases topOrderOrNoTopOrder ι with ha | hb
  · exact locally_of_prop hX.classD
  · obtain ⟨v, hv1, hv2⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
    refine ⟨fun n ω => v n, ⟨⟨fun n => ?_, ?_⟩, ?_⟩, fun n => ⟨?_, ?_⟩⟩
    · simp [isStoppingTime_const]
    · filter_upwards with ω
      simp only [tendsto_atTop_atTop] at hv2
      refine tendsto_atTop_isLUB (fun _ _ h => mod_cast hv1 h) ⟨?_, fun x hx => ?_⟩
      · exact top_mem_upperBounds _
      · simp only [top_le_iff, WithTop.eq_top_iff_forall_gt]
        simp only [mem_upperBounds, Set.mem_range, forall_exists_index,
          forall_apply_eq_imp_iff] at hx
        intro a
        obtain ⟨c, hc⟩ := (NoTopOrder.to_noMaxOrder ι).exists_gt a
        obtain ⟨n, hn⟩ := hv2 c
        exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (lt_of_lt_of_le hc (hn n le_rfl))) (hx n)
    · filter_upwards with ω
      exact fun _ _ h => WithTop.coe_le_coe.mpr (hv1 h)
    · refine ProgMeasurable.stoppedProcess (fun t => ?_) (by simp [isStoppingTime_const])
      by_cases hb : ⊥ < (v n : WithTop ι)
      · simp [hb, hX.1 t]
      · simp [hb, stronglyMeasurable_const]
    · let A := {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}
      let Y := fun T : A ↦ stoppedValue (stoppedProcess X (fun ω ↦ ↑(v n))) T
      refine uniformIntegrable_of_dominated (Y := Y) le_rfl ?_ (fun T => ?_) (fun T => ?_)
      · let B := {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ v n}
        let f : A → B := fun T => ⟨T.1 ⊓ (fun ω => ↑(v n)), ⟨T.2.1.min_const (v n), by simp⟩⟩
        have : Y = (fun T : B ↦ stoppedValue X T) ∘ f := by
          ext T; simpa [Y, f] using stoppedValue_stoppedProcess_apply (T.2.2 _)
        rw [this]
        exact UniformIntegrable.comp (hX.2 (v n)) f
      · by_cases hb : ⊥ < (v n : WithTop ι)
        · simp only [hb, Set.setOf_true, Set.indicator_univ, ne_eq, Set.mem_setOf_eq]
          refine AEStronglyMeasurable.congr ?_ (stoppedValue_stoppedProcess_ae_eq ?_).symm
          · refine (StronglyMeasurable.mono ?_ (𝓕.le' (v n))).aestronglyMeasurable
            refine stronglyMeasurable_stoppedValue_of_le hX.1 ((T.2.1).min_const _) (fun ω => ?_)
            grind
          · exact ae_of_all P T.2.2
        · unfold stoppedValue
          simp [hb]
          measurability
      · by_cases hb : ⊥ < (v n : WithTop ι)
        · simpa [hb, Y] using ⟨T.1, T.2, ae_of_all P fun ω => rfl.le⟩
        · simpa [hb, Y, stoppedValue] using ⟨T.1, T.2⟩

lemma locally_classD_of_locally_classDL [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [MeasurableSpace ι]
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
  locally_induction₂ h𝓕 (fun _ hCad hDL ↦ ClassDL.hasLocallyIntegrableSup hCad hDL h𝓕)
     isStable_isCadlag isStable_classDL isStable_hasIntegrableSup (locally_isCadlag_iff.mpr hX1) hX2

end ConditionallyCompleteLinearOrderBot

end ProbabilityTheory
