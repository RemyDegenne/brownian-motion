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

/-- A stochastic process has locally integrable supremum if it satisfies locally the property that
for all `t`, the random variable `ω ↦ sup_{s ≤ t} ‖X s ω‖` is integrable. -/
def HasLocallyIntegrableSup [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    (X : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω := by volume_tac) : Prop :=
  Locally (fun Y ↦ ∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖Y s ω‖ₑ) P) 𝓕 X P

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
  refine ⟨hX1.1, fun t => ?_⟩
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

lemma _root_.MeasureTheory.Submartingale.classD_iff_uniformIntegrable (hX1 : Submartingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) (hX3 : 0 ≤ X) :
    ClassD X 𝓕 P ↔ UniformIntegrable X 1 P := by
  let S := {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}
  let G (T : S) : (Ω → E) := stoppedValue X T.1
  refine ⟨fun hp => ?_, fun hq => ?_⟩
  · let constT (t : ι) : S := ⟨fun ω : Ω => t, ⟨isStoppingTime_const 𝓕 t, by simp⟩⟩
    have eq : X = G ∘ constT := by ext; simp [constT, G, stoppedValue]
    simpa [eq] using hp.2.comp constT
  · refine ⟨hX1.1, ?_⟩
    -- set of bounded stopping times
    let B := {T | IsStoppingTime 𝓕 T ∧ ∃ t : ι, ∀ ω, T ω ≤ t}
    -- set of condtional expectations of `stoppedValue X T.1` for `T ∈ B` is uniformly integrable
    have hcond := hq.condExp' (fun T : B => IsStoppingTime.measurableSpace_le T.2.1)
    -- set of `stoppedValue X T.1` for `T ∈ B` is uniformly integrable
    have hB : UniformIntegrable (fun T : B ↦ stoppedValue X T.1) 1 P := by
      refine uniformIntegrable_of_dominated le_rfl hcond (fun ⟨T, hT, ⟨t, ht⟩⟩ => ?_)
        (fun ⟨T, hT, ⟨t, ht⟩⟩ => ⟨⟨t, ⟨T, hT, ⟨t, ht⟩⟩⟩, ?_⟩)
      · refine ((stronglyMeasurable_stoppedValue_of_le (β := E) ?_ hT ht).mono
          (𝓕.le' t)).aestronglyMeasurable
        exact Adapted.progMeasurable_of_rightContinuous hX1.1 hX2
      · have : stoppedValue X T ≤ᵐ[P] P[stoppedValue X (fun ω => t)|hT.measurableSpace] := by
          suffices lem : stoppedValue X ((fun ω => t) ⊓ T) ≤ᵐ[P]
            P[stoppedValue X (fun ω => t)|hT.measurableSpace] from by
            have : T ⊓ (fun ω => t) = T := by simpa [inf_eq_left] using ht
            simpa [inf_comm, this] using lem
          exact hX1.stoppedValue_min_ae_le_condExp 𝓕 hX2
            (Eventually.of_forall (fun ω => le_rfl)) hT (isStoppingTime_const 𝓕 t)
        simp only [stoppedValue_const] at this
        filter_upwards [this] with ω hω
        apply norm_le_norm_of_abs_le_abs
        have p1 : 0 ≤ stoppedValue X T ω := by simpa [stoppedValue] using (hX3 (T ω).untopA ω)
        have p2 : |P[X t|hT.measurableSpace] ω| = P[X t|hT.measurableSpace] ω :=
          abs_of_nonneg (le_trans p1 hω)
        rw [← abs_of_nonneg p1, ← p2] at hω
        exact hω
    -- set of limit in probability is uniformly integrable
    have hlim := hB.uniformIntegrable_of_tendsto_ae 1
    -- stoppedValue of a finite stopping time is a.e limit of sequences in B
    have (T : S) : ∃ N : ℕ → B,
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ stoppedValue X (N n).1 ω) atTop (nhds (stoppedValue X T.1 ω)) := by
      -- We need second countable order topology on `ι` in the following lemma
      obtain ⟨v, hv⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
      refine ⟨fun n => ⟨(fun ω => v n) ⊓ T.1, ⟨IsStoppingTime.min ?_ T.2.1, ?_⟩⟩, ?_⟩
      · exact (isStoppingTime_const 𝓕 (v n))
      · exact ⟨v n, fun ω => by simp⟩
      · filter_upwards with ω
        simp_all only [tendsto_atTop_atTop, tendsto_atTop_nhds]
        intros U hU _
        obtain ⟨N, hN⟩ := hv.2 (T.1 ω).untopA
        refine ⟨N, fun n hn => ?_⟩
        have : (T.1 ω).untopA = T.1 ω := by simp [WithTop.untopA_eq_untop (T.2.2 ω)]
        rw [stoppedValue, Pi.inf_apply, ← this, ← WithTop.coe_min (v n) (T.1 ω).untopA,
          min_eq_right (hN n hn)]
        simpa using hU
    let I (T : S) : {g : Ω → E | ∃ N : ℕ → B,
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ stoppedValue X (N n).1 ω) atTop (nhds (g ω))} :=
      ⟨stoppedValue X T.1, this T⟩
    have eq : G = Subtype.val ∘ I := by ext; simp [I, G]
    exact hlim.comp I

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

lemma isStable_hasLocallyIntegrableSup [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] :
    IsStable 𝓕 (HasLocallyIntegrableSup (E := E) · 𝓕 P) := by
  sorry

lemma isStable_classD [OrderBot ι] : IsStable 𝓕 (ClassD (E := E) · 𝓕 P) := by
  sorry

lemma isStable_classDL [OrderBot ι] : IsStable 𝓕 (ClassDL (E := E) · 𝓕 P) := by
  sorry

lemma _root_.MeasureTheory.Integrable.classDL [Nonempty ι]
    (hX : ∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖X t ω‖ₑ) P) :
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
    (hX1 : ∀ ω, IsCadlag (X · ω)) (hX2 : ClassDL X 𝓕 P)
    (h𝓕 : 𝓕.IsRightContinuous) :
    HasLocallyIntegrableSup X 𝓕 P := by
  sorry

lemma hasLocallyIntegrableSup_of_locally_classDL [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] [InfSet ι] [CompactIccSpace ι] [OrderBot ι]
    (hX1 : ∀ ω, IsCadlag (X · ω)) (hX2 : Locally (ClassDL · 𝓕 P) 𝓕 X P)
    (h𝓕 : 𝓕.IsRightContinuous) :
    HasLocallyIntegrableSup X 𝓕 P := by
  sorry

end LinearOrder

end ProbabilityTheory
