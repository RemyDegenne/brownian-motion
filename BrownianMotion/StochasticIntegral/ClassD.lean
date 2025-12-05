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


/-- Helper Lemma -/
@[simp]
lemma WithTop.untopA_coe {α : Type*} [Nonempty α] {σ : α} :
    (σ : WithTop α).untopA = σ := rfl

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

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ}

section RightContinuous

variable [TopologicalSpace ι] [OrderTopology ι] [OrderBot ι] [MeasurableSpace ι]
  [SecondCountableTopology ι]

/-- If `{stoppedValue X T : T is a bounded stopping time}` is uniformly integrable, then `X` is
of class D. -/
lemma classD_of_uniformIntegrable_bounded_stoppingTime {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : UniformIntegrable (fun T : {T | IsStoppingTime 𝓕 T ∧ ∃ t : ι, ∀ ω, T ω ≤ t}
      ↦ stoppedValue X T) 1 P) (hm : ProgMeasurable 𝓕 X) :
    ClassD X 𝓕 P := by
  have (T : {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}) :
    ∃ N : ℕ → {T | IsStoppingTime 𝓕 T ∧ ∃ t : ι, ∀ ω, T ω ≤ t},
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ stoppedValue X (N n).1 ω) atTop (nhds (stoppedValue X T.1 ω)) := by
    obtain ⟨v, hv⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
    refine ⟨fun n => ⟨(fun ω => v n) ⊓ T.1, ⟨IsStoppingTime.min ?_ T.2.1, ?_⟩⟩, ?_⟩
    · exact (isStoppingTime_const 𝓕 (v n))
    · exact ⟨v n, fun ω => by simp⟩
    · filter_upwards with ω
      simp_all only [tendsto_atTop_atTop, tendsto_atTop_nhds]
      intro U hU _
      obtain ⟨N, hN⟩ := hv.2 (T.1 ω).untopA
      refine ⟨N, fun n hn => ?_⟩
      have : (T.1 ω).untopA = T.1 ω := by simp [WithTop.untopA_eq_untop (T.2.2 ω)]
      rw [stoppedValue, Pi.inf_apply, ← this, ← WithTop.coe_min (v n) (T.1 ω).untopA,
        min_eq_right (hN n hn)]
      simpa using hU
  exact ⟨hm, (hX.uniformIntegrable_of_tendsto_ae 1).comp
    (fun T : {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤} => ⟨stoppedValue X T.1, this T⟩)⟩

variable [NormedSpace ℝ E] [CompleteSpace E]

section Order

variable [PseudoMetrizableSpace ι] [BorelSpace ι] [Lattice E]
  [HasSolidNorm E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [IsFiniteMeasure P]

lemma _root_.MeasureTheory.Submartingale.classDL (hX1 : Submartingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) (hX3 : 0 ≤ X) :
    ClassDL X 𝓕 P := by
  refine ⟨Adapted.progMeasurable_of_rightContinuous hX1.1 hX2, fun t => ?_⟩
  have := (hX1.2.2 t).uniformIntegrable_condExp' (fun T :
    {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≤ t} => IsStoppingTime.measurableSpace_le T.2.1)
  refine uniformIntegrable_of_dominated this (fun T => ?_) (fun T => ⟨T, ?_⟩)
  · exact ((stronglyMeasurable_stoppedValue_of_le (hX1.1.progMeasurable_of_rightContinuous
      hX2) T.2.1 T.2.2).mono (𝓕.le' t)).aestronglyMeasurable
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

lemma _root_.MeasureTheory.Submartingale.uniformIntegrable_bounded_stoppingTime
    (hX1 : Submartingale X 𝓕 P) (hX2 : ∀ ω, RightContinuous (X · ω)) (hX3 : 0 ≤ X)
    (hX4 : UniformIntegrable X 1 P) :
    UniformIntegrable (fun T : {T | IsStoppingTime 𝓕 T ∧ ∃ t : ι, ∀ ω, T ω ≤ t}
      ↦ stoppedValue X T) 1 P := by
    have hcond := hX4.condExp' (fun T : {T | IsStoppingTime 𝓕 T ∧ ∃ t : ι, ∀ ω, T ω ≤ t} =>
        IsStoppingTime.measurableSpace_le T.2.1)
    refine uniformIntegrable_of_dominated hcond (fun ⟨T, hT, ⟨t, ht⟩⟩ => ?_)
      (fun ⟨T, hT, ⟨t, ht⟩⟩ => ⟨⟨t, ⟨T, hT, ⟨t, ht⟩⟩⟩, ?_⟩)
    · exact ((stronglyMeasurable_stoppedValue_of_le (hX1.1.progMeasurable_of_rightContinuous
        hX2) hT ht).mono (𝓕.le' t)).aestronglyMeasurable
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

lemma _root_.MeasureTheory.Submartingale.classD_iff_uniformIntegrable
    (hX1 : Submartingale X 𝓕 P) (hX2 : ∀ ω, RightContinuous (X · ω)) (hX3 : 0 ≤ X) :
    ClassD X 𝓕 P ↔ UniformIntegrable X 1 P := by
  let S := {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}
  let G (T : S) : (Ω → E) := stoppedValue X T.1
  refine ⟨fun hp => ?_, fun hq => ?_⟩
  · let constT (t : ι) : S := ⟨fun ω : Ω => t, ⟨isStoppingTime_const 𝓕 t, by simp⟩⟩
    have eq : X = G ∘ constT := by ext; simp [constT, G, stoppedValue]
    simpa [eq] using hp.2.comp constT
  · refine classD_of_uniformIntegrable_bounded_stoppingTime ?_ ?_
    · exact hX1.uniformIntegrable_bounded_stoppingTime hX2 hX3 hq
    · exact hX1.1.progMeasurable_of_rightContinuous hX2

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

lemma isStable_stronglyMeasurable_uncurry [OrderBot ι] [TopologicalSpace ι]
    [SecondCountableTopology ι] [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ StronglyMeasurable (uncurry X)) := by
  intro X hX τ hτ
  let M : ι × Ω → ι × Ω := fun p ↦ ((min ↑p.1 (τ p.2)).untopA, p.2)
  have hM : Measurable M := (WithTop.measurable_coe.comp measurable_fst).min
      (hτ.measurable'.comp measurable_snd) |>.untopA.prodMk measurable_snd
  have h_eq : uncurry (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ) =
      {p | ⊥ < τ p.2}.indicator (uncurry X ∘ M) := by
    ext ⟨t, ω⟩
    simp only
        [uncurry, stoppedProcess, Set.indicator_apply, Set.mem_setOf_eq, Function.comp_apply, M]
  rw [h_eq]
  exact StronglyMeasurable.indicator (hX.comp_measurable hM)
    (measurableSet_lt measurable_const (hτ.measurable'.comp measurable_snd))

lemma isStable_progMeasurable [OrderBot ι] [MeasurableSpace ι] [TopologicalSpace ι]
  [PseudoMetrizableSpace ι] [BorelSpace ι] [SecondCountableTopology ι] [OrderTopology ι] :
    IsStable (E := E) 𝓕 (ProgMeasurable 𝓕) := by
  refine fun X hX τ hτ ↦ ProgMeasurable.stoppedProcess ?_ hτ
  intro i
  have h_prog : MeasurableSet[𝓕 i] {ω | ⊥ < τ ω} := by
    have hw: {ω | ⊥ < τ ω} = {ω | τ ω ≤ ⊥}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      exact lt_iff_not_ge
    rw [hw]
    convert (MeasurableSet.compl (𝓕.mono bot_le _ (hτ ⊥)))
  exact StronglyMeasurable.indicator (hX i) <| measurable_snd h_prog


lemma ProgMeasurable.stronglyMeasurable_uncurry_stoppedProcess_const
    [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] [OrderBot ι]
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hX : ProgMeasurable 𝓕 X) (t : ι) :
    (StronglyMeasurable <| uncurry (stoppedProcess X (fun _ ↦ t))) := by
  let g : ι × Ω → (Set.Iic t) × Ω := fun p ↦ (⟨min p.1 t, min_le_right p.1 t⟩, p.2)
  have hg_meas : @Measurable _ _ _
      (MeasurableSpace.prod (inferInstance : MeasurableSpace (Set.Iic t)) (𝓕 t)) g := by
    apply Measurable.prodMk _ (measurable_snd.mono le_rfl (𝓕.le t))
    exact ((continuous_id.min continuous_const).measurable.comp measurable_fst).subtype_mk
  exact StronglyMeasurable.comp_measurable (hX t) hg_meas

lemma ProgMeasurable.stronglyMeasurable_uncurry_of_isCountablyGenerated_atTop
    [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι]
    [IsCountablyGenerated (atTop : Filter ι)] {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
    (hX : ProgMeasurable 𝓕 X) : (StronglyMeasurable (uncurry X)) := by
  rcases exists_seq_monotone_tendsto_atTop_atTop (α := ι) with ⟨t, -, ht_lim⟩
  refine stronglyMeasurable_of_tendsto atTop
    (fun n ↦ stronglyMeasurable_uncurry_stoppedProcess_const hX (t n)) ?_
  rw [tendsto_pi_nhds]
  intro ⟨s, ω⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [ht_lim.eventually (Filter.eventually_ge_atTop s)] with n hn
  simp only [uncurry_apply_pair, stoppedProcess]
  rw [←WithTop.coe_min, WithTop.untopA_coe, min_eq_left hn]

private lemma ProgMeasurable.aestronglyMeasurable_stoppedValue_stoppedProcess
    [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [NoMaxOrder ι]
    [BorelSpace ι] [SecondCountableTopology ι] [PseudoMetrizableSpace ι]
    {X : ι → Ω → E} (hX_prog : ProgMeasurable 𝓕 X) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ)
    (sigma : {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≠ ⊤}) :
    AEStronglyMeasurable
    (stoppedValue (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ) sigma.1) P := by
  have hY_prog := isStable_progMeasurable X hX_prog τ hτ
  have hY_sm := ProgMeasurable.stronglyMeasurable_uncurry_of_isCountablyGenerated_atTop hY_prog
  let idx_map : Ω → ι := fun ω ↦ (sigma.val ω).untop (sigma.property.2 ω)
  have h_idx_meas : @Measurable Ω ι mΩ _ idx_map := by
    have h_emb : MeasurableEmbedding (fun x : ι ↦ (x : WithTop ι)) := by
      apply Topology.IsEmbedding.measurableEmbedding WithTop.isEmbedding_coe
      rw [WithTop.range_coe]
      exact IsOpen.measurableSet isOpen_Iio
    apply (MeasurableEmbedding.measurable_comp_iff h_emb).mp
    convert IsStoppingTime.measurable' (m := mΩ) sigma.property.1
    ext ω; simp only [Function.comp_apply]; rw [WithTop.coe_untop]
  refine (hY_sm.comp_measurable (h_idx_meas.prodMk measurable_id)).aestronglyMeasurable.congr ?_
  apply Filter.EventuallyEq.of_eq; ext ω
  simp only [stoppedValue, uncurry, Function.comp_apply]
  congr 2
  rw [WithTop.untopA_eq_untop]

private lemma stoppedValue_stoppedProcess_dominated_le
    [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι]
    (X : ι → Ω → E) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ)
    (sigma : {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≠ ⊤}) :
    ∃ rho : {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≠ ⊤},
      (∀ ω, rho.1 ω ≤ sigma.1 ω) ∧
      ∀ᵐ ω ∂P, ‖stoppedValue (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ) sigma.1 ω‖ ≤
        ‖stoppedValue X rho.1 ω‖ := by
  let rho_val := sigma.1 ⊓ τ
  have h_rho_stop : IsStoppingTime 𝓕 rho_val := IsStoppingTime.min sigma.2.1 hτ
  have h_rho_finite : ∀ ω, rho_val ω ≠ ⊤ :=
    fun ω ↦ ne_of_lt (lt_of_le_of_lt inf_le_left (lt_top_iff_ne_top.mpr (sigma.2.2 ω)))
  refine ⟨⟨rho_val, h_rho_stop, h_rho_finite⟩, fun ω ↦ inf_le_left, ?_⟩
  filter_upwards with ω
  simp only [stoppedValue, stoppedProcess, Set.indicator, Set.mem_setOf_eq, rho_val]
  split_ifs with h_bot
  · apply le_of_eq
    congr
    rw [WithTop.untopA_eq_untop, WithTop.coe_untop]
    exact sigma.prop.2 ω
  · simp only [norm_zero]; exact norm_nonneg _

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

lemma isStable_classD [OrderBot ι] [MeasurableSpace ι] [TopologicalSpace ι] [OrderTopology ι]
    [PseudoMetrizableSpace ι] [BorelSpace ι] [SecondCountableTopology ι] [NoMaxOrder ι] :
    IsStable 𝓕 (ClassD (E := E) · 𝓕 P) := by
  refine fun X ⟨hX_prog, hUI_X⟩ τ hτ ↦ ⟨isStable_progMeasurable X hX_prog τ hτ, ?_⟩
  refine uniformIntegrable_of_dominated hUI_X
    (ProgMeasurable.aestronglyMeasurable_stoppedValue_stoppedProcess hX_prog hτ) ?_
  intro sigma
  rcases stoppedValue_stoppedProcess_dominated_le X hτ sigma with ⟨rho, _, h_dom⟩
  exact ⟨rho, h_dom⟩

lemma isStable_classDL [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι]
    [NoMaxOrder ι] [BorelSpace ι] [SecondCountableTopology ι] [PseudoMetrizableSpace ι] :
    IsStable 𝓕 (ClassDL (E := E) · 𝓕 P) := by
  refine fun X ⟨hX_prog, hUI_X⟩ τ hτ ↦ ⟨isStable_progMeasurable X hX_prog τ hτ, fun t ↦ ?_⟩
  let embed : {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ ↑t} →
              {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤} :=
    fun σ ↦ ⟨σ.1, σ.2.1, fun ω ↦ ne_of_lt (lt_of_le_of_lt (σ.2.2 ω) (WithTop.coe_lt_top t))⟩
  refine uniformIntegrable_of_dominated (hUI_X t) ?_ ?_
  · intro sigma
    exact ProgMeasurable.aestronglyMeasurable_stoppedValue_stoppedProcess hX_prog hτ (embed sigma)
  · intro sigma
    rcases stoppedValue_stoppedProcess_dominated_le X hτ (embed sigma) with ⟨rho, h_le_sigma, h_dom⟩
    let rho_bounded : {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ ↑t} :=
      ⟨rho.1, rho.2.1, fun ω ↦ le_trans (h_le_sigma ω) (sigma.2.2 ω)⟩
    exact ⟨rho_bounded, h_dom⟩

/-- A progressively measurable process is necessarily a.e. strongly measurable at each time `i`. -/
private lemma aestronglyMeasurable_of_progMeasurable [Nonempty ι] [MeasurableSpace ι]
    {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} (hprog : ProgMeasurable 𝓕 X) :
    ∀ i, AEStronglyMeasurable (X i) P := by
  intro i
  have hsm_f_i : StronglyMeasurable[𝓕 i] (X i) :=
    hprog.adapted i
  have hae_f_i : AEStronglyMeasurable[𝓕 i] (X i) P :=
    MeasureTheory.StronglyMeasurable.aestronglyMeasurable hsm_f_i
  exact hae_f_i.mono (𝓕.le' i)

private lemma ae_finite_of_integrable {f : Ω → ℝ≥0∞} (hf : Integrable f P) :
    ∀ᵐ ω ∂P, f ω ≠ ∞ := by
  refine (ae_lt_top' hf.1.aemeasurable (ne_of_lt hf.2)).mono ?_
  intro ω hω; exact ne_of_lt hω

private lemma ae_finite_sup_of_integrable_sup [Nonempty ι] [MeasurableSpace ι]
    {X : ι → Ω → E} (hX : HasIntegrableSup X P) (t : ι) :
    AEMeasurable (fun ω ↦ ⨆ s ≤ t, ‖X s ω‖ₑ) P ∧
    ∀ᵐ ω ∂P, (⨆ s ≤ t, ‖X s ω‖ₑ) ≠ ∞ := by
  let supX := fun (tω : ι × Ω) ↦ ⨆ s ≤ tω.1, ‖X s tω.2‖ₑ
  let supX_t := fun ω ↦ ⨆ s ≤ t, ‖X s ω‖ₑ
  have hsm' : StronglyMeasurable supX := by
    simpa [HasStronglyMeasurableSupProcess, supX] using hX.1
  have hsm : StronglyMeasurable supX_t :=
    hsm'.comp_measurable (measurable_const.prodMk measurable_id)
  have hsupXt : Integrable supX_t P := hX.2 t
  have hintsupXt : ∫⁻ (ω : Ω), supX_t ω ∂P ≠ ⊤ := by
    exact ne_of_lt hsupXt.hasFiniteIntegral
  have haefin : ∀ᵐ ω ∂P, supX_t ω < ∞ := by
    apply ae_lt_top' (hsm.aemeasurable) hintsupXt
  have haenoninf : ∀ᵐ ω ∂P, supX_t ω ≠ ∞ := by
    filter_upwards [haefin] with ω hω
    exact ne_of_lt hω
  exact ⟨hsm.aemeasurable, haenoninf⟩

lemma _root_.MeasureTheory.Integrable.classDL [Nonempty ι] [MeasurableSpace ι]
    (hX1 : ProgMeasurable 𝓕 X)
    (hX2 : ∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖X s ω‖ₑ) P) :
    ClassDL X 𝓕 P := by
  refine ⟨hX1, fun t ↦ ?_⟩
  let supX_t := fun ω ↦ ⨆ s ≤ t, ‖X s ω‖ₑ
  have hsupfinite : ∀ᵐ ω ∂P, supX_t ω ≠ ∞ := ae_finite_of_integrable (hX2 t)
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
      refine uniformIntegrable_of_dominated (Y := Y) ?_ (fun T => ?_) (fun T => ?_)
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


variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [MeasurableSpace ι] [SecondCountableTopology ι] [DenselyOrdered ι] [NoMaxOrder ι] [BorelSpace ι]
  [PseudoMetrizableSpace ι] [IsFiniteMeasure P] {𝓕 : Filtration ι mΩ}

lemma hasLocallyIntegrableSup_of_locally_classDL {h𝓕 : 𝓕.IsRightContinuous}
    (hX1 : Locally (fun X ↦ ∀ ω, IsCadlag (X · ω)) 𝓕 X P) (hX2 : Locally (ClassDL · 𝓕 P) 𝓕 X P) :
    HasLocallyIntegrableSup X 𝓕 P :=
  locally_induction₂ h𝓕 (fun _ hCad hDL ↦ ClassDL.hasLocallyIntegrableSup hCad hDL h𝓕)
     isStable_isCadlag isStable_classDL isStable_hasIntegrableSup hX1 hX2

end ConditionallyCompleteLinearOrderBot

end ProbabilityTheory
