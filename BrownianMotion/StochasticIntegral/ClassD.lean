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
lemma WithTop.coe_untopA {α : Type*} [Nonempty α] {σ : α} :
    (σ : WithTop α).untopA = σ := rfl

namespace ProbabilityTheory

variable {ι Ω E : Type*} [NormedAddCommGroup E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ι → Ω → E}

/-- The process `X` is jointly strongly measurable if it is strongly measurable as a function
on the total space `ι × Ω`. -/
def JointlyStronglyMeasurable [MeasurableSpace ι] (X : ι → Ω → E) : Prop :=
  StronglyMeasurable (uncurry X)

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


lemma ProgMeasurable.jointlyStronglyMeasurable_stoppedProcess_const
    [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] [OrderBot ι]
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hX : ProgMeasurable 𝓕 X) (t : ι) :
    JointlyStronglyMeasurable (mΩ := mΩ) (stoppedProcess X (fun _ ↦ t)) := by
  let g : ι × Ω → (Set.Iic t) × Ω := fun p ↦ (⟨min p.1 t, min_le_right p.1 t⟩, p.2)
  have hg_meas : @Measurable _ _ _
      (MeasurableSpace.prod (inferInstance : MeasurableSpace (Set.Iic t)) (𝓕 t)) g := by
    apply Measurable.prodMk _ (measurable_snd.mono le_rfl (𝓕.le t))
    exact ((continuous_id.min continuous_const).measurable.comp measurable_fst).subtype_mk
  exact StronglyMeasurable.comp_measurable (hX t) hg_meas

lemma ProgMeasurable.jointlyStronglyMeasurable
    [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι]
    [SecondCountableTopology ι] {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
    (hX : ProgMeasurable 𝓕 X) : (JointlyStronglyMeasurable (mΩ := mΩ) X) := by
  rcases exists_seq_monotone_tendsto_atTop_atTop (α := ι) with ⟨t, -, ht_lim⟩
  refine stronglyMeasurable_of_tendsto atTop
    (fun n ↦ jointlyStronglyMeasurable_stoppedProcess_const hX (t n)) ?_
  rw [tendsto_pi_nhds]
  intro ⟨s, ω⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [ht_lim.eventually (Filter.eventually_ge_atTop s)] with n hn
  simp only [uncurry_apply_pair, stoppedProcess]
  rw [←WithTop.coe_min, WithTop.coe_untopA, min_eq_left hn]

private lemma ProgMeasurable.stoppedValue_stoppedProcess_aestronglyMeasurable
    [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [NoMaxOrder ι]
    [BorelSpace ι] [SecondCountableTopology ι] [PseudoMetrizableSpace ι]
    {X : ι → Ω → E} (hX_prog : ProgMeasurable 𝓕 X) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ)
    (sigma : {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≠ ⊤}) :
    AEStronglyMeasurable
    (stoppedValue (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ) sigma.1) P := by
  have hY_prog := isStable_progMeasurable X hX_prog τ hτ
  have hY_sm := ProgMeasurable.jointlyStronglyMeasurable hY_prog
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


lemma isStable_jointlyStronglyMeasurable [OrderBot ι] [TopologicalSpace ι]
    [SecondCountableTopology ι] [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] :
    IsStable 𝓕 (JointlyStronglyMeasurable (E := E) (mΩ := mΩ) · ) := by
      sorry

lemma JointlyStronglyMeasurable.HasStronglyMeasurableSupProcess [OrderBot ι] [TopologicalSpace ι]
    [MeasurableSpace ι] {X : ι → Ω → E} (hX : JointlyStronglyMeasurable (mΩ := mΩ) X) :
      HasStronglyMeasurableSupProcess (mΩ := mΩ) X := by
  sorry

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
    by_cases h : ⊥ < τ ω <;> simp only [h, ↓reduceIte, enorm_zero, ENNReal.iSup_zero,
      ciSup_const]; apply le_antisymm
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
  refine uniformIntegrable_of_dominated le_rfl hUI_X
    (ProgMeasurable.stoppedValue_stoppedProcess_aestronglyMeasurable hX_prog hτ) ?_
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
  refine uniformIntegrable_of_dominated le_rfl (hUI_X t) ?_ ?_
  · intro sigma
    exact ProgMeasurable.stoppedValue_stoppedProcess_aestronglyMeasurable hX_prog hτ (embed sigma)
  · intro sigma
    rcases stoppedValue_stoppedProcess_dominated_le X hτ (embed sigma) with ⟨rho, h_le_sigma, h_dom⟩
    let rho_bounded : {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ ↑t} :=
      ⟨rho.1, rho.2.1, fun ω ↦ le_trans (h_le_sigma ω) (sigma.2.2 ω)⟩
    exact ⟨rho_bounded, h_dom⟩


lemma _root_.MeasureTheory.Integrable.classDL [Nonempty ι] [MeasurableSpace ι]
    (hX : ∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖X t ω‖ₑ) P) :
    ClassDL X 𝓕 P := by
  sorry

lemma HasLocallyIntegrableSup.locally_classDL [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [MeasurableSpace ι]
    (hX1 : HasLocallyIntegrableSup X 𝓕 P) (hX2 : Adapted 𝓕 X) (h𝓕 : 𝓕.IsRightContinuous) :
    Locally (ClassDL · 𝓕 P) 𝓕 X P := by
  sorry

lemma ClassDL.locally_classD [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι]
    (hX : ClassDL X 𝓕 P) :
    Locally (ClassD · 𝓕 P) 𝓕 X P := by
  sorry

lemma locally_classD_of_locally_classDL [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [MeasurableSpace ι] (hX : Locally (ClassDL · 𝓕 P) 𝓕 X P) (h𝓕 : 𝓕.IsRightContinuous) :
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

lemma MeasureTheory.Adapted.norm {ι E : Type*} [NormedAddCommGroup E] [PartialOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι] [InfSet ι] [Bot ι]
    [CompactIccSpace ι] (𝓕 : Filtration ι mΩ) {X : ι → Ω → E} (hX1 : Adapted 𝓕 X) :
    Adapted 𝓕 (fun t ω ↦ ‖X t ω‖) := by
  sorry



lemma iSup_le_eq_iSup_stopped_min_generic [LinearOrder ι] [OrderBot ι]
    {α : Type*} [CompleteLattice α] {f : ι → α} (t : ι) :
    (⨆ s, ⨆ (_ : s ≤ t), f s) = ⨆ s, f (min s t) := by
  sorry

lemma iSup_le_eq_iSup_stopped_min [LinearOrder ι] [OrderBot ι]
    {α : Type*} [CompleteLattice α] {f : ι → α} (t : ι) :
    (⨆ s, ⨆ (_ : s ≤ t), f s) = ⨆ s, f (min s t) := by
  rw [iSup, iSup, sSup_eq_iSup, sSup_eq_iSup]
  congr 1
  ext x
  simp only [Set.mem_range]
  sorry

lemma ClassDL.hasLocallyIntegrableSup [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι]
    [FirstCountableTopology ι] [InfSet ι] [CompactIccSpace ι] [OrderBot ι] [BorelSpace ι]
    [SecondCountableTopology ι] [PseudoMetrizableSpace ι] [IsFiniteMeasure P]
    (hX1 : ∀ ω, IsCadlag (X · ω))
    (hX2 : ClassDL X 𝓕 P) (h𝓕 : 𝓕.IsRightContinuous) :
    HasLocallyIntegrableSup X 𝓕 P := by
  unfold HasLocallyIntegrableSup
  rcases hX2 with ⟨hX2, hX3⟩
  let Y : ι → Ω → ℝ := fun t ω ↦ ‖X t ω‖
  have hY1 : Adapted 𝓕 Y := by exact MeasureTheory.Adapted.norm 𝓕 hX2.adapted
  have hY2 : ∀ (ω : Ω), RightContinuous (Y · ω) := by
    intro ω
    exact (Function.RightContinuous.continuous_comp continuous_norm (hX1 ω).1)
  let τ : ℕ → Ω → WithTop ι := (fun n ↦ hittingAfter Y (Set.Ici n) ⊥)
  have hτ : IsLocalizingSequence 𝓕 τ P:= by
    exact isLocalizingSequence_hittingAfter_Ici 𝓕 τ hY1 hY2 h𝓕
  use τ
  refine ⟨hτ, ?_⟩
  intro n
  have hX4 := fun (t : ι) (ω : Ω) ↦
    sup_stoppedProcess_hittingAfter_Ici_le (X := X) t n ω

  have hX5 : JointlyStronglyMeasurable (mΩ := mΩ) X := ProgMeasurable.jointlyStronglyMeasurable hX2
  let rhs := fun (t : ι) (ω : Ω) ↦
    ↑n + {ω | hittingAfter (fun t ω ↦ ‖X t ω‖) (Set.Ici ↑n) ⊥ ω ≤ ↑t}.indicator
    (fun ω ↦ ‖stoppedValue X (hittingAfter (fun t ω ↦ ‖X t ω‖) (Set.Ici ↑n) ⊥) ω‖) ω
  unfold HasIntegrableSup
  constructor
  · refine JointlyStronglyMeasurable.HasStronglyMeasurableSupProcess ?_
    refine ProgMeasurable.jointlyStronglyMeasurable (𝓕 := 𝓕) ?_
    exact isStable_progMeasurable (ι := ι) (E := E) X hX2 (τ n) (hτ.isStoppingTime n)
  · intro t
    -- 1. Define a dominating variable `dom` in ℝ.
    -- We use (n + ‖X_{τ_n ⊓ t}‖) because ClassDL guarantees this is integrable.
    -- The `rhs` you defined earlier is also a bound, but this one is easier to integrate.
    let dom := fun ω ↦ ↑n + ‖stoppedValue X (τ n ⊓ fun _ ↦ t) ω‖
    let σ : Ω → WithTop ι := (τ n) ⊓ (fun _ ↦ t : Ω → WithTop ι)
    have hσ : IsStoppingTime 𝓕 σ := (hτ.isStoppingTime n).min (isStoppingTime_const 𝓕 t)

    -- 2. Use standard mono. We must prove:
    --    a. dom is integrable
    --    b. The sup process is AE measurable
    --    c. The sup process ≤ dom
    refine Integrable.mono_enorm (g := dom) ?_ ?_ ?_

    -- Goal 1: Prove dom is integrable
    · unfold dom

      change Integrable ((fun ω : Ω ↦ (n : ℝ)) + (fun ω ↦ ‖stoppedValue X (τ n ⊓ fun x ↦ ↑t) ω‖)) P
      refine Integrable.add (integrable_const (n : ℝ)) ( ?_)


      -- We observe that σ is bounded by t
      have h_le : σ ≤ (fun _ ↦ t : Ω → WithTop ι)  := by
        intro ω
        apply min_le_right

      rcases hX3 t with ⟨h_meas, _, ⟨C, h_bound⟩⟩
      have := hX3 t
      -- Prove Integrable by checking its two fields manually
      constructor
      · -- 1. Measurability
        exact (h_meas ⟨σ, ⟨hσ, h_le⟩ ⟩).norm
      · -- 2. Finite Integral (HasFiniteIntegral)
        -- We map eLpNorm (p=1) to the integral
        rw [HasFiniteIntegral]
        simp only [enorm_norm]
        rw [← eLpNorm_one_eq_lintegral_enorm]

        -- Use the bound C provided by UniformIntegrable
        refine lt_of_le_of_lt (h_bound ⟨σ, ⟨ hσ , h_le ⟩⟩ ) ?_

        exact ENNReal.coe_lt_top
    -- Goal 2: Prove the sup process is measurable
    · apply StronglyMeasurable.aestronglyMeasurable

      have h_meas_sup := JointlyStronglyMeasurable.HasStronglyMeasurableSupProcess
        (ProgMeasurable.jointlyStronglyMeasurable (isStable_progMeasurable X hX2 σ hσ))
      have eq_indicator :
        (fun ω ↦ ⨆ s, ⨆ (_ : s ≤ t), ‖stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n) s ω‖ₑ) =
        {ω | ⊥ < τ n ω}.indicator (fun ω ↦ ⨆ s, ⨆ (_ : s ≤ t), ‖stoppedProcess X (τ n) s ω‖ₑ) := by
        ext ω
        simp only [Set.indicator]
        split_ifs with h
        ·
          congr
          ext t
          congr
          ext x
          congr 1
          simp only [stoppedProcess, Set.indicator_of_mem h]
        · have h_bot : τ n ω = ⊥ := not_bot_lt_iff.mp h
          simp only [stoppedProcess, h_bot, bot_le, inf_of_le_right, Set.mem_setOf_eq,
            lt_self_iff_false, not_false_eq_true, Set.indicator_of_notMem, enorm_zero,
            ENNReal.iSup_zero, ciSup_const]


      -- 3. Rewrite and solve
      rw [eq_indicator]
      apply StronglyMeasurable.indicator

      · simp [stoppedProcess]

        have hX6 := JointlyStronglyMeasurable.HasStronglyMeasurableSupProcess hX5
        unfold HasStronglyMeasurableSupProcess at hX6
        sorry
      · apply?
        apply measurableSet_lt measurable_const
        -- τ n is a stopping time, hence measurable
        exact (hτ.isStoppingTime n).measurable

    -- Goal 3: Prove the domination inequality
    · apply eventually_of_forall
      intro ω
      -- Apply the pointwise bound from the hitting time lemma (hX4)
      specialize hX4 t ω
      refine le_trans hX4 ?_

      -- Now show hX4's rhs ≤ our dom
      -- Logic:
      -- If τ ≤ t: rhs = n + ‖X_τ‖, dom = n + ‖X_τ‖. Equal.
      -- If τ > t: rhs = n, dom = n + ‖X_t‖. Since ‖X_t‖ ≥ 0, rhs ≤ dom.
      dsimp [dom]
      simp only [add_le_add_iff_left]
      by_cases h : τ n ω ≤ t
      · -- Hit happened
        simp [h, Set.indicator_of_mem, stoppedValue]
      · -- Hit didn't happen
        simp [h, Set.indicator_of_not_mem, stoppedValue]
        exact norm_nonneg _


end LinearOrder

section ConditionallyCompleteLinearOrderBot


variable [ConditionallyCompleteLinearOrderBot ι] {𝓕 : Filtration ι mΩ}
  [Filtration.HasUsualConditions 𝓕 P] [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι]
    [SecondCountableTopology ι] [DenselyOrdered ι] [NoMaxOrder ι] [BorelSpace ι]
    [PseudoMetrizableSpace ι] [IsFiniteMeasure P] [CompleteSpace E] [NormedSpace ℝ E]

lemma hasLocallyIntegrableSup_of_locally_classDL (hX1 : ∀ᵐ (ω : Ω) ∂P, IsCadlag (X · ω))
    (hX2 : Locally (ClassDL · 𝓕 P) 𝓕 X P) (h𝓕 : 𝓕.IsRightContinuous) :
    HasLocallyIntegrableSup X 𝓕 P :=
  locally_induction₂ h𝓕 (fun _ hCad hDL ↦ ClassDL.hasLocallyIntegrableSup hCad hDL h𝓕)
     isStable_isCadlag isStable_classDL isStable_hasIntegrableSup (locally_isCadlag_iff.mpr hX1) hX2

end ConditionallyCompleteLinearOrderBot

end ProbabilityTheory
