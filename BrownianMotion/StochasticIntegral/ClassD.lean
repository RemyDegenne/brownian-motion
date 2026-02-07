/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.StochasticIntegral.LocalMartingale
import Mathlib.Probability.Process.HittingTime

/-! # Locally integrable, class D, class DL

-/

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal


/-- Helper Lemma -/
@[simp]
lemma WithTop.untopA_coe {α : Type*} [Nonempty α] {σ : α} :
    (σ : WithTop α).untopA = σ := rfl

namespace MeasureTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [MeasurableSpace ι] [BorelSpace ι] [NormedAddCommGroup E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ι → Ω → E} {τ : Ω → WithTop ι} {𝓕 : Filtration ι mΩ}

lemma ProgMeasurable.stronglyMeasurable_uncurry_stoppedProcess_const
    (hX : ProgMeasurable 𝓕 X) (t : ι) :
    StronglyMeasurable <| uncurry (MeasureTheory.stoppedProcess X (fun _ ↦ t)) := by
  let g : ι × Ω → (Set.Iic t) × Ω := fun p ↦ (⟨min p.1 t, min_le_right p.1 t⟩, p.2)
  have hg_meas : Measurable[_, MeasurableSpace.prod inferInstance (𝓕 t)] g := by
    apply Measurable.prodMk _ (measurable_snd.mono le_rfl (𝓕.le t))
    fun_prop
  exact StronglyMeasurable.comp_measurable (hX t) hg_meas

lemma ProgMeasurable.stronglyMeasurable_uncurry_of_isCountablyGenerated_atTop
    [IsCountablyGenerated (atTop : Filter ι)] (hX : ProgMeasurable 𝓕 X) :
    StronglyMeasurable (uncurry X) := by
  rcases exists_seq_monotone_tendsto_atTop_atTop (α := ι) with ⟨t, -, ht_lim⟩
  refine stronglyMeasurable_of_tendsto atTop
    (fun n ↦ stronglyMeasurable_uncurry_stoppedProcess_const hX (t n)) ?_
  rw [tendsto_pi_nhds]
  intro ⟨s, ω⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [ht_lim.eventually (Filter.eventually_ge_atTop s)] with n hn
  simp only [uncurry_apply_pair, MeasureTheory.stoppedProcess]
  rw [← WithTop.coe_min, WithTop.untopA_coe, min_eq_left hn]

private lemma ProgMeasurable.stronglyMeasurable_stoppedValue_stoppedProcess
    [SecondCountableTopology ι] [PseudoMetrizableSpace ι]
    (hX_prog : ProgMeasurable 𝓕 X) (hτ : IsStoppingTime 𝓕 τ)
    (σ : {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}) :
    StronglyMeasurable (stoppedValue
      (MeasureTheory.stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ) σ.1) := by
  have hY_prog := ProbabilityTheory.isStable_progMeasurable X hX_prog τ hτ
  have hY_sm := ProgMeasurable.stronglyMeasurable_uncurry_of_isCountablyGenerated_atTop hY_prog
  let idx_map : Ω → ι := fun ω ↦ (σ.val ω).untop (σ.property.2 ω)
  have h_idx_meas : Measurable[mΩ] idx_map := by
    have h_emb : MeasurableEmbedding (fun x : ι ↦ (x : WithTop ι)) := by
      apply Topology.IsEmbedding.measurableEmbedding WithTop.isEmbedding_coe
      rw [WithTop.range_coe]
      exact IsOpen.measurableSet isOpen_Iio
    apply (MeasurableEmbedding.measurable_comp_iff h_emb).mp
    convert IsStoppingTime.measurable' (m := mΩ) σ.property.1
    ext
    simp [idx_map]
  convert (hY_sm.comp_measurable (h_idx_meas.prodMk measurable_id))
  ext ω
  simp only [stoppedValue, uncurry, Function.comp_apply]
  congr 2
  rw [WithTop.untopA_eq_untop]

end MeasureTheory

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
  HasStronglyMeasurableSupProcess (mΩ:= mΩ) X ∧ ∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖X s ω‖ₑ) P

/-- A stochastic process has locally integrable supremum if it satisfies locally the property that
for all `t`, the random variable `ω ↦ sup_{s ≤ t} ‖X s ω‖` is integrable. -/
def HasLocallyIntegrableSup [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [MeasurableSpace ι]
    (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω := by volume_tac) : Prop :=
  Locally (HasIntegrableSup · P) 𝓕 X P

section Defs

variable [Preorder ι] [Nonempty ι] [MeasurableSpace ι]

/-- A stochastic process $(X_t)$ is of class D (or in the Doob-Meyer class) if it is adapted
and the set $\{X_\tau \mid \tau \text{ is a finite stopping time}\}$ is uniformly integrable. -/
structure ClassD (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop where
  progMeasurable : ProgMeasurable 𝓕 X
  uniformIntegrable : UniformIntegrable
    (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}) ↦ stoppedValue X τ.1) 1 P

/-- A stochastic process $(X_t)$ is of class DL if it is adapted and for all $t$, the set
$\{X_\tau \mid \tau \text{ is a stopping time with } \tau \le t\}$ is uniformly integrable. -/
structure ClassDL (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop where
  progMeasurable : ProgMeasurable 𝓕 X
  uniformIntegrable (t : ι) : UniformIntegrable
    (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ t}) ↦ stoppedValue X τ.1) 1 P

/-- Class D implies Class DL. -/
lemma ClassD.classDL {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} (hX : ClassD X 𝓕 P) :
    ClassDL X 𝓕 P := by
  let f (t : ι) : {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≤ t} →
      {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≠ ⊤} :=
    fun τ => ⟨τ, τ.2.1, fun ω => ne_of_lt
      (lt_of_le_of_lt (τ.2.2 ω) (WithTop.coe_lt_top t))⟩
  exact ⟨hX.1, fun t => hX.2.comp (f t)⟩

end Defs

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ}

section RightContinuous

variable [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] [OrderBot ι]
  [MeasurableSpace ι]

/-- If `{stoppedValue X T : T is a bounded stopping time}` is uniformly integrable, then `X` is
of class D. -/
lemma classD_of_uniformIntegrable_bounded_stoppingTime
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
  exact ⟨hm, (hX.uniformIntegrable_of_ae_tendsto _).comp
    (fun T : {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤} => ⟨stoppedValue X T.1, this T⟩)⟩

variable [NormedSpace ℝ E] [CompleteSpace E]

section Order

variable [PseudoMetrizableSpace ι] [BorelSpace ι] [Lattice E]
  [HasSolidNorm E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [IsFiniteMeasure P]

/-- A nonnegative right-continuous submartingale is of class DL. -/
lemma _root_.MeasureTheory.Submartingale.classDL (hX1 : Submartingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) (hX3 : 0 ≤ X) :
    ClassDL X 𝓕 P := by
  refine ⟨StronglyAdapted.progMeasurable_of_rightContinuous hX1.1 hX2, fun t => ?_⟩
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
  · exact ((stronglyMeasurable_stoppedValue_of_le
      (hX1.1.progMeasurable_of_rightContinuous hX2) hT ht).mono (𝓕.le' t)).aestronglyMeasurable
  · have : stoppedValue X T ≤ᵐ[P] P[stoppedValue X (fun ω => t)|hT.measurableSpace] := by
      suffices lem : stoppedValue X ((fun ω => t) ⊓ T) ≤ᵐ[P]
          P[stoppedValue X (fun ω => t)|hT.measurableSpace] by
        have : T ⊓ (fun _ ↦ t) = T := by simpa [inf_eq_left] using ht
        simpa [inf_comm, this] using lem
      exact hX1.stoppedValue_min_ae_le_condExp 𝓕 hX2
        (ae_of_all _ fun _ ↦ le_rfl) hT (isStoppingTime_const 𝓕 t)
    simp only [stoppedValue_const] at this
    filter_upwards [this] with ω hω
    apply norm_le_norm_of_abs_le_abs
    have p1 : 0 ≤ stoppedValue X T ω := by simpa [stoppedValue] using (hX3 (T ω).untopA ω)
    have p2 : |P[X t|hT.measurableSpace] ω| = P[X t|hT.measurableSpace] ω :=
      abs_of_nonneg (p1.trans hω)
    rwa [← abs_of_nonneg p1, ← p2] at hω

/-- A nonnegative right-continuous submartingale is of class D iff it is uniformly integrable. -/
lemma _root_.MeasureTheory.Submartingale.classD_iff_uniformIntegrable
    (hX1 : Submartingale X 𝓕 P) (hX2 : ∀ ω, RightContinuous (X · ω)) (hX3 : 0 ≤ X) :
    ClassD X 𝓕 P ↔ UniformIntegrable X 1 P := by
  let S := {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}
  let G (T : S) : Ω → E := stoppedValue X T.1
  refine ⟨fun hp => ?_, fun hq => ?_⟩
  · let constT (t : ι) : S := ⟨fun ω : Ω => t, ⟨isStoppingTime_const 𝓕 t, by simp⟩⟩
    have eq : X = G ∘ constT := by ext; simp [constT, G, stoppedValue]
    simpa [eq] using hp.2.comp constT
  · refine classD_of_uniformIntegrable_bounded_stoppingTime ?_ ?_
    · exact hX1.uniformIntegrable_bounded_stoppingTime hX2 hX3 hq
    · exact hX1.1.progMeasurable_of_rightContinuous hX2

end Order

/-- A martingale with right-continuous paths is of class DL. -/
lemma _root_.MeasureTheory.Martingale.classDL [PseudoMetrizableSpace ι] [BorelSpace ι]
    [IsFiniteMeasure P]
    (hX1 : Martingale X 𝓕 P) (hX2 : ∀ ω, RightContinuous (X · ω)) :
    ClassDL X 𝓕 P := by
  let Y := fun t ω ↦ ‖X t ω‖
  have hY_sub : Submartingale Y 𝓕 P := hX1.submartingale_convex_comp
    (convexOn_norm convex_univ) continuous_norm
    (fun t ↦ (hX1.integrable t).norm)
  have hY_cont : ∀ ω, RightContinuous (Y · ω) := fun ω t ↦ (hX2 ω t).norm
  have hY_nonneg : 0 ≤ Y := fun t ω ↦ norm_nonneg _
  have hY_DL : ClassDL Y 𝓕 P := hY_sub.classDL hY_cont hY_nonneg
  have h_prog := hX1.stronglyAdapted.progMeasurable_of_rightContinuous hX2
  refine ⟨h_prog, fun t ↦ ?_⟩
  rw [uniformIntegrable_iff_norm]
  · exact hY_DL.uniformIntegrable t
  · exact fun T ↦ ((stronglyMeasurable_stoppedValue_of_le h_prog T.2.1 T.2.2).mono
      (𝓕.le' t)).aestronglyMeasurable

lemma _root_.MeasureTheory.Martingale.classD_iff_uniformIntegrable (hX1 : Martingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) :
    ClassD X 𝓕 P ↔ UniformIntegrable X 1 P := by
  sorry

end RightContinuous

section ClassDClassDL

/-- If the index type has a top element, then class DL implies class D. -/
lemma ClassDL.classD {ι : Type*} [Preorder ι] {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
    [OrderTop ι] [MeasurableSpace ι]
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

variable [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι]
  {τ : Ω → WithTop ι}

/-- The class of processes that are jointly measurable is stable. -/
lemma isStable_stronglyMeasurable_uncurry [SecondCountableTopology ι] :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ StronglyMeasurable (uncurry X)) := by
  intro X hX τ hτ
  let M : ι × Ω → ι × Ω := fun p ↦ ((min ↑p.1 (τ p.2)).untopA, p.2)
  have hM : Measurable M := (WithTop.measurable_coe.comp measurable_fst).min
    (hτ.measurable'.comp measurable_snd) |>.untopA.prodMk measurable_snd
  have h_eq : uncurry (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ) =
      {p | ⊥ < τ p.2}.indicator (uncurry X ∘ M) := by
    ext ⟨t, ω⟩
    simp [stoppedProcess, Set.indicator_apply, M]
  rw [h_eq]
  exact StronglyMeasurable.indicator (hX.comp_measurable hM)
    (measurableSet_lt measurable_const (hτ.measurable'.comp measurable_snd))

omit [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] in
private lemma stoppedValue_stoppedProcess_dominated_le (X : ι → Ω → E) (hτ : IsStoppingTime 𝓕 τ)
    (σ : {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}) :
    ∃ rho : {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤},
      rho.1 ≤ σ.1 ∧
      ∀ᵐ ω ∂P, ‖stoppedValue (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ) σ.1 ω‖ ≤
        ‖stoppedValue X rho.1 ω‖ := by
  let rho_val := σ.1 ⊓ τ
  have h_rho_stop : IsStoppingTime 𝓕 rho_val := IsStoppingTime.min σ.2.1 hτ
  have h_rho_finite : ∀ ω, rho_val ω ≠ ⊤ :=
    fun ω ↦ ne_of_lt (lt_of_le_of_lt inf_le_left (lt_top_iff_ne_top.mpr (σ.2.2 ω)))
  refine ⟨⟨rho_val, h_rho_stop, h_rho_finite⟩, fun ω ↦ inf_le_left, ?_⟩
  filter_upwards with ω
  simp only [stoppedValue, stoppedProcess, Set.indicator, Set.mem_setOf_eq, rho_val]
  split_ifs with h_bot
  · apply le_of_eq
    congr
    rw [WithTop.untopA_eq_untop, WithTop.coe_untop]
    exact σ.prop.2 ω
  · simp only [norm_zero]; exact norm_nonneg _

lemma HasStronglyMeasurableSupProcess.of_stronglyMeasurable_isCadlag
    (hX1 : StronglyMeasurable (uncurry X)) (hX2 : ∀ ω : Ω, IsCadlag (X · ω)) :
    HasStronglyMeasurableSupProcess (mΩ := mΩ) X := by
  sorry

lemma _root_.MeasureTheory.ProgMeasurable.hasStronglyMeasurableSupProcess_of_isCadlag
    [IsCountablyGenerated (atTop : Filter ι)]
    (hX_prog : ProgMeasurable 𝓕 X) (hX_cadlag : ∀ ω : Ω, IsCadlag (X · ω)) :
    HasStronglyMeasurableSupProcess (mΩ := mΩ) X := by
  refine HasStronglyMeasurableSupProcess.of_stronglyMeasurable_isCadlag ?_ hX_cadlag
  exact ProgMeasurable.stronglyMeasurable_uncurry_of_isCountablyGenerated_atTop hX_prog

lemma isStable_hasStronglyMeasurableSupProcess [SecondCountableTopology ι] :
    IsStable 𝓕 (HasStronglyMeasurableSupProcess (E := E) (mΩ := mΩ) ·) := by
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
    swap; · simp
    apply le_antisymm
    · refine iSup₂_le fun s hst ↦ ?_
      apply le_iSup₂_of_le (min ↑s (τ ω)).untopA ?_
      · exact le_rfl
      · refine WithTop.untopA_mono (by simp) ?_
        gcongr
        exact mod_cast hst
    · refine iSup₂_le fun u hu ↦ ?_
      rw [WithTop.le_untopA_iff (by simp)] at hu
      · apply le_iSup₂_of_le (α := ℝ≥0∞) u ?_
        · rw [min_eq_left]
          · exact le_rfl
          · exact le_trans hu (min_le_right _ _)
        · exact WithTop.coe_le_coe.mp (le_trans hu (min_le_left _ _))
  rw [key_eq]
  exact StronglyMeasurable.indicator (hX.comp_measurable hM)
    (measurableSet_lt measurable_const (hτ.measurable'.comp measurable_snd))

/-- The class of processes with integrable supremum is stable. -/
lemma isStable_hasIntegrableSup [SecondCountableTopology ι] :
    IsStable 𝓕 (HasIntegrableSup (E := E) · P) := by
  refine fun X hX τ hτ ↦ ⟨isStable_hasStronglyMeasurableSupProcess X hX.1 τ hτ, ?_⟩
  refine fun t ↦ ⟨(isStable_hasStronglyMeasurableSupProcess X hX.1 τ hτ).comp_measurable
      (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable, ?_⟩
  have h_bound := (hX.2 t).hasFiniteIntegral
  simp_rw [hasFiniteIntegral_def, enorm_eq_self] at h_bound ⊢
  refine lt_of_le_of_lt (lintegral_mono fun ω ↦ ?_) h_bound
  apply iSup₂_le
  intro s hs
  simp only [stoppedProcess, Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs with h_bot
  · refine le_iSup₂_of_le (min ↑s (τ ω)).untopA ?_ le_rfl
    · rw [WithTop.untopA_le_iff]
      · exact le_trans (min_le_left _ _) (WithTop.coe_le_coe.mpr hs)
      · exact ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  · simp

/-- The class of processes with locally integrable supremum is stable. -/
lemma isStable_hasLocallyIntegrableSup [SecondCountableTopology ι] :
    IsStable 𝓕 (HasLocallyIntegrableSup (E := E) · 𝓕 P) :=
  IsStable.isStable_locally isStable_hasIntegrableSup

/-- The Class D is stable. -/
lemma isStable_classD [PseudoMetrizableSpace ι] [SecondCountableTopology ι] :
    IsStable 𝓕 (ClassD (E := E) · 𝓕 P) := by
  refine fun X ⟨hX_prog, hUI_X⟩ τ hτ ↦ ⟨isStable_progMeasurable X hX_prog τ hτ, ?_⟩
  refine uniformIntegrable_of_dominated hUI_X
    (fun _ ↦ (ProgMeasurable.stronglyMeasurable_stoppedValue_stoppedProcess hX_prog hτ
      _).aestronglyMeasurable) fun σ ↦ ?_
  rcases stoppedValue_stoppedProcess_dominated_le X hτ σ with ⟨rho, _, h_dom⟩
  exact ⟨rho, h_dom⟩

/-- The Class DL is stable. -/
lemma isStable_classDL [SecondCountableTopology ι] [PseudoMetrizableSpace ι] :
    IsStable 𝓕 (ClassDL (E := E) · 𝓕 P) := by
  refine fun X ⟨hX_prog, hUI_X⟩ τ hτ ↦ ⟨isStable_progMeasurable X hX_prog τ hτ, fun t ↦ ?_⟩
  let embed : {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ t} →
              {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤} :=
    fun σ ↦ ⟨σ.1, σ.2.1, fun ω ↦ ne_top_of_le_ne_top WithTop.coe_ne_top (σ.2.2 ω)⟩
  refine uniformIntegrable_of_dominated (hUI_X t) (fun σ ↦ ?_) (fun σ ↦ ?_)
  · exact (ProgMeasurable.stronglyMeasurable_stoppedValue_stoppedProcess hX_prog hτ
      (embed σ)).aestronglyMeasurable
  · rcases stoppedValue_stoppedProcess_dominated_le X hτ (embed σ) with ⟨rho, h_le_sigma, h_dom⟩
    let rho_bounded : {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ ↑t} :=
      ⟨rho.1, rho.2.1, fun ω ↦ le_trans (h_le_sigma ω) (σ.2.2 ω)⟩
    exact ⟨rho_bounded, h_dom⟩

omit [OrderBot ι] in
lemma _root_.MeasureTheory.Integrable.classDL [Nonempty ι] [SecondCountableTopology ι]
    (hX1 : ProgMeasurable 𝓕 X) (hX2 : ∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖X s ω‖ₑ) P) :
    ClassDL X 𝓕 P := by
  refine ⟨hX1, fun t ↦ ?_⟩
  let supX_t : Ω → ℝ≥0∞ := fun ω ↦ ⨆ s ≤ t, ‖X s ω‖ₑ
  have hY : MemLp supX_t 1 P := memLp_one_iff_integrable.mpr (hX2 t)
  -- measurability of each stopped value
  have mX (τ : {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ t}) :
      AEStronglyMeasurable (stoppedValue X τ.1) P :=
    ((stronglyMeasurable_stoppedValue_of_le hX1 τ.2.1 τ.2.2).mono (𝓕.le' t)).aestronglyMeasurable
  -- pointwise domination by the supremum process
  have hDom (τ : {T | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ t}) (ω : Ω) :
      ‖stoppedValue X τ.1 ω‖ₑ ≤ supX_t ω :=
    calc ‖stoppedValue X τ.1 ω‖ₑ
    _ = ‖X (τ.1 ω).untopA ω‖ₑ := by simp[stoppedValue]
    _ ≤ supX_t ω := by
      refine le_iSup_of_le (τ.1 ω).untopA (le_iSup_of_le ?_ le_rfl)
      exact (WithTop.untopA_le_iff (ne_of_lt (lt_of_le_of_lt (τ.2.2 ω) (by simp)))).mpr
        (τ.2.2 ω)
  -- apply domination lemma with p = 1
  exact uniformIntegrable_of_dominated_enorm_singleton hY mX (fun τ ↦ ae_of_all _ (hDom τ))

omit [OrderBot ι] in
lemma HasIntegrableSup.classDL [Nonempty ι] [SecondCountableTopology ι]
    (hX1 : ProgMeasurable 𝓕 X) (hX2 : HasIntegrableSup X P) :
    ClassDL X 𝓕 P :=
  Integrable.classDL hX1 (fun t ↦ hX2.2 t)

lemma HasLocallyIntegrableSup.locally_classDL [SecondCountableTopology ι] [PseudoMetrizableSpace ι]
    (hX1 : Locally (ProgMeasurable 𝓕 ·) 𝓕 X P) (hX2 : HasLocallyIntegrableSup X 𝓕 P) :
    Locally (ClassDL · 𝓕 P) 𝓕 X P := by
  have h_and : Locally (fun X ↦ ProgMeasurable 𝓕 X ∧ HasIntegrableSup X P) 𝓕 X P := by
    rw [locally_and]
    · exact ⟨hX1, hX2⟩
    · exact isStable_progMeasurable
    · exact isStable_hasIntegrableSup
  exact h_and.mono fun X ⟨hX_prog, hX_int⟩ ↦ hX_int.classDL hX_prog

/-- A process of class DL is locally of class D. -/
lemma ClassDL.locally_classD [SecondCountableTopology ι] [PseudoMetrizableSpace ι]
    (hX : ClassDL X 𝓕 P) :
    Locally (ClassD · 𝓕 P) 𝓕 X P := by
  rcases topOrderOrNoTopOrder ι with ha | hb
  · exact locally_of_prop hX.classD
  obtain ⟨v, hv1, hv2⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  refine ⟨fun n ω => v n, ⟨⟨fun n => ?_, ?_⟩, ?_⟩, fun n => ⟨?_, ?_⟩⟩
  · simp [isStoppingTime_const]
  · filter_upwards with ω
    simp only [tendsto_atTop_atTop] at hv2
    refine tendsto_atTop_isLUB (fun _ _ h => mod_cast hv1 h) ⟨top_mem_upperBounds _, fun x hx => ?_⟩
    simp only [top_le_iff, WithTop.eq_top_iff_forall_gt]
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hx
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
    let Y := fun T : A ↦ stoppedValue (stoppedProcess X (fun _ ↦ v n)) T
    refine uniformIntegrable_of_dominated (Y := Y) ?_ (fun T => ?_) (fun T => ?_)
    · let B := {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ v n}
      let f : A → B := fun T => ⟨T.1 ⊓ (fun ω => ↑(v n)), ⟨T.2.1.min_const (v n), by simp⟩⟩
      have : Y = (fun T : B ↦ stoppedValue X T) ∘ f := by
        ext T
        simpa [Y, f] using stoppedValue_stoppedProcess_apply (T.2.2 _)
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
        simp only [hb, Set.setOf_false, Set.indicator_empty, ne_eq, Set.mem_setOf_eq,
          stoppedProcess_const]
        fun_prop
    · by_cases hb : ⊥ < (v n : WithTop ι)
      · simpa [hb, Y] using ⟨T.1, T.2, ae_of_all P fun ω => rfl.le⟩
      · simpa [hb, Y, stoppedValue] using ⟨T.1, T.2⟩

lemma locally_classD_of_locally_classDL {ι : Type*} [ConditionallyCompleteLinearOrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] [SecondCountableTopology ι]
    [NoMaxOrder ι] [MeasurableSpace ι] [BorelSpace ι] [PseudoMetrizableSpace ι]
    {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} [IsFiniteMeasure P]
    (hX : Locally (ClassDL · 𝓕 P) 𝓕 X P) (h𝓕 : 𝓕.IsRightContinuous) :
    Locally (ClassD · 𝓕 P) 𝓕 X P :=
  locally_induction h𝓕 (fun _ ↦ ClassDL.locally_classD) isStable_classD hX

end ClassDClassDL

variable {ι β : Type*}
noncomputable def leastGE [Preorder ι] [OrderBot ι] [InfSet ι] [Preorder β]
    (f : ι → Ω → β) (r : β) : Ω → WithTop ι :=
  hittingAfter f (Set.Ici r) ⊥

instance {ι : Type*} [LE ι] [OrderTop ι] [OrderBot ι] : BoundedOrder ι where
  top := ⊤
  le_top := OrderTop.le_top
  bot := ⊥
  bot_le := OrderBot.bot_le

-- TODO: The assumptions should be refined with those of Début theorem.
lemma isLocalizingSequence_hittingAfter_Ici {ι : Type*} [ConditionallyCompleteLinearOrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι] [CompactIccSpace ι]
    (𝓕 : Filtration ι mΩ) {X : ι → Ω → ℝ} (hX1 : StronglyAdapted 𝓕 X)
    (hX2 : ∀ ω, IsCadlag (X · ω)) (h𝓕 : 𝓕.IsRightContinuous) :
    IsLocalizingSequence 𝓕 (fun n => leastGE X n) P where
  isStoppingTime n := sorry
  mono := by filter_upwards with ω n m hnm using
    hittingAfter_anti X ⊥ (Set.Ici_subset_Ici.2 (Nat.cast_le.2 hnm)) ω
  tendsto_top := by
    filter_upwards with ω
    -- Consider two cases. If `ι` has a top element, then `ι` is compact and the range of `X · ω` is
    -- bounded. Hence, `leastGE X n` is eventually equal to `⊤`.
    rcases topOrderOrNoTopOrder ι with ha | hb
    · have : Bornology.IsBounded (Set.range (X · ω)) := by
        have : Set.Icc (⊥ : ι) ⊤ = Set.univ := Set.Icc_bot_top
        exact Set.image_univ ▸ this ▸ isBounded_image_of_isCadlag_of_isCompact (hX2 ω) isCompact_Icc
      obtain ⟨m, hm⟩ : ∃ (m : ℕ), ∀ i, X i ω ≤ m := by
        obtain ⟨x, hx⟩ := bddAbove_def.1 this.bddAbove
        exact ⟨⌈x⌉₊, fun i => (hx (X i ω) (Set.mem_range_self i)).trans (Nat.le_ceil x)⟩
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [Ioi_mem_atTop m] with n hn
      simpa [leastGE, hittingAfter] using fun i => lt_of_le_of_lt (hm i) (Nat.cast_lt.2 hn)
    -- If `ι` does not have a top element, then it suffices to show that every `i : ι`,
    -- `leastGE X n` is eventually larger than `i`.
    refine nhds_top_basis.tendsto_right_iff.2 fun i hi => ?_
    obtain ⟨c, hc⟩ := (NoTopOrder.to_noMaxOrder ι).exists_gt (i.untop (lt_top_iff_ne_top.1 hi))
    have : Bornology.IsBounded ((X · ω) '' (Set.Icc ⊥ c)) :=
      isBounded_image_of_isCadlag_of_isCompact (hX2 ω) isCompact_Icc
    obtain ⟨m, hm⟩ : ∃ (m : ℕ), ∀ j ≤ c, X j ω ≤ m := by
      obtain ⟨x, hx⟩ := bddAbove_def.1 this.bddAbove
      exact ⟨⌈x⌉₊, fun i hi => (hx (X i ω)
        (Set.mem_image_of_mem _ ⟨bot_le, hi⟩)).trans (Nat.le_ceil x)⟩
    filter_upwards [Ioi_mem_atTop m] with n hn
    simp only [leastGE, hittingAfter]
    by_cases hj : ∃ j, X j ω ∈ Set.Ici ↑n
    · simp_all only [bot_le, true_and, ↓reduceIte]
      have : c ≤ sInf {j | ↑n ≤ X j ω} := by
        refine le_csInf hj fun k hk1 => ?_
        by_contra! hk2
        grind [Nat.cast_le.1 (hk1.trans (hm k hk2.le))]
      exact lt_of_le_of_lt' (mod_cast this) (by simp_all : i < c)
    · grind

lemma sup_stoppedProcess_hittingAfter_Ici_le
    {ι : Type*} [ConditionallyCompleteLinearOrderBot ι] {X : ι → Ω → E} (t : ι) (K : ℝ)
    (hK : 0 ≤ K) (ω : Ω) :
    ⨆ s ≤ t, ‖stoppedProcess X (leastGE  (fun t ω ↦ ‖X t ω‖) K) s ω‖ ≤
    K + Set.indicator {ω | leastGE (fun t ω ↦ ‖X t ω‖) K ω ≤ t}
      (fun ω ↦ ‖stoppedValue X (leastGE (fun t ω ↦ ‖X t ω‖) K) ω‖) ω := by
  let τ := leastGE (fun t ω ↦ ‖X t ω‖) K
  have bound1 (i : ι) (hi : i < τ ω) : ‖X i ω‖ ≤ K := by
    by_contra! h
    have := Exists.intro i (p := fun j => ⊥ ≤ j ∧ ‖X j ω‖ ∈ Set.Ici K) ⟨by simp, by grind⟩
    simp_all only [leastGE, hittingAfter, bot_le, Set.mem_Ici, true_and, ↓reduceIte,
      WithTop.coe_lt_coe, τ]
    have := csInf_le (OrderBot.bddBelow {j | K ≤ ‖X j ω‖}) h.le
    grind
  by_cases ht : ¬ τ ω ≤ t
  · calc
    _ ≤ K := by
      refine ciSup_le fun i => ?_
      by_cases hN : Nonempty (i ≤ t)
      · have hi : i < τ ω := lt_of_le_of_lt (WithTop.coe_le_coe.mpr hN.some) (not_le.mp ht)
        simp_all [stoppedProcess, τ, min_eq_left hi.le]
      · simp_all
    _ ≤ K + Set.indicator {ω | τ ω ≤ t} (fun ω ↦ ‖stoppedValue X τ ω‖) ω := by simp [ht]
  · simp only [not_le, not_lt] at ht
    have : τ ω ≠ ⊤ := by simpa [← WithTop.lt_top_iff_ne_top] using lt_of_le_of_lt ht (by simp)
    have bound2 (i : ι) : ⨆ (_ : i ≤ (τ ω).untopA), ‖X i ω‖ ≤ K + ‖X (τ ω).untopA ω‖ := by
      by_cases hNi : Nonempty (i ≤ (τ ω).untopA)
      · refine ciSup_le fun q => ?_
        rcases lt_or_eq_of_le q with ha | hb
        · linarith [bound1 i ((WithTop.lt_untopA_iff this).mp ha), norm_nonneg (X (τ ω).untopA ω)]
        · simp [hb, hK]
      · simp only [nonempty_prop, not_le] at hNi
        simp only [isEmpty_Prop, not_le, hNi, Real.iSup_of_isEmpty]
        positivity
    calc
    _ ≤ ⨆ s ≤ (τ ω).untopA, ‖X s ω‖ := by
      refine ciSup_le fun i => ?_
      by_cases hN : Nonempty (i ≤ t)
      · by_cases hi : i ≤ τ ω
        · simp_all only [nonempty_prop, stoppedProcess, inf_of_le_left, WithTop.untopD_coe,
            ciSup_unique, τ]
          have : i ≤ (τ ω).untopA := (WithTop.le_untopA_iff this).mpr hi
          have : ‖X i ω‖ ≤ ⨆ (_ : i ≤ (τ ω).untopA), ‖X i ω‖ := by
            refine le_ciSup (f := fun h : i ≤ (τ ω).untopA => ‖X i ω‖) ?_ this
            exact ⟨‖X i ω‖, fun _ _ => by grind⟩
          refine le_trans this (le_ciSup (f := fun i => ⨆ (_ : i ≤ (τ ω).untopA), ‖X i ω‖) ?_ i)
          exact ⟨K + ‖X (τ ω).untopA ω‖, fun y ⟨x, hx⟩ => hx ▸ bound2 x⟩
        · simp_all only [nonempty_prop, not_le, stoppedProcess, τ]
          simp_all only [min_eq_right hi.le, ciSup_unique]
          refine le_trans (le_ciSup (f := fun h : (τ ω).untopA ≤ (τ ω).untopA =>
            ‖X (τ ω).untopA ω‖) ?_ le_rfl) (le_ciSup (f := fun i =>
            ⨆ (_ : i ≤ (τ ω).untopA), ‖X i ω‖) ?_ (τ ω).untopA)
          · exact ⟨‖X (τ ω).untopA ω‖, fun y ⟨x, hx⟩ => by simp [hx]⟩
          · exact ⟨K + ‖X (τ ω).untopA ω‖, fun y ⟨x, hx⟩ => hx ▸ bound2 x⟩
      · simp_all only [nonempty_prop, Real.iSup_of_isEmpty]
        exact Real.iSup_nonneg fun i => Real.iSup_nonneg fun h => norm_nonneg _
    _ ≤ K + ‖X (τ ω).untopA ω‖ := ciSup_le fun i => bound2 i
    _ = K + Set.indicator {ω | τ ω ≤ t} (fun ω ↦ ‖stoppedValue X τ ω‖) ω := by
      simp [stoppedValue, ht]

lemma ClassDL.hasLocallyIntegrableSup {ι : Type*} [Nonempty ι]
    [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] [PseudoMetrizableSpace ι]
    [MeasurableSpace ι] [BorelSpace ι]
    [IsFiniteMeasure P]
    {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX1 : ∀ ω, IsCadlag (X · ω)) (hX2 : ClassDL X 𝓕 P) (h𝓕 : 𝓕.IsRightContinuous) :
    HasLocallyIntegrableSup X 𝓕 P := by
  rcases hX2 with ⟨hX2, hX3⟩
  let Y : ι → Ω → ℝ := fun t ω ↦ ‖X t ω‖
  have hY1 : StronglyAdapted 𝓕 Y := hX2.stronglyAdapted.norm
  have hY2 : ∀ (ω : Ω), IsCadlag (Y · ω) := by
    refine fun ω ↦ ⟨?_, fun i ↦ ?_⟩
    · exact Function.RightContinuous.continuous_comp continuous_norm (hX1 ω).1
    · obtain ⟨l, hl⟩ := (hX1 ω).2 i
      exact ⟨‖l‖, (continuous_norm.tendsto l).comp hl⟩
  let τ : ℕ → Ω → WithTop ι := (fun n ↦ hittingAfter Y (Set.Ici n) ⊥)
  have hτ : IsLocalizingSequence 𝓕 τ P := isLocalizingSequence_hittingAfter_Ici 𝓕 hY1 hY2 h𝓕
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  have hX4 := fun (t : ι) (ω : Ω) ↦ sup_stoppedProcess_hittingAfter_Ici_le (X := X) t n (by simp) ω
  have hX6 :=  hX2.hasStronglyMeasurableSupProcess_of_isCadlag hX1
  let Xs : ι → Ω → E := (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))
  have hX1s : ∀ ω,  IsCadlag fun t ↦ Xs t ω := isStable_isCadlag X (hX1) (τ n) (hτ.isStoppingTime n)
  let rhs := fun (t : ι) (ω : Ω) ↦
    ↑n + {ω | hittingAfter (fun t ω ↦ ‖X t ω‖) (Set.Ici ↑n) ⊥ ω ≤ ↑t}.indicator
    (fun ω ↦ ‖stoppedValue X (hittingAfter (fun t ω ↦ ‖X t ω‖) (Set.Ici ↑n) ⊥) ω‖) ω
  constructor
  · refine ProgMeasurable.hasStronglyMeasurableSupProcess_of_isCadlag (𝓕 := 𝓕) ?_ hX1s
    exact isStable_progMeasurable (ι := ι) (E := E) X hX2 (τ n) (hτ.isStoppingTime n)
  · intro t
    let dom := fun ω ↦ ↑n + ‖stoppedValue X (τ n ⊓ fun _ ↦ t) ω‖
    let σ : Ω → WithTop ι := (τ n) ⊓ (fun _ ↦ t : Ω → WithTop ι)
    have hσ : IsStoppingTime 𝓕 σ := (hτ.isStoppingTime n).min (isStoppingTime_const 𝓕 t)
    have hσ_le : σ ≤ (fun _ ↦ t : Ω → WithTop ι) := inf_le_right
    refine Integrable.mono_enorm (g := dom) ?_ ?_ ?_
    · change Integrable ((fun ω : Ω ↦ (n : ℝ)) + (fun ω ↦ ‖stoppedValue X (τ n ⊓ fun x ↦ ↑t) ω‖)) P
      refine Integrable.add (integrable_const (n : ℝ)) ( ?_)
      rcases hX3 t with ⟨h_meas, _, ⟨C, h_bound⟩⟩
      refine ⟨(h_meas ⟨σ, ⟨hσ, hσ_le⟩ ⟩).norm , ?_⟩
      · simp_rw [HasFiniteIntegral, enorm_norm, ← eLpNorm_one_eq_lintegral_enorm]
        exact lt_of_le_of_lt (h_bound ⟨σ, ⟨hσ, hσ_le⟩⟩) ENNReal.coe_lt_top
    · apply StronglyMeasurable.aestronglyMeasurable
      have h_stopped := isStable_hasStronglyMeasurableSupProcess X hX6 (τ n) (hτ.isStoppingTime n)
      exact h_stopped.comp_measurable (measurable_const.prodMk measurable_id)
    · filter_upwards with ω
      have h_LE (ω : Ω): 0 ≤ dom ω :=
        add_nonneg (Nat.cast_nonneg' n) (norm_nonneg (stoppedValue X (τ n ⊓ fun x ↦ ↑t) ω))
      have h_bdd_subtype : BddAbove (Set.range fun (u : {x // x ≤ t}) ↦
            ‖stoppedProcess X (τ n) u ω‖) := by
        let S := Set.Icc ⊥ t
        have hS_compact : IsCompact S := isCompact_Icc
        have h_subset : (Set.range fun (u : {x // x ≤ t}) ↦ ‖stoppedProcess X (τ n) u ω‖) ⊆
                        (fun x ↦ ‖X x ω‖) '' S := by
          rintro _ ⟨u, rfl⟩
          simp only [stoppedProcess, Set.mem_image]
          refine ⟨((τ n ⊓ fun _ ↦ ↑u) ω).untopA, ⟨bot_le, ?_ ⟩, by rw [min_comm, Pi.inf_apply]⟩
          · apply le_trans _ u.2
            rw [WithTop.untopA_eq_untop, WithTop.untop_le_iff]
            · exact inf_le_right
            · exact ne_top_of_le_ne_top (WithTop.coe_ne_top) inf_le_right
        apply BddAbove.mono h_subset
        have h_metric_bdd := isBounded_image_of_isCadlag_of_isCompact (hX1 ω) hS_compact
        obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ (X · ω) '' S, ‖x‖ ≤ C := by
          rw [Metric.isBounded_iff_subset_ball (0 : E)] at h_metric_bdd
          rcases h_metric_bdd with ⟨C, h_subset_ball⟩
          refine ⟨C, fun x hx ↦ ?_⟩
          specialize h_subset_ball hx
          rw [Metric.mem_ball, dist_zero_right] at h_subset_ball
          exact le_of_lt h_subset_ball
        use C
        rintro y ⟨x, hx, rfl⟩
        exact hC _ (Set.mem_image_of_mem _ hx)
      have h_val_le_rhs (s : ι) (hs : s ≤ t) : ‖stoppedProcess X (τ n) s ω‖ ≤ rhs t ω := by
        apply le_trans ?_ (hX4 t ω)
        have h_bdd_nested :
            BddAbove (Set.range fun s ↦ ⨆ (_ : s ≤ t), ‖stoppedProcess X (τ n) s ω‖) := by
          obtain ⟨M, hM⟩ := h_bdd_subtype
          refine ⟨max M 0, fun y hy ↦ ?_⟩
          obtain ⟨s', rfl⟩ := hy
          by_cases hs' : s' ≤ t
          · calc ⨆ (_ : s' ≤ t), ‖stoppedProcess X (τ n) s' ω‖
                = ‖stoppedProcess X (τ n) s' ω‖ := ciSup_pos hs'
              _ ≤ M := hM ⟨⟨s', hs'⟩, rfl⟩
              _ ≤ max M 0 := le_max_left M 0
          · show (fun s ↦ ⨆ (_ : s ≤ t), ‖stoppedProcess X (τ n) s ω‖) s' ≤ max M 0
            have : IsEmpty (s' ≤ t) := ⟨fun h => hs' h⟩
            simp only [Real.iSup_of_isEmpty, le_sup_right]
        refine le_ciSup_of_le h_bdd_nested s ?_
        refine le_ciSup_of_le ?_ hs le_rfl
        use ‖stoppedProcess X (τ n) s ω‖
        rintro _ ⟨_, rfl⟩
        exact le_rfl
      have h_rhs_le_dom : rhs t ω ≤ dom ω := by
        simp only [rhs, dom, add_le_add_iff_left]
        rw [Set.indicator]
        split_ifs with h
        · simp only [Set.mem_setOf_eq] at h
          simp only [stoppedValue, Pi.inf_apply]
          rw [min_eq_left h]
        · simp only [norm_nonneg]
      calc
        ⨆ s, ⨆ (_ : s ≤ t), ‖stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n) s ω‖ₑ
      _ ≤ ⨆ s, ⨆ (_ : s ≤ t), ‖stoppedProcess X (τ n) s ω‖ₑ := by
        gcongr with s hs
        simp only [stoppedProcess, Set.indicator, Set.mem_setOf_eq]
        split_ifs <;> simp
      _ ≤ ENNReal.ofReal (rhs t ω) := by
        rw [iSup_subtype']
        simp only [iSup_le_iff, Subtype.forall]
        intro s hs
        rw [← enorm_norm, Real.enorm_of_nonneg]
        · exact ENNReal.ofReal_le_ofReal <| h_val_le_rhs s hs
        · exact norm_nonneg (stoppedProcess X (τ n) s ω)
      _ ≤ ENNReal.ofReal (dom ω) := ENNReal.ofReal_le_ofReal h_rhs_le_dom
      _ ≤ ‖dom ω‖ₑ := by rw [← Real.enorm_of_nonneg <| h_LE ω]

end LinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [MeasurableSpace ι] [SecondCountableTopology ι] [DenselyOrdered ι] [NoMaxOrder ι] [BorelSpace ι]
  [PseudoMetrizableSpace ι] [IsFiniteMeasure P] {𝓕 : Filtration ι mΩ}

lemma hasLocallyIntegrableSup_of_locally_classDL (h𝓕 : 𝓕.IsRightContinuous)
    (hX1 : Locally (fun X ↦ ∀ ω, IsCadlag (X · ω)) 𝓕 X P) (hX2 : Locally (ClassDL · 𝓕 P) 𝓕 X P) :
    HasLocallyIntegrableSup X 𝓕 P :=
  locally_induction₂ h𝓕 (fun _ hCad hDL ↦ ClassDL.hasLocallyIntegrableSup hCad hDL h𝓕)
     isStable_isCadlag isStable_classDL isStable_hasIntegrableSup hX1 hX2

lemma locally_classDL_iff_hasLocallyIntegrableSup (h𝓕 : 𝓕.IsRightContinuous)
    (hX_prog : Locally (ProgMeasurable 𝓕 ·) 𝓕 X P)
    (hX1 : Locally (fun X ↦ ∀ ω, IsCadlag (X · ω)) 𝓕 X P) :
    Locally (ClassDL · 𝓕 P) 𝓕 X P ↔ HasLocallyIntegrableSup X 𝓕 P :=
  ⟨hasLocallyIntegrableSup_of_locally_classDL h𝓕 hX1, fun h_sup ↦ h_sup.locally_classDL hX_prog⟩

lemma locally_classD_iff_locally_classDL (h𝓕 : 𝓕.IsRightContinuous) :
    Locally (ClassD · 𝓕 P) 𝓕 X P ↔ Locally (ClassDL · 𝓕 P) 𝓕 X P :=
  ⟨fun hD ↦ hD.mono fun _ hXD ↦ hXD.classDL, fun hDL ↦ locally_classD_of_locally_classDL hDL h𝓕⟩

lemma locally_classD_iff_hasLocallyIntegrableSup (h𝓕 : 𝓕.IsRightContinuous)
    (hX_prog : Locally (ProgMeasurable 𝓕 ·) 𝓕 X P)
    (hX1 : Locally (fun X ↦ ∀ ω, IsCadlag (X · ω)) 𝓕 X P) :
    Locally (ClassD · 𝓕 P) 𝓕 X P ↔ HasLocallyIntegrableSup X 𝓕 P := by
  rw [locally_classD_iff_locally_classDL h𝓕,
      locally_classDL_iff_hasLocallyIntegrableSup h𝓕 hX_prog hX1]

/-- A right-continuous, nonnegative submartingale is locally of class D. -/
lemma _root_.MeasureTheory.Submartingale.locally_classD
    [NormedSpace ℝ E] [CompleteSpace E] [Lattice E] [HasSolidNorm E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    (h𝓕 : 𝓕.IsRightContinuous) (hX : Submartingale X 𝓕 P) (hC : ∀ ω, RightContinuous (X · ω))
    (hX_nonneg : 0 ≤ X) :
    Locally (ClassD · 𝓕 P) 𝓕 X P := by
  rw [locally_classD_iff_locally_classDL h𝓕]
  exact locally_of_prop (hX.classDL hC hX_nonneg)

/-- A nonnegative local submartingale is locally of class D. -/
lemma IsLocalSubmartingale.locally_classD [NormedSpace ℝ E] [CompleteSpace E] [Lattice E]
    [HasSolidNorm E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
    [Approximable 𝓕 P]
    (h𝓕 : 𝓕.IsRightContinuous) (hX : IsLocalSubmartingale X 𝓕 P) (hX_nonneg : 0 ≤ X) :
    Locally (ClassD · 𝓕 P) 𝓕 X P := by
  refine locally_induction h𝓕 ?_ isStable_classD ?_
    (p := fun X : ι → Ω → E ↦ Submartingale X 𝓕 P ∧ (∀ ω, IsCadlag (X · ω)) ∧ 0 ≤ X)
  · intro X ⟨hX, hXC, hX_nonneg⟩
    exact hX.locally_classD h𝓕 (fun ω ↦ (hXC ω).right_continuous) hX_nonneg
  · simp_rw [← and_assoc]
    rw [locally_and]
    · constructor
      · exact hX
      · exact locally_of_prop hX_nonneg
    · exact isStable_submartingale
    · intro X hX τ hτ
      -- todo: stoppedProcess_nonneg
      unfold stoppedProcess
      intro i ω
      simp only [Pi.zero_apply, Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs with h
      · exact hX _ _
      · rfl

end ConditionallyCompleteLinearOrderBot

end ProbabilityTheory
