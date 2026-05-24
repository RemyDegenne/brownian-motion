/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.Jensen
public import Mathlib.Probability.Martingale.OptionalSampling

/-!
# Uniform integrability

-/

@[expose] public section

open scoped NNReal ENNReal Topology
open Filter

namespace MeasureTheory

variable {ι κ Ω E F : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A family of random variables is uniformly integrable iff its `L¹` tails above `c` tend to
zero uniformly in the index. -/
lemma uniformIntegrable_iff_tendsto_iSup_eLpNorm_indicator_norm [IsFiniteMeasure μ]
    [NormedAddCommGroup E] {X : κ → Ω → E} (hX : ∀ k, AEStronglyMeasurable (X k) μ) :
    UniformIntegrable X 1 μ ↔
      Tendsto (fun c : ℝ≥0 =>
        ⨆ k, eLpNorm ({ω | c ≤ ‖X k ω‖₊}.indicator (X k)) 1 μ) atTop (𝓝 0) := by
  let tail : ℝ≥0 → ℝ≥0∞ := fun c ↦ ⨆ i : κ, eLpNorm ({ω | c ≤ ‖X i ω‖₊}.indicator (X i)) 1 μ
  -- We first show that this tail function is antitone so that convergence at `atTop` can be checked
  -- by `ENNReal.tendsto_atTop_zero_iff_le_of_antitone htail_mono`.
  have htail_anti : Antitone tail := by
    refine fun c d hcd => iSup_mono fun k => eLpNorm_mono_enorm fun ω => ?_
    by_cases hω : d ≤ ‖X k ω‖₊
    · simp [hω, hcd.trans hω]
    · simp [hω]
  rw [uniformIntegrable_iff (refl 1) ENNReal.one_ne_top]
  refine ⟨fun ⟨_, htail⟩ => ?_, fun htail => ⟨hX, fun ε hε => ?_⟩⟩
  · rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone htail_anti]
    intro ε hε
    by_cases hε_top : ε = ∞
    · exact ⟨0, by simp [hε_top]⟩
    · have hε_real_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
      obtain ⟨C, hC⟩ := htail ε.toReal hε_real_pos
      exact ⟨C, iSup_le_iff.2 fun i => (hC i).trans_eq (ENNReal.ofReal_toReal hε_top)⟩
  · rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone htail_anti] at htail
    obtain ⟨C, hC⟩ := htail (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
    exact ⟨C, fun i => (le_iSup _ i).trans hC⟩

lemma uniformIntegrable_iff_tendsto_iSup_setIntegral_norm [IsFiniteMeasure μ]
    [NormedAddCommGroup E] {X : κ → Ω → E} (hX : ∀ k, AEStronglyMeasurable (X k) μ) :
    UniformIntegrable X 1 μ ↔
      Tendsto (fun c : ℝ => ⨆ k, ∫ ω in {ω | c ≤ ‖X k ω‖₊}, ‖X k ω‖ ∂μ) atTop (𝓝 0) := by
  sorry

lemma uniformIntegrable_iff_tendsto_iSup_setIntegral_of_nonneg [IsFiniteMeasure μ]
    {X : κ → Ω → ℝ} (hX : ∀ k, AEStronglyMeasurable (X k) μ) (hnoneg : ∀ k, 0 ≤ᵐ[μ] X k) :
    UniformIntegrable X 1 μ ↔
      Tendsto (fun c : ℝ => ⨆ k, ∫ ω in {ω | c ≤ X k ω}, X k ω ∂μ) atTop (𝓝 0) := by
  sorry

/-- Uniform integrability makes the `Lp` mass on sets of vanishing measure vanish uniformly in
the index. -/
lemma UnifIntegrable.tendsto_iSup_eLpNorm_indicator_of_tendsto_measure_zero
    [NormedAddCommGroup E] {X : ι → Ω → E} {p : ℝ≥0∞} (hX : UnifIntegrable X p μ)
    {l : Filter κ} {s : κ → Set Ω} (hs : ∀ᶠ k in l, MeasurableSet (s k))
    (hμs : Tendsto (fun k ↦ μ (s k)) l (𝓝 0)) :
    Tendsto (fun k ↦ ⨆ i, eLpNorm ((s k).indicator (X i)) p μ) l (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  by_cases hε_top : ε = ∞
  · simp [hε_top]
  · obtain ⟨δ, hδ_pos, hδ⟩ := hX (ENNReal.toReal_pos hε.ne' hε_top)
    filter_upwards [hs, (ENNReal.tendsto_nhds_zero.1 hμs)
      (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ_pos)] with k hsk hμk
      using iSup_le_iff.2 fun i => (hδ i (s k) hsk hμk).trans_eq (ENNReal.ofReal_toReal hε_top)

lemma UniformIntegrable.tendsto_iSup_eLpNorm_indicator_of_tendsto_measure_zero
    [NormedAddCommGroup E] {X : ι → Ω → E} {p : ℝ≥0∞} (hX : UniformIntegrable X p μ)
    {l : Filter κ} {s : κ → Set Ω} (hs : ∀ᶠ k in l, MeasurableSet (s k))
    (hμs : Tendsto (fun k ↦ μ (s k)) l (𝓝 0)) :
    Tendsto (fun k ↦ ⨆ i, eLpNorm ((s k).indicator (X i)) p μ) l (𝓝 0) :=
  hX.unifIntegrable.tendsto_iSup_eLpNorm_indicator_of_tendsto_measure_zero hs hμs

/-- The supremum of the integrals of `‖X i‖` over sets of vanishing measure tends to zero. -/
lemma UniformIntegrable.tendsto_iSup_setIntegral_norm_of_tendsto_measure_zero
    [NormedAddCommGroup E] {X : ι → Ω → E} (hX : UniformIntegrable X 1 μ)
    {l : Filter κ} {s : κ → Set Ω} (hs : ∀ᶠ k in l, MeasurableSet (s k))
    (hμs : Tendsto (fun k ↦ μ (s k)) l (𝓝 0)) :
    Tendsto (fun k ↦ ⨆ i, ENNReal.ofReal (∫ ω in s k, ‖X i ω‖ ∂μ)) l (𝓝 0) := by
  refine (hX.tendsto_iSup_eLpNorm_indicator_of_tendsto_measure_zero hs hμs).congr' ?_
  filter_upwards [hs] with k hsk
  congr with i
  -- We probably should create a lemma that converts `eLpNorm` into
  -- `ENNReal.ofReal (∫ (x : α), ‖f x‖ ∂μ)`
  simp [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm
    ((memLp_one_iff_integrable.1 (hX.memLp i)).indicator hsk),
    norm_indicator_eq_indicator_norm, integral_indicator hsk]

lemma UniformIntegrable.add [NormedAddCommGroup E] {X Y : ι → Ω → E} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hX : UniformIntegrable X p μ) (hY : UniformIntegrable Y p μ) :
    UniformIntegrable (X + Y) p μ := by
  refine ⟨fun _ ↦ (hX.1 _).add (hY.1 _), ?_, ?_⟩
  · rcases hX with ⟨hX₁, hX₂, hX₃⟩
    rcases hY with ⟨hY₁, hY₂, hY₃⟩
    exact hX₂.add hY₂ hp hX₁ hY₁
  · obtain ⟨C_X, hC_X⟩ := hX.2.2
    obtain ⟨C_Y, hC_Y⟩ := hY.2.2
    exact ⟨C_X + C_Y,
      fun i ↦ le_trans (eLpNorm_add_le (hX.1 i) (hY.1 i) hp) (add_le_add (hC_X i) (hC_Y i))⟩

lemma UniformIntegrable.neg [NormedAddCommGroup E] {X : ι → Ω → E} {p : ℝ≥0∞}
    (hX : UniformIntegrable X p μ) :
    UniformIntegrable (-X) p μ := by
  refine ⟨fun i => (hX.1 i).neg, hX.unifIntegrable.neg, ?_⟩
  obtain ⟨C, hC⟩ := hX.2.2
  exact ⟨C, by simp [hC]⟩

lemma uniformIntegrable_of_dominated [NormedAddCommGroup E] [NormedAddCommGroup F]
    {X : ι → Ω → E} {Y : κ → Ω → F} {p : ℝ≥0∞}
    (hY : UniformIntegrable Y p μ) (mX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hX : ∀ i, ∃ j, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ ‖Y j ω‖) :
    UniformIntegrable X p μ := by
  refine ⟨mX, fun ε hε ↦ ?_, ?_⟩
  · obtain ⟨δ, hδ, h⟩ := hY.2.1 hε
    refine ⟨δ, hδ, fun i s hs hμs ↦ let ⟨j, hj⟩ := hX i
      le_trans (eLpNorm_mono_ae ?_) <| h j s hs hμs⟩
    filter_upwards [hj] with ω hω
    rw [Set.indicator]
    split_ifs with hmem
    · rw [Set.indicator_of_mem hmem]
      exact hω
    · simp [Set.indicator_of_notMem hmem]
  · obtain ⟨C, hC⟩ := hY.2.2
    exact ⟨C, fun i ↦ let ⟨j, hj⟩ := hX i
      le_trans (eLpNorm_mono_ae hj) <| hC j⟩

lemma UniformIntegrable.norm [NormedAddCommGroup E] {X : ι → Ω → E} {p : ℝ≥0∞}
    (hY : UniformIntegrable X p μ) :
    UniformIntegrable (fun t ω ↦ ‖X t ω‖) p μ := by
  refine uniformIntegrable_of_dominated hY ?_ (fun i ↦ ⟨i, by simp⟩)
  exact fun i ↦ (UniformIntegrable.aestronglyMeasurable hY i).norm

lemma uniformIntegrable_iff_norm [NormedAddCommGroup E] {X : ι → Ω → E} {p : ℝ≥0∞}
    (mX : ∀ i, AEStronglyMeasurable (X i) μ) :
    UniformIntegrable X p μ ↔ UniformIntegrable (fun t ω ↦ ‖X t ω‖) p μ := by
  refine ⟨UniformIntegrable.norm, fun hNorm ↦ uniformIntegrable_of_dominated hNorm mX ?_⟩
  exact fun i ↦ ⟨i, by simp⟩

lemma uniformIntegrable_of_dominated_singleton [NormedAddCommGroup E] {X : ι → Ω → E} {Y : Ω → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hY : MemLp Y p μ)
    (mX : ∀ i, AEStronglyMeasurable (X i) μ) (hX : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ Y ω) :
    UniformIntegrable X p μ :=
  uniformIntegrable_of_dominated (κ := ι) (uniformIntegrable_const hp hp_ne_top hY) mX
    <| fun i ↦ ⟨i, by filter_upwards [hX i] with ω hω using hω.trans <| Real.le_norm_self _⟩

lemma norm_le_toReal_of_enorm_le [NormedAddCommGroup E] {r : ℝ≥0∞} (hr : r ≠ ∞) {x : E}
    (hle : ‖x‖ₑ ≤ r) :
    ‖x‖ ≤ r.toReal := by
  -- `‖x‖ₑ = ENNReal.ofReal ‖x‖`; translate the bound via `ofReal_le_iff_le_toReal`.
  have hx : ENNReal.ofReal ‖x‖ ≤ r := by simpa using hle
  exact (ENNReal.ofReal_le_iff_le_toReal hr).1 hx

lemma MemLp.enorm_ae_lt_top [TopologicalSpace E] [ContinuousENorm E]
    {f : Ω → E} {p : ℝ≥0∞} (hlp : MemLp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    ∀ᵐ x ∂μ, ‖f x‖ₑ < ∞ := by
  let f_to_p := fun x ↦ ‖f x‖ₑ ^ p.toReal
  have hf : Integrable f_to_p μ :=
    MemLp.integrable_enorm_rpow hlp hp_ne_zero hp_ne_top
  have hfin : ∀ᵐ ω ∂μ, f_to_p ω ≠ ∞ := by
    refine (ae_lt_top' hf.1.aemeasurable (ne_of_lt hf.2)).mono ?_
    intro ω hω; exact ne_of_lt hω
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hpos_ne : p.toReal ≠ 0 := hpos.ne'
  refine hfin.mono ?_
  intro x hx
  have hne : ‖f x‖ₑ ≠ ∞ := by
    by_contra htop
    have hpow : (∞ : ℝ≥0∞) ^ p.toReal = ∞ := ENNReal.top_rpow_of_pos hpos
    have : f_to_p x = ∞ := by simpa [f_to_p, htop] using hpow
    exact hx this
  exact lt_of_le_of_ne le_top hne

lemma uniformIntegrable_of_dominated_enorm_singleton [NormedAddCommGroup E] {X : ι → Ω → E}
    {Y : Ω → ℝ≥0∞} (hY : MemLp Y 1 μ)
    (mX : ∀ i, AEStronglyMeasurable (X i) μ) (hX : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ₑ ≤ Y ω) :
    UniformIntegrable X 1 μ := by
  have : ∫⁻ x, Y x ∂μ ≠ ⊤ := by
    simpa [eLpNorm_one_eq_lintegral_enorm, enorm_eq_self] using ne_of_lt hY.2
  have hY_fin : ∀ᵐ ω ∂μ, Y ω < ∞ := ae_lt_top' hY.1.aemeasurable this
  have hY_real : MemLp (fun ω => (Y ω).toReal) 1 μ := mem_L1_toReal_of_lintegral_ne_top
    hY.1.aemeasurable this
  refine uniformIntegrable_of_dominated_singleton (by simp) (by simp) hY_real mX fun i => ?_
  filter_upwards [hX i, hY_fin] with ω hbound hfin
  exact norm_le_toReal_of_enorm_le hfin.ne hbound

lemma UniformIntegrable.condExp' {X : ι → Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [IsFiniteMeasure μ] (hX : UniformIntegrable X 1 μ)
    {𝓕 : κ → MeasurableSpace Ω} (h𝓕 : ∀ i, 𝓕 i ≤ mΩ) :
    UniformIntegrable (fun (p : ι × κ) ↦ μ[X p.1 | 𝓕 p.2]) 1 μ := by
  have hX' := hX
  obtain ⟨hX1, hX2, ⟨C, hC⟩⟩ := hX
  refine ⟨fun p ↦ (stronglyMeasurable_condExp.mono (h𝓕 p.2)).aestronglyMeasurable, ?_,
    ⟨C, fun p ↦ (eLpNorm_condExp_le_eLpNorm le_rfl (X p.1)).trans (hC p.1)⟩⟩
  refine unifIntegrable_of le_rfl (by simp)
    (fun p ↦ (stronglyMeasurable_condExp.mono (h𝓕 p.2)).aestronglyMeasurable) fun ε hε ↦ ?_
  obtain ⟨δ, δ_pos, hδ⟩ := hX2 hε
  lift δ to ℝ≥0 using δ_pos.le
  have hδ' : δ ≠ 0 := by
    convert δ_pos.ne'
    simp
  refine ⟨(⨆ i, eLpNorm (X i) 1 μ).toNNReal / δ + 1, fun p ↦ ?_⟩
  rw [eLpNorm_congr_ae (condExp_indicator ?_ ?_).symm]
  rotate_left
  · exact memLp_one_iff_integrable.1 (hX'.memLp p.1)
  · exact stronglyMeasurable_const.measurableSet_le stronglyMeasurable_condExp.nnnorm
  grw [eLpNorm_condExp_le_eLpNorm le_rfl, hδ]
  · exact stronglyMeasurable_const.measurableSet_le <|
      stronglyMeasurable_condExp.mono (h𝓕 p.2) |>.nnnorm
  calc
  _ ≤ eLpNorm μ[X p.1 | 𝓕 p.2] 1 μ / ((⨆ i, eLpNorm (X i) 1 μ).toNNReal / δ + 1) := by
    simp_rw [← ENNReal.coe_le_coe, ← enorm_eq_nnnorm]
    grw [meas_ge_le_lintegral_div (by fun_prop) (by simp) (by simp),
      ← eLpNorm_one_eq_lintegral_enorm]
    norm_cast
  _ ≤ eLpNorm μ[X p.1 | 𝓕 p.2] 1 μ / ((⨆ i, eLpNorm (X i) 1 μ) / δ) := by
    grw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top (by simp) <| iSup_le hC),
      ENNReal.div_le_div_left (a := (⨆ i, eLpNorm (X i) 1 μ) / δ)]
    simp
  _ = eLpNorm μ[X p.1 | 𝓕 p.2] 1 μ / (⨆ i, eLpNorm (X i) 1 μ) * δ := by
    rw [← ENNReal.div_mul _ (Or.inr <| ENNReal.coe_ne_zero.2 hδ') (by simp)]
  _ ≤ 1 * δ := by
    grw [eLpNorm_condExp_le_eLpNorm le_rfl]
    gcongr
    exact ENNReal.div_le_one_of_le <| le_iSup (α := ℝ≥0∞) _ p.1
  _ = _ := by simp

lemma UnifIntegrable.comp {κ : Type*} [NormedAddCommGroup E]
    {X : ι → Ω → E} {p : ℝ≥0∞} (hX : UnifIntegrable X p μ) (f : κ → ι) :
    UnifIntegrable (X ∘ f) p μ := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hX hε
  exact ⟨δ, ⟨hδ, fun i ↦ h (f i)⟩⟩

lemma UniformIntegrable.comp {κ : Type*} [NormedAddCommGroup E]
    {X : ι → Ω → E} {p : ℝ≥0∞} (hX : UniformIntegrable X p μ) (f : κ → ι) :
    UniformIntegrable (X ∘ f) p μ := by
  obtain ⟨hX1, hX2, ⟨C, hC⟩⟩ := hX
  exact ⟨fun _ ↦ hX1 _, hX2.comp f, ⟨C, fun i ↦ hC (f i)⟩⟩

lemma UniformIntegrable.condExp {X : ι → Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [IsFiniteMeasure μ] (hX : UniformIntegrable X 1 μ) {𝓕 : ι → MeasurableSpace Ω}
    (h𝓕 : ∀ i, 𝓕 i ≤ mΩ) :
    UniformIntegrable (fun i ↦ μ[X i | 𝓕 i]) 1 μ :=
  (hX.condExp' h𝓕).comp (fun i ↦ (i, i))

variable {ι : Type*} [LinearOrder ι] [OrderBot ι] [Countable ι] [TopologicalSpace ι]
  [OrderTopology ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕]

lemma Martingale.ae_eq_condExp_of_isStoppingTime {X : ι → Ω → E}
    (hX : Martingale X 𝓕 μ) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) {n : ι}
    (hτ_le : ∀ ω, τ ω ≤ n) :
    stoppedValue X τ =ᵐ[μ] μ[X n | hτ.measurableSpace] :=
  stoppedValue_ae_eq_condExp_of_le hX (isStoppingTime_const 𝓕 n) hτ (n := n) hτ_le
    (fun _ ↦ le_rfl)

lemma Martingale.uniformIntegrable_stoppedValue {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration μ 𝓕] [IsFiniteMeasure μ]
    (hX : Martingale X 𝓕 μ) (τ : ℕ → Ω → WithTop ι) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ι} (hτ_le : ∀ i ω, τ i ω ≤ n) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ :=
  (((uniformIntegrable_subsingleton (f := fun _ : Unit ↦ X n) le_rfl (by simp)
    (fun _ ↦ memLp_one_iff_integrable.2 <| hX.integrable n)).condExp'
    (fun i ↦ (hτ i).measurableSpace_le)).ae_eq <| fun m ↦
      (hX.ae_eq_condExp_of_isStoppingTime (hτ m.2) (hτ_le m.2)).symm).comp (fun i ↦ ((), i))

lemma Submartingale.uniformIntegrable_stoppedValue {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration μ 𝓕]
    (hX : Submartingale X 𝓕 μ) (τ : ℕ → Ω → WithTop ι) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ι} (hτ_le : ∀ i ω, τ i ω ≤ n) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ :=
  sorry

omit [Countable ι]

variable [FirstCountableTopology ι]

lemma Martingale.uniformIntegrable_stoppedValue_of_countable_range
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕] [IsFiniteMeasure μ]
    (hX : Martingale X 𝓕 μ) (τ : ℕ → Ω → WithTop ι) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ι} (hτ_le : ∀ i ω, τ i ω ≤ n) (hτ_countable : ∀ i, (Set.range <| τ i).Countable) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ :=
  (((uniformIntegrable_subsingleton (f := fun _ : Unit ↦ X n) le_rfl (by simp)
    (fun _ ↦ memLp_one_iff_integrable.2 <| hX.integrable n)).condExp'
    (fun i ↦ (hτ i).measurableSpace_le)).ae_eq fun _ ↦
      (hX.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hτ _) (hτ_le _)
      (hτ_countable _)).symm).comp (fun i ↦ ((), i))

lemma Martingale.integrable_stoppedValue_of_countable_range
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕] [IsFiniteMeasure μ]
    (hX : Martingale X 𝓕 μ) (τ : Ω → WithTop ι) (hτ : IsStoppingTime 𝓕 τ)
    {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) (hτ_countable : (Set.range τ).Countable) :
    Integrable (stoppedValue X τ) μ := by
  rw [← memLp_one_iff_integrable]
  exact (hX.uniformIntegrable_stoppedValue_of_countable_range (fun _ ↦ τ)
    (fun _ ↦ hτ) (fun _ _ ↦ hτ_le _) (fun _ ↦ hτ_countable)).memLp 0

lemma seq_tendsto_ae_bounded
    {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {f : ℕ → α → β} {g : α → β} {C : ℝ≥0∞} (p : ℝ≥0∞) (bound : ∀ n, eLpNorm (f n) p μ ≤ C)
    (h_tendsto : ∀ᵐ (x : α) ∂μ, Tendsto (fun n => f n x) atTop (nhds (g x)))
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) : eLpNorm g p μ ≤ C := by
  calc
    _ ≤ atTop.liminf (fun (n : ℕ) => eLpNorm (f n) p μ) :=
      Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => hf n) g h_tendsto
    _ ≤ C := by
      refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
      obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hb
      exact le_trans (hn n (by linarith)) (bound n)

lemma tendstoInMeasure_bounded
    {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → β} {g : α → β} {C : ℝ≥0∞} (p : ℝ≥0∞) (bound : ∀ i, eLpNorm (f i) p μ ≤ C)
    (h_tendsto : TendstoInMeasure μ f u g)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) : eLpNorm g p μ ≤ C := by
  obtain ⟨l, hl⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact seq_tendsto_ae_bounded p (fun n => bound (l n)) hl.2 (fun n => hf (l n))

end MeasureTheory
