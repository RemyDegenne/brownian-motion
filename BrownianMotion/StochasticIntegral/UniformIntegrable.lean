/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.Adapted
public import BrownianMotion.Auxiliary.Jensen
public import BrownianMotion.Auxiliary.StoppedProcess
public import BrownianMotion.Auxiliary.StoppedValue
public import BrownianMotion.StochasticIntegral.Cadlag
public import Mathlib.Probability.Martingale.OptionalSampling

/-!
# Uniform integrability

-/

public section

open Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace MeasureTheory

section UniformIntegrable

variable {ι κ Ω E F : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- An analogue of `uniformIntegrable_iff`, but the nonstrict inequality in `C ≤ ‖X i x‖₊` is
replaced by a strict inequality. -/
theorem uniformIntegrable_iff' [IsFiniteMeasure μ] [NormedAddCommGroup E] {X : κ → Ω → E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    UniformIntegrable X p μ ↔
      (∀ i, AEStronglyMeasurable (X i) μ) ∧
        ∀ ε > 0, ∃ C : ℝ≥0, ∀ i, eLpNorm ({x | C < ‖X i x‖₊}.indicator (X i)) p μ ≤ ε := by
  rw [uniformIntegrable_iff hp hp']
  refine ⟨fun h ↦ ⟨h.1, fun ε hε ↦ ?_⟩, fun h ↦ ⟨h.1, fun ε hε ↦ ?_⟩⟩
  · obtain ⟨C, hC⟩ := h.2 ε hε
    refine ⟨C, fun i ↦ (eLpNorm_mono ((h.1 i).indicator₀
      (nullMeasurableSet_lt aemeasurable_const (h.1 i).nnnorm.aemeasurable)) fun x ↦ ?_).trans
      (hC i)⟩
    by_cases hx : C < ‖X i x‖₊
    · simp [hx, hx.le]
    · simp [hx]
  · obtain ⟨C, hC⟩ := h.2 ε hε
    refine ⟨C + 1, fun i ↦ (eLpNorm_mono ((h.1 i).indicator₀
      (nullMeasurableSet_le aemeasurable_const (h.1 i).nnnorm.aemeasurable)) fun x ↦ ?_).trans
      (hC i)⟩
    by_cases hx : C + 1 ≤ ‖X i x‖₊
    · have hx' : C < ‖X i x‖₊ := (lt_add_of_pos_right C zero_lt_one).trans_le hx
      simp [hx, hx']
    · simp [hx]

/-- A family of random variables is uniformly integrable iff its `L¹` tails above `c` tend to
zero uniformly in the index. -/
lemma uniformIntegrable_iff_tendsto_iSup_eLpNorm_indicator_norm [IsFiniteMeasure μ]
    [NormedAddCommGroup E] {X : κ → Ω → E} (hX : ∀ k, AEStronglyMeasurable (X k) μ) :
    UniformIntegrable X 1 μ ↔
      Tendsto (fun c : ℝ≥0 =>
        ⨆ k, eLpNorm ({ω | c < ‖X k ω‖₊}.indicator (X k)) 1 μ) atTop (𝓝 0) := by
  let tail : ℝ≥0 → ℝ≥0∞ := fun c ↦ ⨆ i : κ, eLpNorm ({ω | c < ‖X i ω‖₊}.indicator (X i)) 1 μ
  -- We first show that this tail function is antitone so that convergence at `atTop` can be checked
  -- by `ENNReal.tendsto_atTop_zero_iff_le_of_antitone htail_mono`.
  have htail_anti : Antitone tail := by
    refine fun c d hcd => iSup_mono fun k => eLpNorm_mono_enorm ((hX k).indicator₀
      (nullMeasurableSet_lt aemeasurable_const (hX k).nnnorm.aemeasurable)) fun ω => ?_
    by_cases hω : d < ‖X k ω‖₊
    · simp [hω, hcd.trans_lt hω]
    · simp [hω]
  rw [uniformIntegrable_iff' le_rfl ENNReal.one_ne_top]
  refine ⟨fun ⟨_, htail⟩ => ?_, fun htail => ⟨hX, fun ε hε => ?_⟩⟩
  · refine (ENNReal.tendsto_atTop_zero_iff_le_of_antitone htail_anti).2 fun ε hε => ?_
    obtain ⟨C, hC⟩ := htail ε hε
    exact ⟨C, iSup_le hC⟩
  · rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone htail_anti] at htail
    obtain ⟨C, hC⟩ := htail ε hε
    exact ⟨C, fun i => (le_iSup
      (f := fun i ↦ eLpNorm ({ω | C < ‖X i ω‖₊}.indicator (X i)) 1 μ) i).trans hC⟩

/-- A helper lemma for `uniformIntegrable_iff_tendsto_iSup_setIntegral_norm`. -/
lemma eLpNorm_indicator_tail_eq_setIntegral_norm [NormedAddCommGroup E] {f : Ω → E}
    (hf : Integrable f μ) (c : ℝ≥0) :
    eLpNorm ({ω | c < ‖f ω‖₊}.indicator f) 1 μ =
      ENNReal.ofReal (∫ ω in {ω | c < ‖f ω‖}, ‖f ω‖ ∂μ) := by
  have hs : NullMeasurableSet {ω | c < ‖f ω‖} μ :=
    aestronglyMeasurable_const.nullMeasurableSet_lt hf.aestronglyMeasurable.norm
  have hs_eq : {ω | c < ‖f ω‖₊} = {ω | c < ‖f ω‖} := by ext; simp [NNReal.coe_lt_coe.symm]
  rw [hs_eq, eLpNorm_one_eq_lintegral_enorm (hf.aestronglyMeasurable.indicator₀ hs),
    ← ofReal_integral_norm_eq_lintegral_enorm (hf.indicator₀ hs)]
  simp [norm_indicator_eq_indicator_norm, integral_indicator₀ hs]

/-- Use integral of norm instead of `eLpNorm` in the characterization of `UniformIntegrable`. -/
lemma uniformIntegrable_iff_tendsto_nnReal_iSup_setIntegral_norm [IsFiniteMeasure μ]
    [NormedAddCommGroup E] {X : κ → Ω → E} (hX : ∀ k, AEStronglyMeasurable (X k) μ)
    (hXint : ∀ k, Integrable (X k) μ) :
    UniformIntegrable X 1 μ ↔
      Tendsto (fun c : ℝ≥0 =>
        ⨆ k, ENNReal.ofReal (∫ ω in {ω | c < ‖X k ω‖}, ‖X k ω‖ ∂μ)) atTop (𝓝 0) := by
  rw [uniformIntegrable_iff_tendsto_iSup_eLpNorm_indicator_norm hX]
  apply tendsto_congr'
  filter_upwards with c using iSup_congr
    fun i => eLpNorm_indicator_tail_eq_setIntegral_norm (hXint i) c

/-- A helper lemma for `uniformIntegrable_iff_tendsto_iSup_setIntegral_of_nonneg`. -/
lemma eLpNorm_indicator_tail_eq_setIntegral_of_nonneg {f : Ω → ℝ}
    (hf : Integrable f μ) (hnonneg : 0 ≤ᵐ[μ] f) (c : ℝ≥0) :
    eLpNorm ({ω | c < ‖f ω‖₊}.indicator f) 1 μ =
      ENNReal.ofReal (∫ ω in {ω | c < f ω}, f ω ∂μ) := by
  rw [eLpNorm_indicator_tail_eq_setIntegral_norm hf]
  apply congrArg
  calc
  _ = ∫ (ω : Ω) in {ω | c < f ω}, ‖f ω‖ ∂μ := by
    apply setIntegral_congr_set
    filter_upwards [hnonneg] with ω hω
    simp [abs_of_nonneg hω]
  _ = _ := by
    refine setIntegral_congr_fun₀
      (aestronglyMeasurable_const.nullMeasurableSet_lt hf.aestronglyMeasurable) fun ω hω => ?_
    exact Real.norm_of_nonneg (c.2.trans hω.le)

/-- Use integral instead of `eLpNorm` in the characterization of `UniformIntegrable` for nonnegative
functions. -/
lemma uniformIntegrable_iff_tendsto_nnReal_iSup_setIntegral_of_nonneg [IsFiniteMeasure μ]
    {X : κ → Ω → ℝ} (hX : ∀ k, AEStronglyMeasurable (X k) μ) (hnonneg : ∀ k, 0 ≤ᵐ[μ] X k)
    (hXint : ∀ k, Integrable (X k) μ) :
    UniformIntegrable X 1 μ ↔
      Tendsto (fun c : ℝ≥0 =>
        ⨆ k, ENNReal.ofReal (∫ ω in {ω | c < X k ω}, X k ω ∂μ)) atTop (𝓝 0) := by
  rw [uniformIntegrable_iff_tendsto_iSup_eLpNorm_indicator_norm hX]
  apply tendsto_congr'
  filter_upwards with c using iSup_congr
    fun i => eLpNorm_indicator_tail_eq_setIntegral_of_nonneg (hXint i) (hnonneg i) c

lemma UniformIntegrable.add [NormedAddCommGroup E] {X Y : ι → Ω → E} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hX : UniformIntegrable X p μ) (hY : UniformIntegrable Y p μ) :
    UniformIntegrable (X + Y) p μ := by
  obtain ⟨hX₁, C_X, hC_X⟩ := hX
  obtain ⟨hY₁, C_Y, hC_Y⟩ := hY
  exact ⟨hX₁.add hY₁, C_X + C_Y,
    fun i ↦ (eLpNorm_add_le hp).trans (add_le_add (hC_X i) (hC_Y i))⟩

lemma UniformIntegrable.neg [NormedAddCommGroup E] {X : ι → Ω → E} {p : ℝ≥0∞}
    (hX : UniformIntegrable X p μ) :
    UniformIntegrable (-X) p μ := by
  obtain ⟨hX₁, C, hC⟩ := hX
  exact ⟨hX₁.neg, C, by simp [hC]⟩

lemma UniformIntegrable.sub [NormedAddCommGroup E] {X Y : ι → Ω → E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hX : UniformIntegrable X p μ) (hY : UniformIntegrable Y p μ) :
    UniformIntegrable (X - Y) p μ := by
  simpa [sub_eq_add_neg] using hX.add hp hY.neg

lemma uniformIntegrable_of_dominated [NormedAddCommGroup E] [NormedAddCommGroup F]
    {X : ι → Ω → E} {Y : κ → Ω → F} {p : ℝ≥0∞}
    (hY : UniformIntegrable Y p μ) (mX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hX : ∀ i, ∃ j, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ ‖Y j ω‖) :
    UniformIntegrable X p μ := by
  choose j hj using hX
  obtain ⟨hY₁, C, hC⟩ := hY
  refine ⟨unifIntegrable_iff.2 fun ε hε ↦ ?_,
    C, fun i ↦ (eLpNorm_mono_ae (mX i) (hj i)).trans (hC (j i))⟩
  obtain ⟨δ, hδ, h⟩ := unifIntegrable_iff.1 hY₁ ε hε
  exact ⟨δ, hδ, fun i s hs ↦
    (eLpNorm_mono_ae (mX i).restrict (ae_restrict_of_ae (hj i))).trans (h (j i) s hs)⟩

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
    refine (ae_lt_top' hf.aemeasurable (ne_of_lt hf.2)).mono ?_
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
    simpa [eLpNorm_one_eq_lintegral_enorm hY.aestronglyMeasurable, enorm_eq_self] using
      hY.eLpNorm_ne_top
  have hY_fin : ∀ᵐ ω ∂μ, Y ω < ∞ := ae_lt_top' hY.aemeasurable this
  have hY_real : MemLp (fun ω => (Y ω).toReal) 1 μ := mem_L1_toReal_of_lintegral_ne_top
    hY.aemeasurable this
  refine uniformIntegrable_of_dominated_singleton (by simp) (by simp) hY_real mX fun i => ?_
  filter_upwards [hX i, hY_fin] with ω hbound hfin
  exact norm_le_toReal_of_enorm_le hfin.ne hbound

lemma UniformIntegrable.condExp' {X : ι → Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (hX : UniformIntegrable X 1 μ)
    {𝓕 : κ → MeasurableSpace Ω} (h𝓕 : ∀ i, 𝓕 i ≤ mΩ) :
    UniformIntegrable (fun (p : ι × κ) ↦ μ[X p.1 | 𝓕 p.2]) 1 μ := by
  have hX' := hX
  obtain ⟨hX2, C, hC⟩ := hX
  refine ⟨?_, ⟨C, fun p ↦ (eLpNorm_condExp_le_eLpNorm (X p.1) le_rfl).trans (hC p.1)⟩⟩
  refine unifIntegrable_of le_rfl (by simp)
    (fun p ↦ (stronglyMeasurable_condExp.mono (h𝓕 p.2)).aestronglyMeasurable) fun ε hε ↦ ?_
  obtain ⟨δ', δ'_pos, hδ⟩ := unifIntegrable_iff.1 hX2 ε hε
  obtain ⟨δ, δ_pos, hδδ'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 δ'_pos
  have hδ' : δ ≠ 0 := by simpa using δ_pos.ne'
  refine ⟨(⨆ i, eLpNorm (X i) 1 μ).toNNReal / δ + 1, fun p ↦ ?_⟩
  rw [eLpNorm_congr_ae (condExp_indicator ?_ ?_).symm]
  rotate_left
  · exact memLp_one_iff_integrable.1 (hX'.memLp p.1)
  · exact stronglyMeasurable_const.measurableSet_le stronglyMeasurable_condExp.nnnorm
  have hs : MeasurableSet
      {x | (⨆ i, eLpNorm (X i) 1 μ).toNNReal / δ + 1 ≤ ‖μ[X p.1 | 𝓕 p.2] x‖₊} :=
    stronglyMeasurable_const.measurableSet_le <|
      stronglyMeasurable_condExp.mono (h𝓕 p.2) |>.nnnorm
  grw [eLpNorm_condExp_le_eLpNorm _ le_rfl,
    eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
  refine hδ _ _ (le_trans ?_ hδδ'.le)
  calc
  _ ≤ eLpNorm μ[X p.1 | 𝓕 p.2] 1 μ / ((⨆ i, eLpNorm (X i) 1 μ).toNNReal / δ + 1) := by
    simp_rw [← ENNReal.coe_le_coe, ← enorm_eq_nnnorm]
    grw [meas_ge_le_lintegral_div (by fun_prop) (by simp) (by simp),
      ← eLpNorm_one_eq_lintegral_enorm
        (stronglyMeasurable_condExp.mono (h𝓕 p.2)).aestronglyMeasurable]
    norm_cast
  _ ≤ eLpNorm μ[X p.1 | 𝓕 p.2] 1 μ / ((⨆ i, eLpNorm (X i) 1 μ) / δ) := by
    grw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top (by simp) <| iSup_le hC),
      ENNReal.div_le_div_left (a := (⨆ i, eLpNorm (X i) 1 μ) / δ)]
    simp
  _ = eLpNorm μ[X p.1 | 𝓕 p.2] 1 μ / (⨆ i, eLpNorm (X i) 1 μ) * δ := by
    rw [← ENNReal.div_mul _ (Or.inr <| ENNReal.coe_ne_zero.2 hδ') (by simp)]
  _ ≤ 1 * δ := by
    grw [eLpNorm_condExp_le_eLpNorm _ le_rfl]
    gcongr
    exact ENNReal.div_le_one_of_le <| le_iSup (fun i ↦ eLpNorm (X i) 1 μ) p.1
  _ = _ := by simp

lemma UniformIntegrable.comp {κ : Type*} [NormedAddCommGroup E]
    {X : ι → Ω → E} {p : ℝ≥0∞} (hX : UniformIntegrable X p μ) (f : κ → ι) :
    UniformIntegrable (X ∘ f) p μ := by
  obtain ⟨hX2, C, hC⟩ := hX
  exact ⟨hX2.comp f, C, fun i ↦ hC (f i)⟩

lemma UniformIntegrable.condExp {X : ι → Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (hX : UniformIntegrable X 1 μ) {𝓕 : ι → MeasurableSpace Ω}
    (h𝓕 : ∀ i, 𝓕 i ≤ mΩ) :
    UniformIntegrable (fun i ↦ μ[X i | 𝓕 i]) 1 μ :=
  (hX.condExp' h𝓕).comp (fun i ↦ (i, i))

/-- If a a family of random variables in bounded in `Lp` for `p > q ≥ 1`, then it is uniformly
integrable in `Lq`. -/
lemma uniformIntegrable_of_eLpNorm_le {X : ι → Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [IsFiniteMeasure μ] (p q : ℝ≥0∞) (hp : q < p) (hq : 1 ≤ q) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hX2 : ∀ i, eLpNorm (X i) p μ ≤ C) :
    UniformIntegrable X q μ := by
  have hX1 i : AEStronglyMeasurable (X i) μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top ((hX2 i).trans_lt hC.lt_top).ne
  lift C to ℝ≥0 using hC
  have hq' : q ≠ ∞ := by
    contrapose hp
    simp [hp]
  have hpq_top : q⁻¹ - p⁻¹ ≠ ∞ :=
    ENNReal.sub_ne_top (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hq).ne')
  have hr : 0 < (q⁻¹ - p⁻¹).toReal :=
    ENNReal.toReal_pos (tsub_pos_of_lt (ENNReal.inv_lt_inv.2 hp)).ne' hpq_top
  refine ⟨unifIntegrable_iff'.2 fun ε hε ↦ ?_, ?_⟩
  · have {s : Set Ω} (hs : MeasurableSet s) (t : ι) :
        eLpNorm (s.indicator (X t)) q μ ≤
          (eLpNorm (X t) p μ) * (μ s) ^ (q⁻¹ - p⁻¹).toReal := calc
      eLpNorm (s.indicator (X t)) q μ
        = eLpNorm ((s.indicator (fun _ ↦ 1 : Ω → ℝ)) • (X t)) q μ := by
        congr with ω
        simp [Set.indicator]
      _ ≤ eLpNorm (s.indicator (fun _ ↦ 1 : Ω → ℝ)) (q⁻¹ - p⁻¹)⁻¹ μ *
          eLpNorm (X t) p μ := by
        have : (q⁻¹ - p⁻¹)⁻¹.HolderTriple p q := ⟨by
          rw [inv_inv, tsub_add_cancel_of_le (by simp [hp.le])]⟩
        exact eLpNorm_smul_le_mul_eLpNorm (aestronglyMeasurable_const.indicator hs) (hX1 t)
      _ = (eLpNorm (X t) p μ) * (μ s) ^ (q⁻¹ - p⁻¹).toReal := by
        rw [eLpNorm_indicator_const hs.nullMeasurableSet, mul_comm]
        · simp
        · exact ENNReal.inv_ne_zero.2 hpq_top
        · simpa [tsub_eq_zero_iff_le]
    refine ⟨(ε / (C + 1)) ^ (q⁻¹ - p⁻¹).toReal⁻¹,
      ENNReal.rpow_pos_of_nonneg (ENNReal.div_pos hε.ne' (by simp)) (by positivity),
      fun t s hs hμs ↦ ?_⟩
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
    calc eLpNorm (s.indicator (X t)) q μ
      _ ≤ eLpNorm (X t) p μ * μ s ^ (q⁻¹ - p⁻¹).toReal := this hs t
      _ ≤ (C + 1) * ((ε / (C + 1)) ^ (q⁻¹ - p⁻¹).toReal⁻¹) ^ (q⁻¹ - p⁻¹).toReal := by
        gcongr
        exact (hX2 t).trans le_self_add
      _ = (C + 1) * (ε / (C + 1)) := by rw [ENNReal.rpow_inv_rpow hr.ne']
      _ ≤ ε := ENNReal.mul_div_le
  · let (eq := D_def) D : ℝ≥0∞ := μ Set.univ ^ (1 / q.toReal - 1 / p.toReal)
    have hD : D ≠ ⊤ := by
      refine ENNReal.rpow_ne_top_of_nonneg ?_ (by simp)
      by_cases hp' : p = ∞
      · simp [hp']
      simp only [one_div, sub_nonneg]
      rw [inv_le_inv₀, ENNReal.toReal_le_toReal hq' hp']
      · exact hp.le
      · exact ENNReal.toReal_pos (zero_le.trans_lt hp |>.ne') hp'
      · exact ENNReal.toReal_pos (zero_lt_one.trans_le hq |>.ne') hq'
    lift D to ℝ≥0 using hD with E
    refine ⟨E * C, fun t ↦ ?_⟩
    grw [eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp.le (hX1 t), hX2]
    simp [D_def, mul_comm]

variable {ι : Type*} [LinearOrder ι] [OrderBot ι] [Countable ι] [TopologicalSpace ι]
  [OrderTopology ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕]

lemma Martingale.uniformIntegrable_stoppedValue {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration μ 𝓕]
    (hX : Martingale X 𝓕 μ) (τ : ℕ → Ω → WithTop ι) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ι} (hτ_le : ∀ i ω, τ i ω ≤ n) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ :=
  (((uniformIntegrable_subsingleton (f := fun _ : Unit ↦ X n) le_rfl (by simp)
    (fun _ ↦ memLp_one_iff_integrable.2 <| hX.integrable n)).condExp'
    (fun i ↦ (hτ i).measurableSpace_le)).ae_eq <| fun m ↦
      (hX.stoppedValue_ae_eq_condExp_of_le_const (hτ m.2) (hτ_le m.2)).symm).comp (fun i ↦ ((), i))

lemma Submartingale.uniformIntegrable_stoppedValue {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration μ 𝓕]
    (hX : Submartingale X 𝓕 μ) (τ : ℕ → Ω → WithTop ι) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ι} (hτ_le : ∀ i ω, τ i ω ≤ n) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ :=
  sorry

omit [Countable ι]

variable [FirstCountableTopology ι]

lemma Martingale.uniformIntegrable_stoppedValue_of_countable_range
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕]
    (hX : Martingale X 𝓕 μ) (τ : ℕ → Ω → WithTop ι) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ι} (hτ_le : ∀ i ω, τ i ω ≤ n) (hτ_countable : ∀ i, (Set.range <| τ i).Countable) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ :=
  (((uniformIntegrable_subsingleton (f := fun _ : Unit ↦ X n) le_rfl (by simp)
    (fun _ ↦ memLp_one_iff_integrable.2 <| hX.integrable n)).condExp'
    (fun i ↦ (hτ i).measurableSpace_le)).ae_eq fun _ ↦
      (hX.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hτ _) (hτ_le _)
      (hτ_countable _)).symm).comp (fun i ↦ ((), i))

lemma Martingale.integrable_stoppedValue_of_countable_range
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕]
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
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) : eLpNorm g p μ ≤ C :=
  Lp.eLpNorm_le_of_ae_tendsto (.of_forall bound) hf
    (aestronglyMeasurable_of_tendsto_ae atTop hf h_tendsto) h_tendsto

end UniformIntegrable

section Martingale

/-! ### Uniformly integrable martingales -/

variable {ι Ω E : Type*} [LinearOrder ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ι mΩ} {X Y : ι → Ω → E} {τ : Ω → WithTop ι} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [TopologicalSpace ι]

/-- A càdlàg uniformly integrable martingale converges. -/
theorem Martingale.ae_tendsto_limitProcess
    (hX1 : Martingale X 𝓕 P) (hX2 : UniformIntegrable X 1 P)
    (hX3 : ∀ ω, IsRightContinuous (X · ω)) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
  sorry

@[to_fun limitProcess_fun_add]
lemma Martingale.limitProcess_add [Nonempty ι]
    (hX1 : Martingale X 𝓕 P) (hX2 : UniformIntegrable X 1 P)
    (hX3 : ∀ ω, IsRightContinuous (X · ω))
    (hY1 : Martingale Y 𝓕 P) (hY2 : UniformIntegrable Y 1 P)
    (hY3 : ∀ ω, IsRightContinuous (Y · ω)) :
    𝓕.limitProcess (X + Y) P =ᵐ[P] 𝓕.limitProcess X P + 𝓕.limitProcess Y P := by
  apply 𝓕.limitProcess_ae_eq
    (𝓕.stronglyMeasurable_limitProcess.add 𝓕.stronglyMeasurable_limitProcess)
  filter_upwards [hX1.ae_tendsto_limitProcess hX2 hX3,
    hY1.ae_tendsto_limitProcess hY2 hY3] with ω h1 h2 using h1.add h2

@[to_fun limitProcess_fun_sub]
lemma Martingale.limitProcess_sub [Nonempty ι]
    (hX1 : Martingale X 𝓕 P) (hX2 : UniformIntegrable X 1 P)
    (hX3 : ∀ ω, IsRightContinuous (X · ω))
    (hY1 : Martingale Y 𝓕 P) (hY2 : UniformIntegrable Y 1 P)
    (hY3 : ∀ ω, IsRightContinuous (Y · ω)) :
    𝓕.limitProcess (X - Y) P =ᵐ[P] 𝓕.limitProcess X P - 𝓕.limitProcess Y P := by
  apply 𝓕.limitProcess_ae_eq
    (𝓕.stronglyMeasurable_limitProcess.sub 𝓕.stronglyMeasurable_limitProcess)
  filter_upwards [hX1.ae_tendsto_limitProcess hX2 hX3,
    hY1.ae_tendsto_limitProcess hY2 hY3] with ω h1 h2 using h1.sub h2

/-- For a càdlàg uniformly integrable martingale, `P[X ∞ | 𝓕 t] = X t`. -/
theorem Martingale.condExp_limitProcess_ae_eq
    (hX1 : Martingale X 𝓕 P) (hX2 : UniformIntegrable X 1 P)
    (hX3 : ∀ ω, IsRightContinuous (X · ω)) (t : ι) :
    P[𝓕.limitProcess X P | 𝓕 t] =ᵐ[P] X t := by
  sorry

/-- For a càdlàg uniformly integrable martingale and a stopping time `τ`, `P[X ∞ | 𝓕 τ] = X τ`. -/
theorem Martingale.condExp_limitProcess_ae_eq'
    (hX1 : Martingale X 𝓕 P) (hX2 : UniformIntegrable X 1 P)
    (hX3 : ∀ ω, IsRightContinuous (X · ω)) (hτ : IsStoppingTime 𝓕 τ) :
    P[𝓕.limitProcess X P | hτ.measurableSpace] =ᵐ[P] 𝓕.stoppedValue' X τ P := by
  sorry

/-- For a càdlàg uniformly integrable martingale, `⨆ t, ‖X t‖ₑ ≤ ‖X ∞‖ₑ`. -/
lemma iSup_eLpNorm_le_eLpNorm_limitProcess [CompleteSpace E]
    (hX1 : Martingale X 𝓕 P) (hX2 : UniformIntegrable X 1 P) (hX3 : ∀ ω, IsRightContinuous (X · ω))
     {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ⨆ t, eLpNorm (X t) p P ≤ eLpNorm (𝓕.limitProcess X P) p P := by
  refine iSup_le fun t ↦ ?_
  rw [eLpNorm_congr_ae (hX1.condExp_limitProcess_ae_eq hX2 hX3 t).symm]
  exact eLpNorm_condExp_le_eLpNorm _ hp

lemma Filtration.limitProcess_stoppedProcess [OrderBot ι] [OrderTopology ι]
    [SecondCountableTopology ι]
    (hX1 : Martingale X 𝓕 P) (hX2 : UniformIntegrable X 1 P)
    (hX3 : ∀ ω, _root_.IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) :
    𝓕.limitProcess (stoppedProcess X τ) P =ᵐ[P] 𝓕.stoppedValue' X τ P := by
  borelize ι E
  apply 𝓕.limitProcess_ae_eq
  · exact 𝓕.stronglyMeasurable_stoppedValue'
      (hX1.stronglyAdapted.isStronglyProgressive_of_rightContinuous hX3) hX3 hτ |>.mono
      hτ.measurableSpace_le'
  filter_upwards [hX1.ae_tendsto_limitProcess hX2 hX3] with ω h
  cases h1 : τ ω with
  | top => simpa [h1]
  | coe t =>
    simp only [h1, WithTop.coe_inj, stoppedProcess_of_eq_coe, Filtration.stoppedValue'_of_eq_coe]
    exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨t, fun s hs ↦ by simp [hs]⟩)

end Martingale

end MeasureTheory
