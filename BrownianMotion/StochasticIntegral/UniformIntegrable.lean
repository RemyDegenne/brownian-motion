/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.ENNReal
import Mathlib.Probability.Martingale.OptionalSampling
import BrownianMotion.Auxiliary.Jensen

/-!
# Uniform integrability

-/

open scoped NNReal ENNReal
open Filter

namespace MeasureTheory

variable {ι κ Ω E F : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

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

private lemma norm_le'_of_enorm_le [NormedAddCommGroup E] {r : ℝ≥0∞} (hr : r ≠ ∞) {x : E} :
    ‖x‖ₑ ≤ r → ‖x‖ ≤ r.toReal := by
  intro hle
  -- `‖x‖ₑ = ENNReal.ofReal ‖x‖`; translate the bound via `ofReal_le_iff_le_toReal`.
  have hx : ENNReal.ofReal ‖x‖ ≤ r := by simpa using hle
  exact (ENNReal.ofReal_le_iff_le_toReal hr).1 hx

private lemma MemLp.enorm_ae_finite [TopologicalSpace E] [ContinuousENorm E]
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
    {Y : Ω → ℝ≥0∞} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hY : MemLp Y p μ)
    (mX : ∀ i, AEStronglyMeasurable (X i) μ) (hX : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ₑ ≤ Y ω) :
    UniformIntegrable X p μ := by
  have hp_ne_zero : p ≠ 0 := by exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  -- `Y` is a.e. finite, so we can switch to `toReal`.
  have hY_fin : ∀ᵐ ω ∂μ, Y ω < ∞ :=
    MemLp.enorm_ae_finite (E := ℝ≥0∞) (f := Y) hY hp_ne_zero hp_ne_top
  have hY_real : MemLp (fun ω => (Y ω).toReal) p μ := by
    -- a.e. measurability
    have h_meas : AEStronglyMeasurable (fun ω => (Y ω).toReal) μ :=
      (hY.1.aemeasurable.ennreal_toReal).aestronglyMeasurable
    -- identify the p-moment of `toReal ∘ Y` with that of `Y`, using a.e. finiteness
    have hp_ne_top' : p ≠ ∞ := hp_ne_top
    have hp_ne_zero' : p ≠ 0 := hp_ne_zero
    have h_eq_integrand : ∀ᵐ ω ∂μ,
        ‖(Y ω).toReal‖ₑ ^ p.toReal = ‖Y ω‖ₑ ^ p.toReal := by
      filter_upwards [hY_fin] with ω hfin
      have hne : Y ω ≠ ∞ := hfin.ne
      -- for finite Y ω, toReal/ ofReal cancel
      have hto : ENNReal.ofReal (Y ω).toReal = Y ω := ENNReal.ofReal_toReal hne
      have hnonneg : 0 ≤ (Y ω).toReal := by
        have h := ENNReal.toReal_nonneg (a := Y ω)
        exact h
      calc
        ‖(Y ω).toReal‖ₑ ^ p.toReal
            = (ENNReal.ofReal (Y ω).toReal) ^ p.toReal := by
              simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg hnonneg]
        _ = (Y ω) ^ p.toReal := by simp [hto]
    -- compare eLpNorm via the integral expressions
    have h_eq_norm : eLpNorm (fun ω => (Y ω).toReal) p μ = eLpNorm Y p μ := by
      have h1 := eLpNorm_eq_lintegral_rpow_enorm (μ := μ) (f := fun ω => (Y ω).toReal)
        hp_ne_zero' hp_ne_top'
      have h2 := eLpNorm_eq_lintegral_rpow_enorm (μ := μ) (f := Y) hp_ne_zero' hp_ne_top'
      -- rewrite integrals using h_eq_integrand
      have hlin :
        (∫⁻ x, ‖(Y x).toReal‖ₑ ^ p.toReal ∂μ) = (∫⁻ x, ‖Y x‖ₑ ^ p.toReal ∂μ) :=
        lintegral_congr_ae h_eq_integrand
      -- assemble
      have hp_pos : (1 / p.toReal) ≠ 0 := by
        have hpos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero' hp_ne_top'
        exact one_div_ne_zero hpos.ne'
      calc
        eLpNorm (fun ω => (Y ω).toReal) p μ
            = (∫⁻ x, ‖(Y x).toReal‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
                simpa using h1
        _ = (∫⁻ x, ‖Y x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by simp [hlin]
        _ = eLpNorm Y p μ := by simpa using h2.symm
    exact ⟨h_meas, h_eq_norm.trans_lt hY.2⟩
  refine uniformIntegrable_of_dominated_singleton hp hp_ne_top hY_real mX ?_
  intro i
  filter_upwards [hX i, hY_fin] with ω hbound hfin
  -- Convert the `ℝ≥0∞`-bound to a real bound.
  exact norm_le'_of_enorm_le hfin.ne hbound

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
  [OrderTopology ι] [FirstCountableTopology ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
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

lemma TendstoInMeasure.aestronglyMeasurable
    {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [PseudoEMetricSpace β]
    {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → β} {g : α → β} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h_tendsto : TendstoInMeasure μ f u g) : AEStronglyMeasurable g μ := by
  obtain ⟨ns, -, hns⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => hf (ns n)) hns

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

lemma UniformIntegrable.memLp_of_tendstoInMeasure
    {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ℕ → α → β} {f : α → β} (p : ℝ≥0∞) (hUI : UniformIntegrable fn p μ)
    (htends : TendstoInMeasure μ fn atTop f) :
    MemLp f p μ := by
  refine ⟨htends.aestronglyMeasurable hUI.1, ?_⟩
  obtain ⟨C, hC⟩ := hUI.2.2
  exact lt_of_le_of_lt (tendstoInMeasure_bounded p (fun i => hC i) htends (fun i => hUI.1 i))
    ENNReal.coe_lt_top

lemma UnifIntegrable.unifIntegrable_of_tendsto_ae
    {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ι → α → β} (p : ℝ≥0∞) (hUI : UnifIntegrable fn p μ)
    (hfn : ∀ i, AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α → β | ∃ ni : ℕ → ι,
      ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ fn (ni n) x) atTop (nhds (g x))}) ↦ f.1) p μ := by
  refine fun ε hε => ?_
  obtain ⟨δ, hδ, hδ'⟩ := hUI hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht ht' => ?_⟩
  refine seq_tendsto_ae_bounded p (fun n => hδ' (s n) t ht ht') ?_ ?_
  · filter_upwards [hs] with a ha
    by_cases memt : a ∈ t
    · simpa [memt]
    · simp [memt]
  · exact fun n => (hfn (s n)).indicator ht

lemma UnifIntegrable.unifIntegrable_of_tendstoInMeasure
    {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ι → α → β} (p : ℝ≥0∞) (hUI : UnifIntegrable fn p μ)
    (hfn : ∀ i, AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α → β | ∃ ni : ℕ → ι,
      TendstoInMeasure μ (fn ∘ ni) atTop g}) ↦ f.1) p μ := by
  refine fun ε hε => ?_
  obtain ⟨δ, hδ, hδ'⟩ := hUI hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht ht' => ?_⟩
  obtain ⟨u, hu⟩ := hs.exists_seq_tendsto_ae
  refine seq_tendsto_ae_bounded p (fun n => hδ' (s (u n)) t ht ht') ?_ ?_
  · filter_upwards [hu.2] with a ha
    by_cases memt : a ∈ t
    · simpa [memt]
    · simp [memt]
  · exact fun n => (hfn (s (u n))).indicator ht

lemma UniformIntegrable.uniformIntegrable_of_tendsto_ae
    {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ι → α → β} (p : ℝ≥0∞) (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α → β | ∃ ni : ℕ → ι,
      ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ fn (ni n) x) atTop (nhds (g x))}) ↦ f.1) p μ := by
  refine ⟨fun ⟨f, s, hs⟩ => ?_, hUI.2.1.unifIntegrable_of_tendsto_ae p (fun i => hUI.1 i), ?_⟩
  · exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => hUI.1 (s n)) hs
  · obtain ⟨C, hC⟩ := hUI.2.2
    refine ⟨C, fun ⟨f, s, hs⟩ => ?_⟩
    exact seq_tendsto_ae_bounded p (fun n => hC (s n)) hs (fun n => hUI.1 (s n))

lemma UniformIntegrable.uniformIntegrable_of_tendstoInMeasure
    {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ι → α → β} (p : ℝ≥0∞) (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α → β | ∃ ni : ℕ → ι,
      TendstoInMeasure μ (fn ∘ ni) atTop g}) ↦ f.1) p μ := by
  refine ⟨fun ⟨f, s, hs⟩ => ?_, hUI.2.1.unifIntegrable_of_tendstoInMeasure p (fun i => hUI.1 i), ?_⟩
  · exact hs.aestronglyMeasurable (fun n => hUI.1 (s n))
  · obtain ⟨C, hC⟩ := hUI.2.2
    refine ⟨C, fun ⟨f, s, hs⟩ => ?_⟩
    exact tendstoInMeasure_bounded p (fun n => hC (s n)) hs (fun n => hUI.1 (s n))

lemma UniformIntegrable.integrable_of_tendstoInMeasure
    {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ℕ → α → β} {f : α → β} (hUI : UniformIntegrable fn 1 μ)
    (htends : TendstoInMeasure μ fn atTop f) :
    Integrable f μ := by
  rw [← memLp_one_iff_integrable]
  exact hUI.memLp_of_tendstoInMeasure 1 htends

end MeasureTheory
