/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.ENNReal
import Mathlib.Probability.Martingale.OptionalSampling

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
    {X : ι → Ω → E} {Y : ι → Ω → F} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hY : UniformIntegrable Y p μ) (mX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hX : ∀ i, ∃ j, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ ‖Y j ω‖) :
    UniformIntegrable X p μ := sorry

lemma UniformIntegrable.norm [NormedAddCommGroup E] {X : ι → Ω → E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hY : UniformIntegrable X p μ) :
    UniformIntegrable (fun t ω ↦ ‖X t ω‖) p μ := sorry

lemma uniformIntegrable_iff_norm [NormedAddCommGroup E] {X : ι → Ω → E} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    UniformIntegrable X p μ ↔ UniformIntegrable (fun t ω ↦ ‖X t ω‖) p μ := sorry

lemma uniformIntegrable_of_dominated_singleton [NormedAddCommGroup E] {X : ι → Ω → E} {Y : Ω → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hY : MemLp Y p μ) (mX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hX : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ Y ω) :
    UniformIntegrable X p μ := sorry

variable {X : ι → Ω → ℝ}

-- todo: `X` takes values in `ℝ` because
-- `MeasureTheory.Integrable.uniformIntegrable_condExp` is written only for `ℝ`. Investigate why.
lemma UniformIntegrable.condExp' (hX : UniformIntegrable X 1 μ)
    {𝓕 : κ → MeasurableSpace Ω} (h𝓕 : ∀ i, 𝓕 i ≤ mΩ) :
    UniformIntegrable (fun (p : ι × κ) ↦ μ[X p.1 | 𝓕 p.2]) 1 μ := by
  have hX' := hX
  obtain ⟨hX1, hX2, ⟨C, hC⟩⟩ := hX
  refine ⟨fun p ↦ (stronglyMeasurable_condExp.mono (h𝓕 p.2)).aestronglyMeasurable, ?_,
    ⟨C, fun p ↦ (eLpNorm_one_condExp_le_eLpNorm _).trans (hC p.1)⟩⟩
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
  grw [eLpNorm_one_condExp_le_eLpNorm, hδ]
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
    grw [eLpNorm_one_condExp_le_eLpNorm]
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

lemma UniformIntegrable.condExp (hX : UniformIntegrable X 1 μ)
    {𝓕 : ι → MeasurableSpace Ω} (h𝓕 : ∀ i, 𝓕 i ≤ mΩ) :
    UniformIntegrable (fun i ↦ μ[X i | 𝓕 i]) 1 μ :=
  (hX.condExp' h𝓕).comp (fun i ↦ (i, i))

variable {ι : Type*} [LinearOrder ι] [OrderBot ι] [Countable ι] [TopologicalSpace ι]
  [OrderTopology ι] [FirstCountableTopology ι] {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕]

lemma Martingale.ae_eq_condExp_of_isStoppingTime {X : ι → Ω → ℝ}
    (hX : Martingale X 𝓕 μ) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) {n : ι}
    (hτ_le : ∀ ω, τ ω ≤ n) :
    stoppedValue X τ =ᵐ[μ] μ[X n | hτ.measurableSpace] :=
  stoppedValue_ae_eq_condExp_of_le hX (isStoppingTime_const 𝓕 n) hτ (n := n) hτ_le
    (fun _ ↦ le_rfl)

lemma Martingale.uniformIntegrable_stoppedValue {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration μ 𝓕]
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
    {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕]
    (hX : Martingale X 𝓕 μ) (τ : ℕ → Ω → WithTop ι) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ι} (hτ_le : ∀ i ω, τ i ω ≤ n) (hτ_countable : ∀ i, (Set.range <| τ i).Countable) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ := by
  sorry

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
      exact LE.le.trans (hn n (by linarith)) (bound n)

lemma UniformIntegrable.memLp_of_tendstoInMeasure
    {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ℕ → α → β} {f : α → β} (p : ℝ≥0∞) (hUI : UniformIntegrable fn p μ)
    (htends : TendstoInMeasure μ fn atTop f) :
    MemLp f p μ := by
  obtain ⟨g, hg⟩ := htends.exists_seq_tendsto_ae
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop (fun i => hUI.1 (g i)) hg.2, ?_⟩
  obtain ⟨C, hC⟩ := hUI.2.2
  exact lt_of_le_of_lt (seq_tendsto_ae_bounded p (fun i => hC (g i)) hg.2 (fun i => hUI.1 (g i)))
    ENNReal.coe_lt_top

lemma TendstoInMeasure.aestronglyMeasurable
    {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [PseudoEMetricSpace β]
    {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → β} {g : α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (h_tendsto : TendstoInMeasure μ f u g) : AEStronglyMeasurable g μ := by
  obtain ⟨ns, -, hns⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => hf (ns n)) hns

lemma UnifIntegrable.unifIntegrable_of_tendstoInMeasure
    {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ι → α → β} (p : ℝ≥0∞) (hUI : UnifIntegrable fn p μ)
    (hfn : ∀ (i : ι), AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α → β | ∃ ni : ℕ → ι,
      TendstoInMeasure μ (fn ∘ ni) atTop g}) ↦ f.1) p μ := by
  refine fun ε hε => ?_
  obtain ⟨_, hδ, hδ'⟩ := hUI hε
  refine ⟨_, hδ, fun f t ht ht' => ?_⟩
  obtain ⟨s, hs⟩ := f.2
  obtain ⟨u, hu⟩ := hs.exists_seq_tendsto_ae
  refine seq_tendsto_ae_bounded p (fun n => hδ' (s (u n)) t ht ht') ?_ ?_
  · filter_upwards [hu.2] with a ha
    by_cases memt : a ∈ t
    · simpa [memt]
    · simp [memt]
  · exact fun i => (hfn (s (u i))).indicator ht

lemma UniformIntegrable.uniformIntegrable_of_tendstoInMeasure
    {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ι → α → β} (p : ℝ≥0∞) (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α → β | ∃ ni : ℕ → ι,
      TendstoInMeasure μ (fn ∘ ni) atTop g}) ↦ f.1) p μ := by
  refine ⟨fun f => ?_, hUI.2.1.unifIntegrable_of_tendstoInMeasure p (fun i => hUI.1 i), ?_⟩
  · obtain ⟨s, hs⟩ := f.2
    exact hs.aestronglyMeasurable (fun n => hUI.1 (s n))
  · obtain ⟨C, hC⟩ := hUI.2.2
    refine ⟨C, fun f => ?_⟩
    obtain ⟨s, hs⟩ := f.2
    obtain ⟨u, hu⟩ := hs.exists_seq_tendsto_ae
    exact seq_tendsto_ae_bounded p (fun n => hC (s (u n))) hu.2 (fun i => hUI.1 (s (u i)))

lemma UniformIntegrable.integrable_of_tendstoInMeasure
    {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ℕ → α → β} {f : α → β} (hUI : UniformIntegrable fn 1 μ)
    (htends : TendstoInMeasure μ fn atTop f) :
    Integrable f μ := by
  rw [← memLp_one_iff_integrable]
  exact hUI.memLp_of_tendstoInMeasure 1 htends

end MeasureTheory
