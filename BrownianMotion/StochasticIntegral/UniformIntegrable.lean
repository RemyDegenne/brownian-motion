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

namespace MeasureTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → ℝ}

-- todo: `X` takes values in `ℝ` because
-- `MeasureTheory.Integrable.uniformIntegrable_condExp` is written only for `ℝ`. Investigate why.
lemma UniformIntegrable.condExp' {κ : Type*} (hX : UniformIntegrable X 1 μ)
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

omit [Countable ι] in
lemma Martingale.uniformIntegrable_stoppedValue_of_countable_range
    {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕]
    (hX : Martingale X 𝓕 μ) (τ : ℕ → Ω → WithTop ι) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ι} (hτ_le : ∀ i ω, τ i ω ≤ n) (hτ_countable : ∀ i, (Set.range <| τ i).Countable) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ := by
  sorry

end MeasureTheory
