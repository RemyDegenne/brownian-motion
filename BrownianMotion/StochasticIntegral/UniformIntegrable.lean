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

variable {ι Ω E : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {X : ι → Ω → ℝ}

-- todo: `X` takes values in `ℝ` because
-- `MeasureTheory.Integrable.uniformIntegrable_condExp` is written only for `ℝ`. Investigate why.
lemma UniformIntegrable.condExp (hX : UniformIntegrable X 1 μ) {𝓕 : ι → MeasurableSpace Ω}
    (h𝓕 : ∀ i, 𝓕 i ≤ mΩ) :
    UniformIntegrable (fun i ↦ μ[X i | 𝓕 i]) 1 μ := by
  have hX' := hX
  obtain ⟨hX1, hX2, ⟨C, hC⟩⟩ := hX
  refine ⟨fun i ↦ (stronglyMeasurable_condExp.mono (h𝓕 i)).aestronglyMeasurable, ?_, ?_⟩
  · refine unifIntegrable_of le_rfl (by simp)
      (fun i ↦ (stronglyMeasurable_condExp.mono (h𝓕 i)).aestronglyMeasurable)
      fun ε hε ↦ ?_
    obtain ⟨δ, δ_pos, hδ⟩ := hX2 hε
    lift δ to ℝ≥0 using δ_pos.le
    refine ⟨(⨆ i, eLpNorm (X i) 1 μ).toNNReal / δ + 1, fun i ↦ ?_⟩
    rw [eLpNorm_congr_ae (condExp_indicator ?_ ?_).symm]
    grw [eLpNorm_one_condExp_le_eLpNorm, hδ]
    · apply StronglyMeasurable.measurableSet_le
      · fun_prop
      · exact stronglyMeasurable_condExp.mono (h𝓕 i) |>.nnnorm
    · simp_rw [← ENNReal.coe_le_coe]
      grw [meas_ge_le_lintegral_div]
      simp_rw [← enorm_eq_nnnorm, ← eLpNorm_one_eq_lintegral_enorm]
      grw [ENNReal.coe_add, ENNReal.coe_div, ENNReal.coe_toNNReal,
        ENNReal.div_le_div_left (a := (⨆ i, eLpNorm (X i) 1 μ) / δ), ← ENNReal.div_mul,
        eLpNorm_one_condExp_le_eLpNorm]
      simp [ENNReal.ofReal_coe_nnreal]
      nth_rw 2 [← one_mul (δ : ℝ≥0∞)]
      gcongr
      apply ENNReal.div_le_one_of_le
      exact le_iSup (α := ℝ≥0∞) _ i
      convert Or.inr δ_pos.ne
      simp [Eq.comm]
      simp
      simp
      apply ne_top_of_le_ne_top (b := (C : ℝ≥0∞))
      simp
      apply iSup_le
      exact hC
      convert δ_pos.ne
      simp [Eq.comm]
      fun_prop
      simp
      simp
    exact memLp_one_iff_integrable.1 (hX'.memLp i)
    · apply StronglyMeasurable.measurableSet_le
      · fun_prop
      · exact stronglyMeasurable_condExp.nnnorm
  · exact ⟨C, fun i ↦ (eLpNorm_one_condExp_le_eLpNorm _).trans (hC i)⟩

lemma Martingale.uniformIntegrable_stoppedValue {X : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ}
    (hX : Martingale X 𝓕 μ) (τ : ℕ → Ω → ℕ∞) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ℕ} (hτ_le : ∀ i ω, τ i ω ≤ n) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ := by
  sorry

end MeasureTheory
