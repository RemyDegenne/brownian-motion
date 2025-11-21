/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Jensen's inequality for conditional expectations

-/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {m mα : MeasurableSpace α} {μ : Measure α}
  {s : Set E} {f : α → E} {φ : E → ℝ}

-- Proved in Mathlib PR #27953 for finite measures. Here written for σ-finite measures.
theorem conditional_jensen (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  sorry

lemma norm_condExp_le (hm : m ≤ mα) (hf_int : Integrable f μ) :
    (fun x ↦ ‖μ[f | m] x‖) ≤ᵐ[μ] μ[fun x ↦ ‖f x‖ | m] :=
  conditional_jensen hm convexOn_univ_norm continuous_norm.lowerSemicontinuous hf_int hf_int.norm

theorem eLpNorm_one_condExp_le_eLpNorm' (f : α → E) :
    eLpNorm (μ[f|m]) 1 μ ≤ eLpNorm f 1 μ := by
  by_cases hf : Integrable f μ
  swap; · rw [condExp_of_not_integrable hf, eLpNorm_zero]; exact zero_le _
  by_cases hm : m ≤ mα
  swap; · rw [condExp_of_not_le hm, eLpNorm_zero]; exact zero_le _
  by_cases hsig : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hsig, eLpNorm_zero]; exact zero_le _
  have lem (x : α) (hx : ‖μ[f | m] x‖ ≤ μ[fun x ↦ ‖f x‖ | m] x) :
    0 ≤ μ[fun x ↦ ‖f x‖|m] x := le_trans (norm_nonneg _) hx
  calc
    eLpNorm (μ[f|m]) 1 μ ≤ eLpNorm (μ[(fun a => ‖f a‖)|m]) 1 μ := by
      refine eLpNorm_mono_ae ?_
      filter_upwards [norm_condExp_le hm hf] with x hx
      simpa [Real.norm_eq_abs, abs_of_nonneg (lem x hx)] using hx
    _ = eLpNorm f 1 μ := by
      simp only [eLpNorm_one_eq_lintegral_enorm, ← ENNReal.toReal_eq_toReal_iff'
        (hasFiniteIntegral_iff_enorm.mp integrable_condExp.2).ne
        (hasFiniteIntegral_iff_enorm.mp hf.2).ne, ← integral_norm_eq_lintegral_enorm
        (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable,
        Real.norm_eq_abs, ← integral_norm_eq_lintegral_enorm hf.1]
      rw (config := {occs := .pos [2]}) [← integral_condExp hm]
      refine integral_congr_ae ?_
      filter_upwards [norm_condExp_le hm hf] with x hx
      exact abs_of_nonneg (lem x hx)

end MeasureTheory
