/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Analysis
import BrownianMotion.Auxiliary.ENNReal
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Jensen's inequality for conditional expectations
-/

open MeasureTheory Filter ENNReal

namespace MeasureTheory

variable {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {s : Set E} {f : Ω → E} {φ : E → ℝ}

-- Proved in Mathlib PR #27953 for finite measures. Here written for σ-finite measures.
theorem conditional_jensen [SigmaFinite μ] (hm : m ≤ mΩ)
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  sorry

variable [IsFiniteMeasure μ]

theorem norm_condExp_le (f : Ω → E) :
    ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ ≤ μ[fun ω ↦ ‖f ω‖|m] ω := by
  by_cases hm : m ≤ mΩ
  swap; · simp [condExp_of_not_le, hm]
  have : 0 ≤ᵐ[μ] μ[fun ω ↦ ‖f ω‖|m] :=
    condExp_nonneg (ae_of_all _ fun _ ↦ by positivity)
  by_cases hf : Integrable f μ
  swap; · filter_upwards [this]; simp [condExp_of_not_integrable, hf]
  filter_upwards [conditional_jensen hm convexOn_univ_norm continuous_norm.lowerSemicontinuous
    hf hf.norm] with _ h using h

theorem enorm_condExp_le (f : Ω → E) :
    ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ₑ ≤ .ofReal (μ[fun ω ↦ ‖f ω‖|m] ω) := by
  have : 0 ≤ᵐ[μ] μ[fun ω ↦ ‖f ω‖|m] :=
    condExp_nonneg (ae_of_all _ fun _ ↦ by positivity)
  filter_upwards [norm_condExp_le f, this] with ω hω1 hω2
  rwa [le_ofReal_iff_toReal_le (by simp) hω2, toReal_enorm]

theorem norm_rpow_condExp_le {p : ℝ≥0∞} (one_le_p : 1 ≤ p) (p_ne_top : p ≠ ∞) (hf : MemLp f p μ) :
    ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ ^ p.toReal ≤ μ[fun ω ↦ ‖f ω‖ ^ p.toReal|m] ω := by
  by_cases hm : m ≤ mΩ
  swap; · simp [condExp_of_not_le, hm, (toReal_pos_of_one_le one_le_p p_ne_top).ne']
  have hf' : Integrable (fun x ↦ ‖f x‖ ^ p.toReal) μ := by
    rwa [integrable_norm_rpow_iff hf.aestronglyMeasurable (by positivity) p_ne_top]
  have hc : Continuous (fun x : E ↦ ‖x‖ ^ p.toReal) := by fun_prop (disch := positivity)
  filter_upwards [conditional_jensen hm (convexOn_rpow_norm (one_le_toReal one_le_p p_ne_top))
    hc.lowerSemicontinuous (hf.integrable one_le_p) hf'] with _ h using h

theorem enorm_rpow_condExp_le {p : ℝ≥0∞} (one_le_p : 1 ≤ p) (p_ne_top : p ≠ ∞) (hf : MemLp f p μ) :
    ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ₑ ^ p.toReal ≤ .ofReal (μ[fun ω ↦ ‖f ω‖ ^ p.toReal|m] ω) := by
  have : 0 ≤ᵐ[μ] μ[fun ω ↦ ‖f ω‖ ^ p.toReal|m] :=
    condExp_nonneg (ae_of_all _ fun _ ↦ by positivity)
  filter_upwards [norm_rpow_condExp_le one_le_p p_ne_top hf, this] with ω hω1 hω2
  rwa [le_ofReal_iff_toReal_le (by simp) hω2, ← toReal_rpow, toReal_enorm]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma ofReal_condExp_norm_ae_le_eLpNormEssSup (hf : AEStronglyMeasurable f μ) :
    ∀ᵐ ω ∂μ, .ofReal (μ[(‖f ·‖)|m] ω) ≤ eLpNormEssSup f μ := by
  by_cases hm : m ≤ mΩ
  swap; · simp [condExp_of_not_le hm]
  by_cases h : eLpNormEssSup f μ = ∞
  · simp [h]
  have hf' : MemLp f ∞ μ := ⟨hf, Ne.lt_top h⟩
  have : (‖f ·‖) ≤ᵐ[μ] fun _ ↦ (eLpNormEssSup f μ).toReal := by
    filter_upwards [enorm_ae_le_eLpNormEssSup f μ] with ω hω
    exact (ofReal_le_iff_le_toReal h).1 (by simpa)
  filter_upwards [condExp_mono (m := m) (hf'.integrable (by simp)).norm
    (integrable_const _) this] with ω hω
  exact ofReal_le_of_le_toReal (by simpa [condExp_const hm] using hω)

theorem eLpNorm_condExp_le_eLpNorm {p : ℝ≥0∞} (hp : 1 ≤ p) (f : Ω → E) :
    eLpNorm (μ[f|m]) p μ ≤ eLpNorm f p μ := by
  by_cases hf : Integrable f μ
  swap; · simp [condExp_of_not_integrable hf]
  by_cases hm : m ≤ mΩ
  swap; · simp [condExp_of_not_le hm]
  by_cases hsig : SigmaFinite (μ.trim hm)
  swap; · simp [condExp_of_not_sigmaFinite hm hsig, eLpNorm_zero]
  obtain h | h := eq_or_ne (eLpNorm f p μ) ∞
  · simp [h]
  obtain rfl | hp' := eq_or_ne p ∞
  · simp_rw [eLpNorm_exponent_top] at h ⊢
    apply eLpNormEssSup_le_of_ae_enorm_bound
    filter_upwards [enorm_condExp_le f,
      ofReal_condExp_norm_ae_le_eLpNormEssSup hf.aestronglyMeasurable] with ω hω1 hω2 using
      hω1.trans hω2
  have hff : MemLp f p μ := ⟨hf.aestronglyMeasurable, h.lt_top⟩
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm ((show (0 : ℝ≥0∞) < 1 by simp).trans_le hp |>.ne') hp']
  calc
  _ ≤ (∫⁻ ω, (.ofReal (μ[fun ω ↦ ‖f ω‖ ^ p.toReal|m] ω)) ∂μ) ^ (1 / p.toReal) := by
    gcongr 1
    exact lintegral_mono_ae (enorm_rpow_condExp_le hp hp' hff)
  _ = (.ofReal (∫ ω, μ[fun ω ↦ ‖f ω‖ ^ p.toReal|m] ω ∂μ)) ^ (1 / p.toReal) := by
    congr
    rw [ofReal_integral_eq_lintegral_ofReal integrable_condExp]
    exact condExp_nonneg <| ae_of_all _ fun _ ↦ by positivity
  _ = (.ofReal (∫ ω, ‖f ω‖ ^ p.toReal ∂μ)) ^ (1 / p.toReal) := by rw [integral_condExp]
  _ = (∫⁻ ω, ‖f ω‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
    rw [ofReal_integral_eq_lintegral_ofReal hff.integrable_norm_rpow'
      (ae_of_all _ fun _ ↦ by positivity)]
    congr with
    rw [← ofReal_rpow_of_nonneg (by simp) (by simp), ofReal_norm]

theorem MemLp.condExp' {p : ℝ≥0∞} (hp : 1 ≤ p) (hf : MemLp f p μ) :
    MemLp μ[f|m] p μ :=
  ⟨integrable_condExp.aestronglyMeasurable, (eLpNorm_condExp_le_eLpNorm hp f).trans_lt hf.2⟩

end MeasureTheory
