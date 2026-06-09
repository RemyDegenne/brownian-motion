/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.Analysis
public import BrownianMotion.Auxiliary.ENNReal
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Jensen's inequality for conditional expectations
-/

@[expose] public section

open MeasureTheory Filter ENNReal
open scoped NNReal

namespace MeasureTheory

variable {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {s : Set E} {f : Ω → E} {φ : E → ℝ}

variable [IsFiniteMeasure μ]

theorem norm_condExp_le (f : Ω → E) :
    ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ ≤ μ[fun ω ↦ ‖f ω‖|m] ω := by
  by_cases hm : m ≤ mΩ
  swap; · simp [condExp_of_not_le, hm]
  have : 0 ≤ᵐ[μ] μ[fun ω ↦ ‖f ω‖|m] :=
    condExp_nonneg (ae_of_all _ fun _ ↦ by positivity)
  by_cases hf : Integrable f μ
  swap; · filter_upwards [this]; simp [condExp_of_not_integrable, hf]
  exact convexOn_univ_norm.map_condExp_le_univ hm continuous_norm.lowerSemicontinuous hf hf.norm

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
  filter_upwards [ConvexOn.map_condExp_le_univ hm
    (convexOn_rpow_norm (one_le_toReal one_le_p p_ne_top))
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
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal ((show (0 : ℝ≥0∞) < 1 by simp).trans_le hp |>.ne')
    hp']
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

/-- If a function `f` is bounded almost everywhere by `R`, then so is its conditional
expectation. -/
theorem ae_bdd_condExp_of_ae_bdd' {R : ℝ} {f : Ω → E} (hbdd : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ R) :
    ∀ᵐ x ∂μ, ‖(μ[f|m]) x‖ ≤ R := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  have hR : 0 ≤ R := by
    have := ae_neBot.2 hμ
    obtain ⟨ω, hω⟩ := hbdd.exists
    exact (norm_nonneg _).trans hω
  by_cases hm : m ≤ mΩ
  swap; · simp [condExp_of_not_le hm, hR]
  by_cases hf : Integrable f μ
  swap; · simp [condExp_of_not_integrable hf, hR]
  filter_upwards [norm_condExp_le (m := m) f, condExp_mono (m := m) hf.norm
    (integrable_const _) hbdd] with ω hω1 hω2
  grw [hω1, hω2, condExp_const hm]

set_option backward.isDefEq.respectTransparency false in
/-- Given an integrable function `g`, the conditional expectations of `g` with respect to
a sequence of sub-σ-algebras is uniformly integrable. -/
theorem Integrable.uniformIntegrable_condExp' {ι : Type*} {g : Ω → E}
    (hint : Integrable g μ) {ℱ : ι → MeasurableSpace Ω} (hℱ : ∀ i, ℱ i ≤ mΩ) :
    UniformIntegrable (fun i => μ[g|ℱ i]) 1 μ := by
  let A : MeasurableSpace Ω := mΩ
  have hmeas : ∀ n, ∀ C, MeasurableSet {x | C ≤ ‖(μ[g|ℱ n]) x‖₊} := fun n C =>
    stronglyMeasurable_const.measurableSet_le (stronglyMeasurable_condExp.mono (hℱ n)).nnnorm
  have hg : MemLp g 1 μ := memLp_one_iff_integrable.2 hint
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
    (fun n => (stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable) fun ε hε => ?_
  by_cases hne : eLpNorm g 1 μ = 0
  · rw [eLpNorm_eq_zero_iff hg.1 one_ne_zero] at hne
    refine ⟨0, fun n => (le_of_eq <|
      (eLpNorm_eq_zero_iff ((stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable.indicator
        (hmeas n 0)) one_ne_zero).2 ?_).trans zero_le⟩
    filter_upwards [condExp_congr_ae (m := ℱ n) hne] with x hx
    simp only [zero_le', Set.setOf_true, Set.indicator_univ, Pi.zero_apply, hx, condExp_zero]
  obtain ⟨δ, hδ, h⟩ := hg.eLpNorm_indicator_le le_rfl ENNReal.one_ne_top hε
  set C : ℝ≥0 := ⟨δ, hδ.le⟩⁻¹ * (eLpNorm g 1 μ).toNNReal with hC
  have hCpos : 0 < C := mul_pos (inv_pos.2 hδ) (ENNReal.toNNReal_pos hne hg.eLpNorm_lt_top.ne)
  have : ∀ n, μ {x : Ω | C ≤ ‖(μ[g|ℱ n]) x‖₊} ≤ ENNReal.ofReal δ := by
    intro n
    have : C ^ ENNReal.toReal 1 * μ {x | ENNReal.ofNNReal C ≤ ‖μ[g|ℱ n] x‖₊} ≤
        eLpNorm μ[g|ℱ n] 1 μ ^ ENNReal.toReal 1 := by
      rw [ENNReal.toReal_one, ENNReal.rpow_one]
      convert mul_meas_ge_le_pow_eLpNorm μ one_ne_zero ENNReal.one_ne_top
        (stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable C
      · rw [ENNReal.toReal_one, ENNReal.rpow_one, enorm_eq_nnnorm]
    rw [ENNReal.toReal_one, ENNReal.rpow_one, mul_comm, ←
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne'))
        (Or.inl ENNReal.coe_lt_top.ne)] at this
    simp_rw [ENNReal.coe_le_coe] at this
    refine this.trans ?_
    rw [ENNReal.div_le_iff_le_mul (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne'))
        (Or.inl ENNReal.coe_lt_top.ne),
      hC, Nonneg.inv_mk, ENNReal.coe_mul, ENNReal.coe_toNNReal hg.eLpNorm_lt_top.ne, ← mul_assoc,
      ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul hδ.le, rpow_one]
    convert eLpNorm_condExp_le_eLpNorm le_rfl _
    · convert one_mul _
      simp only [ofReal_eq_one]
      exact mul_inv_cancel₀ hδ.ne'
    · infer_instance
    · infer_instance
  refine ⟨C, fun n => le_trans ?_ (h {x : Ω | C ≤ ‖(μ[g|ℱ n]) x‖₊} (hmeas n C) (this n))⟩
  have hmeasℱ : MeasurableSet[ℱ n] {x : Ω | C ≤ ‖(μ[g|ℱ n]) x‖₊} :=
    @StronglyMeasurable.measurableSet_le _ _ (ℱ n) _ _ _ _ _ _ stronglyMeasurable_const
      stronglyMeasurable_condExp.nnnorm
  rw [← eLpNorm_congr_ae (condExp_indicator hint hmeasℱ)]
  exact eLpNorm_condExp_le_eLpNorm le_rfl _

end MeasureTheory
