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
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

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

omit [IsFiniteMeasure μ] in
lemma enorm_condExp_le (f : Ω → E) :
    ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ₑ ≤ .ofReal (μ[fun ω ↦ ‖f ω‖|m] ω) := by
  have : 0 ≤ᵐ[μ] μ[fun ω ↦ ‖f ω‖|m] :=
    condExp_nonneg (ae_of_all _ fun _ ↦ by positivity)
  filter_upwards [norm_condExp_le f, this] with ω hω1 hω2
  rwa [le_ofReal_iff_toReal_le (by simp) hω2, toReal_enorm]

lemma norm_rpow_condExp_le {p : ℝ≥0∞} (one_le_p : 1 ≤ p) (p_ne_top : p ≠ ∞) (hf : MemLp f p μ) :
    ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ ^ p.toReal ≤ μ[fun ω ↦ ‖f ω‖ ^ p.toReal|m] ω := by
  by_cases hm : m ≤ mΩ
  swap; · simp [condExp_of_not_le, hm, (toReal_pos_of_one_le one_le_p p_ne_top).ne']
  have hf' : Integrable (fun x ↦ ‖f x‖ ^ p.toReal) μ := by
    rwa [integrable_norm_rpow_iff hf.aestronglyMeasurable (by positivity) p_ne_top]
  have hc : Continuous (fun x : E ↦ ‖x‖ ^ p.toReal) := by fun_prop (disch := positivity)
  filter_upwards [ConvexOn.map_condExp_le_univ hm
    (convexOn_rpow_norm (one_le_toReal one_le_p p_ne_top))
    hc.lowerSemicontinuous (hf.integrable one_le_p) hf'] with _ h using h

lemma enorm_rpow_condExp_le {p : ℝ≥0∞} (one_le_p : 1 ≤ p) (p_ne_top : p ≠ ∞) (hf : MemLp f p μ) :
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
  have hf' : MemLp f ∞ μ := memLp_iff.2 ((eLpNorm_exponent_top hf).trans_lt (Ne.lt_top h))
  have : (‖f ·‖) ≤ᵐ[μ] fun _ ↦ (eLpNormEssSup f μ).toReal := by
    filter_upwards [enorm_ae_le_eLpNormEssSup f μ] with ω hω
    exact (ofReal_le_iff_le_toReal h).1 (by simpa)
  filter_upwards [condExp_mono (m := m) (hf'.integrable (by simp)).norm
    (integrable_const _) this] with ω hω
  exact ofReal_le_of_le_toReal (by simpa [condExp_const hm] using hω)

/-- Given an integrable function `g`, the conditional expectations of `g` with respect to
a sequence of sub-σ-algebras is uniformly integrable. -/
lemma Integrable.uniformIntegrable_condExp' {ι : Type*} {g : Ω → E}
    (hint : Integrable g μ) {ℱ : ι → MeasurableSpace Ω} (hℱ : ∀ i, ℱ i ≤ mΩ) :
    UniformIntegrable (fun i => μ[g|ℱ i]) 1 μ := by
  let A : MeasurableSpace Ω := mΩ
  have hmeas : ∀ n, ∀ C, MeasurableSet {x | C ≤ ‖(μ[g|ℱ n]) x‖₊} := fun n C =>
    stronglyMeasurable_const.measurableSet_le (stronglyMeasurable_condExp.mono (hℱ n)).nnnorm
  have hg : MemLp g 1 μ := memLp_one_iff_integrable.2 hint
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
    (fun n => (stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable) fun ε hε => ?_
  by_cases hne : eLpNorm g 1 μ = 0
  · rw [eLpNorm_eq_zero_iff one_ne_zero] at hne
    refine ⟨0, fun n => (le_of_eq <| (eLpNorm_eq_zero_iff one_ne_zero).2 ?_).trans zero_le⟩
    filter_upwards [condExp_congr_ae (m := ℱ n) hne] with x hx
    simp [hx]
  obtain ⟨δ, hδ, h⟩ := hg.eLpNorm_indicator_le le_rfl ENNReal.one_ne_top hε
  rcases eq_top_or_lt_top δ with rfl | hδ_top
  · refine ⟨0, fun i ↦ ?_⟩
    specialize h .univ
    simp only [zero_le, Set.ofPred_true, Set.indicator_univ, nullMeasurableSet_univ, le_top,
      forall_const] at h ⊢
    exact (eLpNorm_condExp_le_eLpNorm g le_rfl).trans h
  set C : ℝ≥0 := δ⁻¹.toNNReal * (eLpNorm g 1 μ).toNNReal with hC
  have hCpos : 0 < C := mul_pos (toNNReal_pos (ENNReal.inv_ne_zero.2 hδ_top.ne)
    (inv_ne_top.2 hδ.ne')) (toNNReal_pos hne hg.ne)
  have : ∀ n, μ {x : Ω | C ≤ ‖(μ[g|ℱ n]) x‖₊} ≤ δ := by
    intro n
    have : C ^ ENNReal.toReal 1 * μ {x | ENNReal.ofNNReal C ≤ ‖μ[g|ℱ n] x‖₊} ≤
        eLpNorm μ[g|ℱ n] 1 μ ^ ENNReal.toReal 1 := by
      rw [ENNReal.toReal_one, ENNReal.rpow_one]
      convert! mul_meas_ge_le_pow_eLpNorm μ one_ne_zero ENNReal.one_ne_top C
      rw [ENNReal.toReal_one, ENNReal.rpow_one, enorm_eq_nnnorm]
    rw [ENNReal.toReal_one, ENNReal.rpow_one, mul_comm, ←
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne'))
        (Or.inl ENNReal.coe_lt_top.ne)] at this
    simp_rw [ENNReal.coe_le_coe] at this
    refine this.trans ?_
    rw [ENNReal.div_le_iff_le_mul (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne'))
        (Or.inl ENNReal.coe_lt_top.ne), hC, ← toNNReal_mul,
      coe_toNNReal (mul_ne_top (inv_ne_top.2 hδ.ne') hg.ne), ← mul_assoc,
      ENNReal.mul_inv_cancel hδ.ne' hδ_top.ne, one_mul, rpow_one]
    exact eLpNorm_condExp_le_eLpNorm _ le_rfl
  refine ⟨C, fun n => le_trans ?_
    (h {x : Ω | C ≤ ‖(μ[g|ℱ n]) x‖₊} (hmeas n C).nullMeasurableSet (this n))⟩
  have hmeasℱ : MeasurableSet[ℱ n] {x : Ω | C ≤ ‖(μ[g|ℱ n]) x‖₊} :=
    @StronglyMeasurable.measurableSet_le _ _ (ℱ n) _ _ _ _ _ _ stronglyMeasurable_const
      stronglyMeasurable_condExp.nnnorm
  rw [← eLpNorm_congr_ae (condExp_indicator hint hmeasℱ)]
  exact eLpNorm_condExp_le_eLpNorm _ le_rfl

end MeasureTheory
