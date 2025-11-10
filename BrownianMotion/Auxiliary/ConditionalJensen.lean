import Mathlib

/-!
# Facts relying on conditional Jensen's inequality

This file contains facts which rely on conditional Jensen's inequality. We write the statements
and leave them as sorries until the inequality is added to mathlib (PR #27953).

-/

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap Set

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {Ω E : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

attribute [simp] convex_empty
attribute [simp] convex_univ

@[nontriviality]
lemma convexOn_subsingleton {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [Subsingleton E] [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 E] [Module 𝕜 β] (s : Set E)
    (f : E → β) : ConvexOn 𝕜 s f := by
  constructor
  · refine Subsingleton.set_cases (by simp) (by simp) s
  · intro x hx y hy a b ha hb hab
    simp_rw [Subsingleton.eq_zero (α := E), ← add_smul, hab, one_smul]
    rfl

lemma convexOn_rpow_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : E ↦ ‖x‖ ^ p) := by
  nontriviality E
  refine ConvexOn.comp (g := fun x ↦ x ^ p) ?_ convexOn_univ_norm ?_
  · convert convexOn_rpow hp
    simp
  · simp only [image_univ, range_norm]
    exact Real.monotoneOn_rpow_Ici_of_exponent_nonneg (by linarith)

/-- Conditional Jensen inequality -/
theorem convex_comp_condExp_le (hm : m ≤ mΩ) {φ : E → ℝ} (hφ1 : ConvexOn ℝ univ φ)
    (hφ2 : LowerSemicontinuous φ)
    {f : Ω → E} (hf1 : Integrable f μ) (hf2 : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f|m] ≤ᵐ[μ] μ[φ ∘ f|m] := sorry

theorem enorm_comp_condExp_le (f : Ω → E) :
    ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ₑ ≤ .ofReal (μ[fun ω ↦ ‖f ω‖|m] ω) := by
  by_cases hm : m ≤ mΩ
  swap; · simp [condExp_of_not_le, hm]
  by_cases hf : Integrable f μ
  swap; · simp [condExp_of_not_integrable, hf]
  have : ∀ᵐ ω ∂μ, 0 ≤ ‖f ω‖ := ae_of_all μ (fun _ ↦ norm_nonneg _)
  filter_upwards [convex_comp_condExp_le hm convexOn_univ_norm continuous_norm.lowerSemicontinuous
    hf hf.norm, condExp_nonneg this] with ω hω1 hω2
  change ‖μ[f|m] ω‖ ≤ μ[fun ω ↦ ‖f ω‖|m] ω at hω1
  rwa [ENNReal.le_ofReal_iff_toReal_le, toReal_enorm]
  simp
  assumption

theorem enorm_pow_comp_condExp_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) (f : Ω → E)
    (hff : MemLp f p μ) :
    ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ₑ ^ p.toReal ≤ .ofReal (μ[fun ω ↦ ‖f ω‖ ^ p.toReal|m] ω) := by
  have hp'' : 0 < p.toReal := by
    rw [ENNReal.toReal_pos_iff]
    refine ⟨?_, lt_top_iff_ne_top.2 hp'⟩
    exact (show (0 : ℝ≥0∞) < 1 by simp).trans_le hp
  have hp''' : 1 ≤ p.toReal := by
    calc
      1 = (1 : ℝ≥0∞).toReal := rfl
      _ ≤ p.toReal := by
        rwa [ENNReal.toReal_le_toReal]
        simp
        exact hp'
  obtain hE | hE := subsingleton_or_nontrivial E
  · simp [hE.eq_zero, hp'']
  by_cases hm : m ≤ mΩ
  swap; · apply ae_of_all; simp [condExp_of_not_le, hm]; grind
  by_cases hf : Integrable f μ
  swap
  · apply ae_of_all _ fun _ ↦ ?_; simp [condExp_of_not_integrable, hf, hp'']
  have : ∀ᵐ ω ∂μ, 0 ≤ ‖f ω‖ ^ p.toReal := ae_of_all μ (fun _ ↦ by positivity)
  have : ConvexOn ℝ univ (fun x : E ↦ ‖x‖ ^ p.toReal) := by
    refine ConvexOn.comp (g := fun x ↦ x ^ p.toReal) ?_ convexOn_univ_norm ?_
    · convert convexOn_rpow hp'''
      simp
    · simp
      apply Real.monotoneOn_rpow_Ici_of_exponent_nonneg
      linarith
  have hmm : Integrable (fun x ↦ ‖f x‖ ^ p.toReal) μ := by
    rwa [integrable_norm_rpow_iff]
    exact hff.aestronglyMeasurable
    apply LT.lt.ne'
    exact (show (0 : ℝ≥0∞) < 1 by simp).trans_le hp
    exact hp'
  have hc : Continuous (fun x : E ↦ ‖x‖ ^ p.toReal) := by
    fun_prop (disch := positivity)
  have lol : ∀ᵐ ω ∂μ, 0 ≤ ‖f ω‖ ^ p.toReal := ae_of_all _ fun _ ↦ by positivity
  filter_upwards [convex_comp_condExp_le hm this hc.lowerSemicontinuous
    hf hmm, condExp_nonneg lol] with ω hω1 hω2
  change ‖μ[f|m] ω‖ ^ p.toReal ≤ μ[fun ω ↦ ‖f ω‖ ^ p.toReal|m] ω at hω1
  rwa [ENNReal.le_ofReal_iff_toReal_le, ← ENNReal.toReal_rpow, toReal_enorm]
  simp
  assumption

theorem eLpNorm_condExp_le_eLpNorm {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : Ω → E) :
    eLpNorm (μ[f|m]) p μ ≤ eLpNorm f p μ := by
  by_cases hf : Integrable f μ
  swap; · rw [condExp_of_not_integrable hf, eLpNorm_zero]; exact zero_le _
  by_cases hm : m ≤ mΩ
  swap; · rw [condExp_of_not_le hm, eLpNorm_zero]; exact zero_le _
  by_cases hsig : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hsig, eLpNorm_zero]; exact zero_le _
  obtain rfl | hp' := eq_or_ne p ∞
  · simp_rw [eLpNorm_exponent_top]
    by_cases h : eLpNormEssSup f μ = ∞
    · simp [h]
    rw [← ENNReal.ofReal_toReal h]
    apply eLpNormEssSup_le_of_ae_bound
    have h1 := convex_comp_condExp_le hm (φ := (‖·‖)) ?_ ?_ hf ?_
    have h2 := enorm_ae_le_eLpNormEssSup f μ
    have h3 : ∀ᵐ ω ∂μ , ‖f ω‖ ≤ (eLpNormEssSup f μ).toReal := by
      filter_upwards [h2] with ω hω
      rwa [← ENNReal.ofReal_le_iff_le_toReal, ofReal_norm]
      exact h
    filter_upwards [h1, condExp_mono hf.norm (integrable_const _) h3] with ω hω1 hω2
    change ‖μ[f|m] ω‖ ≤ μ[fun ω ↦ ‖f ω‖|m] ω at hω1
    grw [hω1, hω2, condExp_const]
    exact hm
    exact convexOn_univ_norm
    exact continuous_norm.lowerSemicontinuous
    exact hf.norm
  obtain h | h := eq_or_ne (eLpNorm f p μ) ∞
  · simp [h]
  have hp'' : p ≠ 0 := by by_contra!; simp_all; exact hp.out
  have hff : MemLp f p μ := by
    unfold MemLp
    exact ⟨hf.aestronglyMeasurable, lt_top_iff_ne_top.2 h⟩
  calc
  eLpNorm μ[f|m] p μ = (∫⁻ ω, ‖μ[f|m] ω‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
    eLpNorm_eq_lintegral_rpow_enorm hp'' hp'
  _ ≤ (∫⁻ ω, (.ofReal (μ[fun ω ↦ ‖f ω‖ ^ p.toReal|m] ω)) ∂μ) ^ (1 / p.toReal) := by
    gcongr 1
    refine lintegral_mono_ae ?_
    filter_upwards [enorm_pow_comp_condExp_le (m := m) hp.out hp' f hff] with ω hω
    gcongr
  _ = (.ofReal (∫ ω, μ[fun ω ↦ ‖f ω‖ ^ p.toReal|m] ω ∂μ)) ^ (1 / p.toReal) := by
    congr
    rw [ofReal_integral_eq_lintegral_ofReal]
    apply integrable_condExp
    apply condExp_nonneg
    exact ae_of_all _ fun _ ↦ by positivity
  _ = (.ofReal (∫ ω, ‖f ω‖ ^ p.toReal ∂μ)) ^ (1 / p.toReal) := by
    rw [integral_condExp]
  _ = (∫⁻ ω, ‖f ω‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    congr with ω
    rw [← ENNReal.ofReal_rpow_of_nonneg, ofReal_norm]
    simp
    simp
    exact hff.integrable_norm_rpow'
    exact ae_of_all _ fun _ ↦ by positivity
  _ = eLpNorm f p μ := by rw [eLpNorm_eq_lintegral_rpow_enorm hp'' hp']
  -- rw [eLpNorm_eq_lintegral_rpow_enorm]
  -- calc
  --   eLpNorm (μ[f|m]) 1 μ ≤ eLpNorm (μ[(|f|)|m]) 1 μ := by
  --     refine eLpNorm_mono_ae ?_
  --     filter_upwards [condExp_mono hf hf.abs
  --       (ae_of_all μ (fun x => le_abs_self (f x) : ∀ x, f x ≤ |f x|)),
  --       (condExp_neg ..).symm.le.trans (condExp_mono hf.neg hf.abs
  --         (ae_of_all μ (fun x => neg_le_abs (f x) : ∀ x, -f x ≤ |f x|)))] with x hx₁ hx₂
  --     exact abs_le_abs hx₁ hx₂
  --   _ = eLpNorm f 1 μ := by
  --     rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
  --       ← ENNReal.toReal_eq_toReal_iff' (hasFiniteIntegral_iff_enorm.mp integrable_condExp.2).ne
  --         (hasFiniteIntegral_iff_enorm.mp hf.2).ne,
  --       ← integral_norm_eq_lintegral_enorm
  --         (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable,
  --       ← integral_norm_eq_lintegral_enorm hf.1]
  --     simp_rw [Real.norm_eq_abs]
  --     rw (config := {occs := .pos [2]}) [← integral_condExp hm]
  --     refine integral_congr_ae ?_
  --     have : 0 ≤ᵐ[μ] μ[(|f|)|m] := by
  --       rw [← condExp_zero]
  --       exact condExp_mono (integrable_zero _ _ _) hf.abs
  --         (ae_of_all μ (fun x => abs_nonneg (f x) : ∀ x, 0 ≤ |f x|))
  --     filter_upwards [this] with x hx
  --     exact abs_eq_self.2 hx

theorem integral_abs_condExp_le (f : α → ℝ) : ∫ x, |(μ[f|m]) x| ∂μ ≤ ∫ x, |f x| ∂μ := by
  by_cases hm : m ≤ m0
  swap
  · simp_rw [condExp_of_not_le hm, Pi.zero_apply, abs_zero, integral_zero]
    positivity
  by_cases hfint : Integrable f μ
  swap
  · simp only [condExp_of_not_integrable hfint, Pi.zero_apply, abs_zero, integral_const,
      Algebra.id.smul_eq_mul, mul_zero]
    positivity
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
  · apply ENNReal.toReal_mono <;> simp_rw [← Real.norm_eq_abs, ofReal_norm_eq_enorm]
    · exact hfint.2.ne
    · rw [← eLpNorm_one_eq_lintegral_enorm, ← eLpNorm_one_eq_lintegral_enorm]
      exact eLpNorm_one_condExp_le_eLpNorm _
  · filter_upwards with x using abs_nonneg _
  · simp_rw [← Real.norm_eq_abs]
    exact hfint.1.norm
  · filter_upwards with x using abs_nonneg _
  · simp_rw [← Real.norm_eq_abs]
    exact (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable.norm

theorem setIntegral_abs_condExp_le {s : Set α} (hs : MeasurableSet[m] s) (f : α → ℝ) :
    ∫ x in s, |(μ[f|m]) x| ∂μ ≤ ∫ x in s, |f x| ∂μ := by
  by_cases hnm : m ≤ m0
  swap
  · simp_rw [condExp_of_not_le hnm, Pi.zero_apply, abs_zero, integral_zero]
    positivity
  by_cases hfint : Integrable f μ
  swap
  · simp only [condExp_of_not_integrable hfint, Pi.zero_apply, abs_zero, integral_const,
      Algebra.id.smul_eq_mul, mul_zero]
    positivity
  have : ∫ x in s, |(μ[f|m]) x| ∂μ = ∫ x, |(μ[s.indicator f|m]) x| ∂μ := by
    rw [← integral_indicator (hnm _ hs)]
    refine integral_congr_ae ?_
    have : (fun x => |(μ[s.indicator f|m]) x|) =ᵐ[μ] fun x => |s.indicator (μ[f|m]) x| :=
      (condExp_indicator hfint hs).fun_comp abs
    refine EventuallyEq.trans (Eventually.of_forall fun x => ?_) this.symm
    rw [← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]
    simp only [Real.norm_eq_abs]
  rw [this, ← integral_indicator (hnm _ hs)]
  refine (integral_abs_condExp_le _).trans
    (le_of_eq <| integral_congr_ae <| Eventually.of_forall fun x => ?_)
  simp_rw [← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]

/-- If the real-valued function `f` is bounded almost everywhere by `R`, then so is its conditional
expectation. -/
theorem ae_bdd_condExp_of_ae_bdd {R : ℝ≥0} {f : α → ℝ} (hbdd : ∀ᵐ x ∂μ, |f x| ≤ R) :
    ∀ᵐ x ∂μ, |(μ[f|m]) x| ≤ R := by
  by_cases hnm : m ≤ m0
  swap
  · simp_rw [condExp_of_not_le hnm, Pi.zero_apply, abs_zero]
    exact Eventually.of_forall fun _ => R.coe_nonneg
  by_cases hfint : Integrable f μ
  swap
  · simp_rw [condExp_of_not_integrable hfint]
    filter_upwards [hbdd] with x hx
    rw [Pi.zero_apply, abs_zero]
    exact (abs_nonneg _).trans hx
  by_contra h
  change μ _ ≠ 0 at h
  simp only [← zero_lt_iff, Set.compl_def, Set.mem_setOf_eq, not_le] at h
  suffices μ.real {x | ↑R < |(μ[f|m]) x|} * ↑R < μ.real {x | ↑R < |(μ[f|m]) x|} * ↑R by
    exact this.ne rfl
  refine lt_of_lt_of_le (setIntegral_gt_gt R.coe_nonneg ?_ h.ne') ?_
  · exact integrable_condExp.abs.integrableOn
  refine (setIntegral_abs_condExp_le ?_ _).trans ?_
  · simp_rw [← Real.norm_eq_abs]
    exact @measurableSet_lt _ _ _ _ _ m _ _ _ _ _ measurable_const
      stronglyMeasurable_condExp.norm.measurable
  simp only [← smul_eq_mul, ← setIntegral_const]
  refine setIntegral_mono_ae hfint.abs.integrableOn ?_ hbdd
  refine ⟨aestronglyMeasurable_const, lt_of_le_of_lt ?_
    (integrable_condExp.integrableOn : IntegrableOn (μ[f|m]) {x | ↑R < |(μ[f|m]) x|} μ).2⟩
  refine setLIntegral_mono
    (stronglyMeasurable_condExp.mono hnm).measurable.nnnorm.coe_nnreal_ennreal fun x hx => ?_
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, Real.nnnorm_of_nonneg R.coe_nonneg]
  exact Subtype.mk_le_mk.2 (le_of_lt hx)

/-- Given an integrable function `g`, the conditional expectations of `g` with respect to
a sequence of sub-σ-algebras is uniformly integrable. -/
theorem Integrable.uniformIntegrable_condExp {ι : Type*} [IsFiniteMeasure μ] {g : α → ℝ}
    (hint : Integrable g μ) {ℱ : ι → MeasurableSpace α} (hℱ : ∀ i, ℱ i ≤ m0) :
    UniformIntegrable (fun i => μ[g|ℱ i]) 1 μ := by
  let A : MeasurableSpace α := m0
  have hmeas : ∀ n, ∀ C, MeasurableSet {x | C ≤ ‖(μ[g|ℱ n]) x‖₊} := fun n C =>
    measurableSet_le measurable_const (stronglyMeasurable_condExp.mono (hℱ n)).measurable.nnnorm
  have hg : MemLp g 1 μ := memLp_one_iff_integrable.2 hint
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
    (fun n => (stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable) fun ε hε => ?_
  by_cases hne : eLpNorm g 1 μ = 0
  · rw [eLpNorm_eq_zero_iff hg.1 one_ne_zero] at hne
    refine ⟨0, fun n => (le_of_eq <|
      (eLpNorm_eq_zero_iff ((stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable.indicator
        (hmeas n 0)) one_ne_zero).2 ?_).trans (zero_le _)⟩
    filter_upwards [condExp_congr_ae (m := ℱ n) hne] with x hx
    simp only [zero_le', Set.setOf_true, Set.indicator_univ, Pi.zero_apply, hx, condExp_zero]
  obtain ⟨δ, hδ, h⟩ := hg.eLpNorm_indicator_le le_rfl ENNReal.one_ne_top hε
  set C : ℝ≥0 := ⟨δ, hδ.le⟩⁻¹ * (eLpNorm g 1 μ).toNNReal with hC
  have hCpos : 0 < C := mul_pos (inv_pos.2 hδ) (ENNReal.toNNReal_pos hne hg.eLpNorm_lt_top.ne)
  have : ∀ n, μ {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} ≤ ENNReal.ofReal δ := by
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
      hC, Nonneg.inv_mk, ENNReal.coe_mul, ENNReal.coe_toNNReal hg.eLpNorm_lt_top.ne, ← mul_assoc, ←
      ENNReal.ofReal_eq_coe_nnreal, ← ENNReal.ofReal_mul hδ.le, mul_inv_cancel₀ hδ.ne',
      ENNReal.ofReal_one, one_mul, ENNReal.rpow_one]
    exact eLpNorm_one_condExp_le_eLpNorm _
  refine ⟨C, fun n => le_trans ?_ (h {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} (hmeas n C) (this n))⟩
  have hmeasℱ : MeasurableSet[ℱ n] {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} :=
    @measurableSet_le _ _ _ _ _ (ℱ n) _ _ _ _ _ measurable_const
      (@Measurable.nnnorm _ _ _ _ _ (ℱ n) _ stronglyMeasurable_condExp.measurable)
  rw [← eLpNorm_congr_ae (condExp_indicator hint hmeasℱ)]
  exact eLpNorm_one_condExp_le_eLpNorm _
