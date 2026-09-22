/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.Martingale
public import BrownianMotion.StochasticIntegral.Predictable
public import BrownianMotion.StochasticIntegral.MonotoneProcess
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Martingale.Basic

/-! # Doléans measure

For an adapted process `A` with monotone right-continuous paths, the Doléans measure of `A` is the
measure `s ↦ E[∫ 1_s(t, ω) dA_t(ω)]` on `ι × Ω`.

## Main definitions

* `MeasureTheory.doleansMeasureOfMono`: the Doléans measure of a monotone process `A`.

## Main statements

* `MeasureTheory.doleansMeasureOfMono_Ioc_prod`: the Doléans measure of `(a, b] × F` is
  `E[1_F (A b - A a)]`.
* `MeasureTheory.lintegral_doleansMeasureOfMono`: the integral with respect to the Doléans measure
  is the iterated integral `E[∫ f(s, ω) dA_s(ω)]`.
* `MeasureTheory.isFiniteMeasure_doleansMeasureOfMono_of_integral_le`: the Doléans measure is finite
  if `E[A t - A ⊥]` is bounded in `t`.
* `MeasureTheory.doleansMeasureOfMono_eq_of_martingale`: if the index set has a top element and
  `A - B` is a martingale, then the Doléans measures of `A` and `B` agree on predictable sets.
-/

@[expose] public section

open MeasureTheory Filter Order ProbabilityTheory
open scoped NNReal ENNReal Topology

section General

/-! ### Index set which does not necessarily have a top element -/

variable {ι Ω : Type*} [ConditionallyCompleteLinearOrderBot ι] [DenselyOrdered ι]
  [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι] [MeasurableSpace ι] [BorelSpace ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ι mΩ} {A : ι → Ω → ℝ}
  (hA : Adapted 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω)) (hA_mono : ∀ ω, Monotone (A · ω))

namespace MeasureTheory

open StieltjesFunction

/-- The Doléans measure on `ι × Ω` of a right-continuous, monotone, adapted process `A`:
the measure `s ↦ E[∫ 1_s(t, ω) dA_t(ω)]`. -/
noncomputable def doleansMeasureOfMono (P : Measure Ω) (A : ι → Ω → ℝ) (hA : Adapted 𝓕 A)
    (hA_rc : ∀ ω, IsRightContinuous (A · ω)) (hA_mono : ∀ ω, Monotone (A · ω)) :
    Measure (ι × Ω) :=
  (P ⊗ₘ kernelOfRightContAdaptedMono hA hA_rc hA_mono).map Prod.swap

variable [SFinite P]

/-- The Doléans measure of a measurable rectangle. -/
lemma doleansMeasureOfMono_prod {s : Set ι} {F : Set Ω} (hs : MeasurableSet s)
    (hF : MeasurableSet F) :
    doleansMeasureOfMono P A hA hA_rc hA_mono (s ×ˢ F)
      = ∫⁻ ω in F, kernelOfRightContAdaptedMono hA hA_rc hA_mono ω s ∂P := by
  rw [doleansMeasureOfMono, Measure.map_apply measurable_swap (hs.prod hF), Set.preimage_swap_prod,
    Measure.compProd_apply_prod hF hs]

/-- The Doléans measure does not charge `{⊥} × Ω`. -/
@[simp]
lemma doleansMeasureOfMono_singleton_bot_prod (F : Set Ω) :
    doleansMeasureOfMono P A hA hA_rc hA_mono ({⊥} ×ˢ F) = 0 := by
  refine measure_mono_null (Set.prod_mono subset_rfl (Set.subset_univ F)) ?_
  rw [doleansMeasureOfMono_prod hA hA_rc hA_mono (measurableSet_singleton ⊥) MeasurableSet.univ]
  simp

/-- The Doléans measure of `(a, b] × F` is `E[1_F (A b - A a)]`. -/
lemma doleansMeasureOfMono_Ioc_prod (hA_int : ∀ t, Integrable (A t) P) {a b : ι} (hab : a ≤ b)
    {F : Set Ω} (hF : MeasurableSet F) :
    doleansMeasureOfMono P A hA hA_rc hA_mono (Set.Ioc a b ×ˢ F)
      = ENNReal.ofReal (∫ ω in F, (A b ω - A a ω) ∂P) := by
  have h_int : Integrable (fun ω ↦ A b ω - A a ω) P := (hA_int b).sub (hA_int a)
  rw [doleansMeasureOfMono_prod hA hA_rc hA_mono measurableSet_Ioc hF,
    ofReal_integral_eq_lintegral_ofReal h_int.integrableOn
      (ae_of_all _ fun ω ↦ sub_nonneg.2 (hA_mono ω hab))]
  simp_rw [kernelOfRightContAdaptedMono_Ioc]

/-- The Doléans measure of `[⊥, b] × F` is `E[1_F (A b - A ⊥)]`. -/
lemma doleansMeasureOfMono_Iic_prod (hA_int : ∀ t, Integrable (A t) P) (b : ι) {F : Set Ω}
    (hF : MeasurableSet F) :
    doleansMeasureOfMono P A hA hA_rc hA_mono (Set.Iic b ×ˢ F)
      = ENNReal.ofReal (∫ ω in F, (A b ω - A ⊥ ω) ∂P) := by
  have h_int : Integrable (fun ω ↦ A b ω - A ⊥ ω) P := (hA_int b).sub (hA_int ⊥)
  rw [doleansMeasureOfMono_prod hA hA_rc hA_mono measurableSet_Iic hF,
    ofReal_integral_eq_lintegral_ofReal h_int.integrableOn
      (ae_of_all _ fun ω ↦ sub_nonneg.2 (hA_mono ω bot_le))]
  simp_rw [kernelOfRightContAdaptedMono_Iic]

/-- The integral with respect to the Doléans measure is the iterated integral
`E[∫ f(s, ω) dA_s(ω)]`. -/
lemma lintegral_doleansMeasureOfMono {f : ι × Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂(doleansMeasureOfMono P A hA hA_rc hA_mono)
      = ∫⁻ ω, ∫⁻ s, f (s, ω) ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) ∂P := by
  rw [doleansMeasureOfMono, lintegral_map hf measurable_swap]
  exact Measure.lintegral_compProd (hf.comp measurable_swap)

/-- If `E[A t - A ⊥]` is bounded by `C` for all `t`, then the total mass of the Doléans measure is
at most `C`. -/
lemma doleansMeasureOfMono_univ_le (hA_int : ∀ t, Integrable (A t) P) {C : ℝ}
    (hC : ∀ t, ∫ ω, (A t ω - A ⊥ ω) ∂P ≤ C) :
    doleansMeasureOfMono P A hA hA_rc hA_mono Set.univ ≤ ENNReal.ofReal C := by
  obtain ⟨u, hu_mono, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  have h_univ : (Set.univ : Set (ι × Ω)) = ⋃ n, Set.Iic (u n) ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_prod, Set.mem_Iic, and_true, true_iff]
    exact (hu.eventually_ge_atTop p.1).exists
  have h_mono : Monotone fun n ↦ Set.Iic (u n) ×ˢ (Set.univ : Set Ω) :=
    fun n m hnm ↦ Set.prod_mono (Set.Iic_subset_Iic.2 (hu_mono hnm)) subset_rfl
  rw [h_univ, h_mono.measure_iUnion]
  refine iSup_le fun n ↦ ?_
  rw [doleansMeasureOfMono_Iic_prod hA hA_rc hA_mono hA_int (u n) .univ, Measure.restrict_univ]
  exact ENNReal.ofReal_le_ofReal (hC (u n))

/-- The Doléans measure is finite if `E[A t - A ⊥]` is bounded in `t`. -/
lemma isFiniteMeasure_doleansMeasureOfMono_of_integral_le (hA_int : ∀ t, Integrable (A t) P) {C : ℝ}
    (hC : ∀ t, ∫ ω, (A t ω - A ⊥ ω) ∂P ≤ C) :
    IsFiniteMeasure (doleansMeasureOfMono P A hA hA_rc hA_mono) :=
  ⟨(doleansMeasureOfMono_univ_le hA hA_rc hA_mono hA_int hC).trans_lt ENNReal.ofReal_lt_top⟩

end MeasureTheory

end General

/-! ### Index set with a top element -/

variable {ι Ω : Type*} [CompleteLinearOrder ι] [DenselyOrdered ι] [TopologicalSpace ι]
  [OrderTopology ι] [PolishSpace ι] [MeasurableSpace ι] [BorelSpace ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration ι mΩ}
  {A B : ι → Ω → ℝ}

namespace MeasureTheory

open StieltjesFunction

section DoleansMeasure

variable (hA : Adapted 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω))
  (hA_mono : ∀ ω, Monotone (A · ω))

/-- The Doléans measure of `(i, ⊤] × F` is `E[1_F (A ⊤ - A i)]`. -/
lemma doleansMeasureOfMono_Ioi_prod (hA_int : ∀ t, Integrable (A t) P) (i : ι) {F : Set Ω}
    (hF : MeasurableSet F) :
    doleansMeasureOfMono P A hA hA_rc hA_mono (Set.Ioi i ×ˢ F)
      = ENNReal.ofReal (∫ ω in F, (A ⊤ ω - A i ω) ∂P) := by
  have h_int : Integrable (fun ω ↦ A ⊤ ω - A i ω) P := (hA_int ⊤).sub (hA_int i)
  rw [doleansMeasureOfMono_prod hA hA_rc hA_mono measurableSet_Ioi hF,
    ofReal_integral_eq_lintegral_ofReal h_int.integrableOn
      (ae_of_all _ fun ω ↦ sub_nonneg.2 (hA_mono ω le_top))]
  simp_rw [kernelOfRightContAdaptedMono_Ioi]

/-- The total mass of the Doléans measure is `E[A ⊤ - A ⊥]`. -/
lemma doleansMeasureOfMono_univ (hA_int : ∀ t, Integrable (A t) P) :
    doleansMeasureOfMono P A hA hA_rc hA_mono Set.univ
      = ENNReal.ofReal (∫ ω, (A ⊤ ω - A ⊥ ω) ∂P) := by
  have h_int : Integrable (fun ω ↦ A ⊤ ω - A ⊥ ω) P := (hA_int ⊤).sub (hA_int ⊥)
  rw [← Set.univ_prod_univ, doleansMeasureOfMono_prod hA hA_rc hA_mono .univ .univ,
    Measure.restrict_univ,
    ofReal_integral_eq_lintegral_ofReal h_int
      (ae_of_all _ fun ω ↦ sub_nonneg.2 (hA_mono ω le_top))]
  simp_rw [kernelOfRightContAdaptedMono_univ]

/-- The Doléans measure of an integrable process is finite. -/
lemma isFiniteMeasure_doleansMeasureOfMono (hA_int : ∀ t, Integrable (A t) P) :
    IsFiniteMeasure (doleansMeasureOfMono P A hA hA_rc hA_mono) :=
  ⟨by simp [doleansMeasureOfMono_univ hA hA_rc hA_mono hA_int]⟩

/-- The integral of a bounded jointly measurable function with respect to the Doléans measure is
the iterated integral `E[∫ H(s, ω) dA_s(ω)]`. -/
lemma integral_doleansMeasureOfMono (hA_int : ∀ t, Integrable (A t) P) {H : ι × Ω → ℝ} {C : ℝ}
    (hH : Measurable H) (hC : ∀ p, |H p| ≤ C) :
    ∫ p, H p ∂(doleansMeasureOfMono P A hA hA_rc hA_mono)
      = ∫ ω, ∫ s, H (s, ω) ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) ∂P := by
  have := isFiniteMeasure_doleansMeasureOfMono hA hA_rc hA_mono hA_int
  have h_int : Integrable H (doleansMeasureOfMono P A hA hA_rc hA_mono) :=
    Integrable.of_bound hH.aestronglyMeasurable C (ae_of_all _ fun p ↦ by
      rw [Real.norm_eq_abs]
      exact hC p)
  rw [doleansMeasureOfMono,
    integrable_map_measure hH.aestronglyMeasurable measurable_swap.aemeasurable] at h_int
  rw [doleansMeasureOfMono, integral_map measurable_swap.aemeasurable hH.aestronglyMeasurable]
  exact Measure.integral_compProd h_int

end DoleansMeasure

section Uniqueness

variable (hA : Adapted 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω))
  (hA_mono : ∀ ω, Monotone (A · ω))
  (hB : Adapted 𝓕 B) (hB_rc : ∀ ω, IsRightContinuous (B · ω))
  (hB_mono : ∀ ω, Monotone (B · ω))

/-- If `A - B` is a martingale, then the Doléans measures of `A` and `B` agree on the predictable
σ-algebra. -/
lemma doleansMeasureOfMono_trim_eq_of_martingale (hA_int : ∀ t, Integrable (A t) P)
    (hB_int : ∀ t, Integrable (B t) P) (hAB : Martingale (A - B) 𝓕 P) :
    (doleansMeasureOfMono P A hA hA_rc hA_mono).trim 𝓕.predictable_le_prod
      = (doleansMeasureOfMono P B hB hB_rc hB_mono).trim 𝓕.predictable_le_prod := by
  have := isFiniteMeasure_doleansMeasureOfMono hA hA_rc hA_mono hA_int
  refine @ext_of_generate_finite (ι × Ω) 𝓕.predictable _ _ _ rfl
    𝓕.isPiSystem_predictable_generators inferInstance ?_ ?_
  · rintro _ (⟨F, hF, rfl⟩ | ⟨i, F, hF, rfl⟩)
    · rw [trim_measurableSet_eq _ (measurableSet_predictable_singleton_bot_prod hF),
        trim_measurableSet_eq _ (measurableSet_predictable_singleton_bot_prod hF),
        doleansMeasureOfMono_singleton_bot_prod, doleansMeasureOfMono_singleton_bot_prod]
    · rw [trim_measurableSet_eq _ (measurableSet_predictable_Ioi_prod hF),
        trim_measurableSet_eq _ (measurableSet_predictable_Ioi_prod hF),
        doleansMeasureOfMono_Ioi_prod hA hA_rc hA_mono hA_int i (𝓕.le i _ hF),
        doleansMeasureOfMono_Ioi_prod hB hB_rc hB_mono hB_int i (𝓕.le i _ hF),
        Martingale.setIntegral_sub_top_eq hA_int hB_int hAB i hF]
  · rw [trim_measurableSet_eq _ MeasurableSet.univ, trim_measurableSet_eq _ MeasurableSet.univ,
      doleansMeasureOfMono_univ hA hA_rc hA_mono hA_int,
      doleansMeasureOfMono_univ hB hB_rc hB_mono hB_int]
    have h := Martingale.setIntegral_sub_top_eq hA_int hB_int hAB ⊥ (F := Set.univ) .univ
    rw [Measure.restrict_univ] at h
    rw [h]

/-- If `A - B` is a martingale, then the Doléans measures of `A` and `B` agree on predictable
sets. -/
lemma doleansMeasureOfMono_eq_of_martingale (hA_int : ∀ t, Integrable (A t) P)
    (hB_int : ∀ t, Integrable (B t) P) (hAB : Martingale (A - B) 𝓕 P) {s : Set (ι × Ω)}
    (hs : MeasurableSet[𝓕.predictable] s) :
    doleansMeasureOfMono P A hA hA_rc hA_mono s = doleansMeasureOfMono P B hB hB_rc hB_mono s := by
  rw [← trim_measurableSet_eq 𝓕.predictable_le_prod hs,
    doleansMeasureOfMono_trim_eq_of_martingale hA hA_rc hA_mono hB hB_rc hB_mono hA_int hB_int hAB,
    trim_measurableSet_eq _ hs]

/-- **Uniqueness of the Doléans measure on predictable integrands**: if `A` and `B` are
right-continuous, monotone, adapted, integrable processes such that `A - B` is a martingale, then
for every bounded predictable `H`, `E[∫ H dA] = E[∫ H dB]`. -/
theorem integral_integral_kernelOfRightContAdaptedMono_eq_of_martingale
    (hA_int : ∀ t, Integrable (A t) P) (hB_int : ∀ t, Integrable (B t) P)
    (hAB : Martingale (A - B) 𝓕 P) {H : ι × Ω → ℝ} {C : ℝ}
    (hH : StronglyMeasurable[𝓕.predictable] H) (hC : ∀ p, |H p| ≤ C) :
    ∫ ω, ∫ s, H (s, ω) ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) ∂P
      = ∫ ω, ∫ s, H (s, ω) ∂(kernelOfRightContAdaptedMono hB hB_rc hB_mono ω) ∂P := by
  have hH' : Measurable H := hH.measurable.mono 𝓕.predictable_le_prod le_rfl
  rw [← integral_doleansMeasureOfMono hA hA_rc hA_mono hA_int hH' hC,
    ← integral_doleansMeasureOfMono hB hB_rc hB_mono hB_int hH' hC,
    integral_trim 𝓕.predictable_le_prod hH, integral_trim 𝓕.predictable_le_prod hH,
    doleansMeasureOfMono_trim_eq_of_martingale hA hA_rc hA_mono hB hB_rc hB_mono hA_int hB_int hAB]

/-- Version of `integral_integral_kernelOfRightContAdaptedMono_eq_of_martingale` for an integrand
which is `Measurable` with respect to the predictable σ-algebra. -/
theorem integral_integral_kernelOfRightContAdaptedMono_eq_of_martingale'
    (hA_int : ∀ t, Integrable (A t) P) (hB_int : ∀ t, Integrable (B t) P)
    (hAB : Martingale (A - B) 𝓕 P) {H : ι × Ω → ℝ} {C : ℝ}
    (hH : Measurable[𝓕.predictable] H) (hC : ∀ p, |H p| ≤ C) :
    ∫ ω, ∫ s, H (s, ω) ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) ∂P
      = ∫ ω, ∫ s, H (s, ω) ∂(kernelOfRightContAdaptedMono hB hB_rc hB_mono ω) ∂P :=
  integral_integral_kernelOfRightContAdaptedMono_eq_of_martingale hA hA_rc hA_mono hB hB_rc
    hB_mono hA_int hB_int hAB hH.stronglyMeasurable hC

/-- Version of `integral_integral_kernelOfRightContAdaptedMono_eq_of_martingale` for a bounded
strongly predictable process. -/
theorem IsStronglyPredictable.integral_integral_kernelOfRightContAdaptedMono_eq
    (hA_int : ∀ t, Integrable (A t) P) (hB_int : ∀ t, Integrable (B t) P)
    (hAB : Martingale (A - B) 𝓕 P) {u : ι → Ω → ℝ} {C : ℝ}
    (hu : IsStronglyPredictable 𝓕 u) (hC : ∀ s ω, |u s ω| ≤ C) :
    ∫ ω, ∫ s, u s ω ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) ∂P
      = ∫ ω, ∫ s, u s ω ∂(kernelOfRightContAdaptedMono hB hB_rc hB_mono ω) ∂P :=
  integral_integral_kernelOfRightContAdaptedMono_eq_of_martingale hA hA_rc hA_mono hB hB_rc
    hB_mono hA_int hB_int hAB (H := Function.uncurry u) hu (fun p ↦ hC p.1 p.2)

end Uniqueness

end MeasureTheory
