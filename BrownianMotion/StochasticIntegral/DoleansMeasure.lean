/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.L2M
public import BrownianMotion.StochasticIntegral.MonotoneProcess
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Martingale.Basic

/-! # Doléans measure

-/

@[expose] public section

open MeasureTheory Filter Order ProbabilityTheory
open scoped NNReal ENNReal Topology

section Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- A kernel all of whose measures are finite is s-finite. -/
lemma ProbabilityTheory.Kernel.isSFiniteKernel_of_isFiniteMeasure (κ : Kernel α β)
    [∀ a, IsFiniteMeasure (κ a)] : IsSFiniteKernel κ := by
  classical
  let s : ℕ → Set α := fun n ↦ (fun a ↦ ⌊(κ a Set.univ).toNNReal⌋₊) ⁻¹' {n}
  have hs n : MeasurableSet (s n) :=
    Measurable.nat_floor (κ.measurable_coe MeasurableSet.univ).ennreal_toNNReal
      (measurableSet_singleton n)
  refine ⟨⟨fun n ↦ Kernel.piecewise (hs n) κ 0, fun n ↦ ⟨n + 1, by simp, fun a ↦ ?_⟩, ?_⟩⟩
  · rw [Kernel.piecewise_apply']
    split_ifs with ha
    · rw [← ENNReal.coe_toNNReal (measure_ne_top (κ a) Set.univ)]
      have h := Nat.lt_floor_add_one (κ a Set.univ).toNNReal
      have ha' : ⌊(κ a Set.univ).toNNReal⌋₊ = n := ha
      rw [ha'] at h
      exact_mod_cast h.le
    · simp
  · ext a t ht
    rw [Kernel.sum_apply, Measure.sum_apply _ ht, tsum_eq_single ⌊(κ a Set.univ).toNNReal⌋₊]
    · simp [Kernel.piecewise_apply', s]
    · intro n hn
      simp [Kernel.piecewise_apply', s, hn.symm]

end Kernel

namespace MeasureTheory

/-- The generators of the predictable σ-algebra form a π-system. -/
lemma Filtration.isPiSystem_predictable_generators {ι Ω : Type*} [LinearOrder ι] [OrderBot ι]
    {m : MeasurableSpace Ω} (𝓕 : Filtration ι m) :
    IsPiSystem ({s | ∃ A, MeasurableSet[𝓕 ⊥] A ∧ s = {⊥} ×ˢ A} ∪
      {s | ∃ i A, MeasurableSet[𝓕 i] A ∧ s = Set.Ioi i ×ˢ A}) := by
  rintro _ (⟨F, hF, rfl⟩ | ⟨i, F, hF, rfl⟩) _ (⟨G, hG, rfl⟩ | ⟨j, G, hG, rfl⟩) hne
  · exact Or.inl ⟨F ∩ G, hF.inter hG, by rw [Set.prod_inter_prod, Set.inter_self]⟩
  · obtain ⟨p, hp1, hp2⟩ := hne
    simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Ioi] at hp1 hp2
    exact absurd (hp1.1 ▸ hp2.1) not_lt_bot
  · obtain ⟨p, hp1, hp2⟩ := hne
    simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Ioi] at hp1 hp2
    exact absurd (hp2.1 ▸ hp1.1) not_lt_bot
  · exact Or.inr ⟨i ⊔ j, F ∩ G,
      (𝓕.mono le_sup_left _ hF).inter (𝓕.mono le_sup_right _ hG),
      by rw [Set.prod_inter_prod, Set.Ioi_inter_Ioi]⟩

/-- If `A - B` is a martingale, the increments of `A` and `B` up to `⊤` have the same integral on
every `𝓕 i`-measurable set. -/
lemma Martingale.setIntegral_sub_top_eq {ι Ω : Type*} [Preorder ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration P 𝓕]
    {A B : ι → Ω → ℝ} (hA_int : ∀ t, Integrable (A t) P) (hB_int : ∀ t, Integrable (B t) P)
    (hAB : Martingale (A - B) 𝓕 P) (i : ι) {F : Set Ω} (hF : MeasurableSet[𝓕 i] F) :
    ∫ ω in F, (A ⊤ ω - A i ω) ∂P = ∫ ω in F, (B ⊤ ω - B i ω) ∂P := by
  have h := hAB.setIntegral_eq (le_top : i ≤ ⊤) hF
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hA_int i).integrableOn (hB_int i).integrableOn,
    integral_sub (hA_int ⊤).integrableOn (hB_int ⊤).integrableOn] at h
  rw [integral_sub (hA_int ⊤).integrableOn (hA_int i).integrableOn,
    integral_sub (hB_int ⊤).integrableOn (hB_int i).integrableOn]
  linarith

end MeasureTheory

variable {ι Ω : Type*} [CompleteLinearOrder ι] [DenselyOrdered ι] [TopologicalSpace ι]
  [OrderTopology ι] [PolishSpace ι] [MeasurableSpace ι] [BorelSpace ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration ι mΩ}
  {A B : ι → Ω → ℝ}

namespace StieltjesFunction

section Basic

variable (hA : Adapted 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω))
  (hA_mono : ∀ ω, Monotone (A · ω))

/-- The Stieltjes kernel of `A` at `ω` is the Stieltjes measure of the path `A · ω`. -/
lemma kernelOfRightContAdaptedMono_apply (ω : Ω) :
    kernelOfRightContAdaptedMono hA hA_rc hA_mono ω = (rightContMono hA_rc hA_mono ω).measure :=
  rfl

omit [DenselyOrdered ι] [OrderTopology ι] [PolishSpace ι] [MeasurableSpace ι] [BorelSpace ι] in
/-- The Stieltjes function `rightContMono hA_rc hA_mono ω` is the path `A · ω`. -/
@[simp]
lemma rightContMono_apply (ω : Ω) (i : ι) : rightContMono hA_rc hA_mono ω i = A i ω := rfl

/-- The Stieltjes kernel of `A` gives mass `A b ω - A a ω` to `(a, b]`. -/
lemma kernelOfRightContAdaptedMono_Ioc (ω : Ω) (a b : ι) :
    kernelOfRightContAdaptedMono hA hA_rc hA_mono ω (Set.Ioc a b)
      = ENNReal.ofReal (A b ω - A a ω) := by
  simp [kernelOfRightContAdaptedMono_apply, measure_Ioc]

/-- The Stieltjes kernel of `A` gives mass zero to `{⊥}`. -/
@[simp]
lemma kernelOfRightContAdaptedMono_singleton_bot (ω : Ω) :
    kernelOfRightContAdaptedMono hA hA_rc hA_mono ω {⊥} = 0 := by
  rw [kernelOfRightContAdaptedMono_apply, ← botSet_eq_singleton_of_isBot isBot_bot,
    measure_botSet]

/-- The Stieltjes kernel of `A` gives mass `A ⊤ ω - A a ω` to `(a, ⊤]`. -/
lemma kernelOfRightContAdaptedMono_Ioi (ω : Ω) (a : ι) :
    kernelOfRightContAdaptedMono hA hA_rc hA_mono ω (Set.Ioi a)
      = ENNReal.ofReal (A ⊤ ω - A a ω) := by
  rw [← Set.Ioc_top, kernelOfRightContAdaptedMono_Ioc]

/-- The total mass of the Stieltjes kernel of `A` is `A ⊤ ω - A ⊥ ω`. -/
lemma kernelOfRightContAdaptedMono_univ (ω : Ω) :
    kernelOfRightContAdaptedMono hA hA_rc hA_mono ω Set.univ
      = ENNReal.ofReal (A ⊤ ω - A ⊥ ω) := by
  have h_univ : (Set.univ : Set ι) = {⊥} ∪ Set.Ioi ⊥ := by
    ext x
    simp
  refine le_antisymm ?_ ?_
  · rw [h_univ]
    refine (measure_union_le _ _).trans ?_
    simp [kernelOfRightContAdaptedMono_Ioi]
  · rw [← kernelOfRightContAdaptedMono_Ioi hA hA_rc hA_mono]
    exact measure_mono (Set.subset_univ _)

/-- The Stieltjes kernel of `A` consists of finite measures (since `ι` has a bottom and a top). -/
instance isFiniteMeasure_kernelOfRightContAdaptedMono (ω : Ω) :
    IsFiniteMeasure (kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) :=
  ⟨by simp [kernelOfRightContAdaptedMono_univ]⟩

/-- The Stieltjes kernel of `A` is s-finite. -/
instance isSFiniteKernel_kernelOfRightContAdaptedMono :
    IsSFiniteKernel (kernelOfRightContAdaptedMono hA hA_rc hA_mono) :=
  Kernel.isSFiniteKernel_of_isFiniteMeasure _

end Basic

end StieltjesFunction

namespace MeasureTheory

open StieltjesFunction

section DoleansMeasure

variable (hA : Adapted 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω))
  (hA_mono : ∀ ω, Monotone (A · ω))

/-- The Doléans measure on `ι × Ω` of a right-continuous, monotone, adapted process `A`:
the measure `s ↦ E[∫ 1_s(t, ω) dA_t(ω)]`. -/
noncomputable def doleansMeasure (P : Measure Ω) (hA : Adapted 𝓕 A)
    (hA_rc : ∀ ω, IsRightContinuous (A · ω)) (hA_mono : ∀ ω, Monotone (A · ω)) :
    Measure (ι × Ω) :=
  (P ⊗ₘ kernelOfRightContAdaptedMono hA hA_rc hA_mono).map Prod.swap

/-- The Doléans measure of a measurable rectangle. -/
lemma doleansMeasure_prod {s : Set ι} {F : Set Ω} (hs : MeasurableSet s) (hF : MeasurableSet F) :
    doleansMeasure P hA hA_rc hA_mono (s ×ˢ F)
      = ∫⁻ ω in F, kernelOfRightContAdaptedMono hA hA_rc hA_mono ω s ∂P := by
  rw [doleansMeasure, Measure.map_apply measurable_swap (hs.prod hF), Set.preimage_swap_prod,
    Measure.compProd_apply_prod hF hs]

/-- The Doléans measure does not charge `{⊥} × Ω`. -/
@[simp]
lemma doleansMeasure_singleton_bot_prod (F : Set Ω) :
    doleansMeasure P hA hA_rc hA_mono ({⊥} ×ˢ F) = 0 := by
  refine measure_mono_null (Set.prod_mono subset_rfl (Set.subset_univ F)) ?_
  rw [doleansMeasure_prod hA hA_rc hA_mono (measurableSet_singleton ⊥) MeasurableSet.univ]
  simp

/-- The Doléans measure of `(i, ⊤] × F` is `E[1_F (A ⊤ - A i)]`. -/
lemma doleansMeasure_Ioi_prod (hA_int : ∀ t, Integrable (A t) P) (i : ι) {F : Set Ω}
    (hF : MeasurableSet F) :
    doleansMeasure P hA hA_rc hA_mono (Set.Ioi i ×ˢ F)
      = ENNReal.ofReal (∫ ω in F, (A ⊤ ω - A i ω) ∂P) := by
  have h_int : Integrable (fun ω ↦ A ⊤ ω - A i ω) P := (hA_int ⊤).sub (hA_int i)
  rw [doleansMeasure_prod hA hA_rc hA_mono measurableSet_Ioi hF,
    ofReal_integral_eq_lintegral_ofReal h_int.integrableOn
      (ae_of_all _ fun ω ↦ sub_nonneg.2 (hA_mono ω le_top))]
  simp_rw [kernelOfRightContAdaptedMono_Ioi]

/-- The total mass of the Doléans measure is `E[A ⊤ - A ⊥]`. -/
lemma doleansMeasure_univ (hA_int : ∀ t, Integrable (A t) P) :
    doleansMeasure P hA hA_rc hA_mono Set.univ
      = ENNReal.ofReal (∫ ω, (A ⊤ ω - A ⊥ ω) ∂P) := by
  have h_int : Integrable (fun ω ↦ A ⊤ ω - A ⊥ ω) P := (hA_int ⊤).sub (hA_int ⊥)
  rw [← Set.univ_prod_univ, doleansMeasure_prod hA hA_rc hA_mono .univ .univ,
    Measure.restrict_univ,
    ofReal_integral_eq_lintegral_ofReal h_int
      (ae_of_all _ fun ω ↦ sub_nonneg.2 (hA_mono ω le_top))]
  simp_rw [kernelOfRightContAdaptedMono_univ]

/-- The Doléans measure of an integrable process is finite. -/
lemma isFiniteMeasure_doleansMeasure (hA_int : ∀ t, Integrable (A t) P) :
    IsFiniteMeasure (doleansMeasure P hA hA_rc hA_mono) :=
  ⟨by simp [doleansMeasure_univ hA hA_rc hA_mono hA_int]⟩

/-- The integral of a bounded jointly measurable function with respect to the Doléans measure is
the iterated integral `E[∫ H(s, ω) dA_s(ω)]`. -/
lemma integral_doleansMeasure (hA_int : ∀ t, Integrable (A t) P) {H : ι × Ω → ℝ} {C : ℝ}
    (hH : Measurable H) (hC : ∀ p, |H p| ≤ C) :
    ∫ p, H p ∂(doleansMeasure P hA hA_rc hA_mono)
      = ∫ ω, ∫ s, H (s, ω) ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) ∂P := by
  have := isFiniteMeasure_doleansMeasure hA hA_rc hA_mono hA_int
  have h_int : Integrable H (doleansMeasure P hA hA_rc hA_mono) :=
    Integrable.of_bound hH.aestronglyMeasurable C (ae_of_all _ fun p ↦ by
      rw [Real.norm_eq_abs]
      exact hC p)
  rw [doleansMeasure,
    integrable_map_measure hH.aestronglyMeasurable measurable_swap.aemeasurable] at h_int
  rw [doleansMeasure, integral_map measurable_swap.aemeasurable hH.aestronglyMeasurable]
  exact Measure.integral_compProd h_int

end DoleansMeasure

section Uniqueness

variable (hA : Adapted 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω))
  (hA_mono : ∀ ω, Monotone (A · ω))
  (hB : Adapted 𝓕 B) (hB_rc : ∀ ω, IsRightContinuous (B · ω))
  (hB_mono : ∀ ω, Monotone (B · ω))

/-- If `A - B` is a martingale, then the Doléans measures of `A` and `B` agree on the predictable
σ-algebra. -/
lemma doleansMeasure_trim_eq_of_martingale (hA_int : ∀ t, Integrable (A t) P)
    (hB_int : ∀ t, Integrable (B t) P) (hAB : Martingale (A - B) 𝓕 P) :
    (doleansMeasure P hA hA_rc hA_mono).trim 𝓕.predictable_le_prod
      = (doleansMeasure P hB hB_rc hB_mono).trim 𝓕.predictable_le_prod := by
  have := isFiniteMeasure_doleansMeasure hA hA_rc hA_mono hA_int
  refine @ext_of_generate_finite (ι × Ω) 𝓕.predictable _ _ _ rfl
    𝓕.isPiSystem_predictable_generators inferInstance ?_ ?_
  · rintro _ (⟨F, hF, rfl⟩ | ⟨i, F, hF, rfl⟩)
    · rw [trim_measurableSet_eq _ (measurableSet_predictable_singleton_bot_prod hF),
        trim_measurableSet_eq _ (measurableSet_predictable_singleton_bot_prod hF),
        doleansMeasure_singleton_bot_prod, doleansMeasure_singleton_bot_prod]
    · rw [trim_measurableSet_eq _ (measurableSet_predictable_Ioi_prod hF),
        trim_measurableSet_eq _ (measurableSet_predictable_Ioi_prod hF),
        doleansMeasure_Ioi_prod hA hA_rc hA_mono hA_int i (𝓕.le i _ hF),
        doleansMeasure_Ioi_prod hB hB_rc hB_mono hB_int i (𝓕.le i _ hF),
        Martingale.setIntegral_sub_top_eq hA_int hB_int hAB i hF]
  · rw [trim_measurableSet_eq _ MeasurableSet.univ, trim_measurableSet_eq _ MeasurableSet.univ,
      doleansMeasure_univ hA hA_rc hA_mono hA_int, doleansMeasure_univ hB hB_rc hB_mono hB_int]
    have h := Martingale.setIntegral_sub_top_eq hA_int hB_int hAB ⊥ (F := Set.univ) .univ
    rw [Measure.restrict_univ] at h
    rw [h]

/-- If `A - B` is a martingale, then the Doléans measures of `A` and `B` agree on predictable
sets. -/
lemma doleansMeasure_eq_of_martingale (hA_int : ∀ t, Integrable (A t) P)
    (hB_int : ∀ t, Integrable (B t) P) (hAB : Martingale (A - B) 𝓕 P) {s : Set (ι × Ω)}
    (hs : MeasurableSet[𝓕.predictable] s) :
    doleansMeasure P hA hA_rc hA_mono s = doleansMeasure P hB hB_rc hB_mono s := by
  rw [← trim_measurableSet_eq 𝓕.predictable_le_prod hs,
    doleansMeasure_trim_eq_of_martingale hA hA_rc hA_mono hB hB_rc hB_mono hA_int hB_int hAB,
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
  rw [← integral_doleansMeasure hA hA_rc hA_mono hA_int hH' hC,
    ← integral_doleansMeasure hB hB_rc hB_mono hB_int hH' hC,
    integral_trim 𝓕.predictable_le_prod hH, integral_trim 𝓕.predictable_le_prod hH,
    doleansMeasure_trim_eq_of_martingale hA hA_rc hA_mono hB hB_rc hB_mono hA_int hB_int hAB]

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
