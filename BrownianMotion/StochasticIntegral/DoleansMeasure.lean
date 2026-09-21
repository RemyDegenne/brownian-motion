/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.Predictable
public import BrownianMotion.StochasticIntegral.MonotoneProcess
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Martingale.Basic

/-! # Doléans measure

For an adapted process `A` with monotone right-continuous paths, the Doléans measure of `A` is the
measure `s ↦ E[∫ 1_s(t, ω) dA_t(ω)]` on `ι × Ω`.

## Main definitions

* `MeasureTheory.doleansMeasure`: the Doléans measure of `A`, defined for an index set `ι` which
  does not necessarily have a top element (for example `ℝ≥0`).

## Main statements

* `MeasureTheory.doleansMeasure_Ioc_prod`: the Doléans measure of `(a, b] × F` is
  `E[1_F (A b - A a)]`.
* `MeasureTheory.lintegral_doleansMeasure`: the integral with respect to the Doléans measure is
  the iterated integral `E[∫ f(s, ω) dA_s(ω)]`.
* `MeasureTheory.isFiniteMeasure_doleansMeasure_of_integral_le`: the Doléans measure is finite if
  `E[A t - A ⊥]` is bounded in `t`.
* `MeasureTheory.doleansMeasure_eq_of_martingale`: if the index set has a top element and `A - B`
  is a martingale, then the Doléans measures of `A` and `B` agree on predictable sets.
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

/-- A kernel whose measures are finite on each set of a countable measurable cover is s-finite. -/
lemma ProbabilityTheory.Kernel.isSFiniteKernel_of_measure_lt_top (κ : Kernel α β) {s : ℕ → Set β}
    (hs : ∀ n, MeasurableSet (s n)) (hs_univ : ⋃ n, s n = Set.univ)
    (h_fin : ∀ a n, κ a (s n) < ∞) : IsSFiniteKernel κ := by
  have hd n : MeasurableSet (disjointed s n) := MeasurableSet.disjointed hs n
  have h_eq : κ = Kernel.sum fun n ↦ κ.restrict (hd n) := by
    ext a t ht
    rw [Kernel.sum_apply, Measure.sum_apply _ ht]
    simp_rw [Kernel.restrict_apply' _ _ _ ht]
    rw [← measure_iUnion, ← Set.inter_iUnion, iUnion_disjointed, hs_univ, Set.inter_univ]
    · exact fun i j hij ↦ (disjoint_disjointed s hij).mono Set.inter_subset_right
        Set.inter_subset_right
    · exact fun n ↦ ht.inter (hd n)
  rw [h_eq]
  have h_sfin n : IsSFiniteKernel (κ.restrict (hd n)) := by
    have : ∀ a, IsFiniteMeasure (κ.restrict (hd n) a) := fun a ↦ ⟨by
      rw [Kernel.restrict_apply, Measure.restrict_apply_univ]
      exact (measure_mono (disjointed_subset s n)).trans_lt (h_fin a n)⟩
    exact Kernel.isSFiniteKernel_of_isFiniteMeasure _
  infer_instance

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

section General

/-! ### Index set which does not necessarily have a top element -/

variable {ι Ω : Type*} [ConditionallyCompleteLinearOrderBot ι] [DenselyOrdered ι]
  [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι] [MeasurableSpace ι] [BorelSpace ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ι mΩ} {A : ι → Ω → ℝ}
  (hA : Adapted 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω)) (hA_mono : ∀ ω, Monotone (A · ω))

namespace StieltjesFunction

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

/-- The Stieltjes kernel of `A` gives mass `A b ω - A ⊥ ω` to `[⊥, b]`. -/
lemma kernelOfRightContAdaptedMono_Iic (ω : Ω) (b : ι) :
    kernelOfRightContAdaptedMono hA hA_rc hA_mono ω (Set.Iic b)
      = ENNReal.ofReal (A b ω - A ⊥ ω) := by
  have h_eq : Set.Iic b = {⊥} ∪ Set.Ioc ⊥ b := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioc]
    refine ⟨fun h ↦ ?_, ?_⟩
    · by_cases hx : x = ⊥
      · exact Or.inl hx
      · exact Or.inr ⟨bot_lt_iff_ne_bot.2 hx, h⟩
    · rintro (rfl | h)
      exacts [bot_le, h.2]
  refine le_antisymm ?_ ?_
  · rw [h_eq]
    refine (measure_union_le _ _).trans ?_
    simp [kernelOfRightContAdaptedMono_Ioc]
  · rw [← kernelOfRightContAdaptedMono_Ioc hA hA_rc hA_mono]
    exact measure_mono Set.Ioc_subset_Iic_self

/-- The Stieltjes kernel of `A` is s-finite: its measures are finite on the intervals `[⊥, b]`. -/
instance isSFiniteKernel_kernelOfRightContAdaptedMono :
    IsSFiniteKernel (kernelOfRightContAdaptedMono hA hA_rc hA_mono) := by
  obtain ⟨u, -, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  refine Kernel.isSFiniteKernel_of_measure_lt_top _ (s := fun n ↦ Set.Iic (u n))
    (fun n ↦ measurableSet_Iic) ?_ fun ω n ↦ ?_
  · ext x
    simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    exact (hu.eventually_ge_atTop x).exists
  · rw [kernelOfRightContAdaptedMono_Iic]
    exact ENNReal.ofReal_lt_top

end StieltjesFunction

namespace MeasureTheory

open StieltjesFunction

/-- The Doléans measure on `ι × Ω` of a right-continuous, monotone, adapted process `A`:
the measure `s ↦ E[∫ 1_s(t, ω) dA_t(ω)]`. -/
noncomputable def doleansMeasure (P : Measure Ω) (hA : Adapted 𝓕 A)
    (hA_rc : ∀ ω, IsRightContinuous (A · ω)) (hA_mono : ∀ ω, Monotone (A · ω)) :
    Measure (ι × Ω) :=
  (P ⊗ₘ kernelOfRightContAdaptedMono hA hA_rc hA_mono).map Prod.swap

variable [SFinite P]

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

/-- The Doléans measure of `(a, b] × F` is `E[1_F (A b - A a)]`. -/
lemma doleansMeasure_Ioc_prod (hA_int : ∀ t, Integrable (A t) P) {a b : ι} (hab : a ≤ b)
    {F : Set Ω} (hF : MeasurableSet F) :
    doleansMeasure P hA hA_rc hA_mono (Set.Ioc a b ×ˢ F)
      = ENNReal.ofReal (∫ ω in F, (A b ω - A a ω) ∂P) := by
  have h_int : Integrable (fun ω ↦ A b ω - A a ω) P := (hA_int b).sub (hA_int a)
  rw [doleansMeasure_prod hA hA_rc hA_mono measurableSet_Ioc hF,
    ofReal_integral_eq_lintegral_ofReal h_int.integrableOn
      (ae_of_all _ fun ω ↦ sub_nonneg.2 (hA_mono ω hab))]
  simp_rw [kernelOfRightContAdaptedMono_Ioc]

/-- The Doléans measure of `[⊥, b] × F` is `E[1_F (A b - A ⊥)]`. -/
lemma doleansMeasure_Iic_prod (hA_int : ∀ t, Integrable (A t) P) (b : ι) {F : Set Ω}
    (hF : MeasurableSet F) :
    doleansMeasure P hA hA_rc hA_mono (Set.Iic b ×ˢ F)
      = ENNReal.ofReal (∫ ω in F, (A b ω - A ⊥ ω) ∂P) := by
  have h_int : Integrable (fun ω ↦ A b ω - A ⊥ ω) P := (hA_int b).sub (hA_int ⊥)
  rw [doleansMeasure_prod hA hA_rc hA_mono measurableSet_Iic hF,
    ofReal_integral_eq_lintegral_ofReal h_int.integrableOn
      (ae_of_all _ fun ω ↦ sub_nonneg.2 (hA_mono ω bot_le))]
  simp_rw [kernelOfRightContAdaptedMono_Iic]

/-- The integral with respect to the Doléans measure is the iterated integral
`E[∫ f(s, ω) dA_s(ω)]`. -/
lemma lintegral_doleansMeasure {f : ι × Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂(doleansMeasure P hA hA_rc hA_mono)
      = ∫⁻ ω, ∫⁻ s, f (s, ω) ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) ∂P := by
  rw [doleansMeasure, lintegral_map hf measurable_swap]
  exact Measure.lintegral_compProd (hf.comp measurable_swap)

/-- If `E[A t - A ⊥]` is bounded by `C` for all `t`, then the total mass of the Doléans measure is
at most `C`. -/
lemma doleansMeasure_univ_le (hA_int : ∀ t, Integrable (A t) P) {C : ℝ}
    (hC : ∀ t, ∫ ω, (A t ω - A ⊥ ω) ∂P ≤ C) :
    doleansMeasure P hA hA_rc hA_mono Set.univ ≤ ENNReal.ofReal C := by
  obtain ⟨u, hu_mono, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  have h_univ : (Set.univ : Set (ι × Ω)) = ⋃ n, Set.Iic (u n) ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_prod, Set.mem_Iic, and_true, true_iff]
    exact (hu.eventually_ge_atTop p.1).exists
  have h_mono : Monotone fun n ↦ Set.Iic (u n) ×ˢ (Set.univ : Set Ω) :=
    fun n m hnm ↦ Set.prod_mono (Set.Iic_subset_Iic.2 (hu_mono hnm)) subset_rfl
  rw [h_univ, h_mono.measure_iUnion]
  refine iSup_le fun n ↦ ?_
  rw [doleansMeasure_Iic_prod hA hA_rc hA_mono hA_int (u n) .univ, Measure.restrict_univ]
  exact ENNReal.ofReal_le_ofReal (hC (u n))

/-- The Doléans measure is finite if `E[A t - A ⊥]` is bounded in `t`. -/
lemma isFiniteMeasure_doleansMeasure_of_integral_le (hA_int : ∀ t, Integrable (A t) P) {C : ℝ}
    (hC : ∀ t, ∫ ω, (A t ω - A ⊥ ω) ∂P ≤ C) :
    IsFiniteMeasure (doleansMeasure P hA hA_rc hA_mono) :=
  ⟨(doleansMeasure_univ_le hA hA_rc hA_mono hA_int hC).trans_lt ENNReal.ofReal_lt_top⟩

end MeasureTheory

end General

/-! ### Index set with a top element -/

variable {ι Ω : Type*} [CompleteLinearOrder ι] [DenselyOrdered ι] [TopologicalSpace ι]
  [OrderTopology ι] [PolishSpace ι] [MeasurableSpace ι] [BorelSpace ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration ι mΩ}
  {A B : ι → Ω → ℝ}

namespace StieltjesFunction

section Basic

variable (hA : Adapted 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω))
  (hA_mono : ∀ ω, Monotone (A · ω))

/-- The Stieltjes kernel of `A` gives mass `A ⊤ ω - A a ω` to `(a, ⊤]`. -/
lemma kernelOfRightContAdaptedMono_Ioi (ω : Ω) (a : ι) :
    kernelOfRightContAdaptedMono hA hA_rc hA_mono ω (Set.Ioi a)
      = ENNReal.ofReal (A ⊤ ω - A a ω) := by
  rw [← Set.Ioc_top, kernelOfRightContAdaptedMono_Ioc]

/-- The total mass of the Stieltjes kernel of `A` is `A ⊤ ω - A ⊥ ω`. -/
lemma kernelOfRightContAdaptedMono_univ (ω : Ω) :
    kernelOfRightContAdaptedMono hA hA_rc hA_mono ω Set.univ
      = ENNReal.ofReal (A ⊤ ω - A ⊥ ω) := by
  rw [← Set.Iic_top, kernelOfRightContAdaptedMono_Iic]

/-- The Stieltjes kernel of `A` consists of finite measures (since `ι` has a bottom and a top). -/
instance isFiniteMeasure_kernelOfRightContAdaptedMono (ω : Ω) :
    IsFiniteMeasure (kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) :=
  ⟨by simp [kernelOfRightContAdaptedMono_univ]⟩

end Basic

end StieltjesFunction

namespace MeasureTheory

open StieltjesFunction

section DoleansMeasure

variable (hA : Adapted 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω))
  (hA_mono : ∀ ω, Monotone (A · ω))

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
