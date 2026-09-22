/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.DoleansMeasureOfMono
public import BrownianMotion.StochasticIntegral.QuadraticVariation

/-! # L2 spaces of predictable processes

The integrands of the stochastic integral with respect to a square integrable martingale `M` are
the predictable processes which are square integrable with respect to the measure
`s ↦ E[∫ 1_s(t, ω) d⟨M⟩_t(ω)]` on `ι × Ω`. That measure is not a product measure, since the
predictable quadratic variation `⟨M⟩` depends on `ω`: it is the Doléans measure of `⟨M⟩`.

## Main definitions

* `ProbabilityTheory.L2Predictable E 𝓕 ν`: the `L2` space of predictable processes with values in
  `E`, with respect to a measure `ν` on `ι × Ω`.
* `ProbabilityTheory.predQuadVariationKernel X P 𝓕`: the kernel `ω ↦ d⟨X⟩(ω)`, which maps `ω` to
  the Stieltjes measure of the path of the predictable quadratic variation of `X`.
* `ProbabilityTheory.predQuadVariationMeasure X P 𝓕`: the Doléans measure of the predictable
  quadratic variation of `X`.
* `ProbabilityTheory.L2M F X P 𝓕`: the space of predictable processes with values in `F` which are
  square integrable with respect to `predQuadVariationMeasure X P 𝓕`.

## Main statements

* `ProbabilityTheory.IsStronglyPredictable.eLpNorm_two_trim_pow_eq_lintegral`: the squared norm
  in `L2M F X P 𝓕` of a predictable process `V` is `E[∫ ‖V_t‖² d⟨X⟩_t]`.
-/

@[expose] public section

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal

namespace ProbabilityTheory

section L2Predictable

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderBot ι]
  [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] [NormedAddCommGroup E]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {ν : Measure (ι × Ω)} {V : ι → Ω → E}

/-- `L2` space of predictable processes with values in `E`, with respect to a measure `ν` on
`ι × Ω`: the space `L2(ι × Ω, 𝓟, ν)` in which `𝓟` is the predictable σ-algebra. -/
abbrev L2Predictable (E : Type*) [NormedAddCommGroup E] (𝓕 : Filtration ι mΩ)
    (ν : Measure (ι × Ω)) : Type _ :=
  Lp E 2 (ν.trim 𝓕.predictable_le_prod)

/-- A predictable process which is square integrable with respect to `ν` is square integrable
with respect to the restriction of `ν` to the predictable σ-algebra. -/
lemma _root_.MeasureTheory.IsStronglyPredictable.memLp_trim (hV : IsStronglyPredictable 𝓕 V)
    (hV_mem : MemLp (uncurry V) 2 ν) :
    MemLp (uncurry V) 2 (ν.trim 𝓕.predictable_le_prod) :=
  ⟨hV.aestronglyMeasurable, by
    rw [eLpNorm_trim 𝓕.predictable_le_prod hV]
    exact hV_mem.2⟩

/-- The element of `L2Predictable E 𝓕 ν` defined by a predictable process which is square
integrable with respect to `ν`. -/
noncomputable def _root_.MeasureTheory.IsStronglyPredictable.toL2Predictable
    (hV : IsStronglyPredictable 𝓕 V) (hV_mem : MemLp (uncurry V) 2 ν) :
    L2Predictable E 𝓕 ν :=
  (hV.memLp_trim hV_mem).toLp (uncurry V)

lemma _root_.MeasureTheory.IsStronglyPredictable.coeFn_toL2Predictable
    (hV : IsStronglyPredictable 𝓕 V) (hV_mem : MemLp (uncurry V) 2 ν) :
    hV.toL2Predictable hV_mem =ᵐ[ν.trim 𝓕.predictable_le_prod] uncurry V :=
  MemLp.coeFn_toLp _

/-- The norm of a predictable process in `L2Predictable E 𝓕 ν` is its `L2` norm with respect to
`ν`. -/
lemma _root_.MeasureTheory.IsStronglyPredictable.norm_toL2Predictable
    (hV : IsStronglyPredictable 𝓕 V) (hV_mem : MemLp (uncurry V) 2 ν) :
    ‖hV.toL2Predictable hV_mem‖ = (eLpNorm (uncurry V) 2 ν).toReal := by
  rw [IsStronglyPredictable.toL2Predictable, Lp.norm_toLp,
    eLpNorm_trim 𝓕.predictable_le_prod hV]

end L2Predictable

section L2M

variable {ι Ω E F : Type*} [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
  [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] [PolishSpace ι] [DenselyOrdered ι]
  [NoMaxOrder ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous] [𝓕.IsComplete P] [Approximable 𝓕 P]
  {X : ι → Ω → E} {V : ι → Ω → F}

lemma adapted_predQuadVariation (X : ι → Ω → E) (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ι mΩ) [𝓕.IsRightContinuous] [𝓕.IsComplete P] [Approximable 𝓕 P] :
    Adapted 𝓕 ⟨X; P, 𝓕⟩ₘ :=
  (isStronglyPredictable_predQuadVariation (X := X) (P := P) (𝓕 := 𝓕)).stronglyAdapted.adapted

lemma isRightContinuous_predQuadVariation (X : ι → Ω → E) (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ι mΩ) [𝓕.IsRightContinuous] [𝓕.IsComplete P] [Approximable 𝓕 P] (ω : Ω) :
    IsRightContinuous (⟨X; P, 𝓕⟩ₘ · ω) :=
  (isCadlag_predQuadVariation ω).right_continuous

/-- The kernel `ω ↦ d⟨X⟩(ω)`: it maps `ω` to the Stieltjes measure of the path `⟨X⟩ · ω` of the
predictable quadratic variation of `X`. -/
noncomputable def predQuadVariationKernel (X : ι → Ω → E) (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ι mΩ) [𝓕.IsRightContinuous] [𝓕.IsComplete P] [Approximable 𝓕 P] :
    Kernel Ω ι :=
  StieltjesFunction.kernelOfRightContAdaptedMono (adapted_predQuadVariation X P 𝓕)
    (isRightContinuous_predQuadVariation X P 𝓕) monotone_predQuadVariation

instance : IsSFiniteKernel (predQuadVariationKernel X P 𝓕) := by
  unfold predQuadVariationKernel
  infer_instance

/-- The kernel `d⟨X⟩` gives mass `⟨X⟩ b ω - ⟨X⟩ a ω` to `(a, b]`. -/
lemma predQuadVariationKernel_Ioc (ω : Ω) (a b : ι) :
    predQuadVariationKernel X P 𝓕 ω (Set.Ioc a b)
      = ENNReal.ofReal (⟨X; P, 𝓕⟩ₘ b ω - ⟨X; P, 𝓕⟩ₘ a ω) :=
  StieltjesFunction.kernelOfRightContAdaptedMono_Ioc _ _ _ ω a b

/-- The Doléans measure of the predictable quadratic variation of `X`: the measure
`s ↦ E[∫ 1_s(t, ω) d⟨X⟩_t(ω)]` on `ι × Ω`. -/
noncomputable def predQuadVariationMeasure (X : ι → Ω → E) (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ι mΩ) [𝓕.IsRightContinuous] [𝓕.IsComplete P] [Approximable 𝓕 P] :
    Measure (ι × Ω) :=
  doleansMeasureOfMono P ⟨X; P, 𝓕⟩ₘ (adapted_predQuadVariation X P 𝓕)
    (isRightContinuous_predQuadVariation X P 𝓕) monotone_predQuadVariation

lemma predQuadVariationMeasure_eq_map :
    predQuadVariationMeasure X P 𝓕 = (P ⊗ₘ predQuadVariationKernel X P 𝓕).map Prod.swap := rfl

/-- The measure of `(a, b] × F` is `E[1_F (⟨X⟩ b - ⟨X⟩ a)]`. -/
lemma predQuadVariationMeasure_Ioc_prod (hX_int : ∀ t, Integrable (⟨X; P, 𝓕⟩ₘ t) P) {a b : ι}
    (hab : a ≤ b) {s : Set Ω} (hs : MeasurableSet s) :
    predQuadVariationMeasure X P 𝓕 (Set.Ioc a b ×ˢ s)
      = ENNReal.ofReal (∫ ω in s, (⟨X; P, 𝓕⟩ₘ b ω - ⟨X; P, 𝓕⟩ₘ a ω) ∂P) :=
  doleansMeasureOfMono_Ioc_prod _ _ _ hX_int hab hs

/-- The integral with respect to `predQuadVariationMeasure X P 𝓕` is the iterated integral
`E[∫ f(t, ω) d⟨X⟩_t(ω)]`. -/
lemma lintegral_predQuadVariationMeasure {f : ι × Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂(predQuadVariationMeasure X P 𝓕)
      = ∫⁻ ω, ∫⁻ t, f (t, ω) ∂(predQuadVariationKernel X P 𝓕 ω) ∂P :=
  lintegral_doleansMeasureOfMono _ _ _ hf

/-- The measure `predQuadVariationMeasure X P 𝓕` is finite if `E[⟨X⟩ t - ⟨X⟩ ⊥]` is bounded
in `t`. -/
lemma isFiniteMeasure_predQuadVariationMeasure (hX_int : ∀ t, Integrable (⟨X; P, 𝓕⟩ₘ t) P)
    {C : ℝ} (hC : ∀ t, ∫ ω, (⟨X; P, 𝓕⟩ₘ t ω - ⟨X; P, 𝓕⟩ₘ ⊥ ω) ∂P ≤ C) :
    IsFiniteMeasure (predQuadVariationMeasure X P 𝓕) :=
  isFiniteMeasure_doleansMeasureOfMono_of_integral_le _ _ _ hX_int hC

/-- The space `L2(M)` of predictable processes with values in `F` which are square integrable with
respect to the Doléans measure of the predictable quadratic variation of `X`. -/
abbrev L2M (F : Type*) [NormedAddCommGroup F] (X : ι → Ω → E) (P : Measure Ω)
    [IsFiniteMeasure P] (𝓕 : Filtration ι mΩ) [𝓕.IsRightContinuous] [𝓕.IsComplete P]
    [Approximable 𝓕 P] : Type _ :=
  L2Predictable F 𝓕 (predQuadVariationMeasure X P 𝓕)

/-- The squared `L2(M)` norm of a predictable process `V` is `E[∫ ‖V_t‖² d⟨X⟩_t]`. -/
lemma _root_.MeasureTheory.IsStronglyPredictable.eLpNorm_two_trim_pow_eq_lintegral
    [MeasurableSpace F] [BorelSpace F] (hV : IsStronglyPredictable 𝓕 V) :
    eLpNorm (uncurry V) 2 ((predQuadVariationMeasure X P 𝓕).trim 𝓕.predictable_le_prod) ^ 2
      = ∫⁻ ω, ∫⁻ t, ‖V t ω‖ₑ ^ 2 ∂(predQuadVariationKernel X P 𝓕 ω) ∂P := by
  have hV_meas : Measurable (uncurry V) :=
    (hV.mono 𝓕.predictable_le_prod).measurable
  rw [eLpNorm_trim 𝓕.predictable_le_prod hV]
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := uncurry V)
    (μ := predQuadVariationMeasure X P 𝓕) (p := 2) (by simp)
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  rw [h, lintegral_predQuadVariationMeasure (hV_meas.enorm.pow_const 2)]
  rfl

end L2M

end ProbabilityTheory
