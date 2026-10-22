/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import BrownianMotion.Auxiliary.Adapted
public import BrownianMotion.Auxiliary.StoppedValue
public import BrownianMotion.StochasticIntegral.ApproxSeq
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Martingale.Centering

@[expose] public section

open Filter TopologicalSpace Function
open scoped NNReal ENNReal Topology

namespace MeasureTheory

namespace Martingale

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [OrderBot ι] [SecondCountableTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : ι → Ω → E} {τ σ : Ω → WithTop ι} {n : ι}

lemma condExp_stoppedValue_stopping_time_ae_eq_restrict_le_of_countable_range
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω)) {i : ι} (hτ_le : ∀ x, τ x ≤ i)
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ)
    (hτ_countable_range : (Set.range τ).Countable) :
    μ[stoppedValue X τ|hσ.measurableSpace] =ᵐ[μ.restrict {x : Ω | τ x ≤ σ x}] stoppedValue X τ := by
  borelize ι
  rw [ae_eq_restrict_iff_indicator_ae_eq
    (hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ))]
  refine (condExp_indicator
    (h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range)
    (hτ.measurableSet_stopping_time_le hσ)).symm.trans ?_
  have h_int :
      Integrable ({ω : Ω | τ ω ≤ σ ω}.indicator (stoppedValue X τ)) μ :=
    Integrable.indicator
      (h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range)
      <| hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ)
  have h_meas : AEStronglyMeasurable[hσ.measurableSpace]
      ({ω : Ω | τ ω ≤ σ ω}.indicator (stoppedValue X τ)) μ := by
    refine StronglyMeasurable.aestronglyMeasurable ?_
    refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on
      (hτ.measurableSet_le_stopping_time hσ) ?_ ?_ ?_
    · intro t ht
      rw [Set.inter_comm _ t] at ht ⊢
      rw [hτ.measurableSet_inter_le_iff hσ, IsStoppingTime.measurableSet_min_iff hτ hσ] at ht
      exact ht.2
    · exact (stronglyMeasurable_stoppedValue
        (h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC) hRC
        hτ).indicator (hτ.measurableSet_le_stopping_time hσ)
    · intro x hx
      simp only [hx, Set.indicator_of_notMem, not_false_iff]
  exact condExp_of_aestronglyMeasurable' hσ.measurableSpace_le h_meas h_int

lemma stoppedValue_min_ae_eq_condExp_of_countable_range
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
    (hτ_countable_range : (Set.range τ).Countable) (hσ_countable_range : (Set.range σ).Countable) :
    (stoppedValue X fun x ↦ min (σ x) (τ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] := by
  borelize ι
  refine
    (h.stoppedValue_ae_eq_condExp_of_le_of_countable_range hτ
      (hσ.min hτ) (fun x ↦ min_le_right _ _) hτ_le hτ_countable_range ?_).trans ?_
  · exact (hτ_countable_range.union hσ_countable_range).mono <| by grind
  refine ae_of_ae_restrict_of_ae_restrict_compl {x | σ x ≤ τ x} ?_ ?_
  · exact condExp_min_stopping_time_ae_eq_restrict_le hσ hτ
  · suffices μ[stoppedValue X τ|(hσ.min hτ).measurableSpace] =ᵐ[μ.restrict {x | τ x ≤ σ x}]
        μ[stoppedValue X τ|hσ.measurableSpace] by
      rw [ae_restrict_iff' (hσ.measurableSpace_le _ (hσ.measurableSet_le_stopping_time hτ).compl)]
      rw [Filter.EventuallyEq, ae_restrict_iff'] at this
      swap; · exact hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ)
      filter_upwards [this] with x hx hx_mem
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx_mem
      exact hx hx_mem.le
    apply Filter.EventuallyEq.trans _ ((condExp_min_stopping_time_ae_eq_restrict_le hτ hσ).trans _)
    · exact stoppedValue X τ
    · rw [IsStoppingTime.measurableSpace_min hσ hτ,
        IsStoppingTime.measurableSpace_min hτ hσ, inf_comm]
    · have h1 : μ[stoppedValue X τ|hτ.measurableSpace] = stoppedValue X τ := by
        apply condExp_of_stronglyMeasurable hτ.measurableSpace_le
        · exact (stronglyMeasurable_stoppedValue
            (h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC) hRC
            hτ)
        · exact h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range
      rw [h1]
      exact (h.condExp_stoppedValue_stopping_time_ae_eq_restrict_le_of_countable_range hRC hτ_le
        hτ hσ hτ_countable_range).symm

/-- **Optional sampling theorem** for general time indices
(assuming existence of `DiscreteApproxSequence`). -/
theorem stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
    (τn : DiscreteApproxSequence 𝓕 τ μ) (σn : DiscreteApproxSequence 𝓕 σ μ) :
    (stoppedValue X fun x ↦ min (τ x) (σ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] := by
  borelize ι
  set τn' := (discreteApproxSequence_of 𝓕 hτ_le τn).inf σn
  have hint (m : ℕ) : stoppedValue X (τn' m) =ᵐ[μ]
      μ[stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m) |
        (σn.isStoppingTime m).measurableSpace] := by
    refine EventuallyEq.trans (Eq.eventuallyEq ?_)
      (h.stoppedValue_min_ae_eq_condExp_of_countable_range hRC
        ((discreteApproxSequence_of 𝓕 hτ_le τn).isStoppingTime m)
        (σn.isStoppingTime m) (discreteApproxSequence_of_le hτ_le τn m)
        (DiscreteApproxSequence.countable _ _) (σn.countable m))
    congr 1; ext ω; rw [min_comm]; rfl
  have hintgbl : Integrable (stoppedValue X τ) μ :=
    integrable_stoppedValue_of_discreteApproxSequence' h hRC hτ_le τn
  refine ae_eq_condExp_of_forall_setIntegral_eq _ hintgbl ?_ ?_
    ((stronglyMeasurable_stoppedValue
        (h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC) hRC
        (hτ.min hσ)).aestronglyMeasurable.mono ((hτ.min hσ).measurableSpace_mono hσ <|
          fun ω ↦ min_le_right _ _))
  · exact fun s hs _ ↦ (integrable_stoppedValue_of_discreteApproxSequence' h hRC
      (fun _ ↦ min_le_of_left_le <| hτ_le _) <| τn.inf σn).integrableOn
  rintro s hs -
  have : (fun m ↦ ∫ ω in s, stoppedValue X (τn' m) ω ∂μ) =
    fun m ↦ ∫ ω in s, stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m) ω ∂μ := by
    ext m
    rw [setIntegral_congr_ae (g := μ[stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m) |
        (σn.isStoppingTime m).measurableSpace]) (hσ.measurableSpace_le _ hs)
        (by filter_upwards [hint m] with ω hω _ using hω)]
    exact setIntegral_condExp _
      (h.integrable_stoppedValue_of_countable_range _
        (DiscreteApproxSequence.isStoppingTime _ _) (discreteApproxSequence_of_le hτ_le τn m)
        (DiscreteApproxSequence.countable _ m))
      (hσ.measurableSpace_mono (σn.isStoppingTime m) (σn.le m) _ hs)
  refine tendsto_nhds_unique (f := (fun m ↦ ∫ (ω : Ω) in s, stoppedValue X (τn' m) ω ∂μ))
    (l := atTop) ?_ (this ▸ ?_)
  · refine tendsto_setIntegral_of_L1' _ ?_
      (tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence_of_le h hRC τn'
        (τn.discreteApproxSequence_of_le_inf_le_of_left σn hτ_le)) _
    rw [eventually_atTop]
    exact ⟨0, fun m _ ↦ (h.integrable_stoppedValue_of_countable_range _
      (DiscreteApproxSequence.isStoppingTime _ _)
      (τn.discreteApproxSequence_of_le_inf_le_of_left σn hτ_le m)
      (DiscreteApproxSequence.countable _ m))⟩
  · refine tendsto_setIntegral_of_L1' _ ?_
      (tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence h hRC hτ_le τn) _
    rw [eventually_atTop]
    exact ⟨0, fun m _ ↦ (h.integrable_stoppedValue_of_countable_range _
        (DiscreteApproxSequence.isStoppingTime _ _) (discreteApproxSequence_of_le hτ_le τn m)
        (DiscreteApproxSequence.countable _ m))⟩

-- TODO: change name of `stoppedValue_min_ae_eq_condExp` in mathlib and remove the prime here
/-- **Optional sampling theorem** for approximable time indices. -/
theorem stoppedValue_min_ae_eq_condExp'
    [Approximable 𝓕 μ] (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n) :
    (stoppedValue X fun x ↦ min (τ x) (σ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] :=
  stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence h hRC hτ hσ hτ_le
    (hτ.discreteApproxSequence μ) (hσ.discreteApproxSequence μ)

lemma stoppedValue_ae_eq_condExp_of_le_const'
    [Approximable 𝓕 μ] (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) :
    stoppedValue X τ =ᵐ[μ] μ[X n|hτ.measurableSpace] := by
  convert stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence h hRC
    (isStoppingTime_const 𝓕 n) hτ (fun _ ↦ le_rfl) (discreteApproxSequence_const 𝓕 n)
      (hτ.discreteApproxSequence μ) using 2
  · ext ω
    rw [eq_comm, min_eq_right_iff]
    exact hτ_le ω
  · rfl

theorem condExp_stoppedValue_ae_eq_stoppedProcess [Approximable 𝓕 μ] {n : ι}
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) (i : ι) :
    μ[stoppedValue X τ|𝓕 i] =ᵐ[μ] stoppedProcess X τ i := by
  simp_rw [stoppedProcess_eq_stoppedValue, min_comm]
  exact EventuallyEq.trans (Eq.eventuallyEq <| by simp)
    (stoppedValue_min_ae_eq_condExp' h hRC hτ (isStoppingTime_const 𝓕 i) hτ_le).symm

lemma stoppedProcess [Approximable 𝓕 μ] [PseudoMetrizableSpace ι]
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω)) (hτ : IsStoppingTime 𝓕 τ) :
    Martingale (stoppedProcess X τ) 𝓕 μ := by
  borelize ι
  constructor
  · exact fun t ↦
      h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC |>.stoppedProcess hτ
        |>.stronglyAdapted t
  intro s t hst
  nth_rw 1 [stoppedProcess_eq_stoppedValue]
  grw [condExp_stoppedValue_ae_eq_stoppedProcess h hRC ((isStoppingTime_const 𝓕 t).min hτ) (n := t)]
  · apply ae_of_all
    simp only [MeasureTheory.stoppedProcess]
    intro ω
    rw [min_left_comm, min_eq_right]
    grw [min_le_left]
    simpa
  simp

end Martingale

section subsupermartingale

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]

section Nat

variable {σ τ : Ω → WithTop ℕ} {X : ℕ → Ω → E} (𝓕 : Filtration ℕ mΩ)

theorem Submartingale.stoppedValue_min_ae_le_condExp_nat
    [PartialOrder E] [OrderClosedTopology E] [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration P 𝓕] (hX : Submartingale X 𝓕 P) {k : ℕ} (hτk : ∀ᵐ ω ∂P, τ ω ≤ k)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] := by
  set τ' := τ ⊓ k
  have hτ'_le (ω) : τ' ω ≤ k := inf_le_right
  have hτ'_eq : τ' =ᵐ[P] τ := by filter_upwards [hτk] with ω hω using inf_eq_left.mpr hω
  suffices h : stoppedValue X (τ' ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ'|hσ.measurableSpace] from
    have ⟨hsv_τ, hsv_τσ⟩  : stoppedValue X τ' =ᵐ[P] stoppedValue X τ
      ∧ stoppedValue X (τ' ⊓ σ) =ᵐ[P] stoppedValue X (τ ⊓ σ) := by
        constructor <;> filter_upwards [hτ'_eq] with ω hω using by simp [stoppedValue, hω]
    hsv_τσ.symm.le.trans (h.trans (condExp_congr_ae hsv_τ).le)
  set M := martingalePart X 𝓕 P ; set A := predictablePart X 𝓕 P
  have hMart : Martingale M 𝓕 P := martingale_martingalePart hX.stronglyAdapted hX.integrable
  have hDecomp : M + A = X := martingalePart_add_predictablePart 𝓕 P X
  have hSV_eq (ρ ω) : stoppedValue X ρ ω = stoppedValue M ρ ω + stoppedValue A ρ ω := by
    simp only [stoppedValue, ← hDecomp, Pi.add_apply]
  have hA_integrable (n) : Integrable (A n) P := by
    have hAn : A n = X n - M n := funext fun ω ↦ by
      simpa only [Pi.add_apply, Pi.sub_apply, eq_comm, sub_eq_iff_eq_add, add_comm] using
        congr_fun (congr_fun (martingalePart_add_predictablePart 𝓕 P X) n) ω
    simpa only [hAn] using (hX.integrable n).sub (integrable_martingalePart hX.integrable n)
  have hM_OS : (stoppedValue M <| min σ τ') =ᵐ[P] P[stoppedValue M τ'|hσ.measurableSpace] :=
    Martingale.stoppedValue_min_ae_eq_condExp hMart (hτ.min <| isStoppingTime_const 𝓕 k) hσ hτ'_le
  have hne_top (ω): τ' ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top inf_le_right
  have hA_le : ∀ᵐ ω ∂P, stoppedValue A (τ' ⊓ σ) ω ≤ stoppedValue A τ' ω := by
    filter_upwards [hX.monotone_predictablePart] with ω hm using
      hm (WithTop.untopA_mono (hne_top ω) inf_le_left)
  have hA_int_min : Integrable (stoppedValue A (τ' ⊓ σ)) P :=
    integrable_stoppedValue ℕ ((hτ.min <| isStoppingTime_const 𝓕 k).min hσ) hA_integrable
      (fun ω ↦ (inf_le_left (a := τ' ω)).trans (hτ'_le ω))
  have hA_int : Integrable (stoppedValue A τ') P :=
    integrable_stoppedValue _ (hτ.min <| isStoppingTime_const 𝓕 k) hA_integrable hτ'_le
  have hA_condExp : stoppedValue A (τ' ⊓ σ) ≤ᵐ[P] P[stoppedValue A τ'|hσ.measurableSpace] :=
    have hA_meas : AEStronglyMeasurable[hσ.measurableSpace] (stoppedValue A (τ' ⊓ σ)) P :=
      ((measurable_stoppedValue stronglyAdapted_predictablePart'.isStronglyProgressive_of_discrete
        ((hτ.min <| isStoppingTime_const 𝓕 k).min hσ)).mono
        (((hτ.min <| isStoppingTime_const 𝓕 k).min hσ).measurableSpace_mono hσ
          inf_le_right) le_rfl).stronglyMeasurable.aestronglyMeasurable
    (condExp_of_aestronglyMeasurable' hσ.measurableSpace_le hA_meas hA_int_min).symm.le.trans
      (condExp_mono hA_int_min hA_int hA_le)
  have hM_int : Integrable (stoppedValue M τ') P := integrable_stoppedValue ℕ
      (hτ.min <| isStoppingTime_const 𝓕 k) (integrable_martingalePart hX.integrable) hτ'_le
  filter_upwards [hM_OS.le, hA_condExp, condExp_add hM_int hA_int hσ.measurableSpace,
    condExp_congr_ae (ae_of_all P fun ω ↦ (hSV_eq τ' ω).symm)] with ω h1 h2 h3 h4 using
      hSV_eq (τ' ⊓ σ) ω ▸ calc stoppedValue M (τ' ⊓ σ) ω + stoppedValue A (τ' ⊓ σ) ω
                              ≤ P[stoppedValue M τ' + stoppedValue A τ'|hσ.measurableSpace] ω :=
                                  by grind only [add_le_add h1 h2, Pi.add_apply]
                              _ = _ := h4

theorem Supermartingale.condExp_ae_le_stoppedValue_min_nat [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E] [SigmaFiniteFiltration P 𝓕]
    (hX : Supermartingale X 𝓕 P) {k : ℕ} (hτk : ∀ᵐ ω ∂P, τ ω ≤ k)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    P[stoppedValue X τ|hσ.measurableSpace] ≤ᵐ[P] stoppedValue X (τ ⊓ σ) := by
  have hXneg : Submartingale (-X) 𝓕 P := hX.neg
  have h1 := hXneg.stoppedValue_min_ae_le_condExp_nat 𝓕 hτk hσ hτ
  have hsvn : ∀ τ', stoppedValue (-X) τ' = -stoppedValue X τ' := fun τ' => by
    ext ω; simp [stoppedValue]
  rw [hsvn, hsvn] at h1
  exact (h1.trans (condExp_neg (stoppedValue X τ) hσ.measurableSpace).le).mono
    fun ω hω => neg_le_neg_iff.mp hω

end Nat

section Integrable

/-! ### Integrability of a real submartingale sampled at a bounded stopping time -/

/-- If a sequence of integrable functions with `L¹` norms bounded by `C` converges almost
everywhere to `g`, then `g` is integrable and its `L¹` norm is at most `C`.
This is a consequence of Fatou's lemma. -/
lemma integrable_of_tendsto_ae_of_integral_norm_le {F : Type*} [NormedAddCommGroup F]
    {f : ℕ → Ω → F} {g : Ω → F} {C : ℝ} (hf : ∀ n, Integrable (f n) P)
    (hC : ∀ n, ∫ ω, ‖f n ω‖ ∂P ≤ C) (h : ∀ᵐ ω ∂P, Tendsto (f · ω) atTop (𝓝 (g ω))) :
    Integrable g P ∧ ∫ ω, ‖g ω‖ ∂P ≤ C := by
  have hC0 : 0 ≤ C := (integral_nonneg fun _ ↦ norm_nonneg _).trans (hC 0)
  have hg_meas : AEStronglyMeasurable g P :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n ↦ (hf n).1) h
  have h_le : eLpNorm g 1 P ≤ ENNReal.ofReal C := by
    refine seq_tendsto_ae_bounded 1 (fun n ↦ ?_) h (fun n ↦ (hf n).1)
    rw [eLpNorm_one_eq_lintegral_enorm (hf n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hf n)]
    exact ENNReal.ofReal_le_ofReal (hC n)
  have hg : Integrable g P :=
    memLp_one_iff_integrable.1 (h_le.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hg, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm hg_meas, ← ofReal_integral_norm_eq_lintegral_enorm hg] at h_le
  exact (ENNReal.ofReal_le_ofReal_iff hC0).1 h_le

variable {ι : Type*} [LinearOrder ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → ℝ} {τ : Ω → WithTop ι}
  {k : ι}

/-- If `τ` is a stopping time with countable range which is bounded by `k`, then the time equal
to `τ` on `τ ⁻¹' A` and to `k` elsewhere is a stopping time, for any set `A`. -/
lemma IsStoppingTime.piecewise_preimage_const_of_countable_range {A : Set (WithTop ι)}
    [DecidablePred (· ∈ τ ⁻¹' A)] (hτ : IsStoppingTime 𝓕 τ) (hτk : ∀ ω, τ ω ≤ k)
    (hτ_count : (Set.range τ).Countable) :
    IsStoppingTime 𝓕 ((τ ⁻¹' A).piecewise τ (fun _ ↦ (k : WithTop ι))) := by
  intro i
  by_cases hki : k ≤ i
  · convert MeasurableSet.univ
    rename_i ω
    simp only [Set.mem_eq_mem, Set.mem_univ, iff_true]
    refine le_trans ?_ (WithTop.coe_le_coe.2 hki)
    by_cases hω : ω ∈ τ ⁻¹' A <;> simp [hω, hτk ω]
  · have h_eq : {ω | (τ ⁻¹' A).piecewise τ (fun _ ↦ (k : WithTop ι)) ω ≤ i}
        = ⋃ j ∈ {j : ι | (j : WithTop ι) ∈ Set.range τ ∧ (j : WithTop ι) ∈ A ∧ j ≤ i},
          {ω | τ ω = j} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      by_cases hω : ω ∈ τ ⁻¹' A
      · rw [Set.piecewise_eq_of_mem _ _ _ hω]
        refine ⟨fun h ↦ ?_, fun ⟨j, hj, hjτ⟩ ↦ hjτ ▸ WithTop.coe_le_coe.2 hj.2.2⟩
        obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top h)
        exact ⟨j, ⟨⟨ω, hj.symm⟩, hj ▸ hω, WithTop.coe_le_coe.1 (hj ▸ h)⟩, hj.symm⟩
      · rw [Set.piecewise_eq_of_notMem _ _ _ hω]
        refine ⟨fun h ↦ absurd (WithTop.coe_le_coe.1 h) hki, fun ⟨j, hj, hjτ⟩ ↦ ?_⟩
        exact absurd (show τ ω ∈ A from hjτ ▸ hj.2.1) hω
    rw [h_eq]
    refine MeasurableSet.biUnion ?_ fun j hj ↦
      𝓕.mono hj.2.2 _ (hτ.measurableSet_eq_of_countable_range hτ_count j)
    exact (hτ_count.preimage WithTop.coe_injective).mono fun j hj ↦ hj.1

/-- A stopping time `τ ≤ k` with countable range is the limit of a sequence of stopping times
`ρ m` with values in finite sets, such that `ρ m ω` is either `τ ω` or `k`, and is equal to `τ ω`
for `m` large enough. -/
lemma IsStoppingTime.exists_seq_mem_finset_of_countable_range
    (hτ : IsStoppingTime 𝓕 τ) (hτk : ∀ ω, τ ω ≤ k) (hτ_count : (Set.range τ).Countable) :
    ∃ (ρ : ℕ → Ω → WithTop ι) (S : ℕ → Finset ι), (∀ m, IsStoppingTime 𝓕 (ρ m)) ∧
      (∀ m ω, ρ m ω ∈ WithTop.some '' (S m : Set ι)) ∧ (∀ m ω, ρ m ω = τ ω ∨ ρ m ω = k) ∧
      ∀ ω, ∀ᶠ m in atTop, ρ m ω = τ ω := by
  classical
  -- we enumerate the values of `τ`, and `ρ m` is equal to `τ` if `τ` is one of the first `m`
  -- values and to `k` otherwise
  have : Nonempty ι := ⟨k⟩
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.1
    (hτ_count.preimage (WithTop.coe_injective (α := ι)))
  let A (m : ℕ) : Set (WithTop ι) := WithTop.some '' ((Finset.range m).image f : Set ι)
  let ρ (m : ℕ) : Ω → WithTop ι := (τ ⁻¹' A m).piecewise τ (fun _ ↦ (k : WithTop ι))
  refine ⟨ρ, fun m ↦ insert k ((Finset.range m).image f),
    fun m ↦ hτ.piecewise_preimage_const_of_countable_range hτk hτ_count, fun m ω ↦ ?_,
    fun m ω ↦ ?_, fun ω ↦ ?_⟩
  · by_cases hω : ω ∈ τ ⁻¹' A m
    · have hρω : ρ m ω = τ ω := Set.piecewise_eq_of_mem _ _ _ hω
      obtain ⟨i, hi, hiτ⟩ := hω
      exact ⟨i, Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hi)),
        hiτ.trans hρω.symm⟩
    · have hρω : ρ m ω = k := Set.piecewise_eq_of_notMem _ _ _ hω
      exact ⟨k, Finset.mem_coe.2 (Finset.mem_insert_self _ _), hρω.symm⟩
  · by_cases hω : ω ∈ τ ⁻¹' A m
    · exact .inl (Set.piecewise_eq_of_mem _ _ _ hω)
    · exact .inr (Set.piecewise_eq_of_notMem _ _ _ hω)
  · obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (hτk ω))
    obtain ⟨n, hn⟩ := hf ⟨ω, hj.symm⟩
    refine eventually_atTop.2 ⟨n + 1, fun m hm ↦ ?_⟩
    have hω : ω ∈ τ ⁻¹' A m :=
      ⟨j, Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 hm, hn⟩), hj⟩
    exact Set.piecewise_eq_of_mem _ _ _ hω

variable [OrderBot ι] [IsFiniteMeasure P]

/-- For a real submartingale `X` and a stopping time `τ` with values in a finite set,
`E[X ⊥] ≤ E[X τ]`. -/
lemma Submartingale.integral_bot_le_integral_stoppedValue_of_mem_finset
    (hX : Submartingale X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) {s : Finset ι}
    (hτs : ∀ ω, τ ω ∈ WithTop.some '' s) :
    ∫ ω, X ⊥ ω ∂P ≤ ∫ ω, stoppedValue X τ ω ∂P := by
  classical
  induction s using Finset.induction_on_max generalizing τ with
  | empty =>
    have : IsEmpty Ω := ⟨fun ω ↦ by simpa using hτs ω⟩
    simp [Measure.eq_zero_of_isEmpty P]
  | insert a s has ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · have hτa (ω : Ω) : τ ω = a := by simpa [eq_comm] using hτs ω
      have hXτ : stoppedValue X τ = X a := by ext ω; simp [stoppedValue, hτa ω]
      rw [hXτ]
      simpa using hX.setIntegral_le (bot_le : ⊥ ≤ a) MeasurableSet.univ
    · -- we compare `τ` to `τ ⊓ u`, where `u` is the second largest possible value of `τ`
      set u := s.max' hs
      have hua : u < a := has u (s.max'_mem hs)
      have hτ' : IsStoppingTime 𝓕 (fun ω ↦ min (τ ω) u) := hτ.min_const u
      have hA : MeasurableSet[𝓕 u] {ω | τ ω ≤ u} := hτ u
      have hA' : MeasurableSet {ω | τ ω ≤ u} := 𝓕.le u _ hA
      have h_of_not_le (ω : Ω) (hω : ¬ τ ω ≤ u) : τ ω = a := by
        obtain ⟨i, hi, hiτ⟩ := hτs ω
        rcases Finset.mem_insert.1 hi with rfl | his
        · exact hiτ.symm
        · exact absurd (hiτ ▸ WithTop.coe_le_coe.2 (s.le_max' i his)) hω
      have hτ's (ω : Ω) : min (τ ω) u ∈ WithTop.some '' s := by
        by_cases hω : τ ω ≤ u
        · obtain ⟨i, hi, hiτ⟩ := hτs ω
          rcases Finset.mem_insert.1 hi with rfl | his
          · exact absurd (hiτ ▸ hω) (by simpa using hua)
          · exact ⟨i, his, by rw [min_eq_left hω, hiτ]⟩
        · exact ⟨u, s.max'_mem hs, (min_eq_right (not_le.1 hω).le).symm⟩
      have hint : Integrable (stoppedValue X τ) P :=
        integrable_stoppedValue_of_mem_finset hτ hX.integrable hτs
      have hint' : Integrable (stoppedValue X fun ω ↦ min (τ ω) u) P :=
        integrable_stoppedValue_of_mem_finset hτ' hX.integrable hτ's
      calc ∫ ω, X ⊥ ω ∂P
        _ ≤ ∫ ω, stoppedValue X (fun ω ↦ min (τ ω) u) ω ∂P := ih hτ' hτ's
        _ = ∫ ω in {ω | τ ω ≤ u}, stoppedValue X τ ω ∂P + ∫ ω in {ω | τ ω ≤ u}ᶜ, X u ω ∂P := by
          rw [← integral_add_compl hA' hint']
          congr 1
          · exact setIntegral_congr_fun hA' fun ω (hω : τ ω ≤ u) ↦ by
              simp [stoppedValue, min_eq_left hω]
          · exact setIntegral_congr_fun hA'.compl fun ω (hω : ¬ τ ω ≤ u) ↦ by
              simp [stoppedValue, min_eq_right (not_le.1 hω).le]
        _ ≤ ∫ ω in {ω | τ ω ≤ u}, stoppedValue X τ ω ∂P + ∫ ω in {ω | τ ω ≤ u}ᶜ, X a ω ∂P :=
          add_le_add le_rfl (hX.setIntegral_le hua.le hA.compl)
        _ = ∫ ω, stoppedValue X τ ω ∂P := by
          rw [← integral_add_compl hA' hint]
          congr 1
          exact setIntegral_congr_fun hA'.compl fun ω (hω : ¬ τ ω ≤ u) ↦ by
            simp [stoppedValue, h_of_not_le ω hω]

/-- For a real submartingale `X` and a stopping time `τ ≤ k` with countable range,
`E[(X τ)⁺] ≤ E[(X k)⁺]`, stated in terms of Lebesgue integrals. -/
lemma Submartingale.lintegral_ofReal_stoppedValue_le_of_countable_range
    (hX : Submartingale X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) (hτk : ∀ ω, τ ω ≤ k)
    (hτ_count : (Set.range τ).Countable) :
    ∫⁻ ω, ENNReal.ofReal (stoppedValue X τ ω) ∂P ≤ ∫⁻ ω, ENNReal.ofReal (X k ω) ∂P := by
  let t : Set ι := {i | (i : WithTop ι) ∈ Set.range τ}
  have ht : t.Countable := hτ_count.preimage WithTop.coe_injective
  have hm' (i : ι) : MeasurableSet[𝓕 i] {ω | τ ω = i} :=
    hτ.measurableSet_eq_of_countable_range hτ_count i
  have hm : ∀ i ∈ t, MeasurableSet {ω | τ ω = i} := fun i _ ↦ 𝓕.le i _ (hm' i)
  have hd : t.PairwiseDisjoint (fun i ↦ {ω | τ ω = i}) := fun i _ j _ hij ↦
    Set.disjoint_left.2 fun ω hi hj ↦ hij (WithTop.coe_injective (hi.symm.trans hj))
  have hU : ⋃ i ∈ t, {ω | τ ω = i} = Set.univ := by
    refine Set.eq_univ_of_forall fun ω ↦ ?_
    obtain ⟨j, hj⟩ :=
      WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (hτk ω))
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨j, ⟨ω, hj.symm⟩, hj.symm⟩
  -- we decompose the integrals along the countably many values of `τ`
  have key (f : Ω → ℝ≥0∞) : ∫⁻ ω, f ω ∂P = ∑' i : t, ∫⁻ ω in {ω | τ ω = i}, f ω ∂P := by
    rw [← lintegral_biUnion ht hm hd, hU, Measure.restrict_univ]
  have h_pos (Y : Ω → ℝ) (hY : Integrable Y P) (s : Set Ω) :
      ∫⁻ ω in s, ENNReal.ofReal (Y ω) ∂P = ENNReal.ofReal (∫ ω in s, max (Y ω) 0 ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hY.pos_part.integrableOn
      (ae_of_all _ fun ω ↦ le_max_right _ _)]
    simp
  rw [key, key (fun ω ↦ ENNReal.ofReal (X k ω))]
  refine ENNReal.tsum_le_tsum fun i ↦ ?_
  have hik : (i : ι) ≤ k := by
    obtain ⟨ω, hω⟩ := i.2
    exact WithTop.coe_le_coe.1 (hω ▸ hτk ω)
  calc ∫⁻ ω in {ω | τ ω = i}, ENNReal.ofReal (stoppedValue X τ ω) ∂P
    _ = ∫⁻ ω in {ω | τ ω = i}, ENNReal.ofReal (X i ω) ∂P :=
      setLIntegral_congr_fun (hm i i.2) fun ω (hω : τ ω = i) ↦ by simp [stoppedValue, hω]
    _ = ENNReal.ofReal (∫ ω in {ω | τ ω = i}, max (X i ω) 0 ∂P) := h_pos _ (hX.integrable i) _
    _ ≤ ENNReal.ofReal (∫ ω in {ω | τ ω = i}, max (X k ω) 0 ∂P) :=
      ENNReal.ofReal_le_ofReal (hX.pos.setIntegral_le hik (hm' i))
    _ = ∫⁻ ω in {ω | τ ω = i}, ENNReal.ofReal (X k ω) ∂P := (h_pos _ (hX.integrable k) _).symm

/-- `L¹` bound for a real submartingale sampled at a stopping time `τ ≤ k` with values in a
finite set. -/
lemma Submartingale.integral_abs_stoppedValue_le_of_mem_finset
    (hX : Submartingale X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) (hτk : ∀ ω, τ ω ≤ k) {s : Finset ι}
    (hτs : ∀ ω, τ ω ∈ WithTop.some '' s) :
    ∫ ω, |stoppedValue X τ ω| ∂P ≤ 2 * ∫ ω, max (X k ω) 0 ∂P - ∫ ω, X ⊥ ω ∂P := by
  have hint : Integrable (stoppedValue X τ) P :=
    integrable_stoppedValue_of_mem_finset hτ hX.integrable hτs
  have hτ_count : (Set.range τ).Countable :=
    (s.finite_toSet.image _).countable.mono (Set.range_subset_iff.2 hτs)
  have h_eq {Y : Ω → ℝ} (hY : Integrable Y P) :
      ∫ ω, max (Y ω) 0 ∂P = (∫⁻ ω, ENNReal.ofReal (Y ω) ∂P).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω ↦ max (Y ω) 0)
      (ae_of_all _ fun ω ↦ le_max_right _ _) hY.pos_part.aestronglyMeasurable]
    simp
  have h_pos : ∫ ω, max (stoppedValue X τ ω) 0 ∂P ≤ ∫ ω, max (X k ω) 0 ∂P := by
    rw [h_eq hint, h_eq (hX.integrable k)]
    exact ENNReal.toReal_mono (hX.integrable k).lintegral_lt_top.ne
      (hX.lintegral_ofReal_stoppedValue_le_of_countable_range hτ hτk hτ_count)
  have h_abs (x : ℝ) : |x| = 2 * max x 0 - x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx, max_eq_left hx]; ring
    · rw [abs_of_nonpos hx, max_eq_right hx]; ring
  simp_rw [h_abs (stoppedValue X τ _)]
  rw [integral_sub (hint.pos_part.const_mul 2) hint, integral_const_mul]
  have := hX.integral_bot_le_integral_stoppedValue_of_mem_finset hτ hτs
  linarith

/-- Auxiliary lemma for `Submartingale.integrable_stoppedValue_of_countable_range` and
`Submartingale.integral_abs_stoppedValue_le_of_countable_range`. -/
private lemma Submartingale.integrable_stoppedValue_and_integral_abs_le_of_countable_range
    (hX : Submartingale X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) (hτk : ∀ ω, τ ω ≤ k)
    (hτ_count : (Set.range τ).Countable) :
    Integrable (stoppedValue X τ) P ∧
      ∫ ω, |stoppedValue X τ ω| ∂P ≤ 2 * ∫ ω, max (X k ω) 0 ∂P - ∫ ω, X ⊥ ω ∂P := by
  -- we approximate `τ` by stopping times with values in finite sets, then we use Fatou's lemma
  obtain ⟨ρ, S, hρ, hρS, hρτ, hρ_lim⟩ := hτ.exists_seq_mem_finset_of_countable_range hτk hτ_count
  have hρk (m : ℕ) (ω : Ω) : ρ m ω ≤ k := by
    rcases hρτ m ω with h | h
    · exact h ▸ hτk ω
    · exact h.le
  refine integrable_of_tendsto_ae_of_integral_norm_le
    (fun m ↦ integrable_stoppedValue_of_mem_finset (hρ m) hX.integrable (hρS m))
    (fun m ↦ hX.integral_abs_stoppedValue_le_of_mem_finset (hρ m) (hρk m) (hρS m))
    (ae_of_all _ fun ω ↦ ?_)
  exact tendsto_nhds_of_eventually_eq <| (hρ_lim ω).mono fun m hm ↦ by simp [stoppedValue, hm]

/-- The value of a real submartingale at a bounded stopping time with countable range is
integrable. -/
lemma Submartingale.integrable_stoppedValue_of_countable_range
    (hX : Submartingale X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) (hτk : ∀ ω, τ ω ≤ k)
    (hτ_count : (Set.range τ).Countable) :
    Integrable (stoppedValue X τ) P :=
  (hX.integrable_stoppedValue_and_integral_abs_le_of_countable_range hτ hτk hτ_count).1

/-- `L¹` bound for a real submartingale sampled at a bounded stopping time with countable
range. -/
lemma Submartingale.integral_abs_stoppedValue_le_of_countable_range
    (hX : Submartingale X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) (hτk : ∀ ω, τ ω ≤ k)
    (hτ_count : (Set.range τ).Countable) :
    ∫ ω, |stoppedValue X τ ω| ∂P ≤ 2 * ∫ ω, max (X k ω) 0 ∂P - ∫ ω, X ⊥ ω ∂P :=
  (hX.integrable_stoppedValue_and_integral_abs_le_of_countable_range hτ hτk hτ_count).2

variable [TopologicalSpace ι] [OrderTopology ι]

/-- Auxiliary lemma for `Submartingale.integrable_stoppedValue_of_approximable` and
`Submartingale.integral_abs_stoppedValue_le_of_approximable`. -/
private lemma Submartingale.integrable_stoppedValue_and_integral_abs_le
    (hX : Submartingale X 𝓕 P) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτk : ∀ ω, τ ω ≤ k) (τn : DiscreteApproxSequence 𝓕 τ P) :
    Integrable (stoppedValue X τ) P ∧
      ∫ ω, |stoppedValue X τ ω| ∂P ≤ 2 * ∫ ω, max (X k ω) 0 ∂P - ∫ ω, X ⊥ ω ∂P := by
  let τn' := discreteApproxSequence_of 𝓕 hτk τn
  exact integrable_of_tendsto_ae_of_integral_norm_le
    (fun n ↦ hX.integrable_stoppedValue_of_countable_range (τn'.isStoppingTime n)
      (discreteApproxSequence_of_le hτk τn n) (τn'.countable n))
    (fun n ↦ hX.integral_abs_stoppedValue_le_of_countable_range (τn'.isStoppingTime n)
      (discreteApproxSequence_of_le hτk τn n) (τn'.countable n))
    (tendsto_stoppedValue_discreteApproxSequence τn' hRC)

/-- The value of a right-continuous real submartingale at a bounded stopping time is
integrable. -/
theorem Submartingale.integrable_stoppedValue_of_approximable [Approximable 𝓕 P]
    (hX : Submartingale X 𝓕 P) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτk : ∀ ω, τ ω ≤ k) :
    Integrable (stoppedValue X τ) P :=
  (hX.integrable_stoppedValue_and_integral_abs_le hRC hτk (hτ.discreteApproxSequence P)).1

/-- `L¹` bound for a right-continuous real submartingale sampled at a bounded stopping time. -/
theorem Submartingale.integral_abs_stoppedValue_le_of_approximable [Approximable 𝓕 P]
    (hX : Submartingale X 𝓕 P) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτk : ∀ ω, τ ω ≤ k) :
    ∫ ω, |stoppedValue X τ ω| ∂P ≤ 2 * ∫ ω, max (X k ω) 0 ∂P - ∫ ω, X ⊥ ω ∂P :=
  (hX.integrable_stoppedValue_and_integral_abs_le hRC hτk (hτ.discreteApproxSequence P)).2

end Integrable

section StoppedProcess

/-! ### Optional sampling and optional stopping for real right-continuous submartingales -/

/-- The integrals over a set of the truncations from below `max f (-m)` of an integrable function
`f` tend to the integral of `f`. -/
private lemma tendsto_setIntegral_max_neg {f : Ω → ℝ} (hf : Integrable f P) (C : Set Ω) :
    Tendsto (fun m : ℕ ↦ ∫ ω in C, max (f ω) (-m) ∂P) atTop (𝓝 (∫ ω in C, f ω ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun ω ↦ |f ω|)
    (fun m ↦ (hf.1.sup aestronglyMeasurable_const).restrict) hf.abs.integrableOn
    (fun m ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_)
  · rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_of_le_left (neg_abs_le _),
      max_le (le_abs_self _) ((neg_nonpos.2 (Nat.cast_nonneg m)).trans (abs_nonneg _))⟩
  · obtain ⟨n, hn⟩ := exists_nat_ge (-f ω)
    refine tendsto_nhds_of_eventually_eq (eventually_atTop.2 ⟨n, fun m hm ↦ max_eq_left ?_⟩)
    have : (n : ℝ) ≤ m := Nat.cast_le.2 hm
    linarith

variable {ι : Type*} [LinearOrder ι] [OrderBot ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → ℝ}
  {τ : Ω → WithTop ι} {s t : ι} {C : Set Ω} [IsFiniteMeasure P]

/-- For a real submartingale `X`, a stopping time `τ` with values in a finite set and a set `C`
which is measurable at time `s` and on which `s ≤ τ`, the integral of `X s` over `C` is at most
the integral of `X τ` over `C`. -/
lemma Submartingale.setIntegral_le_setIntegral_stoppedValue_of_mem_finset
    (hX : Submartingale X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) {S : Finset ι}
    (hτS : ∀ ω, τ ω ∈ WithTop.some '' (S : Set ι)) (hC : MeasurableSet[𝓕 s] C)
    (hsτ : ∀ ω ∈ C, s ≤ τ ω) :
    ∫ ω in C, X s ω ∂P ≤ ∫ ω in C, stoppedValue X τ ω ∂P := by
  classical
  have hC' : MeasurableSet C := 𝓕.le s _ hC
  induction S using Finset.induction_on_max generalizing τ with
  | empty =>
    have : IsEmpty Ω := ⟨fun ω ↦ by simpa using hτS ω⟩
    simp [Measure.eq_zero_of_isEmpty P]
  | insert a S has ih =>
    by_cases hS : ∃ v ∈ S, s ≤ v
    · -- we compare `τ` to `τ ⊓ u`, where `u` is the second largest possible value of `τ`
      obtain ⟨v, hvS, hsv⟩ := hS
      have hS_ne : S.Nonempty := ⟨v, hvS⟩
      set u := S.max' hS_ne
      have hsu : s ≤ u := hsv.trans (S.le_max' v hvS)
      have hua : u < a := has u (S.max'_mem hS_ne)
      have hτ' : IsStoppingTime 𝓕 (fun ω ↦ min (τ ω) u) := hτ.min_const u
      have hD : MeasurableSet[𝓕 u] {ω | τ ω ≤ u} := hτ u
      have hD' : MeasurableSet {ω | τ ω ≤ u} := 𝓕.le u _ hD
      have h_of_not_le (ω : Ω) (hω : ¬ τ ω ≤ u) : τ ω = a := by
        obtain ⟨i, hi, hiτ⟩ := hτS ω
        rcases Finset.mem_insert.1 hi with rfl | his
        · exact hiτ.symm
        · exact absurd (hiτ ▸ WithTop.coe_le_coe.2 (S.le_max' i his)) hω
      have hτ'S (ω : Ω) : min (τ ω) u ∈ WithTop.some '' (S : Set ι) := by
        by_cases hω : τ ω ≤ u
        · obtain ⟨i, hi, hiτ⟩ := hτS ω
          rcases Finset.mem_insert.1 hi with rfl | his
          · exact absurd (hiτ ▸ hω) (by simpa using hua)
          · exact ⟨i, his, by rw [min_eq_left hω, hiτ]⟩
        · exact ⟨u, S.max'_mem hS_ne, (min_eq_right (not_le.1 hω).le).symm⟩
      have hint : Integrable (stoppedValue X τ) P :=
        integrable_stoppedValue_of_mem_finset hτ hX.integrable hτS
      have hint' : Integrable (stoppedValue X fun ω ↦ min (τ ω) u) P :=
        integrable_stoppedValue_of_mem_finset hτ' hX.integrable hτ'S
      calc ∫ ω in C, X s ω ∂P
        _ ≤ ∫ ω in C, stoppedValue X (fun ω ↦ min (τ ω) u) ω ∂P :=
          ih hτ' hτ'S fun ω hω ↦ le_min (hsτ ω hω) (WithTop.coe_le_coe.2 hsu)
        _ = ∫ ω in C ∩ {ω | τ ω ≤ u}, stoppedValue X τ ω ∂P
            + ∫ ω in C \ {ω | τ ω ≤ u}, X u ω ∂P := by
          rw [← integral_inter_add_sdiff (s := C) hD' hint'.integrableOn]
          congr 1
          · exact setIntegral_congr_fun (hC'.inter hD') fun ω hω ↦ by
              have hω' : τ ω ≤ u := hω.2
              simp [stoppedValue, min_eq_left hω']
          · exact setIntegral_congr_fun (hC'.diff hD') fun ω hω ↦ by
              have hω' : ¬ τ ω ≤ u := hω.2
              simp [stoppedValue, min_eq_right (not_le.1 hω').le]
        _ ≤ ∫ ω in C ∩ {ω | τ ω ≤ u}, stoppedValue X τ ω ∂P
            + ∫ ω in C \ {ω | τ ω ≤ u}, X a ω ∂P :=
          add_le_add le_rfl (hX.setIntegral_le hua.le ((𝓕.mono hsu _ hC).diff hD))
        _ = ∫ ω in C, stoppedValue X τ ω ∂P := by
          rw [← integral_inter_add_sdiff (s := C) hD' hint.integrableOn]
          congr 1
          exact setIntegral_congr_fun (hC'.diff hD') fun ω hω ↦ by
            simp [stoppedValue, h_of_not_le ω hω.2]
    · -- all the values of `τ` other than `a` are less than `s`, hence `τ = a` on `C`
      push Not at hS
      have hτa (ω : Ω) (hω : ω ∈ C) : τ ω = a := by
        obtain ⟨i, hi, hiτ⟩ := hτS ω
        rcases Finset.mem_insert.1 hi with rfl | his
        · exact hiτ.symm
        · have hsi : (s : WithTop ι) ≤ i := hiτ ▸ hsτ ω hω
          exact absurd (WithTop.coe_le_coe.1 hsi) (not_le.2 (hS i his))
      rcases C.eq_empty_or_nonempty with rfl | ⟨ω₀, hω₀⟩
      · simp
      have hsa : s ≤ a := WithTop.coe_le_coe.1 (hτa ω₀ hω₀ ▸ hsτ ω₀ hω₀)
      calc ∫ ω in C, X s ω ∂P
        _ ≤ ∫ ω in C, X a ω ∂P := hX.setIntegral_le hsa hC
        _ = ∫ ω in C, stoppedValue X τ ω ∂P :=
          setIntegral_congr_fun hC' fun ω hω ↦ by simp [stoppedValue, hτa ω hω]

/-- For a real submartingale `X`, a stopping time `τ ≤ t` with countable range and a set `C`
which is measurable at time `s` and on which `s ≤ τ`, the integral of `X s` over `C` is at most
the integral of `X τ` over `C`. -/
lemma Submartingale.setIntegral_le_setIntegral_stoppedValue_of_countable_range
    (hX : Submartingale X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) (hτt : ∀ ω, τ ω ≤ t)
    (hτ_count : (Set.range τ).Countable) (hC : MeasurableSet[𝓕 s] C)
    (hsτ : ∀ ω ∈ C, s ≤ τ ω) :
    ∫ ω in C, X s ω ∂P ≤ ∫ ω in C, stoppedValue X τ ω ∂P := by
  -- we approximate `τ` by stopping times with values in finite sets and use dominated convergence
  obtain ⟨ρ, S, hρ, hρS, hρτ, hρ_lim⟩ := hτ.exists_seq_mem_finset_of_countable_range hτt hτ_count
  have hint : Integrable (stoppedValue X τ) P :=
    hX.integrable_stoppedValue_of_countable_range hτ hτt hτ_count
  have h_tendsto : Tendsto (fun m ↦ ∫ ω in C, stoppedValue X (ρ m) ω ∂P) atTop
      (𝓝 (∫ ω in C, stoppedValue X τ ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω ↦ |stoppedValue X τ ω| + |X t ω|)
      (fun m ↦ (integrable_stoppedValue_of_mem_finset (hρ m) hX.integrable (hρS m)).1.restrict)
      (hint.abs.add (hX.integrable t).abs).integrableOn (fun m ↦ ae_of_all _ fun ω ↦ ?_)
      (ae_of_all _ fun ω ↦ tendsto_nhds_of_eventually_eq <|
        (hρ_lim ω).mono fun m hm ↦ by simp [stoppedValue, hm])
    rcases hρτ m ω with h | h
    · simp only [stoppedValue, h, Real.norm_eq_abs]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · simp only [stoppedValue, h, WithTop.untopD_coe, Real.norm_eq_abs]
      exact le_add_of_nonneg_left (abs_nonneg _)
  refine ge_of_tendsto' h_tendsto fun m ↦ ?_
  refine hX.setIntegral_le_setIntegral_stoppedValue_of_mem_finset (hρ m) (hρS m) hC fun ω hω ↦ ?_
  rcases hρτ m ω with h | h
  · exact h ▸ hsτ ω hω
  · exact h ▸ (hsτ ω hω).trans (hτt ω)

/-- For a real submartingale `X`, a stopping time `τ ≤ t` with countable range and a set `C`
which is measurable with respect to the σ-algebra of `τ`, the integral of `X τ` over `C` is at
most the integral of `X t` over `C`. -/
lemma Submartingale.setIntegral_stoppedValue_le_setIntegral_of_countable_range
    (hX : Submartingale X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) (hτt : ∀ ω, τ ω ≤ t)
    (hτ_count : (Set.range τ).Countable) (hC : MeasurableSet[hτ.measurableSpace] C) :
    ∫ ω in C, stoppedValue X τ ω ∂P ≤ ∫ ω in C, X t ω ∂P := by
  have : Countable (Set.range τ) := hτ_count.to_subtype
  -- we split `C` according to the value of `τ`
  let A : Set.range τ → Set Ω := fun j ↦ C ∩ {ω | τ ω = j}
  have hCA : C = ⋃ j, A j := by
    ext ω
    simp only [A, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun hω ↦ ⟨⟨τ ω, ω, rfl⟩, hω, rfl⟩, fun ⟨_, hω, _⟩ ↦ hω⟩
  have hA_disj : Pairwise (Disjoint on A) := fun j j' hjj' ↦
    Set.disjoint_left.2 fun ω hω hω' ↦ hjj' (Subtype.ext (hω.2.symm.trans hω'.2))
  -- on each piece, `X τ = X i` for a time `i ≤ t` at which the piece is measurable
  have hA (j : Set.range τ) :
      ∃ i : ι, i ≤ t ∧ (j : WithTop ι) = i ∧ MeasurableSet[𝓕 i] (A j) := by
    obtain ⟨ω, hω⟩ := j.2
    obtain ⟨i, hi⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (hτt ω))
    have hji : (j : WithTop ι) = i := hω.symm.trans hi.symm
    refine ⟨i, WithTop.coe_le_coe.1 (hi.trans_le (hτt ω)), hji, ?_⟩
    change MeasurableSet[𝓕 i] (C ∩ {ω | τ ω = (j : WithTop ι)})
    rw [hji, ← hτ.measurableSet_inter_eq_iff]
    exact hC.inter (hτ.measurableSet_eq_of_countable_range' hτ_count i)
  have hA_meas (j : Set.range τ) : MeasurableSet (A j) := by
    obtain ⟨i, -, -, hAi⟩ := hA j
    exact 𝓕.le i _ hAi
  have h_le (j : Set.range τ) : ∫ ω in A j, stoppedValue X τ ω ∂P ≤ ∫ ω in A j, X t ω ∂P := by
    obtain ⟨i, hit, hji, hAi⟩ := hA j
    calc ∫ ω in A j, stoppedValue X τ ω ∂P
      _ = ∫ ω in A j, X i ω ∂P := setIntegral_congr_fun (𝓕.le i _ hAi) fun ω hω ↦ by
        simp [stoppedValue, show τ ω = i from hω.2.trans hji]
      _ ≤ ∫ ω in A j, X t ω ∂P := hX.setIntegral_le hit hAi
  have h := hasSum_le h_le
    (hasSum_integral_iUnion hA_meas hA_disj
      (hX.integrable_stoppedValue_of_countable_range hτ hτt hτ_count).integrableOn)
    (hasSum_integral_iUnion hA_meas hA_disj (hX.integrable t).integrableOn)
  rwa [← hCA] at h

variable [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]

/-- The values of a real submartingale which is bounded from below, at stopping times with
countable range which are bounded by `t`, are uniformly integrable.

The lower bound cannot be removed: the values of a submartingale at bounded stopping times are
not uniformly integrable in general. -/
lemma Submartingale.uniformIntegrable_stoppedValue_of_countable_range
    (hX : Submartingale X 𝓕 P) {c : ℝ} (hc : ∀ i ω, c ≤ X i ω) {ρ : ℕ → Ω → WithTop ι}
    (hρ : ∀ n, IsStoppingTime 𝓕 (ρ n)) (hρt : ∀ n ω, ρ n ω ≤ t)
    (hρ_count : ∀ n, (Set.range (ρ n)).Countable) :
    UniformIntegrable (fun n ↦ stoppedValue X (ρ n)) 1 P := by
  -- `|X i| ≤ N i` for `i ≤ t`, where `N` is the martingale `i ↦ P[|X t| + |c| | 𝓕 i]`
  let N : ι → Ω → ℝ := fun i ↦ P[fun ω ↦ |X t ω| + |c| | 𝓕 i]
  have hN : Martingale N 𝓕 P := martingale_condExp _ 𝓕 P
  have h_int : Integrable (fun ω ↦ |X t ω| + |c|) P :=
    (hX.integrable t).abs.add (integrable_const _)
  have h_le (i : ι) (hit : i ≤ t) : ∀ᵐ ω ∂P, |X i ω| ≤ N i ω := by
    have h1 : P[X t | 𝓕 i] ≤ᵐ[P] N i := condExp_mono (hX.integrable t) h_int
      (ae_of_all _ fun ω ↦ (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg c)))
    have h2 : (fun _ ↦ |c|) ≤ᵐ[P] N i := by
      have := condExp_mono (m := 𝓕 i) (integrable_const |c|) h_int
        (ae_of_all P fun ω ↦ le_add_of_nonneg_left (abs_nonneg (X t ω)))
      rwa [condExp_const (𝓕.le i)] at this
    filter_upwards [hX.2.1 i t hit, h1, h2] with ω hω1 hω2 hω3
    exact abs_le.2 ⟨by linarith [hc i ω, neg_abs_le c], hω1.trans hω2⟩
  refine uniformIntegrable_of_dominated
    (hN.uniformIntegrable_stoppedValue_of_countable_range ρ hρ hρt hρ_count)
    (fun n ↦ (hX.integrable_stoppedValue_of_countable_range (hρ n) (hρt n) (hρ_count n)).1)
    fun n ↦ ⟨n, ?_⟩
  have h_ae : ∀ᵐ ω ∂P, ∀ i ∈ {i : ι | (i : WithTop ι) ∈ Set.range (ρ n)}, |X i ω| ≤ N i ω := by
    refine (ae_ball_iff ((hρ_count n).preimage WithTop.coe_injective)).2 ?_
    rintro i ⟨ω, hω⟩
    exact h_le i (WithTop.coe_le_coe.1 (hω ▸ hρt n ω))
  filter_upwards [h_ae] with ω hω
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (hρt n ω))
  simp only [stoppedValue, ← hj, WithTop.untopD_coe, Real.norm_eq_abs]
  exact (hω j ⟨ω, hj.symm⟩).trans (le_abs_self _)

variable [Approximable 𝓕 P]

/-- For a right-continuous real submartingale `X` which is bounded from below and a stopping time
`τ ≤ t`, the integrals over a set of the values of `X` at the times of a discrete approximation
sequence of `τ` tend to the integral of `X τ`: these values are uniformly integrable and tend to
`X τ`, hence they converge in `L¹`. -/
private lemma Submartingale.tendsto_setIntegral_stoppedValue_of_const_le
    (hX : Submartingale X 𝓕 P) (hRC : ∀ ω, IsRightContinuous (X · ω)) {c : ℝ}
    (hc : ∀ i ω, c ≤ X i ω) (hτ : IsStoppingTime 𝓕 τ) (hτt : ∀ ω, τ ω ≤ t) (C : Set Ω) :
    Tendsto (fun n ↦ ∫ ω in C,
        stoppedValue X (discreteApproxSequence_of 𝓕 hτt (hτ.discreteApproxSequence P) n) ω ∂P)
      atTop (𝓝 (∫ ω in C, stoppedValue X τ ω ∂P)) := by
  let τn := discreteApproxSequence_of 𝓕 hτt (hτ.discreteApproxSequence P)
  have hτn_le (n : ℕ) (ω : Ω) : τn n ω ≤ t := discreteApproxSequence_of_le hτt _ n ω
  have hτn_int (n : ℕ) : Integrable (stoppedValue X (τn n)) P :=
    hX.integrable_stoppedValue_of_countable_range (τn.isStoppingTime n) (hτn_le n) (τn.countable n)
  have hint : Integrable (stoppedValue X τ) P :=
    hX.integrable_stoppedValue_of_approximable hRC hτ hτt
  refine tendsto_setIntegral_of_L1' _ (.of_forall hτn_int) ?_ C
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top (fun n ↦ (hτn_int n).1)
    (memLp_one_iff_integrable.2 hint)
    (hX.uniformIntegrable_stoppedValue_of_countable_range hc τn.isStoppingTime hτn_le
      τn.countable).1
    (tendsto_stoppedValue_discreteApproxSequence τn hRC)

/-- Auxiliary lemma for `Submartingale.setIntegral_le_setIntegral_stoppedValue`: the case of a
submartingale which is bounded from below. -/
private lemma Submartingale.setIntegral_le_setIntegral_stoppedValue_of_const_le
    (hX : Submartingale X 𝓕 P) (hRC : ∀ ω, IsRightContinuous (X · ω)) {c : ℝ}
    (hc : ∀ i ω, c ≤ X i ω) (hτ : IsStoppingTime 𝓕 τ) (hτt : ∀ ω, τ ω ≤ t)
    (hC : MeasurableSet[𝓕 s] C) (hsτ : ∀ ω ∈ C, s ≤ τ ω) :
    ∫ ω in C, X s ω ∂P ≤ ∫ ω in C, stoppedValue X τ ω ∂P := by
  -- we approximate `τ` from above by stopping times `τn n` with countable range
  let τn := discreteApproxSequence_of 𝓕 hτt (hτ.discreteApproxSequence P)
  refine ge_of_tendsto' (hX.tendsto_setIntegral_stoppedValue_of_const_le hRC hc hτ hτt C)
    fun n ↦ ?_
  exact hX.setIntegral_le_setIntegral_stoppedValue_of_countable_range (τn.isStoppingTime n)
    (discreteApproxSequence_of_le hτt _ n) (τn.countable n) hC
    fun ω hω ↦ (hsτ ω hω).trans (τn.le n ω)

/-- Auxiliary lemma for `Submartingale.setIntegral_stoppedValue_le_setIntegral`: the case of a
submartingale which is bounded from below. -/
private lemma Submartingale.setIntegral_stoppedValue_le_setIntegral_of_const_le
    (hX : Submartingale X 𝓕 P) (hRC : ∀ ω, IsRightContinuous (X · ω)) {c : ℝ}
    (hc : ∀ i ω, c ≤ X i ω) (hτ : IsStoppingTime 𝓕 τ) (hτt : ∀ ω, τ ω ≤ t)
    (hC : MeasurableSet[hτ.measurableSpace] C) :
    ∫ ω in C, stoppedValue X τ ω ∂P ≤ ∫ ω in C, X t ω ∂P := by
  -- we approximate `τ` from above by stopping times `τn n` with countable range: `C` is
  -- measurable with respect to the σ-algebra of `τn n`
  let τn := discreteApproxSequence_of 𝓕 hτt (hτ.discreteApproxSequence P)
  refine le_of_tendsto' (hX.tendsto_setIntegral_stoppedValue_of_const_le hRC hc hτ hτt C)
    fun n ↦ ?_
  exact hX.setIntegral_stoppedValue_le_setIntegral_of_countable_range (τn.isStoppingTime n)
    (discreteApproxSequence_of_le hτt _ n) (τn.countable n)
    (hτ.measurableSpace_mono (τn.isStoppingTime n) (τn.le n) _ hC)

/-- **Optional sampling** for a right-continuous real submartingale `X`, in terms of integrals:
if `τ` is a stopping time bounded by `t` and `C` is a set which is measurable at time `s` and on
which `s ≤ τ`, then the integral of `X s` over `C` is at most the integral of `X τ` over `C`. -/
theorem Submartingale.setIntegral_le_setIntegral_stoppedValue
    (hX : Submartingale X 𝓕 P) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτt : ∀ ω, τ ω ≤ t)
    (hC : MeasurableSet[𝓕 s] C) (hsτ : ∀ ω ∈ C, s ≤ τ ω) :
    ∫ ω in C, X s ω ∂P ≤ ∫ ω in C, stoppedValue X τ ω ∂P := by
  -- we truncate `X` from below by `-m`, then let `m` tend to infinity by dominated convergence
  have hY (m : ℕ) : Submartingale (fun i ω ↦ max (X i ω) (-m)) 𝓕 P :=
    hX.sup (martingale_const 𝓕 P (-(m : ℝ))).submartingale
  refine le_of_tendsto_of_tendsto' (tendsto_setIntegral_max_neg (hX.integrable s) C)
    (tendsto_setIntegral_max_neg (hX.integrable_stoppedValue_of_approximable hRC hτ hτt) C)
    fun m ↦ ?_
  exact (hY m).setIntegral_le_setIntegral_stoppedValue_of_const_le
    (fun ω a ↦ (hRC ω a).max continuousWithinAt_const) (fun i ω ↦ le_max_right _ _) hτ hτt hC hsτ

/-- **Optional sampling** for a right-continuous real submartingale `X`, in terms of integrals:
if `τ` is a stopping time bounded by `t` and `C` is a set which is measurable with respect to the
σ-algebra of `τ`, then the integral of `X τ` over `C` is at most the integral of `X t` over
`C`. -/
theorem Submartingale.setIntegral_stoppedValue_le_setIntegral
    (hX : Submartingale X 𝓕 P) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτt : ∀ ω, τ ω ≤ t) (hC : MeasurableSet[hτ.measurableSpace] C) :
    ∫ ω in C, stoppedValue X τ ω ∂P ≤ ∫ ω in C, X t ω ∂P := by
  -- we truncate `X` from below by `-m`, then let `m` tend to infinity by dominated convergence
  have hY (m : ℕ) : Submartingale (fun i ω ↦ max (X i ω) (-m)) 𝓕 P :=
    hX.sup (martingale_const 𝓕 P (-(m : ℝ))).submartingale
  refine le_of_tendsto_of_tendsto'
    (tendsto_setIntegral_max_neg (hX.integrable_stoppedValue_of_approximable hRC hτ hτt) C)
    (tendsto_setIntegral_max_neg (hX.integrable t) C) fun m ↦ ?_
  exact (hY m).setIntegral_stoppedValue_le_setIntegral_of_const_le
    (fun ω a ↦ (hRC ω a).max continuousWithinAt_const) (fun i ω ↦ le_max_right _ _) hτ hτt hC

omit [FirstCountableTopology ι] in
/-- **Optional stopping**: the stopped process of a right-continuous real submartingale is a
submartingale. -/
theorem Submartingale.stoppedProcess_of_approximable [SecondCountableTopology ι]
    [PseudoMetrizableSpace ι] (hX : Submartingale X 𝓕 P) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) :
    Submartingale (stoppedProcess X τ) 𝓕 P := by
  borelize ι
  have hτ_min (i : ι) : IsStoppingTime 𝓕 (fun ω ↦ min (i : WithTop ι) (τ ω)) :=
    (isStoppingTime_const 𝓕 i).min hτ
  have h_int (i : ι) : Integrable (stoppedProcess X τ i) P :=
    hX.integrable_stoppedValue_of_approximable hRC (hτ_min i) fun ω ↦ min_le_left _ _
  refine submartingale_of_setIntegral_le
    (hX.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC |>.stoppedProcess hτ
      |>.stronglyAdapted) h_int fun s t hst B hB ↦ ?_
  have hB' : MeasurableSet B := 𝓕.le s _ hB
  have hD : MeasurableSet[𝓕 s] {ω | τ ω ≤ s} := hτ s
  have hD' : MeasurableSet {ω | τ ω ≤ s} := 𝓕.le s _ hD
  rw [← integral_inter_add_sdiff (s := B) hD' (h_int s).integrableOn,
    ← integral_inter_add_sdiff (s := B) hD' (h_int t).integrableOn]
  refine add_le_add (le_of_eq ?_) ?_
  · -- on `{τ ≤ s}`, the stopped process is equal to `X τ` at times `s` and `t`
    refine setIntegral_congr_fun (hB'.inter hD') fun ω hω ↦ ?_
    have hω' : τ ω ≤ s := hω.2
    simp [stoppedProcess, min_eq_right hω', min_eq_right (hω'.trans (WithTop.coe_le_coe.2 hst))]
  · -- on `{s < τ}`, the stopped process at time `s` is `X s`, and we use optional sampling
    calc ∫ ω in B \ {ω | τ ω ≤ s}, stoppedProcess X τ s ω ∂P
      _ = ∫ ω in B \ {ω | τ ω ≤ s}, X s ω ∂P :=
        setIntegral_congr_fun (hB'.diff hD') fun ω hω ↦ by
          have hω' : ¬ τ ω ≤ s := hω.2
          simp [stoppedProcess, min_eq_left (not_le.1 hω').le]
      _ ≤ ∫ ω in B \ {ω | τ ω ≤ s}, stoppedValue X (fun ω ↦ min (t : WithTop ι) (τ ω)) ω ∂P :=
        hX.setIntegral_le_setIntegral_stoppedValue hRC (hτ_min t) (fun ω ↦ min_le_left _ _)
          (hB.diff hD) fun ω hω ↦ le_min (WithTop.coe_le_coe.2 hst) (not_le.1 hω.2).le

end StoppedProcess

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [OrderBot ι] [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι]
  [PseudoMetrizableSpace ι] {σ τ : Ω → WithTop ι} {X : ι → Ω → E} (𝓕 : Filtration ι mΩ)

variable {𝓕} in
omit [MeasurableSpace ι] [BorelSpace ι] in
/-- **Optional sampling** for a right-continuous real submartingale `X`, in terms of integrals: if
`τ` and `σ` are stopping times, `τ` is bounded and `A` is a set which is measurable with respect
to the σ-algebra of `σ`, then the integral of `X (τ ⊓ σ)` over `A` is at most the integral of
`X τ` over `A`. -/
theorem Submartingale.setIntegral_stoppedValue_min_le [Approximable 𝓕 P] [IsFiniteMeasure P]
    {X : ι → Ω → ℝ} (hX1 : Submartingale X 𝓕 P) (hX2 : ∀ ω, IsRightContinuous (X · ω)) {k : ι}
    (hτk : ∀ ω, τ ω ≤ k) (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) {A : Set Ω}
    (hA : MeasurableSet[hσ.measurableSpace] A) :
    ∫ ω in A, stoppedValue X (τ ⊓ σ) ω ∂P ≤ ∫ ω in A, stoppedValue X τ ω ∂P := by
  -- the stopped process `Y` is a right-continuous submartingale, and `X τ = Y k`,
  -- `X (τ ⊓ σ) = Y ρ` for the stopping time `ρ = σ ⊓ k`
  let Y := stoppedProcess X τ
  have hY : Submartingale Y 𝓕 P := hX1.stoppedProcess_of_approximable hX2 hτ
  have hY_RC (ω : Ω) : IsRightContinuous (Y · ω) := (hX2 ω).stoppedProcess τ
  let ρ : Ω → WithTop ι := σ ⊓ fun _ ↦ k
  have hρ : IsStoppingTime 𝓕 ρ := hσ.min (isStoppingTime_const 𝓕 k)
  have hρk (ω : Ω) : ρ ω ≤ k := inf_le_right
  have hYk : Y k = stoppedValue X τ := by
    ext ω
    simp [Y, stoppedProcess, stoppedValue, min_eq_right (hτk ω)]
  have hYρ : stoppedValue Y ρ = stoppedValue X (τ ⊓ σ) := by
    ext ω
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (hρk ω))
    have h_min : min (r : WithTop ι) (τ ω) = (τ ⊓ σ) ω := by
      rw [hr, Pi.inf_apply, show ρ ω = min (σ ω) k from rfl, min_assoc, min_eq_right (hτk ω),
        min_comm]
    simp only [stoppedValue, Y, stoppedProcess, ← hr, WithTop.untopD_coe, h_min]
  rw [← hYρ, ← hYk]
  -- on `{σ ≤ k}` we use optional sampling for `Y` at time `ρ`, and on `{k < σ}` we have `ρ = k`
  have hD : MeasurableSet {ω | σ ω ≤ k} := 𝓕.le k _ (hσ k)
  rw [← integral_inter_add_sdiff (s := A) hD
      (hY.integrable_stoppedValue_of_approximable hY_RC hρ hρk).integrableOn,
    ← integral_inter_add_sdiff (s := A) hD (hY.integrable k).integrableOn]
  refine add_le_add ?_ (le_of_eq ?_)
  · exact hY.setIntegral_stoppedValue_le_setIntegral hY_RC hρ hρk
      (hσ.measurableSet_inter_le (isStoppingTime_const 𝓕 k) A hA)
  · refine setIntegral_congr_fun ((hσ.measurableSpace_le _ hA).diff hD) fun ω hω ↦ ?_
    have hω' : (k : WithTop ι) ≤ σ ω := (not_le.1 hω.2).le
    simp [stoppedValue, ρ, min_eq_right hω']

/-- **Optional sampling theorem** for a right-continuous real submartingale `X`: if `τ` and `σ`
are stopping times and `τ` is bounded, then `X (τ ⊓ σ) ≤ P[X τ | 𝓕 σ]` almost surely.

See `Submartingale.stoppedValue_min_ae_le_condExp_of_nonneg` for nonnegative submartingales with
values in a Banach lattice. -/
theorem Submartingale.stoppedValue_min_ae_le_condExp [Approximable 𝓕 P] [IsFiniteMeasure P]
    {X : ι → Ω → ℝ} (hX1 : Submartingale X 𝓕 P) (hX2 : ∀ ω, IsRightContinuous (X · ω)) {k : ι}
    (hτk : ∀ᵐ ω ∂P, τ ω ≤ k) (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ | hσ.measurableSpace] := by
  -- we can suppose that `τ ≤ k` everywhere
  wlog hτk' : ∀ ω, τ ω ≤ k generalizing τ
  · let τ' : Ω → WithTop ι := τ ⊓ fun _ ↦ k
    have hτ'_eq : τ' =ᵐ[P] τ := by filter_upwards [hτk] with ω hω using inf_eq_left.2 hω
    have h := this (τ := τ') (ae_of_all _ fun ω ↦ inf_le_right)
      (hτ.min (isStoppingTime_const 𝓕 k)) fun ω ↦ inf_le_right
    have h1 : stoppedValue X (τ' ⊓ σ) =ᵐ[P] stoppedValue X (τ ⊓ σ) := by
      filter_upwards [hτ'_eq] with ω hω
      simp [stoppedValue, hω]
    have h2 : stoppedValue X τ' =ᵐ[P] stoppedValue X τ := by
      filter_upwards [hτ'_eq] with ω hω
      simp [stoppedValue, hω]
    exact h1.symm.le.trans (h.trans (condExp_congr_ae h2).le)
  have h_int_τ : Integrable (stoppedValue X τ) P :=
    hX1.integrable_stoppedValue_of_approximable hX2 hτ hτk'
  have h_int : Integrable (stoppedValue X (τ ⊓ σ)) P :=
    hX1.integrable_stoppedValue_of_approximable hX2 (hτ.min hσ) fun ω ↦ inf_le_left.trans (hτk' ω)
  have h_meas : StronglyMeasurable[hσ.measurableSpace] (stoppedValue X (τ ⊓ σ)) :=
    (stronglyMeasurable_stoppedValue
      (hX1.stronglyAdapted.isStronglyProgressive_of_rightContinuous hX2) hX2 (hτ.min hσ)).mono
      ((hτ.min hσ).measurableSpace_mono hσ fun ω ↦ inf_le_right)
  -- it suffices to compare the integrals over the sets which are measurable with respect to the
  -- σ-algebra of `σ`
  refine ae_le_of_ae_le_trim (hm := hσ.measurableSpace_le) ?_
  refine ae_le_of_forall_setIntegral_le (h_int.trim hσ.measurableSpace_le h_meas)
    (integrable_condExp.trim hσ.measurableSpace_le stronglyMeasurable_condExp) fun A hA _ ↦ ?_
  rw [← setIntegral_trim hσ.measurableSpace_le h_meas hA,
    ← setIntegral_trim hσ.measurableSpace_le stronglyMeasurable_condExp hA,
    setIntegral_condExp hσ.measurableSpace_le h_int_τ hA]
  exact hX1.setIntegral_stoppedValue_min_le hX2 hτk' hσ hτ hA

/-- **Optional sampling theorem** for a nonnegative right-continuous submartingale `X` with values
in a Banach lattice: if `τ` and `σ` are stopping times and `τ` is bounded, then
`X (τ ⊓ σ) ≤ P[X τ | 𝓕 σ]` almost surely.

The nonnegativity assumption cannot be removed: without it, `X τ` is not integrable in general,
even for a stopping time `τ` with countable range and `E = ℓ²` with the coordinatewise order. -/
theorem Submartingale.stoppedValue_min_ae_le_condExp_of_nonneg [Approximable 𝓕 P]
    [IsFiniteMeasure P] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    (hX1 : Submartingale X 𝓕 P) (hX2 : ∀ ω, IsRightContinuous (X · ω)) (hX3 : 0 ≤ X) {k : ι}
    (hτk : ∀ᵐ ω ∂P, τ ω ≤ k) (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ | hσ.measurableSpace] := by
  sorry

end subsupermartingale

namespace Martingale

/-! ### Optional sampling at infinity for uniformly integrable martingales -/

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [OrderBot ι] [SecondCountableTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [HasRadonNikodymProp E]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : ι → Ω → E} {τ : Ω → WithTop ι}

/-- Auxiliary lemma for `Martingale.condExp_limitProcess_ae_eq'`: the case of a bounded stopping
time. -/
private lemma stoppedValue_ae_eq_condExp_limitProcess_of_le_const [Approximable 𝓕 μ]
    (hX1 : Martingale X 𝓕 μ) (hX2 : UniformIntegrable X 1 μ)
    (hX3 : ∀ ω, IsRightContinuous (X · ω)) (hτ : IsStoppingTime 𝓕 τ) {t : ι}
    (hτt : ∀ ω, τ ω ≤ t) :
    stoppedValue X τ =ᵐ[μ] μ[𝓕.limitProcess X μ | hτ.measurableSpace] := by
  borelize ι
  refine (hX1.stoppedValue_ae_eq_condExp_of_le_const' hX3 hτ hτt).trans ?_
  refine (condExp_congr_ae (hX1.condExp_limitProcess_ae_eq hX2 hX3 t).symm).trans ?_
  exact condExp_condExp_of_le (hτ.measurableSpace_le_of_le_const hτt) (𝓕.le _)

/-- The value at a stopping time `τ`, which can take the value `⊤`, of a right-continuous
uniformly integrable martingale is integrable. -/
lemma integrable_stoppedValue' [Approximable 𝓕 μ]
    (hX1 : Martingale X 𝓕 μ) (hX2 : UniformIntegrable X 1 μ)
    (hX3 : ∀ ω, IsRightContinuous (X · ω)) (hτ : IsStoppingTime 𝓕 τ) :
    Integrable (𝓕.stoppedValue' X τ μ) μ := by
  -- `X τ` is the almost sure limit of the `X (τ ∧ t n) = μ[X ∞ | 𝓕 (τ ∧ t n)]`, which are bounded
  -- in `L¹`
  obtain ⟨t, -, ht⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  have hY (n : ℕ) := stoppedValue_ae_eq_condExp_limitProcess_of_le_const hX1 hX2 hX3
    (hτ.min_const (t n)) fun ω ↦ min_le_right _ _
  have h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ stoppedValue X (fun ω ↦ min (τ ω) (t n)) ω) atTop
      (𝓝 (𝓕.stoppedValue' X τ μ ω)) := by
    filter_upwards [hX1.ae_tendsto_limitProcess hX2 hX3] with ω hω
    cases h : τ ω with
    | top =>
      have h_eq (n : ℕ) : stoppedValue X (fun ω ↦ min (τ ω) (t n)) ω = X (t n) ω := by
        simp [stoppedValue, h]
      simp only [h_eq, Filtration.stoppedValue'_of_eq_top h]
      exact hω.comp ht
    | coe i =>
      refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [ht.eventually_ge_atTop i] with n hn
      exact (Filtration.stoppedValue'_eq_stoppedValue_min_const
        (by rw [h]; exact_mod_cast hn)).symm
  refine (integrable_of_tendsto_ae_of_integral_norm_le (C := ∫ ω, ‖𝓕.limitProcess X μ ω‖ ∂μ)
    (fun n ↦ integrable_condExp.congr (hY n).symm) (fun n ↦ ?_) h_tendsto).1
  exact (integral_congr_ae ((hY n).mono fun ω hω ↦ congrArg norm hω)).trans_le
    (integral_norm_condExp_le _)

/-- **Optional sampling theorem** at infinity: for a right-continuous uniformly integrable
martingale `X` and a stopping time `τ`, which can take the value `⊤`, `μ[X ∞ | 𝓕 τ] = X τ`. -/
theorem condExp_limitProcess_ae_eq' [Approximable 𝓕 μ]
    (hX1 : Martingale X 𝓕 μ) (hX2 : UniformIntegrable X 1 μ)
    (hX3 : ∀ ω, IsRightContinuous (X · ω)) (hτ : IsStoppingTime 𝓕 τ) :
    μ[𝓕.limitProcess X μ | hτ.measurableSpace] =ᵐ[μ] 𝓕.stoppedValue' X τ μ := by
  borelize ι
  have hL_int : Integrable (𝓕.limitProcess X μ) μ := hX1.integrable_limitProcess hX2 hX3
  have hS_int : Integrable (𝓕.stoppedValue' X τ μ) μ := hX1.integrable_stoppedValue' hX2 hX3 hτ
  have hS_sm : StronglyMeasurable[hτ.measurableSpace] (𝓕.stoppedValue' X τ μ) :=
    𝓕.stronglyMeasurable_stoppedValue'
      (hX1.stronglyAdapted.isStronglyProgressive_of_rightContinuous hX3) hX3 hτ
  -- it suffices to compare the integrals over the sets of `𝓕 τ`
  refine (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hL_int
    (fun s _ _ ↦ hS_int.integrableOn) (fun s hs _ ↦ ?_) hS_sm.aestronglyMeasurable).symm
  have hs' : MeasurableSet s := hτ.measurableSpace_le s hs
  -- on `{τ = ⊤}`, both functions are equal
  have hD : MeasurableSet {ω | τ ω = ⊤} := hτ.measurableSet_eq_top
  rw [← integral_inter_add_sdiff hD hS_int.integrableOn,
    ← integral_inter_add_sdiff hD hL_int.integrableOn]
  congr 1
  · exact setIntegral_congr_fun (hs'.inter hD) fun ω hω ↦ by
      simp [Filtration.stoppedValue'_of_eq_top hω.2]
  -- `{τ < ⊤}` is the union of the sets `{τ ≤ t n}` for a sequence `t` which tends to infinity, on
  -- which we use optional sampling at the bounded stopping time `τ ∧ t n`
  obtain ⟨t, ht_mono, ht⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  let B : ℕ → Set Ω := fun n ↦ s ∩ {ω | τ ω ≤ t n}
  have hB_meas (n : ℕ) : MeasurableSet (B n) := hs'.inter (𝓕.le _ _ (hτ (t n)))
  have hB_mono : Monotone B := fun n m h ω hω ↦
    ⟨hω.1, hω.2.trans (WithTop.coe_le_coe.2 (ht_mono h))⟩
  have hB_eq (n : ℕ) : ∫ ω in B n, 𝓕.stoppedValue' X τ μ ω ∂μ
      = ∫ ω in B n, 𝓕.limitProcess X μ ω ∂μ := by
    have hσ : IsStoppingTime 𝓕 (fun ω ↦ min (τ ω) (t n)) := hτ.min_const (t n)
    have hBσ : MeasurableSet[hσ.measurableSpace] (B n) :=
      (hτ.measurableSet_inter_le_const_iff s (t n)).1 (hs.inter (hτ.measurableSet_le' (t n)))
    calc ∫ ω in B n, 𝓕.stoppedValue' X τ μ ω ∂μ
      _ = ∫ ω in B n, stoppedValue X (fun ω ↦ min (τ ω) (t n)) ω ∂μ :=
        setIntegral_congr_fun (hB_meas n) fun ω hω ↦
          Filtration.stoppedValue'_eq_stoppedValue_min_const hω.2
      _ = ∫ ω in B n, (μ[𝓕.limitProcess X μ | hσ.measurableSpace]) ω ∂μ :=
        setIntegral_congr_ae (hB_meas n)
          ((stoppedValue_ae_eq_condExp_limitProcess_of_le_const hX1 hX2 hX3 hσ
            fun ω ↦ min_le_right _ _).mono fun ω hω _ ↦ hω)
      _ = ∫ ω in B n, 𝓕.limitProcess X μ ω ∂μ :=
        setIntegral_condExp hσ.measurableSpace_le hL_int hBσ
  have h_union : s \ {ω | τ ω = ⊤} = ⋃ n, B n := by
    ext ω
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, B]
    refine ⟨fun ⟨hωs, h_top⟩ ↦ ?_,
      fun ⟨n, hωs, hn⟩ ↦ ⟨hωs, ne_top_of_le_ne_top WithTop.coe_ne_top hn⟩⟩
    obtain ⟨i, hi⟩ := WithTop.ne_top_iff_exists.1 h_top
    obtain ⟨n, hn⟩ := (ht.eventually_ge_atTop i).exists
    exact ⟨n, hωs, by rw [← hi]; exact_mod_cast hn⟩
  rw [h_union]
  exact tendsto_nhds_unique (tendsto_setIntegral_of_monotone hB_meas hB_mono hS_int.integrableOn)
    ((tendsto_setIntegral_of_monotone hB_meas hB_mono hL_int.integrableOn).congr
      fun n ↦ (hB_eq n).symm)

end Martingale

end MeasureTheory
