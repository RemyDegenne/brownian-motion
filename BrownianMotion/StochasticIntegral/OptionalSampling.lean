/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import BrownianMotion.Auxiliary.Adapted
public import BrownianMotion.Auxiliary.StoppedValue
public import BrownianMotion.StochasticIntegral.ApproxSeq
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
  · refine tendsto_setIntegral_of_L1' _ (integrable_stoppedValue_of_discreteApproxSequence' h hRC
        (fun _ ↦ min_le_of_left_le <| hτ_le _) τn').aestronglyMeasurable ?_
      (tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence_of_le h hRC τn'
        (τn.discreteApproxSequence_of_le_inf_le_of_left σn hτ_le)) _
    rw [eventually_atTop]
    exact ⟨0, fun m _ ↦ (h.integrable_stoppedValue_of_countable_range _
      (DiscreteApproxSequence.isStoppingTime _ _)
      (τn.discreteApproxSequence_of_le_inf_le_of_left σn hτ_le m)
      (DiscreteApproxSequence.countable _ m))⟩
  · refine tendsto_setIntegral_of_L1' _ hintgbl.aestronglyMeasurable ?_
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
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hf n)]
    exact ENNReal.ofReal_le_ofReal (hC n)
  have hg : Integrable g P :=
    memLp_one_iff_integrable.1 ⟨hg_meas, h_le.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hg, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hg] at h_le
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
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
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
  classical
  -- we enumerate the values of `τ` and approximate `τ` by the stopping time `ρ m` equal to `τ`
  -- if `τ` is one of the first `m` values and to `k` otherwise, then we use Fatou's lemma
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.1
    (hτ_count.preimage (WithTop.coe_injective (α := ι)))
  let A (m : ℕ) : Set (WithTop ι) := WithTop.some '' ((Finset.range m).image f : Set ι)
  let ρ (m : ℕ) : Ω → WithTop ι := (τ ⁻¹' A m).piecewise τ (fun _ ↦ (k : WithTop ι))
  have hρ (m : ℕ) : IsStoppingTime 𝓕 (ρ m) :=
    hτ.piecewise_preimage_const_of_countable_range hτk hτ_count
  have hρk (m : ℕ) (ω : Ω) : ρ m ω ≤ k := by
    by_cases hω : ω ∈ τ ⁻¹' A m <;> simp [ρ, hω, hτk ω]
  have hρs (m : ℕ) (ω : Ω) :
      ρ m ω ∈ WithTop.some '' (insert k ((Finset.range m).image f) : Finset ι) := by
    by_cases hω : ω ∈ τ ⁻¹' A m
    · have hρω : ρ m ω = τ ω := Set.piecewise_eq_of_mem _ _ _ hω
      obtain ⟨i, hi, hiτ⟩ := hω
      exact ⟨i, Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hi)),
        hiτ.trans hρω.symm⟩
    · have hρω : ρ m ω = k := Set.piecewise_eq_of_notMem _ _ _ hω
      exact ⟨k, Finset.mem_coe.2 (Finset.mem_insert_self _ _), hρω.symm⟩
  refine integrable_of_tendsto_ae_of_integral_norm_le
    (fun m ↦ integrable_stoppedValue_of_mem_finset (hρ m) hX.integrable (hρs m))
    (fun m ↦ hX.integral_abs_stoppedValue_le_of_mem_finset (hρ m) (hρk m) (hρs m))
    (ae_of_all _ fun ω ↦ ?_)
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (hτk ω))
  obtain ⟨n, hn⟩ := hf ⟨ω, hj.symm⟩
  refine tendsto_atTop_of_eventually_const (i₀ := n + 1) fun m hm ↦ ?_
  have hω : ω ∈ τ ⁻¹' A m :=
    ⟨j, Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 hm, hn⟩), hj⟩
  simp [stoppedValue, ρ, hω]

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

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [OrderBot ι] [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι] [MetrizableSpace ι]
  {σ τ : Ω → WithTop ι} {X : ι → Ω → E} (𝓕 : Filtration ι mΩ)

theorem Submartingale.stoppedValue_min_ae_le_condExp [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    (hX1 : Submartingale X 𝓕 P) (hX2 : ∀ ω, IsRightContinuous (X · ω)) {k : ι}
    (hτk : ∀ᵐ ω ∂P, τ ω ≤ k) (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] := by
  sorry

end subsupermartingale

end MeasureTheory
