/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import BrownianMotion.Auxiliary.Adapted
public import BrownianMotion.StochasticIntegral.ApproxSeq
public import Mathlib.Probability.Martingale.Centering

@[expose] public section

open Filter TopologicalSpace Function
open scoped NNReal ENNReal Topology

namespace MeasureTheory

namespace Martingale

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [OrderBot ι] [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι] [MetrizableSpace ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : ι → Ω → E} {τ σ : Ω → WithTop ι} {n : ι}

theorem condExp_stoppedValue_stopping_time_ae_eq_restrict_le_of_countable_range
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω)) {i : ι} (hτ_le : ∀ x, τ x ≤ i)
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ)
    (hτ_countable_range : (Set.range τ).Countable) :
    μ[stoppedValue X τ|hσ.measurableSpace] =ᵐ[μ.restrict {x : Ω | τ x ≤ σ x}] stoppedValue X τ := by
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
    · exact (measurable_stoppedValue
        (h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC)
        hτ).stronglyMeasurable.indicator (hτ.measurableSet_le_stopping_time hσ)
    · intro x hx
      simp only [hx, Set.indicator_of_notMem, not_false_iff]
  exact condExp_of_aestronglyMeasurable' hσ.measurableSpace_le h_meas h_int

theorem stoppedValue_min_ae_eq_condExp_of_countable_range
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
    (hτ_countable_range : (Set.range τ).Countable) (hσ_countable_range : (Set.range σ).Countable) :
    (stoppedValue X fun x ↦ min (σ x) (τ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] := by
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
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx_mem
      exact hx hx_mem.le
    apply Filter.EventuallyEq.trans _ ((condExp_min_stopping_time_ae_eq_restrict_le hτ hσ).trans _)
    · exact stoppedValue X τ
    · rw [IsStoppingTime.measurableSpace_min hσ hτ,
        IsStoppingTime.measurableSpace_min hτ hσ, inf_comm]
    · have h1 : μ[stoppedValue X τ|hτ.measurableSpace] = stoppedValue X τ := by
        apply condExp_of_stronglyMeasurable hτ.measurableSpace_le
        · exact Measurable.stronglyMeasurable <|
            measurable_stoppedValue (h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC)
            hτ
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
    ((measurable_stoppedValue (h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC)
      (hτ.min hσ)).mono ((hτ.min hσ).measurableSpace_mono hσ <| fun ω ↦ min_le_right _ _)
      le_rfl).aestronglyMeasurable
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

theorem stoppedValue_ae_eq_condExp_of_le_const'
    [Approximable 𝓕 μ] (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) :
    stoppedValue X τ =ᵐ[μ] μ[X n|hτ.measurableSpace] := by
  convert stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence h hRC
    (isStoppingTime_const 𝓕 n) hτ (fun _ ↦ le_rfl) (discreteApproxSequence_const 𝓕 n)
      (hτ.discreteApproxSequence μ) using 2
  ext ω
  rw [eq_comm, min_eq_right_iff]
  exact hτ_le ω

theorem condExp_stoppedValue_ae_eq_stoppedProcess [Approximable 𝓕 μ] {n : ι}
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) (i : ι) :
    μ[stoppedValue X τ|𝓕 i] =ᵐ[μ] stoppedProcess X τ i := by
  simp_rw [stoppedProcess_eq_stoppedValue, min_comm]
  exact EventuallyEq.trans (Eq.eventuallyEq <| by simp)
    (stoppedValue_min_ae_eq_condExp' h hRC hτ (isStoppingTime_const 𝓕 i) hτ_le).symm

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
