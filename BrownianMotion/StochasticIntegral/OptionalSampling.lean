/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import BrownianMotion.StochasticIntegral.ApproxSeq
import BrownianMotion.Auxiliary.Adapted

open Filter TopologicalSpace Function
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [OrderBot ι] [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι] [MetrizableSpace ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {n : ι}

theorem Martingale.condExp_stoppedValue_stopping_time_ae_eq_restrict_le_of_countable_range
    (h : Martingale X 𝓕 μ) (hRC : rightContinuous X) {i : ι} (hτ_le : ∀ x, τ x ≤ i)
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ)
    (hτ_countable_range : (Set.range τ).Countable) :
    μ[stoppedValue X τ|hσ.measurableSpace] =ᵐ[μ.restrict {x : Ω | τ x ≤ σ x}] stoppedValue X τ := by
  rw [ae_eq_restrict_iff_indicator_ae_eq
    (hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ))]
  refine (condExp_indicator
    (h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range)
    (hτ.measurableSet_stopping_time_le hσ)).symm.trans ?_
  have h_int :
      Integrable ({ω : Ω | τ ω ≤ σ ω}.indicator (stoppedValue (fun n : ι => X n) τ)) μ :=
    Integrable.indicator
      (h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range)
      <| hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ)
  have h_meas : AEStronglyMeasurable[hσ.measurableSpace]
      ({ω : Ω | τ ω ≤ σ ω}.indicator (stoppedValue (fun n : ι => X n) τ)) μ := by
    refine StronglyMeasurable.aestronglyMeasurable ?_
    refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on
      (hτ.measurableSet_le_stopping_time hσ) ?_ ?_ ?_
    · intro t ht
      rw [Set.inter_comm _ t] at ht ⊢
      rw [hτ.measurableSet_inter_le_iff hσ, IsStoppingTime.measurableSet_min_iff hτ hσ] at ht
      exact ht.2
    · exact (measurable_stoppedValue (h.adapted.progMeasurable_of_rightContinuous hRC)
        hτ).stronglyMeasurable.indicator (hτ.measurableSet_le_stopping_time hσ)
    · intro x hx
      simp only [hx, Set.indicator_of_notMem, not_false_iff]
  exact condExp_of_aestronglyMeasurable' hσ.measurableSpace_le h_meas h_int

theorem Martingale.stoppedValue_min_ae_eq_condExp_of_countable_range
    (h : Martingale X 𝓕 μ) (hRC : rightContinuous X)
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
    (hτ_countable_range : (Set.range τ).Countable) (hσ_countable_range : (Set.range σ).Countable) :
    (stoppedValue X fun x => min (σ x) (τ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] := by
  refine
    (h.stoppedValue_ae_eq_condExp_of_le_of_countable_range hτ
      (hσ.min hτ) (fun x => min_le_right _ _) hτ_le hτ_countable_range ?_).trans ?_
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
            measurable_stoppedValue (h.adapted.progMeasurable_of_rightContinuous hRC) hτ
        · exact h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range
      rw [h1]
      exact (h.condExp_stoppedValue_stopping_time_ae_eq_restrict_le_of_countable_range hRC hτ_le
        hτ hσ hτ_countable_range).symm

theorem Martingale.stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence
    [SigmaFiniteFiltration μ 𝓕] (h : Martingale X 𝓕 μ) (hRC : rightContinuous X)
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
    (τn : DiscreteApproxSequence 𝓕 τ μ) (σn : DiscreteApproxSequence 𝓕 σ μ) :
    (stoppedValue X fun x => min (σ x) (τ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] := by
  set τn' := discreteApproxSequence_of 𝓕 hτ_le τn
  have hint (m : ℕ) : stoppedValue X (τn' m) =ᵐ[μ] μ[X n|(τn'.isStoppingTime m).measurableSpace] :=
    h.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (τn'.isStoppingTime m)
      (fun ω ↦ discreteApproxSequence_of_le hτ_le τn m ω) (τn'.countable m)
  have hintgbl : Integrable (stoppedValue X τ) μ :=
    integrable_stoppedValue_of_discreteApproxSequence' h hRC hτ_le τn
  refine ae_eq_condExp_of_forall_setIntegral_eq _ hintgbl ?_ ?_
    ((measurable_stoppedValue (h.adapted.progMeasurable_of_rightContinuous hRC)
      (hσ.min hτ)).mono ((hσ.min hτ).measurableSpace_mono hσ <| fun ω ↦ min_le_left _ _)
      le_rfl).aestronglyMeasurable
  · exact fun s hs _ ↦ (integrable_stoppedValue_of_discreteApproxSequence' h hRC
      (fun _ ↦ min_le_of_right_le <| hτ_le _) <| σn.inf τn).integrableOn
  sorry
  -- rintro s hs -
  -- have : (fun m ↦ ∫ ω in s, stoppedValue X (τn' m) ω ∂μ) = fun m ↦ ∫ ω in s, X n ω ∂μ := by
  --   ext m
  --   rw [← setIntegral_condExp (τn'.isStoppingTime m).measurableSpace_le (h.integrable _)
  --     (hτ.measurableSpace_mono (τn'.isStoppingTime m) (τn'.le m) _ hs)]
  --   refine setIntegral_congr_ae (hτ.measurableSpace_le _ hs) ?_
  --   filter_upwards [hint m] with ω hω _ using hω
  -- rw [eq_comm, ← tendsto_const_nhds_iff (l := (atTop : Filter ℕ)), ← this]
  -- refine tendsto_setIntegral_of_L1' _ hintgbl ?_
  --   (tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence h hRC hτ_le τn) _
  -- rw [eventually_atTop]
  -- refine ⟨0, fun m _ ↦ ?_⟩
  -- rw [integrable_congr (hint m)]
  -- exact integrable_condExp

theorem Martingale.stoppedValue_ae_eq_condExp_of_le_const_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : rightContinuous X)
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) (τn : DiscreteApproxSequence 𝓕 τ μ) :
    stoppedValue X τ =ᵐ[μ] μ[X n|hτ.measurableSpace] := by
  set τn' := discreteApproxSequence_of 𝓕 hτ_le τn
  have hint (m : ℕ) : stoppedValue X (τn' m) =ᵐ[μ] μ[X n|(τn'.isStoppingTime m).measurableSpace] :=
    h.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (τn'.isStoppingTime m)
      (fun ω ↦ discreteApproxSequence_of_le hτ_le τn m ω) (τn'.countable m)
  have hintgbl : Integrable (stoppedValue X τ) μ :=
    UniformIntegrable.integrable_of_tendstoInMeasure
      (h.uniformIntegrable_stoppedValue_of_countable_range τn' τn'.isStoppingTime
        (discreteApproxSequence_of_le hτ_le τn) τn'.countable)
      (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
        (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1)
        (aestronglyMeasurable_stoppedValue_of_discreteApproxSequence h hRC hτ_le τn') <|
        tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence h hRC hτ_le τn)
  refine ae_eq_condExp_of_forall_setIntegral_eq (hτ.measurableSpace_le)
    (h.integrable _) (fun _ _ _ ↦ hintgbl.integrableOn) ?_
    (measurable_stoppedValue (h.adapted.progMeasurable_of_rightContinuous hRC)
      hτ).aestronglyMeasurable
  rintro s hs -
  have : (fun m ↦ ∫ ω in s, stoppedValue X (τn' m) ω ∂μ) = fun m ↦ ∫ ω in s, X n ω ∂μ := by
    ext m
    rw [← setIntegral_condExp (τn'.isStoppingTime m).measurableSpace_le (h.integrable _)
      (hτ.measurableSpace_mono (τn'.isStoppingTime m) (τn'.le m) _ hs)]
    refine setIntegral_congr_ae (hτ.measurableSpace_le _ hs) ?_
    filter_upwards [hint m] with ω hω _ using hω
  rw [eq_comm, ← tendsto_const_nhds_iff (l := (atTop : Filter ℕ)), ← this]
  refine tendsto_setIntegral_of_L1' _ hintgbl ?_
    (tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence h hRC hτ_le τn) _
  rw [eventually_atTop]
  refine ⟨0, fun m _ ↦ ?_⟩
  rw [integrable_congr (hint m)]
  exact integrable_condExp

end MeasureTheory
