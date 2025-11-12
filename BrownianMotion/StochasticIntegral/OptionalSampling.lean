/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import BrownianMotion.StochasticIntegral.ApproxSeq
import BrownianMotion.Auxiliary.Adapted

open Filter TopologicalSpace
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [OrderBot ι] [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι] [MetrizableSpace ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : ι → Ω → ℝ} {τ : Ω → WithTop ι} {n : ι}

theorem stoppedValue_ae_eq_condExp_of_le_const_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : rightContinuous X)
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) (τn : DiscreteApproxSequence 𝓕 μ τ) :
    stoppedValue X τ =ᵐ[μ] μ[X n|hτ.measurableSpace] := by
  set τn' := discreteApproxSequence_of 𝓕 μ hτ_le τn
  have hint (m : ℕ) : stoppedValue X (τn' m) =ᵐ[μ] μ[X n|(τn'.isStoppingTime m).measurableSpace] :=
    h.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (τn'.isStoppingTime m)
      (fun ω ↦ discreteApproxSequence_of_le hτ_le τn m ω) (τn'.discrete m)
  have hintgbl : Integrable (stoppedValue X τ) μ :=
    UniformIntegrable.integrable_of_tendstoInMeasure
      (h.uniformIntegrable_stoppedValue_of_countable_range τn' τn'.isStoppingTime
        (discreteApproxSequence_of_le hτ_le τn) τn'.discrete)
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
