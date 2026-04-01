/-
Copyright (c) 2026 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import BrownianMotion.StochasticIntegral.Cadlag
import BrownianMotion.StochasticIntegral.SimpleProcess
import BrownianMotion.StochasticIntegral.OptionalSampling
import Mathlib.Probability.Notation

/-! # Cadlag modification stochastic processes -/

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [TopologicalSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}
-- Is this the correct time index?
variable [Approximable 𝓕 μ]

local notation:25 V " ● " X => SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ) V X

lemma exists_modification_left_right_limit [IsFiniteMeasure μ]
    -- Perhaps finite measure can be generalized by requiring the elementary predictable sets to be
    -- uniformly integrable?
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ t, Integrable (X t) μ)
    (hXbdd : ∀ t : ι, ∃ C, ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C) :
    ∃ Y : ι → Ω → ℝ, (∀ t, Y t =ᵐ[μ] X t) ∧
      (∀ x ω, ∃ l, Tendsto (Y · ω) (𝓝[<] x) (𝓝 l)) ∧ -- left limit
      (∀ x ω, ∃ l, Tendsto (Y · ω) (𝓝[>] x) (𝓝 l)) ∧ -- right limit
      ∃ s : Set ι, s.Countable ∧ ∀ x ∉ s, ∀ ω, ContinuousWithinAt (Y · ω) (Set.Ioi x) x := by
  sorry

#check ContinuousWithinAt
#check tendsto_nhds_iff_seq_tendsto

lemma exists_modification_isCadlag [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ t, Integrable (X t) μ)
    (hXRC : ∀ t, ∀ᵐ ω ∂μ, ContinuousWithinAt (X · ω) (Set.Ioi t) t) -- RC in probability
    (hXbdd : ∀ t : ι, ∃ C, ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C) :
    ∃ Y : ι → Ω → ℝ, (∀ t, Y t =ᵐ[μ] X t) ∧ ∀ ω, IsCadlag (Y · ω) := by
  classical
  obtain ⟨Y, hY, hYLL, hYRL, s, hs, hYCont⟩ := exists_modification_left_right_limit hX hXint hXbdd
  set S := ⋃ t ∈ s, {ω | ¬ ContinuousWithinAt (Y · ω) (Set.Ioi t) t} with hSdef
  have hS : ∀ᵐ ω ∂μ, ω ∉ S := by
    simp only [ae_iff, not_not, Set.setOf_mem_eq, hSdef, measure_biUnion_null_iff hs]
    intro t ht
    rw [← ae_iff]
    filter_upwards [hY t, hXRC t] with ω hω hCX
    refine continuousWithinAt_of_tendsto_eq <| hω ▸ ?_
    obtain ⟨l, hl⟩ := hYRL t ω
    -- I'm a bit confused here: the proof says "since X is right continuous in probability,
    -- Y (t+) = Y t." But, we only have X (t+) = X t and X t = Y t a.e.
    -- Chaning the tendsto to sequences doesn't work as the argument would be of the form
    -- ∀ᵐ ω, ∀ seq,... while we want ∀ seq, ∀ᵐ ω,... and the latter is uncountable.
    sorry

  refine ⟨fun t ω ↦ if ω ∈ S then 0 else Y t ω,
    fun t ↦ EventuallyEq.trans ?_ (hY t), fun ω ↦ ⟨?_, ?_⟩⟩
  · filter_upwards [hS] with ω hω
    simp [if_neg hω]
  · by_cases hω : ω ∈ S
    · simp_rw [if_pos hω]
      exact Function.isRightContinuous_const _
    · simp_rw [if_neg hω]
      intro t
      simp only [hSdef, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, not_exists,
        not_and, not_not] at hω
      by_cases ht : t ∈ s
      · exact hω _ ht
      · refine hYCont t ht ω
  · intros x
    by_cases hω : ω ∈ S
    · exact ⟨0, by simp [if_pos hω, tendsto_const_nhds]⟩
    · simp [if_neg hω, hYLL x ω]


end ProbabilityTheory
