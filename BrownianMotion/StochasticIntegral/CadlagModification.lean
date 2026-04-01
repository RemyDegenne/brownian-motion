/-
Copyright (c) 2026 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import BrownianMotion.StochasticIntegral.Cadlag
import BrownianMotion.StochasticIntegral.SimpleProcess
import BrownianMotion.StochasticIntegral.OptionalSampling

/-! # Cadlag modification stochastic processes -/

open MeasureTheory Finset Filter
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

#check ElementaryPredictableSet
#check IsCadlag

variable {ι Ω : Type*} [TopologicalSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}
-- Is this the correct time index?
variable [Approximable 𝓕 μ]

lemma exists_modification_left_right_limit [IsFiniteMeasure μ]
    -- Perhaps finite measure can be generalized by requiring the elementary predictable sets to be
    -- uniformly integrable?
    (hX : ∀ t : ι, ∃ C, ∀ S : ElementaryPredictableSet 𝓕, μ[S.indicator 1 ] ≤ C) :
    true := sorry


end ProbabilityTheory
