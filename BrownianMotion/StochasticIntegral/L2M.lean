/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Martingale
import BrownianMotion.StochasticIntegral.ApproxSeq
import BrownianMotion.StochasticIntegral.Locally
import BrownianMotion.Auxiliary.Adapted
import BrownianMotion.StochasticIntegral.OptionalSampling
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Predictable

/-! # L2M space

-/

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal

namespace ProbabilityTheory

variable {T Ω E : Type*} [LinearOrder T] [TopologicalSpace T] [OrderBot T]
  [OrderTopology T] [MeasurableSpace T] [BorelSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : T → Ω → E} {𝓕 : Filtration T mΩ}

lemma _root_.MeasureTheory.Filtration.predictable_le_prod (𝓕 : Filtration T mΩ) :
    𝓕.predictable ≤ Prod.instMeasurableSpace := by
  sorry

-- this will be specialized to the measure coming from the quadratic variation of a martingale
noncomputable
def L2μ (μ : Measure T) :=
  MeasureTheory.Lp E (m := 𝓕.predictable) 2 ((μ.prod P).trim 𝓕.predictable_le_prod)

end ProbabilityTheory
