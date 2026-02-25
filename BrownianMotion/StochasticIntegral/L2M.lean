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
  unfold Filtration.predictable
  apply MeasurableSpace.generateFrom_le
  rintro s (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
  · exact (measurableSet_singleton _).prod (𝓕.le _ _ hA)
  · exact measurableSet_Ioi.prod (𝓕.le _ _ hA)

-- this will be specialized in a later definition to the measure
-- coming from the quadratic variation of a martingale
/-- L2 space of predictable processes with respect to a product measure. -/
noncomputable
def L2Predictable (μ : Measure T) (P : Measure Ω) := Lp E 2 ((μ.prod P).trim 𝓕.predictable_le_prod)

end ProbabilityTheory
