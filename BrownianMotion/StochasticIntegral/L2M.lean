/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.Predictable
public import Mathlib.Probability.Process.Predictable

/-! # L2M space

-/

@[expose] public section

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal

namespace ProbabilityTheory

variable {T Ω E : Type*} [LinearOrder T] [TopologicalSpace T] [OrderBot T]
  [OrderTopology T] [MeasurableSpace T] [BorelSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : T → Ω → E} {𝓕 : Filtration T mΩ}

-- this will be specialized in a later definition to the measure
-- coming from the quadratic variation of a martingale
/-- L2 space of predictable processes with respect to a product measure. -/
noncomputable
def L2Predictable (μ : Measure T) (P : Measure Ω) := Lp E 2 ((μ.prod P).trim 𝓕.predictable_le_prod)

end ProbabilityTheory
