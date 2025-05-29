/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Init

/-!
# Stochastic processes satisfying the Kolmogorov condition

-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  {p q M : ℝ≥0}
  {P : Measure Ω}

structure IsKolmogorovProcess (X : T → Ω → E) (P : Measure Ω) (p q M : ℝ≥0) : Prop where
  measurablePair : ∀ s t : T, Measurable (fun ω ↦ (X s ω, X t ω))
  kolmogorovCondition : ∀ s t : T,
    ∫⁻ ω, (edist (X s ω) (X t ω)) ^ (p : ℝ) ∂P ≤ M * edist s t ^ (q : ℝ)

end ProbabilityTheory
