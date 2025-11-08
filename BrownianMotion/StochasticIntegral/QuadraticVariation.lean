/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.StochasticIntegral.DoobMeyer

/-! # Quadratic variation of local martingales

-/

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

/-- The quadratic variation of a local martingale, defined as the predictable part of the Doob-Meyer
decomposition of its squared norm. -/
noncomputable
def quadraticVariation (hX : IsLocalMartingale X 𝓕 P) : ι → Ω → ℝ :=
  have hX2 : IsLocalSubmartingale (fun t ω ↦ ‖X t ω‖ ^ 2) 𝓕 P := sorry
  hX2.predictablePart

end ProbabilityTheory
