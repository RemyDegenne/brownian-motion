/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Martingale.Centering

/-!
# Lemmas about the Doob decomposition

-/

@[expose] public section

open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : ℕ → Ω → E} {𝓕 : Filtration ℕ mΩ}

variable [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

end MeasureTheory
