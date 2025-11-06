/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Martingale.Centering

/-!
# Lemmas about the Doob decomposition

-/

open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]
  {X : ℕ → Ω → E} {𝓕 : Filtration ℕ mΩ}

lemma isPredictable_predictablePart : IsPredictable 𝓕 (predictablePart X 𝓕 μ) := by
  sorry

-- todo: feel free to replace `Preorder E` by something stonger if needed
lemma Submartingale.monotone_predictablePart [Preorder E] (hX : Submartingale X 𝓕 μ) :
    Monotone (predictablePart X 𝓕 μ) := by
  sorry

end MeasureTheory
