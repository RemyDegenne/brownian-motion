/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Jensen
import Mathlib.Probability.Martingale.OptionalStopping

/-! # Doob's Lᵖ inequality

-/

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
  {Y : ι → Ω → ℝ}

theorem maximal_ineq_countable [Countable ι] [IsFiniteMeasure P]
    (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω}, Y n ω ∂P) := by
  sorry

theorem maximal_ineq_norm_countable [Countable ι] [IsFiniteMeasure P]
    (hsub : Martingale X 𝓕 P) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖}, ‖X n ω‖ ∂P) := by
  sorry

theorem maximal_ineq [SecondCountableTopology ι] [IsFiniteMeasure P]
    (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω}, Y n ω ∂P) := by
  obtain ⟨T, hT_countable, hT_dense⟩ := TopologicalSpace.exists_countable_dense ι
  sorry

theorem maximal_ineq_norm [SecondCountableTopology ι] [IsFiniteMeasure P]
    (hsub : Martingale X 𝓕 P) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖}, ‖X n ω‖ ∂P) := by
  sorry

end ProbabilityTheory
