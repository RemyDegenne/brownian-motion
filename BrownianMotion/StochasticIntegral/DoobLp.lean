/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Martingale
import Mathlib.Probability.Martingale.OptionalStopping

/-! # Doob's Lᵖ inequality

-/

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [Preorder ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} {s : Set ι}

def _root_.MeasureTheory.Filtration.subset (𝓕 : Filtration ι mΩ) :
    Filtration s mΩ where
  seq := 𝓕.seq ∘ Subtype.val
  mono' := fun _ _ h => 𝓕.mono' (Subtype.coe_le_coe.mpr h)
  le' := fun _ => 𝓕.le' _

def _root_.MeasureTheory.Submartingale.subset [LE E] (hsub : Submartingale X 𝓕 P) :
    Submartingale (X ∘ Subtype.val : s → Ω → E) 𝓕.subset P :=
  ⟨fun _ => hsub.1 _, fun _ _ h => hsub.2.1 _ _ h, fun _ => hsub.2.2 _⟩

variable [IsFiniteMeasure P] {Y : ι → Ω → ℝ}

theorem maximal_ineq_countable [Countable ι]
    (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω}, Y n ω ∂P) := by
  sorry

theorem maximal_ineq_norm_countable [Countable ι]
    (hsub : Martingale X 𝓕 P) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖}, ‖X n ω‖ ∂P) := by
  sorry

variable [TopologicalSpace ι] [SecondCountableTopology ι]

theorem maximal_ineq (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) (n : ι)
    (hY_cont : ∀ (ω : Ω) (a : ι), ContinuousWithinAt (fun (y : ι) => Y y ω) (Set.Ioi a) a) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω}, Y n ω ∂P) := by
  obtain ⟨T, hT_countable, hT_dense⟩ := TopologicalSpace.exists_countable_dense ι
  let S := (T ∩ Set.Iic n) ∪ {n}
  have hn : n ∈ S := by simp [S]
  have : Countable S := by
    rw [Set.countable_coe_iff]
    exact Set.Countable.union (Set.Countable.mono (by simp) hT_countable) (by simp)
  have (ω : Ω) : ⨆ i ≤ n, Y i ω = ⨆ s ≤ ⟨n, hn⟩, (Y ∘ Subtype.val : S → Ω → ℝ) s ω := by sorry
  simpa [this] using maximal_ineq_countable hsub.subset (fun _ _ => hnonneg _ _) ε ⟨n, hn⟩

theorem maximal_ineq_norm (hsub : Martingale X 𝓕 P) (ε : ℝ≥0) (n : ι)
    (hX_cont : ∀ (ω : Ω) (a : ι), ContinuousWithinAt (fun (x : ι) => X x ω) (Set.Ioi a) a) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖}, ‖X n ω‖ ∂P) :=
  maximal_ineq hsub.submartingale_norm (fun t ω => norm_nonneg (X t ω)) ε n
    (fun ω a => (hX_cont ω a).norm)

end ProbabilityTheory
