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
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : ℕ → Ω → E} {𝓕 : Filtration ℕ mΩ}

lemma predictablePart_succ (n : ℕ) :
    predictablePart X 𝓕 μ (n + 1) =
      predictablePart X 𝓕 μ n + μ[X (n + 1) - X n | 𝓕 n] := by
  induction n with
  | zero => simp [predictablePart]
  | succ k hk =>
    simp [predictablePart, Finset.sum_range_add]

variable [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

lemma isPredictable_predictablePart : IsPredictable 𝓕 (predictablePart X 𝓕 μ) :=
  isPredictable_of_measurable_add_one (by simp [measurable_const'])
    fun n ↦ (adapted_predictablePart n).measurable

-- todo: feel free to replace `Preorder E` by something stonger if needed
lemma Submartingale.monotone_predictablePart {X : ℕ → Ω → ℝ} (hX : Submartingale X 𝓕 μ) :
    ∀ᵐ ω ∂μ, Monotone (predictablePart X 𝓕 μ · ω) := by
  have := ae_all_iff.2 <| fun n : ℕ ↦ hX.condExp_sub_nonneg n.le_succ
  filter_upwards [this] with ω h
  simp only [Pi.zero_apply, Nat.succ_eq_add_one, ← ge_iff_le] at h
  refine monotone_nat_of_le_succ fun n ↦ (?_ : _ ≥ _)
  grw [predictablePart_succ, Pi.add_apply, h n, add_zero]

end MeasureTheory
