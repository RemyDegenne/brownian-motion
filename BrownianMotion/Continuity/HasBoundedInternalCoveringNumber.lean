/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Continuity.CoveringNumber

/-!
# HasBoundedInternalCoveringNumber

-/

open MeasureTheory
open scoped ENNReal NNReal

variable {T : Type*} [PseudoEMetricSpace T] {A : Set T} {c ε : ℝ≥0∞} {d : ℝ}

def HasBoundedInternalCoveringNumber (A : Set T) (c : ℝ≥0∞) (d : ℝ) : Prop :=
  ∀ ε, ε ≤ EMetric.diam A → internalCoveringNumber ε A ≤ c * ε⁻¹ ^ d

lemma HasBoundedInternalCoveringNumber.internalCoveringNumber_lt_top
    (h : HasBoundedInternalCoveringNumber A c d) (hε_ne : ε ≠ 0)
    (hc : c ≠ ∞) (hd : 0 ≤ d) :
    internalCoveringNumber ε A < ⊤ := by
  by_cases hε_le : ε ≤ EMetric.diam A
  · suffices (internalCoveringNumber ε A : ℝ≥0∞) < ∞ by norm_cast at this
    calc (internalCoveringNumber ε A : ℝ≥0∞)
    _ ≤ c * ε⁻¹ ^ d := h _ hε_le
    _ < ∞ := by
      refine ENNReal.mul_lt_top hc.lt_top ?_
      exact ENNReal.rpow_lt_top_of_nonneg hd (by simp [hε_ne])
  · calc internalCoveringNumber ε A
    _ ≤ 1 := internalCoveringNumber_le_one_of_diam_le (not_le.mp hε_le).le
    _ < ⊤ := by simp

structure IsCoverWithBoundedCoveringNumber (C : ℕ → Set T) (A : Set T) (c : ℕ → ℝ≥0∞) (d : ℕ → ℝ)
    where
  c_ne_top : ∀ n, c n ≠ ∞
  d_pos : ∀ n, 0 < d n
  totallyBounded : ∀ n, TotallyBounded (C n)
  hasBoundedCoveringNumber : ∀ n, HasBoundedInternalCoveringNumber (C n) (c n) (d n)
  mono : ∀ n m, n ≤ m → C n ⊆ C m
  subset_iUnion : A ⊆ ⋃ i, C i

lemma isCoverWithBoundedCoveringNumber_Ico_nnreal :
    IsCoverWithBoundedCoveringNumber (fun n ↦ Set.Ico (0 : ℝ≥0) n) Set.univ
      (fun n ↦ n) (fun _ ↦ 1) where
  c_ne_top := by simp
  d_pos := by simp
  totallyBounded n := by
    sorry
  hasBoundedCoveringNumber n ε hε_le := by
    sorry
  mono n m hnm x hx := by
    simp only [Set.mem_Ico, zero_le, true_and] at hx ⊢
    exact hx.trans_le (mod_cast hnm)
  subset_iUnion x hx := by
    simp only [Set.mem_iUnion, Set.mem_Ico, zero_le, true_and]
    exact exists_nat_gt x
