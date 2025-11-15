/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.Basic

/-!
# Komlos lemmas

-/

variable {E : Type*}

open Filter
open scoped Topology NNReal

lemma komlos_convex [AddCommGroup E] [Module ℝ E]
  {f : ℕ → E} {φ : E → ℝ} (hφ_nonneg : 0 ≤ φ) (hφ_convex : ConvexOn ℝ Set.univ φ)
  (hφ_bdd : ∃ M : ℝ, ∀ n, φ (f n) ≤ M) :
  ∃ g : ℕ → E, (∀ n, g n ∈ convexHull ℝ (Set.range fun m ↦ f (n + m))) ∧
    ∀ δ > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
      φ ((2 : ℝ)⁻¹ • g n) + φ ((2 : ℝ)⁻¹ • g m) - φ ((2 : ℝ)⁻¹ • (g n + g m)) < δ := by
  sorry

lemma komlos_norm [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : ℕ → E} (h_bdd : ∃ M : ℝ, ∀ n, ‖f n‖ ≤ M) :
    ∃ (g : ℕ → E) (x : E), (∀ n, g n ∈ convexHull ℝ (Set.range fun m ↦ f (n + m))) ∧
    Tendsto g atTop (𝓝 x) :=
  sorry
