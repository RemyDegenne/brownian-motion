/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

/-!
# Komlos lemmas

-/

variable {E Ω : Type*} {mΩ : MeasurableSpace Ω}

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

lemma komlos_convex [AddCommGroup E] [Module ℝ E]
  {f : ℕ → E} {φ : E → ℝ} (hφ_nonneg : 0 ≤ φ)
  (hφ_bdd : ∃ M : ℝ, ∀ n, φ (f n) ≤ M) :
  ∃ g : ℕ → E, (∀ n, g n ∈ convexHull ℝ (Set.range fun m ↦ f (n + m))) ∧
    ∀ δ > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
      2⁻¹ * φ (g n) + 2⁻¹ * φ (g m) - φ ((2 : ℝ)⁻¹ • (g n + g m)) < δ := by
  sorry

lemma komlos_norm [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : ℕ → E} (h_bdd : ∃ M : ℝ, ∀ n, ‖f n‖ ≤ M) :
    ∃ (g : ℕ → E) (x : E), (∀ n, g n ∈ convexHull ℝ (Set.range fun m ↦ f (n + m))) ∧
    Tendsto g atTop (𝓝 x) :=
  sorry

-- todo: check measurability hypothesis/conclusion
lemma komlos_ennreal (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable (X n))
    {P : Measure Ω} [IsProbabilityMeasure P] :
    ∃ (Y : ℕ → Ω → ℝ≥0∞) (Y_lim : Ω → ℝ≥0∞),
      (∀ n, Y n ∈ convexHull ℝ≥0∞ (Set.range fun m ↦ X (n + m))) ∧ Measurable Y_lim ∧
      ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (Y_lim ω)) := by
  let φ : (Ω → ℝ≥0∞) → ℝ := fun f => 𝔼[(- f : EReal).exp]
