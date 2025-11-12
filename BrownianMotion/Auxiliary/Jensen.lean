/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Jensen's inequality for conditional expectations

-/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {m mα : MeasurableSpace α} {μ : Measure α} [SigmaFinite μ]
  {s : Set E} {f : α → E} {φ : E → ℝ}

-- Proved in Mathlib PR #27953 for finite measures. Here written for σ-finite measures.
theorem conditional_jensen (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  sorry

lemma norm_condExp_le (hm : m ≤ mα) (hf_int : Integrable f μ) :
    (fun x ↦ ‖μ[f | m] x‖) ≤ᵐ[μ] μ[fun x ↦ ‖f x‖ | m] := by
  sorry -- use conditional_jensen with φ = norm

end MeasureTheory
