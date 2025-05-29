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

variable {T : Type*} [PseudoEMetricSpace T] {c : ℝ≥0∞} {d : ℝ≥0}

def HasBoundedInternalCoveringNumber (A : Set T) (c : ℝ≥0∞) (d : ℝ≥0) : Prop :=
  ∀ ε, ε ≤ EMetric.diam A → internalCoveringNumber ε A ≤ c * ε⁻¹ ^ (d : ℝ)
