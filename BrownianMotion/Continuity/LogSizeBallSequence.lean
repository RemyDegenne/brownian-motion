/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Init

/-!
# TODO

-/

open MeasureTheory
open scoped ENNReal NNReal Finset

variable {T : Type*} [PseudoEMetricSpace T] {a b c : ℝ≥0∞} {n : ℕ}

theorem pair_reduction (J : Finset T) (hJ : #J ≤ b * a ^ n) (ha : 1 < a) (E : Type*) [EDist E] :
    ∃ K : Finset (T × T), K ⊆ J ×ˢ J
      ∧ #K ≤ a * #J
      ∧ (∀ s t, (s, t) ∈ K → edist s t ≤ n * c)
      ∧ (∀ f : T → E,
        ⨆ (s) (t) (hs : s ∈ J) (ht : t ∈ J) (h : edist s t ≤ c), edist (f s) (f t)
        ≤ 2 * ⨆ p ∈ K, edist (f p.1) (f p.2)) := by
  sorry
