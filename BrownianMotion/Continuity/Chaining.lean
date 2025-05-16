/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Continuity.CoveringNumber

/-!
# Chaining

### References
- https://arxiv.org/pdf/2107.13837.pdf Lemma 6.2
- Talagrand, The generic chaining
- Vershynin, High-Dimensional Probability (section 4.2 and chapter 8)

-/

variable {E : Type*} {x y : E} {A : Set E}

-- TODO: find a name
/-- Closest point to `x` in the finite set `s`. -/
def π [Dist E] (s : Finset E) (x : E) : E :=
  sorry

lemma π_mem [Dist E] {s : Finset E} : π s x ∈ s := by
  sorry

lemma dist_π_le [Dist E] {s : Finset E} (hy : y ∈ s) :
    dist x (π s x) ≤ dist x y := by
  sorry

/-- Closest point to `x` in a minimal `ε`-cover of `A`. -/
noncomputable
def πCov [Dist E] (A : Set E) (ε : ℝ) (x : E) : E := π (minimalCover ε A) x

lemma dist_πCov [Dist E] {ε : ℝ} (hxA : x ∈ A) :
    dist x (πCov A ε x) ≤ ε := by
  obtain ⟨y, hy⟩ := isCover_minimalCover sorry x hxA
  exact (dist_π_le hy.1).trans hy.2

lemma dist_πCov_πCov_le_add [PseudoMetricSpace E] {ε₁ ε₂ : ℝ} (hxA : x ∈ A) :
    dist (πCov A ε₁ x) (πCov A ε₂ x) ≤ ε₁ + ε₂ := by
  calc dist (πCov A ε₁ x) (πCov A ε₂ x)
    ≤ dist (πCov A ε₁ x) x + dist x (πCov A ε₂ x) := dist_triangle _ _ _
  _ ≤ ε₁ + ε₂ := add_le_add ((dist_comm _ _).trans_le (dist_πCov hxA)) (dist_πCov hxA)

lemma dist_πCov_succ_le_two_mul [PseudoMetricSpace E] {ε : ℕ → ℝ} (hε : Antitone ε) {i : ℕ}
    (hxA : x ∈ A) :
    dist (πCov A (ε i) x) (πCov A (ε (i + 1)) x) ≤ 2 * ε i := by
  calc dist (πCov A (ε i) x) (πCov A (ε (i + 1)) x) ≤ ε i + ε (i + 1) := dist_πCov_πCov_le_add hxA
  _ ≤ 2 * ε i := by rw [two_mul]; exact add_le_add le_rfl (hε (Nat.le_succ _))

lemma dist_πCov_le_add_dist [PseudoMetricSpace E] {ε : ℝ} (hxA : x ∈ A) (hyA : y ∈ A) :
    dist (πCov A ε x) (πCov A ε y) ≤ 2 * ε + dist x y := by
  calc dist (πCov A ε x) (πCov A ε y)
    ≤ dist (πCov A ε x) y + dist y (πCov A ε y) := dist_triangle _ _ _
  _ ≤ dist (πCov A ε x) x + dist x y + dist y (πCov A ε y) :=
        add_le_add (dist_triangle _ _ _) le_rfl
  _ = dist (πCov A ε x) x + dist y (πCov A ε y) + dist x y := by abel
  _ ≤ 2 * ε + dist x y := by
        rw [two_mul]
        refine add_le_add (add_le_add ?_ (dist_πCov hyA)) le_rfl
        exact (dist_comm _ _).trans_le (dist_πCov hxA)
