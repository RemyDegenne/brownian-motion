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

open scoped ENNReal

variable {E : Type*} {x y : E} {A : Set E} {C C₁ C₂ : Finset E} {ε ε₁ ε₂ : ℝ≥0∞}

open Classical in
/-- Closest point to `x` in the finite set `s`. -/
noncomputable
def nearestPt [EDist E] (s : Finset E) (x : E) : E :=
  if hs : s.Nonempty then (Finset.exists_min_image s (fun y ↦ edist x y) hs).choose else x

lemma nearestPt_mem [EDist E] {s : Finset E} (hs : s.Nonempty) : nearestPt s x ∈ s := by
  rw [nearestPt, dif_pos hs]
  exact (Finset.exists_min_image s (fun y ↦ edist x y) hs).choose_spec.1

variable [PseudoEMetricSpace E]

lemma edist_nearestPt_le {s : Finset E} (hy : y ∈ s) :
    edist x (nearestPt s x) ≤ edist x y := by
  by_cases hs : s.Nonempty
  · rw [nearestPt, dif_pos hs]
    exact (Finset.exists_min_image s (fun y' ↦ edist x y') hs).choose_spec.2 y hy
  · simp [nearestPt, dif_neg hs]

lemma edist_nearestPt_of_isCover (hC : IsCover C ε A) (hxA : x ∈ A) :
    edist x (nearestPt C x) ≤ ε := by
  obtain ⟨y, hy⟩ := hC x hxA
  exact (edist_nearestPt_le hy.1).trans hy.2

lemma edist_nearestPt_nearestPt_le_add (hC₁ : IsCover C₁ ε₁ A) (hC₂ : IsCover C₂ ε₂ A)
    (hxA : x ∈ A) :
    edist (nearestPt C₁ x) (nearestPt C₂ x) ≤ ε₁ + ε₂ := by
  calc edist (nearestPt C₁ x) (nearestPt C₂ x)
    ≤ edist (nearestPt C₁ x) x + edist x (nearestPt C₂ x) := edist_triangle _ _ _
  _ ≤ ε₁ + ε₂ := add_le_add ((edist_comm _ _).trans_le (edist_nearestPt_of_isCover hC₁ hxA))
      (edist_nearestPt_of_isCover hC₂ hxA)

lemma edist_nearestPt_succ_le_two_mul
    {ε : ℕ → ℝ≥0∞} {C : ℕ → Finset E} (hC : ∀ i, IsCover (C i) (ε i) A)
    (hε : Antitone ε) {i : ℕ} (hxA : x ∈ A) :
    edist (nearestPt (C i) x) (nearestPt (C (i + 1)) x) ≤ 2 * ε i := by
  calc edist (nearestPt (C i) x) (nearestPt (C (i + 1)) x) ≤ ε i + ε (i + 1) :=
    edist_nearestPt_nearestPt_le_add (hC i) (hC (i + 1)) hxA
  _ ≤ 2 * ε i := by rw [two_mul]; exact add_le_add le_rfl (hε (Nat.le_succ _))

lemma edist_nearestPt_le_add_dist (hC : IsCover C ε A) (hxA : x ∈ A) (hyA : y ∈ A) :
    edist (nearestPt C x) (nearestPt C y) ≤ 2 * ε + edist x y := by
  calc edist (nearestPt C x) (nearestPt C y)
    ≤ edist (nearestPt C x) y + edist y (nearestPt C y) := edist_triangle _ _ _
  _ ≤ edist (nearestPt C x) x + edist x y + edist y (nearestPt C y) :=
        add_le_add (edist_triangle _ _ _) le_rfl
  _ = edist (nearestPt C x) x + edist y (nearestPt C y) + edist x y := by abel
  _ ≤ 2 * ε + edist x y := by
        rw [two_mul]
        refine add_le_add (add_le_add ?_ (edist_nearestPt_of_isCover hC hyA)) le_rfl
        exact (edist_comm _ _).trans_le (edist_nearestPt_of_isCover hC hxA)

section Sequence

variable {ε : ℕ → ℝ≥0∞} {C : ℕ → Finset E}

noncomputable
def chainingSequenceReverse (hC : ∀ i, IsCover (C i) (ε i) A)
    {k : ℕ} (hxA : x ∈ C k) : ℕ → E
  | 0 => x
  | n + 1 => nearestPt (C (k - (n + 1))) (chainingSequenceReverse hC hxA n)

noncomputable
def chainingSequence (hC : ∀ i, IsCover (C i) (ε i) A) {k : ℕ} (hxA : x ∈ C k) (n : ℕ) : E :=
  if n ≤ k then chainingSequenceReverse hC hxA (k - n) else x

lemma chainingSequence_mem (hC : ∀ i, IsCover (C i) (ε i) A) {k : ℕ} (hxA : x ∈ C k)
    (n : ℕ) (hn : n ≤ k) :
    chainingSequence hC hxA n ∈ C n := by
  simp only [chainingSequence, hn, ↓reduceIte]
  sorry

lemma edist_chainingSequence_add_one (hC : ∀ i, IsCover (C i) (ε i) A) {k : ℕ} (hxA : x ∈ C k)
  (n : ℕ) (hn : n < k) :
    edist (chainingSequence hC hxA (n + 1)) (chainingSequence hC hxA n) ≤ ε n := by
  sorry

end Sequence
