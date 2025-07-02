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

lemma HasBoundedInternalCoveringNumber.diam_lt_top
    (h : HasBoundedInternalCoveringNumber A c d) (hd : 0 < d) :
    EMetric.diam A < ∞ := by
  specialize h _ le_rfl
  by_contra!
  simp only [top_le_iff] at this
  simp only [this, ENNReal.inv_top, hd, ENNReal.zero_rpow_of_pos, mul_zero, nonpos_iff_eq_zero] at h
  norm_cast at h
  simp only [internalCoveringNumber, ENat.iInf_eq_zero, Nat.cast_eq_zero, Finset.card_eq_zero,
    exists_prop, exists_eq_right_right, Finset.coe_empty, isCover_empty_iff, Set.empty_subset] at h
  simp [h] at this

lemma HasBoundedInternalCoveringNumber.subset {B : Set T}
    (h : HasBoundedInternalCoveringNumber A c d) (hBA : B ⊆ A) (hd : 0 ≤ d) :
    HasBoundedInternalCoveringNumber B (2 ^ d * c) d := by
  intro ε hε_le
  by_cases hdA : d = 0 ∧ EMetric.diam A = ∞
  · simp only [hdA.1, ENNReal.rpow_zero, one_mul, mul_one]
    specialize h 0 zero_le'
    simp only [ENNReal.inv_zero, hdA.1, ENNReal.rpow_zero, mul_one] at h
    calc (internalCoveringNumber ε B : ℝ≥0∞)
    _ ≤ internalCoveringNumber 0 B := mod_cast internalCoveringNumber_anti zero_le'
    _ ≤ internalCoveringNumber (0 / 2) A := mod_cast internalCoveringNumber_subset_le (by simp) hBA
    _ = internalCoveringNumber 0 A := by simp
    _ ≤ c := h
  push_neg at hdA
  calc (internalCoveringNumber ε B : ℝ≥0∞)
  _ ≤ internalCoveringNumber (ε / 2) A := by
    refine mod_cast internalCoveringNumber_subset_le (ne_of_lt ?_) hBA
    refine (hε_le.trans (EMetric.diam_mono hBA)).trans_lt ?_
    by_cases hd_zero : d = 0
    · exact (hdA hd_zero).lt_top
    · exact h.diam_lt_top (lt_of_le_of_ne' hd hd_zero)
  _ ≤ c * (ε / 2)⁻¹ ^ d := h _ <| by
    calc ε / 2 ≤ ε := ENNReal.half_le_self
    _ ≤ EMetric.diam B := hε_le
    _ ≤ EMetric.diam A := EMetric.diam_mono hBA
  _ = 2 ^ d * c * ε⁻¹ ^ d := by
    rw [div_eq_mul_inv, ENNReal.mul_inv (by simp) (by simp), inv_inv,
      ENNReal.mul_rpow_of_nonneg _ _ hd]
    ring

structure IsCoverWithBoundedCoveringNumber (C : ℕ → Set T) (A : Set T) (c : ℕ → ℝ≥0∞) (d : ℕ → ℝ)
    where
  c_ne_top : ∀ n, c n ≠ ∞
  d_pos : ∀ n, 0 < d n
  isOpen : ∀ n, IsOpen (C n)
  totallyBounded : ∀ n, TotallyBounded (C n)
  hasBoundedCoveringNumber : ∀ n, HasBoundedInternalCoveringNumber (C n) (c n) (d n)
  mono : ∀ n m, n ≤ m → C n ⊆ C m
  subset_iUnion : A ⊆ ⋃ i, C i

open scoped Pointwise in
lemma isCoverWithBoundedCoveringNumber_Ico_nnreal :
    IsCoverWithBoundedCoveringNumber (fun n ↦ Set.Ico (0 : ℝ≥0) (n + 1)) Set.univ
      (fun n ↦ 4 * (n + 1)) (fun _ ↦ 1) where
  c_ne_top n := by finiteness
  d_pos := by simp
  isOpen n := NNReal.isOpen_Ico_zero
  totallyBounded n := totallyBounded_Ico _ _
  hasBoundedCoveringNumber n ε hε_le := by
    simp only [ENNReal.rpow_one]
    have h_iso : Isometry ((↑) : ℝ≥0 → ℝ) := fun x y ↦ rfl
    rw [← h_iso.internalCoveringNumber_image]
    have h_image : ((↑) : ℝ≥0 → ℝ) '' (Set.Ico (0 : ℝ≥0) (n + 1)) = Set.Ico (0 : ℝ) (n + 1) := by
      ext x
      simp only [Set.mem_image, Set.mem_Ico, zero_le, true_and]
      refine ⟨fun ⟨y, hy, hy_eq⟩ ↦ ?_, fun h ↦ ?_⟩
      · rw [← hy_eq]
        exact ⟨y.2, hy⟩
      · exact ⟨⟨x, h.1⟩, h.2, rfl⟩
    rw [h_image]
    -- todo : extract that have as a lemma
    have h_diam : EMetric.diam (Set.Ico (0 : ℝ≥0) (n + 1)) = n + 1 := by
      rw [← h_iso.ediam_image, h_image]
      simp only [Real.ediam_Ico, sub_zero]
      norm_cast
    rw [h_diam] at hε_le
    have : Set.Ico (0 : ℝ) (n + 1) ⊆ EMetric.closedBall (((n : ℝ) + 1) / 2) ((n + 1) / 2) := by
      intro x hx
      simp only [Set.mem_Ico, EMetric.mem_closedBall, edist_dist, dist] at hx ⊢
      refine ENNReal.ofReal_le_of_le_toReal ?_
      simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
      norm_cast
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith
      · simp [hx.2.le]
    calc (internalCoveringNumber ε (Set.Ico (0 : ℝ) (n + 1)) : ℝ≥0∞)
    _ ≤ internalCoveringNumber (ε / 2) (EMetric.closedBall (((n : ℝ) + 1) / 2) ((n + 1) / 2)) := by
      gcongr
      refine internalCoveringNumber_subset_le ?_ this
      exact ne_top_of_le_ne_top (by finiteness) hε_le
    _ ≤ 2 * ((n + 1) / 2) / (ε / 2) + 1 :=
      (internalCoveringNumber_closedBall_le _ _ _).trans_eq (by simp)
    _ = 2 * (n + 1) / ε + 1 := by
      rw [mul_div_assoc, mul_div_assoc]
      congr 2
      simp_rw [div_eq_mul_inv]
      rw [ENNReal.mul_inv (by simp) (by simp), inv_inv, mul_assoc, mul_comm _ (2 : ℝ≥0∞),
        ← mul_assoc _ (2 : ℝ≥0∞), ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
    _ ≤ 2 * (n + 1) / ε + 2 * (n + 1) / ε := by
      gcongr
      rw [ENNReal.le_div_iff_mul_le (by simp) (.inr <| by finiteness), one_mul, two_mul]
      exact hε_le.trans le_self_add
    _ = 4 * (n + 1) * ε⁻¹ := by
      rw [← two_mul, ← mul_div_assoc, ← mul_assoc]
      congr
      norm_num
  mono n m hnm x hx := by
    simp only [Set.mem_Ico, zero_le, true_and] at hx ⊢
    exact hx.trans_le (mod_cast (by gcongr))
  subset_iUnion x hx := by
    simp only [Set.mem_iUnion, Set.mem_Ico, zero_le, true_and]
    obtain ⟨i, hi⟩ := exists_nat_gt x
    exact ⟨i, hi.trans (by simp)⟩
