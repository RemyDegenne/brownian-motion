/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Continuity.CoveringNumber
public import Mathlib.Topology.MetricSpace.CoveringExponent

/-!
# Covers by sets with bounded covering exponent

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

variable {T : Type*} [PseudoEMetricSpace T] {A : Set T} {c : ℝ≥0∞} {ε : ℝ≥0} {d : ℝ}

/-- The covering condition at scale `diam A` bounds the diameter of `A` by `c ^ (1/d)`. -/
lemma Metric.HasCoveringExponent.ediam_le
    (h : HasCoveringExponent A c d) (hd : 0 < d) :
    Metric.ediam A ≤ c ^ d⁻¹ := by
  rcases eq_or_ne (Metric.ediam A) 0 with h0 | h0
  · simp [h0]
  have hA : A.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    simp at h0
  have hε : ((Metric.ediam A).toNNReal : ℝ≥0∞) = Metric.ediam A :=
    ENNReal.coe_toNNReal h.ediam_lt_top.ne
  have h1 : 1 ≤ c * (Metric.ediam A)⁻¹ ^ d := by
    refine le_trans ?_ (hε ▸ h.coveringNumber_le (Metric.ediam A).toNNReal hε.le)
    exact_mod_cast Order.one_le_iff_pos.mpr (coveringNumber_pos_iff.mpr hA)
  have h2 : Metric.ediam A ^ d ≤ c := by
    have := mul_le_mul' h1 (le_refl (Metric.ediam A ^ d))
    rwa [one_mul, mul_assoc, ← ENNReal.mul_rpow_of_ne_top (by simp [h0]) h.ediam_lt_top.ne,
      ENNReal.inv_mul_cancel h0 h.ediam_lt_top.ne, ENNReal.one_rpow, mul_one] at this
  calc Metric.ediam A = (Metric.ediam A ^ d) ^ d⁻¹ := by
        rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hd.ne', ENNReal.rpow_one]
    _ ≤ c ^ d⁻¹ := ENNReal.rpow_le_rpow h2 (by positivity)

structure IsCoverWithBoundedCoveringNumber (C : ℕ → Set T) (A : Set T) (c : ℕ → ℝ≥0∞) (d : ℕ → ℝ)
    where
  c_ne_top : ∀ n, c n ≠ ∞
  d_pos : ∀ n, 0 < d n
  isOpen : ∀ n, IsOpen (C n)
  totallyBounded : ∀ n, TotallyBounded (C n)
  hasBoundedCoveringNumber : ∀ n, HasCoveringExponent (C n) (c n) (d n)
  mono : ∀ n m, n ≤ m → C n ⊆ C m
  subset_iUnion : A ⊆ ⋃ i, C i

open scoped Pointwise in
lemma isCoverWithBoundedCoveringNumber_Ico_nnreal :
    IsCoverWithBoundedCoveringNumber (fun n ↦ Set.Ico (0 : ℝ≥0) (n + 1)) Set.univ
      (fun n ↦ 3 * (n + 1)) (fun _ ↦ 1) where
  c_ne_top n := by finiteness
  d_pos := by simp
  isOpen n := NNReal.isOpen_Ico_zero
  totallyBounded n := totallyBounded_Ico _ _
  hasBoundedCoveringNumber n := by
    have h_iso : Isometry ((↑) : ℝ≥0 → ℝ) := fun x y ↦ rfl
    have h_image : ((↑) : ℝ≥0 → ℝ) '' (Set.Ico (0 : ℝ≥0) (n + 1)) = Set.Ico (0 : ℝ) (n + 1) := by
      ext x
      simp only [Set.mem_image, Set.mem_Ico, zero_le, true_and]
      refine ⟨fun ⟨y, hy, hy_eq⟩ ↦ ?_, fun h ↦ ?_⟩
      · rw [← hy_eq]
        exact ⟨y.2, hy⟩
      · exact ⟨⟨x, h.1⟩, h.2, rfl⟩
    -- todo : extract that have as a lemma
    have h_diam : Metric.ediam (Set.Ico (0 : ℝ≥0) (n + 1)) = n + 1 := by
      rw [← h_iso.ediam_image, h_image]
      simp only [Real.ediam_Ico, sub_zero]
      norm_cast
    constructor
    · simp [h_diam]
    intro ε hε_le
    simp only [ENNReal.rpow_one]
    rw [← h_iso.coveringNumber_image, h_image]
    rw [h_diam] at hε_le
    have : Set.Ico (0 : ℝ) (n + 1) ⊆ Metric.closedEBall (((n : ℝ) + 1) / 2) ((n + 1) / 2) := by
      intro x hx
      simp only [Set.mem_Ico, Metric.mem_closedEBall, edist_dist, dist] at hx ⊢
      refine ENNReal.ofReal_le_of_le_toReal ?_
      simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
      norm_cast
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith
      · simp [hx.2.le]
    calc (coveringNumber ε (Set.Ico (0 : ℝ) (n + 1)) : ℝ≥0∞)
    _ ≤ coveringNumber (ε / 2) (Metric.closedEBall (((n : ℝ) + 1) / 2) ((n + 1) / 2)) := by
      gcongr
      exact coveringNumber_subset_le this
    _ ≤ 3 * ((n + 1) / 2 : ℝ≥0) / (ε / 2 : ℝ≥0) := by
      have h := coveringNumber_closedBall_le_three_mul (r := (n + 1) / 2) (ε := ε / 2)
        (x := ((n : ℝ) + 1) / 2) ?_ ?_
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_add,
          ENNReal.coe_natCast, ENNReal.coe_one, ENNReal.coe_ofNat, Module.finrank_self, pow_one]
          at h
        rwa [ENNReal.coe_div (by simp), ENNReal.coe_div (by simp)]
      · simp
      · gcongr
        exact mod_cast hε_le
    _ = 3 * (n + 1) / ε := by
      conv_lhs => rw [mul_div_assoc]
      conv_rhs => rw [mul_div_assoc]
      congr 1
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_add,
        ENNReal.coe_natCast, ENNReal.coe_one, ENNReal.coe_ofNat]
      simp_rw [div_eq_mul_inv]
      rw [ENNReal.mul_inv (by simp) (by simp), inv_inv, mul_assoc, mul_comm _ (2 : ℝ≥0∞),
        ← mul_assoc _ (2 : ℝ≥0∞), ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
    _ ≤ 3 * (n + 1) * (ε : ℝ≥0∞)⁻¹ := by rw [div_eq_mul_inv]
  mono n m hnm x hx := by
    simp only [Set.mem_Ico, zero_le, true_and] at hx ⊢
    exact hx.trans_le (mod_cast (by gcongr))
  subset_iUnion x hx := by
    simp only [Set.mem_iUnion, Set.mem_Ico, zero_le, true_and]
    obtain ⟨i, hi⟩ := exists_nat_gt x
    exact ⟨i, hi.trans (by simp)⟩
