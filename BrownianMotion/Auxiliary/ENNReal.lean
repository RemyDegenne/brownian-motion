import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open NNReal

namespace ENNReal

lemma rpow_max {x y : ℝ≥0∞} {p : ℝ} (hp : 0 ≤ p) : max x y ^ p = max (x ^ p) (y ^ p) := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (rpow_le_rpow hxy hp)]
  · rw [max_eq_left hxy, max_eq_left (rpow_le_rpow hxy hp)]

lemma rpow_add_le_two_rpow_mul_add_rpow {p : ℝ} (a b : ℝ≥0∞) (hp : 0 ≤ p) :
    (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := calc
  (a + b) ^ p ≤ (2 * max a b) ^ p := by rw [two_mul]; gcongr <;> simp
  _ = 2 ^ p * (max a b) ^ p := mul_rpow_of_nonneg _ _ hp
  _ = 2 ^ p * max (a ^ p) (b ^ p) := by rw [rpow_max hp]
  _ ≤ 2 ^ p * (a ^ p + b ^ p) := by gcongr; apply max_le_add_of_nonneg <;> simp

lemma sum_geometric_two_le (n : ℕ) : ∑ i ∈ Finset.range n, ((1 : ENNReal) / 2) ^ i ≤ 2 := by
  rw [← ENNReal.toReal_le_toReal (by simp) (by simp), toReal_ofNat, toReal_sum (by simp)]
  simpa [-one_div] using _root_.sum_geometric_two_le _

lemma ofReal_one_div {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (1 / x) = 1 / (ENNReal.ofReal x) := by
  rwa [ENNReal.ofReal_div_of_pos, ofReal_one]

lemma le_one_div_iff {x y : ℝ≥0∞} : x ≤ 1 / y ↔ y ≤ 1 / x := by
  rw [ENNReal.le_div_iff_mul_le, ENNReal.le_div_iff_mul_le, mul_comm]
  all_goals simp

lemma rpow_add_of_add_pos {x : ENNReal} (hx : x ≠ ⊤) (y z : ℝ) (hyz : 0 < y + z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  obtain (rfl|hx') := eq_or_ne x 0
  · by_cases hy' : 0 < y
    · simp [ENNReal.zero_rpow_of_pos hyz, ENNReal.zero_rpow_of_pos hy']
    · have hz' : 0 < z := by
        simp only [not_lt] at hy'
        refine lt_of_lt_of_le hyz ?_
        exact add_le_of_nonpos_left hy'
      simp [ENNReal.zero_rpow_of_pos hyz, ENNReal.zero_rpow_of_pos hz']
  · rw [ENNReal.rpow_add _ _ hx' hx]

end ENNReal
