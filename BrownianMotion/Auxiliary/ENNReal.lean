import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Order.CompletePartialOrder

open ENNReal NNReal

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

@[norm_cast]
lemma ENat.toENNReal_iSup {ι : Sort*} (f : ι → ℕ∞) : ⨆ i, f i = ⨆ i, (f i : ℝ≥0∞) := by
  refine eq_of_forall_ge_iff fun c ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact iSup_le fun i ↦ le_trans (ENat.toENNReal_le.2 (le_iSup f i)) h
  · obtain rfl | hc := eq_or_ne c ⊤
    · exact le_top
    lift c to ℝ≥0 using hc
    have (i : ι) : f i ≤ Nat.floor c := by
      have := (le_iSup _ i).trans h
      have h' : f i ≠ ⊤ := by
        rw [← ENat.toENNReal_ne_top]
        exact this.trans_lt ENNReal.coe_lt_top |>.ne
      lift f i to ℕ using h' with k
      norm_cast
      change ((k : ℝ≥0) : ℝ≥0∞) ≤ c at this
      exact Nat.le_floor_iff (zero_le _) |>.2 <| ENNReal.coe_le_coe.1 this
    calc
    (↑(⨆ i, f i) : ℝ≥0∞) ≤ Nat.floor c := by
      change (↑(⨆ i, f i) : ℝ≥0∞) ≤ ((Nat.floor c : ENat) : ℝ≥0∞)
      exact ENat.toENNReal_le.2 (iSup_le this)
    _ ≤ c := by norm_cast; exact Nat.floor_le (zero_le _)

@[gcongr]
alias ⟨_, ENat.toENNReal_le'⟩ := ENat.toENNReal_le
