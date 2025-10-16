import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Order.CompletePartialOrder

open ENNReal NNReal

namespace ENNReal

lemma sum_geometric_two_le (n : ℕ) : ∑ i ∈ Finset.range n, ((1 : ENNReal) / 2) ^ i ≤ 2 := by
  rw [← ENNReal.toReal_le_toReal (by simp) (by simp), toReal_ofNat, toReal_sum (by simp)]
  simpa [-one_div] using _root_.sum_geometric_two_le _

lemma ofReal_one_div {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (1 / x) = 1 / (ENNReal.ofReal x) := by
  rwa [ENNReal.ofReal_div_of_pos, ofReal_one]

lemma le_one_div_iff {x y : ℝ≥0∞} : x ≤ 1 / y ↔ y ≤ 1 / x := by
  rw [ENNReal.le_div_iff_mul_le, ENNReal.le_div_iff_mul_le, mul_comm]
  all_goals simp

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
