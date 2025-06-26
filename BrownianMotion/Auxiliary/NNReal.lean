import Mathlib.Data.NNReal.Basic

namespace NNReal

lemma add_sub_two_mul_min_eq_max (s t : ℝ≥0) : s + t - 2 * min s t = max (s - t) (t - s) := by
  wlog hst : s ≤ t
  · convert this t s (le_of_not_ge hst) using 1
    · rw [add_comm, min_comm]
    · rw [max_comm]
  rw [min_eq_left hst, max_eq_right, two_mul, add_tsub_add_eq_tsub_left]
  grw [hst]

variable (n : ℕ) (t : ℝ≥0)

/-- If `t : ℝ≥0` and `n : ℕ`, `step n t` is the smallest integer `k : ℕ` such that
`t ≤ (k + 1) / 2 ^ n`. If `0 < t` we also have `k / 2 ^ n < t`.

This quantity is useful in probability theory, to cut `ℝ≥0` into smaller and smaller pieces,
allowing to approximate stochastic processes by simpler processes. -/
noncomputable def step : ℕ := Nat.ceil (t * 2 ^ n) - 1

lemma step_def : step n t = Nat.ceil (t * 2 ^ n) - 1 := rfl

variable {n}

@[simp]
lemma step_zero : step n 0 = 0 := by simp [step]

@[simp]
lemma step_cast_add_one_div (k : ℕ) : step n ((k + 1) / 2 ^ n) = k := by
  rw [step_def]
  field_simp
  norm_cast
  rw [Nat.ceil_natCast, Nat.add_sub_cancel]

variable {t}

lemma step_add_one (ht : 0 < t) : step n t + 1 = Nat.ceil (t * 2 ^ n) := by
  rw [step_def, tsub_add_cancel_of_le]
  rw [Nat.one_le_ceil_iff]
  simpa

lemma step_add_one' (ht : 0 < t) : (step n t : ℝ≥0) + 1 = Nat.ceil (t * 2 ^ n) := by
  norm_cast
  convert step_add_one ht using 3
  norm_cast

lemma ceil_sub_one_lt (ht : 0 < t) :
    Nat.ceil t - 1 < t := by
  rw [tsub_lt_iff_right]
  · exact Nat.ceil_lt_add_one ht.le
  · norm_cast
    exact Nat.one_le_ceil_iff.2 ht

lemma step_div_lt (ht : 0 < t) : step n t / 2 ^ n < t := by
  rw [step_def]
  push_cast
  exact (div_lt_div_iff_of_pos_right (by simp)).2
    (ceil_sub_one_lt (by simpa)) |>.trans_le (by field_simp)

variable (t) in
lemma le_step_add_one_div : t ≤ (step n t + 1) / 2 ^ n := by
  obtain rfl | ht := eq_zero_or_pos t
  · simp
  nth_rw 1 [← mul_div_cancel_right₀ t (b := 2 ^ n) (by simp),
    div_le_div_iff_of_pos_right (by simp), step_add_one' ht]
  exact Nat.le_ceil _

lemma step_eq_of_lt_of_le {k : ℕ} (h1 : k / 2 ^ n < t) (h2 : t ≤ (k + 1) / 2 ^ n) :
    step n t = k := by
  rw [step_def]
  refine Nat.sub_eq_of_eq_add <| le_antisymm ?_ <| Nat.add_one_le_iff.2 <| Nat.lt_ceil.2 ?_
  · grw [Nat.ceil_le, h2]
    field_simp
  · rwa [← div_lt_iff₀ (by simp)]

end NNReal
