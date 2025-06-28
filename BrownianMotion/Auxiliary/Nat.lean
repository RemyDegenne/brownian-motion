import Mathlib.Algebra.Order.Floor.Semiring

lemma Nat.self_sub_floor_lt_one {R : Type*} [Ring R] [LinearOrder R] [FloorSemiring R]
    [IsStrictOrderedRing R] (x : R) : x - ⌊x⌋₊ < 1 := by
  rw [sub_lt_iff_lt_add']
  exact Nat.lt_floor_add_one _

lemma Nat.zero_le_self_sub_floor {R : Type*} [Ring R] [LinearOrder R] [FloorSemiring R]
    [IsStrictOrderedRing R] {x : R} (hx : 0 ≤ x) : 0 ≤ x - ⌊x⌋₊ := by
  rw [sub_nonneg]
  exact Nat.floor_le hx

lemma pow_two_mul_abs {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (n : ℕ) (a : α) :
    |a| ^ (2 * n) = a ^ (2 * n) :=
  Even.pow_abs ⟨n, two_mul n⟩ a
