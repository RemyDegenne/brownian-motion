import Mathlib.LinearAlgebra.Dimension.Finite

theorem div_left_injective₀ {G₀ : Type*} [CommGroupWithZero G₀] {c : G₀} (hc : c ≠ 0) :
    Function.Injective fun x ↦ x / c := by
  intro x y hxy
  apply mul_eq_mul_of_div_eq_div x y hc hc at hxy
  exact mul_left_injective₀ hc hxy

attribute [simp] Module.finrank_zero_of_subsingleton

@[simp]
lemma Module.finrank_ne_zero {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [StrongRankCondition R] [Module.Finite R M] [IsDomain R] [IsTorsionFree R M]
    [h : Nontrivial M] :
    finrank R M ≠ 0 := finrank_pos.ne'

open Finset

/-- Telescopic sum when summing over `Fin`. -/
lemma Fin.sum_Iic_sub {E : Type*} [AddCommGroup E] {n : ℕ} (a : Fin n) (f : Fin (n + 1) → E) :
    ∑ i ∈ Iic a, (f i.succ - f i.castSucc) = f a.succ - f 0 := by
  let g : Fin n → E := fun i ↦ if i ∈ Iic a then f i.succ - f i.castSucc else 0
  let h : ℕ → E := fun i ↦ if hi : i < n then g ⟨i, hi⟩ else 0
  calc
  _ = ∑ i, g i := by
    rw [Finset.sum_ite_mem, univ_inter]
  _ = ∑ i : Fin n, h i := by
    congr with i
    simp_rw [h, dif_pos i.2]
  _ = ∑ i ∈ range a.succ, h i := by
    rw [Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr_of_eq_on_inter ?_ (by grind) (by grind)
    simp only [mem_range, Fin.val_succ, not_lt]
    intro i hi1 hi2
    simp_rw [h, dif_pos hi1, g]
    rw [if_neg (by simpa)]
  _ = ∑ i ∈ range a.succ, (f (Fin.ofNat (n + 1) (i + 1)) - f (Fin.ofNat (n + 1) i)) := by
    apply Finset.sum_congr rfl
    simp only [Fin.val_succ, mem_range, mem_Iic, Fin.succ_mk, Fin.castSucc_mk, Fin.ofNat_eq_cast, h,
      g]
    intro i hi
    rw [dif_pos (by omega), if_pos]
    · congr
      · rw [Nat.mod_eq_of_lt]
        grind
      · rw [Nat.mod_eq_of_lt]
        grind
    rw [Fin.le_def]
    grind
  _ = f a.succ - f 0 := by
    rw [Finset.sum_range_sub (fun i ↦ f (Fin.ofNat (n + 1) i))]
    congr
    ext
    simp
