module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

-- TODO: remove if https://github.com/leanprover-community/mathlib4/pull/40909 has merged.
lemma Set.indicator_apply_apply {ι Ω M : Type*} [Zero M] (s : Set ι) (f : ι → Ω → M) (i : ι)
    (ω : Ω) :
    s.indicator f i ω = s.indicator (fun j ↦ f j ω) i := by
  by_cases h : i ∈ s <;> simp [h]

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
