/-
Copyright (c) 2026 Rohit Manokaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran
-/
module

public import Mathlib.Probability.Martingale.Upcrossing

@[expose] public section

namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω}
  {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}

@[simp]
lemma hittingBtwn_self [ConditionallyCompletePartialOrderInf ι]
    (f : ι → Ω → β) (s : Set β) (n : ι) (ω : Ω) :
    hittingBtwn f s n n ω = n := by
  rw [hittingBtwn]
  simp only [Set.Icc_self, Set.mem_singleton_iff, exists_eq_left, ite_eq_right_iff]
  intro h
  simp [h]

/-- `hittingBtwn` only depends on the hitting predicate. -/
lemma hittingBtwn_congr {s : Set ℝ}
    (h : ∀ i ω, f i ω ∈ s ↔ g i ω ∈ s) (n m : ℕ) :
    hittingBtwn f s n m = hittingBtwn g s n m := by
  ext
  unfold hittingBtwn
  congr <;> ext <;> simp [h]

/-- Upper crossing times only depend on the position of the process relative to `a` and `b`. -/
lemma upperCrossingTime_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) (n : ℕ) :
    upperCrossingTime a b f N n = upperCrossingTime a b g N n := by
  have hIic' : ∀ i ω, f i ω ∈ Set.Iic a ↔ g i ω ∈ Set.Iic a := hIic
  have hIci' : ∀ i ω, f i ω ∈ Set.Ici b ↔ g i ω ∈ Set.Ici b := hIci
  induction n with
  | zero => rfl
  | succ n ih =>
    ext ω
    rw [upperCrossingTime_succ_eq, upperCrossingTime_succ_eq, lowerCrossingTime,
      lowerCrossingTime, ih, hittingBtwn_congr hIic', hittingBtwn_congr hIci']

/-- Lower crossing times only depend on the position of the process relative to `a` and `b`. -/
lemma lowerCrossingTime_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) (n : ℕ) :
    lowerCrossingTime a b f N n = lowerCrossingTime a b g N n := by
  ext ω
  rw [lowerCrossingTime, lowerCrossingTime, upperCrossingTime_congr hIic hIci,
    hittingBtwn_congr hIic]

lemma upcrossingStrat_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) (n : ℕ) :
    upcrossingStrat a b f N n = upcrossingStrat a b g N n := by
  ext ω
  simp_rw [upcrossingStrat, upperCrossingTime_congr hIic hIci, lowerCrossingTime_congr hIic hIci]

lemma upcrossingsBefore_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) :
    upcrossingsBefore a b f N ω = upcrossingsBefore a b g N ω := by
  simp_rw [upcrossingsBefore, upperCrossingTime_congr hIic hIci]

/-- `upcrossingStrat` takes only the values `0` and `1`. -/
lemma upcrossingStrat_eq_zero_or_one (a b : ℝ) (f : ℕ → Ω → ℝ) (N n : ℕ) (ω : Ω) :
    upcrossingStrat a b f N n ω = 0 ∨ upcrossingStrat a b f N n ω = 1 := by
  classical
  rw [upcrossingStrat, ← Finset.indicator_biUnion_apply]
  · rw [Set.indicator_apply]
    split_ifs <;> simp
  intro i _ j _ hij
  simp only [Set.Ico_disjoint_Ico]
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · rw [min_eq_left (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω ≤ upperCrossingTime a b f N _ ω),
      max_eq_right (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ ≤ lowerCrossingTime _ _ _ _ _ _)]
    exact le_trans upperCrossingTime_le_lowerCrossingTime
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))
  · rw [min_eq_right (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω ≤ upperCrossingTime a b f N _ ω),
      max_eq_left (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ ≤ lowerCrossingTime _ _ _ _ _ _)]
    exact upperCrossingTime_le_lowerCrossingTime.trans
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))

/-- Pathwise upcrossing inequality with correction term: unlike
`MeasureTheory.mul_upcrossingsBefore_le`, this requires no assumption `a ≤ f N ω`, at the price
of the extra term `max (a - f N ω) 0`. -/
lemma mul_upcrossingsBefore_le_sum_add_posPart (hab : a < b) :
    (b - a) * upcrossingsBefore a b f N ω ≤
      (∑ k ∈ Finset.range N, upcrossingStrat a b f N k ω * (f (k + 1) - f k) ω) + (a - f N ω)⁺ := by
  rcases N with _ | M
  · simp [posPart, upcrossingsBefore_zero]
  let g : ℕ → Ω → ℝ := fun k ω' ↦ if k = M + 1 then max (f k ω') a else f k ω'
  have hIic i ω' : g i ω' ≤ a ↔ f i ω' ≤ a := by simp [g]; grind
  have hIci i ω' : b ≤ g i ω' ↔ b ≤ f i ω' := by simp [g]; grind
  have hga : a ≤ g (M + 1) ω := by simp [g]
  have key : (b - a) * upcrossingsBefore a b g (M + 1) ω ≤
      ∑ k ∈ Finset.range (M + 1), upcrossingStrat a b g (M + 1) k ω * (g (k + 1) - g k) ω :=
    mul_upcrossingsBefore_le (f := g) (N := M + 1) (ω := ω) hga hab
  simp_rw [upcrossingsBefore_congr hIic hIci, upcrossingStrat_congr hIic hIci] at key
  refine key.trans ?_
  rw [Finset.sum_range_succ, Finset.sum_range_succ
    (f := fun k ↦ upcrossingStrat a b f (M + 1) k ω * (f (k + 1) - f k) ω)]
  have hsum k (hk : k ∈ Finset.range M) :
      upcrossingStrat a b f (M + 1) k ω * (g (k + 1) - g k) ω
        = upcrossingStrat a b f (M + 1) k ω * (f (k + 1) - f k) ω := by simp [g]; grind
  rw [Finset.sum_congr rfl hsum, add_assoc]
  gcongr
  have hgM : g M = f M := by simp [g]
  have hgM1 : g (M + 1) ω = f (M + 1) ω + (a - f (M + 1) ω)⁺ := by simp [g, posPart]; grind
  rw [Pi.sub_apply, hgM, hgM1]
  have h11 : upcrossingStrat a b f (M + 1) M ω ≤ 1 := upcrossingStrat_le_one
  calc upcrossingStrat a b f (M + 1) M ω * (f (M + 1) ω + (a - f (M + 1) ω)⁺ - f M ω)
  _ = upcrossingStrat a b f (M + 1) M ω * (f (M + 1) - f M) ω
      + upcrossingStrat a b f (M + 1) M ω * (a - f (M + 1) ω)⁺ := by rw [Pi.sub_apply]; ring
  _ ≤ upcrossingStrat a b f (M + 1) M ω * (f (M + 1) - f M) ω + 1 * (a - f (M + 1) ω)⁺ := by
    gcongr
  _ = upcrossingStrat a b f (M + 1) M ω * (f (M + 1) - f M) ω + (a - f (M + 1) ω)⁺ := by ring

/-- Alternations force upcrossings: if there are `m` pairs of (strictly increasing) times below
`N` at which `f` is alternately strictly below `a` and strictly above `b`, then `f` has at least
`m` upcrossings of `[a, b]` before `N`. -/
lemma le_upcrossingsBefore_of_alternating (hab : a < b) {m : ℕ} {c : ℕ → ℕ}
    (hmono : ∀ i, i + 1 < 2 * m → c i < c (i + 1)) (hN : ∀ i < 2 * m, c i < N)
    (ha : ∀ i < m, f (c (2 * i)) ω < a) (hb : ∀ i < m, b < f (c (2 * i + 1)) ω) :
    m ≤ upcrossingsBefore a b f N ω := by
  rcases m with _ | m
  · simp
  have key i : i < m + 1 → i + 1 ≤ upcrossingsBefore a b f (c (2 * i + 1) + 1) ω := by
    induction i with
    | zero =>
      intro h0
      have := upcrossingsBefore_lt_of_exists_upcrossing (f := f) (ω := ω) (N := 0) hab
        (by lia) (ha 0 h0) (hmono 0 (by lia)).le (hb 0 h0)
      lia
    | succ i ih =>
      intro hi
      have h2 := upcrossingsBefore_lt_of_exists_upcrossing (f := f) (ω := ω)
        (N := c (2 * i + 1) + 1) hab (hmono (2 * i + 1) (by lia)) (ha (i + 1) hi)
        (hmono (2 * (i + 1)) (by lia)).le (hb (i + 1) hi)
      lia
  refine (key m (by lia)).trans ?_
  exact upcrossingsBefore_mono (f := f) hab (hN (2 * m + 1) (by lia)) ω

end MeasureTheory
