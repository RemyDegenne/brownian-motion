/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Wojciech Czernous
-/
import BrownianMotion.Auxiliary.Martingale
import BrownianMotion.StochasticIntegral.HittingTime
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Data.Finset.Sort

/-! # Doob's upcrossing inequality on NNRat

-/

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-! The original definitions, valid for InfSet (hence not for NNRat), are:

noncomputable def upperCrossingTime [Preorder ι] [OrderBot ι] [InfSet ι] (a b : ℝ) (f : ι → Ω → ℝ)
    (N : ι) : ℕ → Ω → ι
  | 0 => ⊥
  | n + 1 => fun ω =>
    hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f (upperCrossingTime a b f N n ω) N ω) N ω

noncomputable def upcrossingsBefore [Preorder ι] [OrderBot ι] [InfSet ι] (a b : ℝ) (f : ι → Ω → ℝ)
    (N : ι) (ω : Ω) : ℕ :=
  sSup {n | upperCrossingTime a b f N n ω < N}

-/

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} --[LinearOrder ι]

structure UpcrossingData [PartialOrder ι] (a b : ℝ) (f : ι → Ω → ℝ) (n : ℕ) (ω : Ω) where
  hab : a < b
  t : ℕ → ι
  mono: Monotone t
  ft_le_a  : ∀ i : ℕ, i < 2 * n → Even i → f (t i) ω ≤ a
  ft_ge_b  : ∀ i : ℕ, i < 2 * n → Odd i → f (t i) ω ≥ b

/-! We already have (proved in Mathlib.Probability.Process.HittingTime):
theorem hittingBtwn_mem_set_of_hittingBtwn_lt [WellFoundedLT ι] {m : ι}
    (hl : hittingBtwn u s n m ω < m) :
    u (hittingBtwn u s n m ω) ω ∈ s
theorem hittingBtwn_le_of_mem {m : ι} (hin : n ≤ i) (him : i ≤ m) (his : u i ω ∈ s) :
    hittingBtwn u s n m ω ≤ i
-/

namespace UpcrossingData

variable {a b : ℝ} {f : ι → Ω → ℝ} {ω : Ω}

lemma ne_of_ab {x y : ι} (hab : a < b) (ha : f x ω ≤ a) (hb : f y ω ≥ b) : x ≠ y := by
  intro hEq
  exact (not_le_of_gt hab) (le_trans hb (by simpa [hEq] using ha))

variable {n : ℕ} [PartialOrder ι]
variable (h : UpcrossingData a b f n ω)

lemma ti_ne_ti1 {i} (hi1n : i + 1 < 2 * n) : h.t i ≠ h.t (i + 1) := by
  have hi : i < 2*n := Nat.lt_of_succ_lt hi1n
  by_cases hi_even : Even i
  · exact ne_of_ab h.hab (h.ft_le_a i hi hi_even) <| h.ft_ge_b (i + 1) hi1n (Even.add_one hi_even)
  · have hi_odd : Odd i := Nat.not_even_iff_odd.mp hi_even
    exact (ne_of_ab h.hab (h.ft_le_a (i + 1) hi1n (by grind)) (h.ft_ge_b i hi hi_odd)).symm

lemma t_strict_mono {i j} (hij : i < j) (hj : j < 2 * n) : h.t i < h.t j := by
  have hi1n : i + 1 < 2 * n := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hij) hj
  have hti : h.t i < h.t (i + 1) := lt_of_le_of_ne (h.mono (Nat.le_succ i)) (h.ti_ne_ti1 hi1n)
  exact lt_of_lt_of_le hti (h.mono (Nat.succ_le_of_lt hij))

def toShorter {a b : ℝ} {f : ι → Ω → ℝ} {n : ℕ} {ω : Ω} (h : UpcrossingData a b f (n + 1) ω) :
    UpcrossingData a b f n ω :=
{
  hab := h.hab,
  t := h.t,
  mono := h.mono,
  ft_le_a := by
    intro i hi heven
    exact h.ft_le_a i (by grind) heven,
  ft_ge_b := by
    intro i hi hodd
    exact h.ft_ge_b i (by grind) hodd
}

def extend {a b : ℝ} {f : ι → Ω → ℝ} {n : ℕ} {ω : Ω}
  (h : UpcrossingData a b f n ω)
  (s t : ι)
  (hus : h.t (2 * n - 1) ≤ s)
  (hst : s ≤ t)
  (hfs : f s ω ∈ Set.Iic a)
  (hft : f t ω ∈ Set.Ici b) :
    UpcrossingData a b f (n + 1) ω :=
{
  hab := h.hab,
  t := fun i => if i < 2 * n then h.t i else if i = 2 * n then s else t,
  mono := by
    intro i j hij
    by_cases hi_n : i < 2 * n
    · have hi_le_2n1 : i ≤ 2 * n - 1 := by grind
      have hti_le_u : h.t i ≤ h.t (2 * n - 1) := h.mono hi_le_2n1
      by_cases hj_n : j < 2 * n
      · simp only [hi_n, hj_n, if_true, if_true]
        exact h.mono hij
      · by_cases hj_eq : j = 2 * n
        · grind
        · grind
    · grind,
  ft_le_a := by
    intro i hi heven
    by_cases hi_n : i < 2 * n
    · simp only [hi_n, if_true]
      exact h.ft_le_a i (by grind) heven
    · simp only [hi_n, if_false]
      grind
  ft_ge_b := by
    intro i hi hodd
    by_cases hi_n : i < 2 * n
    · simp only [hi_n, if_true]
      exact h.ft_ge_b i (by grind) hodd
    · simp only [hi_n, if_false]
      grind
}

lemma extend_s {a b : ℝ} {f : ι → Ω → ℝ} {n : ℕ} {ω : Ω}
  (h : UpcrossingData a b f n ω)
  (s t : ι)
  (hus : h.t (2 * n - 1) ≤ s)
  (hst : s ≤ t)
  (hfs : f s ω ∈ Set.Iic a)
  (hft : f t ω ∈ Set.Ici b) :
    (h.extend s t hus hst hfs hft).t (2 * n) = s := by
set h2 := h.extend s t hus hst hfs hft with hh2
have ht : h2.t (2 * n) = s := by
  simp only [h2, UpcrossingData.extend]; simp
exact ht

lemma extend_t {a b : ℝ} {f : ι → Ω → ℝ} {n : ℕ} {ω : Ω}
  (h : UpcrossingData a b f n ω)
  (s t : ι)
  (hus : h.t (2 * n - 1) ≤ s)
  (hst : s ≤ t)
  (hfs : f s ω ∈ Set.Iic a)
  (hft : f t ω ∈ Set.Ici b) :
    (h.extend s t hus hst hfs hft).t (2 * n + 1) = t := by
set h2 := h.extend s t hus hst hfs hft with hh2
have ht : h2.t (2 * n + 1) = t := by
  simp only [h2, UpcrossingData.extend]; simp
exact ht

end UpcrossingData

private lemma upperCrossingTime_le_of_UpcrossingData' [ConditionallyCompleteLinearOrderBot ι]
    [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (u' s t N : ι) (ω : Ω) :
    u' ≤ s → s ≤ t → t ≤ N → f s ω ∈ Set.Iic a → f t ω ∈ Set.Ici b →
    hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f u' N ω) N ω ≤ t := by
  intro hu's hst htN hfs hft
  refine hittingBtwn_le_of_mem ?hin htN hft
  simp only [lowerCrossingTimeAux]
  refine le_trans ?hle_s hst
  exact hittingBtwn_le_of_mem hu's (le_trans hst htN) hfs

lemma upperCrossingTime_le_of_UpcrossingData [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) :
  ∀ n (hseq : UpcrossingData a b f (n+1) ω), hseq.t (2 * n + 1) ≤ N →
    upperCrossingTime a b f N (n+1) ω ≤ hseq.t (2 * n + 1) := by
  simp only [upperCrossingTime]
  -- motive depends on n and hseq
  refine Nat.rec (motive := fun n => ∀ hseq : UpcrossingData a b f (n+1) ω, hseq.t (2 * n + 1) ≤ N →
    upperCrossingTime a b f N (n+1) ω ≤ hseq.t (2 * n + 1)) ?base ?step
  · -- n = 0 case; hseq : UpcrossingData a b f 1 ω
    intro hseq h_t1_le_N
    simp only [upperCrossingTime];
    -- have h := Nat.zero_lt_succ 0
    exact upperCrossingTime_le_of_UpcrossingData' a b f ⊥ (hseq.t 0) (hseq.t 1) N ω
      bot_le (hseq.mono (by simp)) h_t1_le_N
      (hseq.ft_le_a 0 (by simp) Even.zero)
      (hseq.ft_ge_b 1 (by simp) (by grind))
  · -- succ case
    intro n ih hseq2 htN
    set hseq1 := hseq2.toShorter with hseq_prev_def
    set u' := upperCrossingTime a b f N (n + 1) ω with hu'
    set t' := hseq2.t (2 * n + 1) with ht'
    set s  := hseq2.t (2 * n + 2) with hs
    set t  := hseq2.t (2 * n + 3) with ht
    have ht's  : t' ≤ s := hseq2.mono (Nat.le_succ (2 * n + 1))
    have hst   : s  ≤ t := hseq2.mono (Nat.le_succ (2 * n + 2))
    have hu't' : u' ≤ t' := ih hseq1 <| le_trans ht's (le_trans hst htN)
    exact upperCrossingTime_le_of_UpcrossingData' a b f u' s t N ω
      (le_trans hu't' ht's) hst htN
      (hseq2.ft_le_a (2 * n + 2) (by grind) (by grind))
      (hseq2.ft_ge_b (2 * n + 3) (by grind) (by grind))

/-! The `ltUpcrossingsBefore a b f N n ω` is shortened as `L n`. -/
noncomputable def ltUpcrossingsBefore [LinearOrder ι] [OrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) : Prop :=
  if N ≤ ⊥ then False else
    if n = 0 then True else
      ∃ seq : UpcrossingData a b f n ω, seq.t (2 * n - 1) < N

/-! The `upcrossingsBeforeUpperCrossingTime a b f N n ω` is shortened as `Q n`. -/
noncomputable def upcrossingsBeforeUpperCrossingTime [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) : Prop :=
  if N ≤ ⊥ then False else
    if n = 0 then True else
      ∃ seq : UpcrossingData a b f n ω, seq.t (2 * n - 1) ≤ upperCrossingTime a b f N n ω

/-! The `upperCrossingTimeLT a b f N n ω` is shortened as `P n`. -/
noncomputable def upperCrossingTimeLT [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) : Prop :=
  if N ≤ ⊥ then False else
    if n = 0 then True else
      upperCrossingTime a b f N n ω < N

/-!
  The current aim is to establish ∀ n, P n ↔ L n.
-/

/-! An auxiliary equivalence lemma. -/
lemma upperCrossingTimeLT_iff_upperCrossingTime_lt
  [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) :
    upperCrossingTimeLT a b f N n ω ↔ upperCrossingTime a b f N n ω < N := by
  by_cases hN : N ≤ ⊥
  · have : upperCrossingTime a b f N n ω ≥ ⊥ := bot_le
    simp only [upperCrossingTimeLT, hN, if_true]
    have : upperCrossingTime a b f N n ω ≥ N := ge_trans (this) (by simp [hN])
    grind
  · simp only [upperCrossingTimeLT, hN, if_false]; push_neg at hN
    by_cases hnzero : n = 0
    · simp only [hnzero, if_true, upperCrossingTime]; simp_all
    · simp only [hnzero]; grind

/-! Clearly, P n → Q n → L n. -/
lemma ltUpcrossingsBefore_of_upcrossingsBeforeUpperCrossingTime_of_upperCrossingTimeLT
  [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω)
  (h : upperCrossingTimeLT a b f N n ω) :
    upcrossingsBeforeUpperCrossingTime a b f N n ω →
    ltUpcrossingsBefore a b f N n ω := by
  by_cases hN : N ≤ ⊥
  · simp only [ltUpcrossingsBefore, upcrossingsBeforeUpperCrossingTime, hN, if_true]; exact id
  · simp only [ltUpcrossingsBefore, upcrossingsBeforeUpperCrossingTime, hN, if_false]
    by_cases hnzero : n = 0
    · simp only [hnzero]; exact id
    · simp only [hnzero]; intro ⟨hseq, ht_le⟩
      use hseq
      simp only [upperCrossingTimeLT] at h
      refine lt_of_le_of_lt ht_le ?_
      grind

/-! The equivalence P n ↔ L n, in the case N = ⊥. -/
lemma upperCrossingTime_lt_bot_iff_ltUpcrossingsBefore [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hN : N ≤ ⊥) :
    ltUpcrossingsBefore a b f N n ω ↔ upperCrossingTimeLT a b f N n ω := by
  simp only [ltUpcrossingsBefore, hN, if_true]
  simp only [upperCrossingTimeLT, hN, if_true]

/-! The left implication: ∀ n, L n → P n. -/
lemma upperCrossingTime_lt_of_ltUpcrossingsBefore [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) :
    ltUpcrossingsBefore a b f N n ω → upperCrossingTimeLT a b f N n ω := by
  by_cases h : N ≤ ⊥
  · exact (upperCrossingTime_lt_bot_iff_ltUpcrossingsBefore a b f N n ω h).mp
  · simp only [ltUpcrossingsBefore, h, if_false]
    rw [upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N n ω]
    by_cases hnzero : n = 0
    · -- n = 0 case
      subst hnzero; simp; grind
    · -- n ≥ 1 case
      simp only [if_neg hnzero]
      rintro ⟨hseq, ht_lt_N⟩
      refine lt_of_le_of_lt ?_ ht_lt_N
      cases n with
      | zero => contradiction
      | succ m =>
          have ht_le_N : hseq.t (2 * m + 1) ≤ N := le_of_lt ht_lt_N
          simpa using upperCrossingTime_le_of_UpcrossingData a b f N ω m hseq ht_le_N

private lemma nondegenerate_of_hittingBtwn_lt [ConditionallyCompleteLinearOrderBot ι]
    [WellFoundedLT ι] (u : ι → Ω → ℝ) (s : Set ℝ) (n m : ι) (ω : Ω)
    (hl : hittingBtwn u s n m ω < m) :
    n < m := by
  have h := (hittingBtwn_lt_iff (i:=m) (le_refl m)).mp hl
  grind

/-! P n gives a pair of witnesses, useful for establishing Q n. -/
lemma upcrossingData_of_upperCrossingTime_lt [ConditionallyCompleteLinearOrderBot ι]
    [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (m N : ι) (ω : Ω) :
    hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f m N ω) N ω < N →
    ∃ s t : ι, m ≤ s ∧ s ≤ t
    ∧ t ≤ hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f m N ω) N ω
    ∧ f s ω ∈ Set.Iic a ∧ f t ω ∈ Set.Ici b := by
  intro ht_lt_N
  set s := lowerCrossingTimeAux a f m N ω with hs
  set t := hittingBtwn f (Set.Ici b) s N ω with ht
  use s, t
  have hft : f t ω ∈ Set.Ici b := hittingBtwn_mem_set_of_hittingBtwn_lt ht_lt_N
  have hsN : s < N := nondegenerate_of_hittingBtwn_lt f (Set.Ici b) s N ω ht_lt_N
  simp only [lowerCrossingTimeAux] at hs
  have hfs : f s ω ∈ Set.Iic a := hittingBtwn_mem_set_of_hittingBtwn_lt hsN
  have hms : m ≤ s :=
    le_hittingBtwn (le_of_lt <| nondegenerate_of_hittingBtwn_lt f (Set.Iic a) m N ω hsN) ω
  have hsltt : s ≤ t := le_hittingBtwn (le_of_lt hsN) ω
  grind

/-! P 1 → Q 1, in the case N ≠ ⊥. -/
lemma upcrossingData_of_first_upperCrossingTime_lt [ConditionallyCompleteLinearOrderBot ι]
    [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) (hab : a < b) (hN : ¬ N ≤ ⊥) :
    upperCrossingTimeLT a b f N 1 ω → upcrossingsBeforeUpperCrossingTime a b f N 1 ω := by
    -- ∃ hseq : UpcrossingData a b f 1 ω, hseq.t 1 ≤ upperCrossingTime a b f N 1 ω := by
  intro hup
  set m := upperCrossingTime a b f N 0 ω with hm
  have hm_bot : m = ⊥ := rfl
  rw [upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N 1 ω] at hup
  have ht_lt_N : hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f m N ω) N ω < N :=
    by simpa [upperCrossingTime] using hup
  rcases upcrossingData_of_upperCrossingTime_lt a b f m N ω ht_lt_N with
    ⟨s, t, hm_s, hs_t, ht_u, hfs, hft⟩
  let hseq : UpcrossingData a b f 1 ω :=
    {
      hab := hab,
      t := fun i => if i = 0 then s else t,
      mono := by
        intro i j hij
        by_cases hi0 : i = 0
        · grind
        · grind,
      ft_le_a := by grind,
      ft_ge_b := by grind
    }
  simp only [upcrossingsBeforeUpperCrossingTime, hN, if_false]
  use hseq
  have ht1 : hseq.t 1 = t := by simp only [hseq]; simp
  simp only [ht1];
  exact ht_u

/-! P (n+1) → Q n → Q (n+1), in the case N ≠ ⊥. -/
lemma upcrossingData_extend_of_upperCrossingTime_lt [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) (hN : ¬ N ≤ ⊥) :
  ∀ n ≥ 1, (upperCrossingTimeLT a b f N (n+1) ω →
    upcrossingsBeforeUpperCrossingTime a b f N n ω →
      upcrossingsBeforeUpperCrossingTime a b f N (n+1) ω) := by
  intro n hn hup hseq
  simp only [upcrossingsBeforeUpperCrossingTime, hN, if_false] at hseq
  have : n ≠ 0 := by linarith
  simp only [this] at hseq
  obtain ⟨hseq, htu'⟩ := hseq
  set u' := upperCrossingTime a b f N n ω with hu'
  set s := hseq.t (2 * n - 2) with hs
  set t := hseq.t (2 * n - 1) with ht
  set u := upperCrossingTime a b f N (n + 1) ω with hu
  rw [upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N (n+1) ω] at hup
  have hu_lt_N : hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f u' N ω) N ω < N :=
    by simpa [upperCrossingTime] using hup
  rcases upcrossingData_of_upperCrossingTime_lt a b f u' N ω hu_lt_N with
    ⟨s', t', hu's', hs't', ht'u, hfs', hft'⟩
  let hseq' : UpcrossingData a b f (n + 1) ω :=
    hseq.extend s' t' (le_trans htu' hu's') hs't' hfs' hft'
  simp only [upcrossingsBeforeUpperCrossingTime, hN, if_false]
  use hseq'
  have ht2n1 : hseq'.t (2 * n + 1) = t' := by
    simp only [hseq', UpcrossingData.extend_t]
  have ht2n1 : hseq'.t (2 * (n + 1) - 1) = t' := by grind
  simp only [ht2n1];
  exact ht'u




/-!
lemma ltUpcrossingsBefore_of_upperCrossingTime_lt_all [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω)
  (hab : a < b) (hNbot : ¬ N ≤ ⊥) :
  ∀ n, upperCrossingTime a b f N n ω < N → ltUpcrossingsBefore a b f N n ω := by
  refine Nat.rec ?base ?step
  · -- n = 0
    intro hup; simp [ltUpcrossingsBefore, hNbot]
  · -- step n → n+1
    intro n ih hup
    cases n with
    | zero =>
        -- n+1 = 1 : use existing lemma
        obtain ⟨hseq, ht1_le⟩ := upcrossingData_of_first_upperCrossingTime_lt a b f N ω hab hup
        simp only [ltUpcrossingsBefore]; simp_all
        use hseq
        exact lt_of_le_of_lt ht1_le hup
    | succ k =>
        -- n+1 = k.succ.succ ≥ 2
        -- get all earlier upperCrossingTimes < N by monotonicity
        have hup_le : ∀ m ≤ k+1, upperCrossingTime a b f N (m+1) ω < N :=
          fun m hm => lt_of_le_of_lt (upperCrossingTime_mono (Nat.succ_le_succ hm)) hup
        -- base upcrossing data at index 1
        obtain ⟨hseq1, ht1_le⟩ :=
          upcrossingData_of_first_upperCrossingTime_lt a b f N ω hab (hup_le 0 (by linarith))
        -- iterate extend from 1 to k+1 using your extend lemma
        have hseq_chain :
          ∀ i (hi : i ≥ 1) (hi_le : i ≤ k+1),
            ∃ hseq : UpcrossingData a b f (i+1) ω,
              hseq.t (2*i+1) ≤ upperCrossingTime a b f N (i+1) ω := by
          refine Nat.rec ?base2 ?step2
          · intro hi hi_le; exact ⟨hseq1, by simpa using ht1_le⟩
          · intro i IH hi hi_le
            have hi_pos : i+1 ≥ 1 := by linarith
            have hi_ge_1 : i ≥ 1 := by linarith
            obtain ⟨hseqi, hti_le⟩ := IH hi (by nlinarith)
            have hup_next := hup_le (i+1) (by nlinarith)
            rcases upcrossingData_extend_of_upperCrossingTime_lt a b f N ω
              (n:=i+1) hi_pos hup_next hseqi hti_le with ⟨hseq', ht'⟩
            exact ⟨hseq', ht'⟩
        -- pick i = k+1 to get the final sequence
        rcases hseq_chain (k+1) (by nlinarith) (by nlinarith) with ⟨hseq_fin, ht_fin⟩
        refine ?goal_for_step -- supply ⟨hseq_fin, lt_of_le_of_lt ht_fin hup⟩ under the if-branch
-/
