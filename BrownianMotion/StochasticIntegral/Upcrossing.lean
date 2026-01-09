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

def size [PartialOrder ι] {n : ℕ} (_h : UpcrossingData a b f n ω) : ℕ := 2 * n

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

lemma t_strict_mono' {i j} (hij : i < j) (hj : j < 2 * n) : h.t i < h.t j := by
  have hi1n : i + 1 < 2 * n := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hij) hj
  have hti : h.t i < h.t (i + 1) := lt_of_le_of_ne (h.mono (Nat.le_succ i)) (h.ti_ne_ti1 hi1n)
  exact lt_of_lt_of_le hti (h.mono (Nat.succ_le_of_lt hij))

def t_on_Fin2n : Fin (2 * n) → ι := fun x => h.t x.toNat

lemma t_strict_mono_on_Fin2n : StrictMono h.t_on_Fin2n := by
  intro x y hxy
  exact h.t_strict_mono' hxy y.isLt

lemma index_set_card_ge_of_upcrossingData {n : ℕ} [Fintype ι] (h : UpcrossingData a b f n ω) :
    Fintype.card ι ≥ 2 * n := by
  have this : Function.Injective h.t_on_Fin2n := h.t_strict_mono_on_Fin2n.injective
  calc
    Fintype.card ι ≥ Fintype.card (Fin (2 * n)) :=
      Fintype.card_le_of_injective h.t_on_Fin2n this
    _ = 2 * n := Fintype.card_fin _

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
    (a b : ℝ) (f : ι → Ω → ℝ) (u' s t N : ι) (ω : Ω) :
    u' ≤ s → s ≤ t → t ≤ N → f s ω ∈ Set.Iic a → f t ω ∈ Set.Ici b →
    hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f u' N ω) N ω ≤ t := by
  intro hu's hst htN hfs hft
  refine hittingBtwn_le_of_mem ?hin htN hft
  simp only [lowerCrossingTimeAux]
  refine le_trans ?hle_s hst
  exact hittingBtwn_le_of_mem hu's (le_trans hst htN) hfs

lemma upperCrossingTime_le_of_UpcrossingData [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) :
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

/-- The number of - alternatively defined - upcrossings (strictly) before time `N`. -/
noncomputable def upcrossingsBefore' [LinearOrder ι] [OrderBot ι] (a b : ℝ) (f : ι → Ω → ℝ)
    (N : ι) (ω : Ω) : ℕ :=
  sSup {n | ltUpcrossingsBefore a b f N n ω}

section UpperCrossingTimeEquivalence

/-! ltUpcrossingsBefore a b f N n ω ↔ upperCrossingTime a b f N n ω < N -/

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

/-! The equivalence P n ↔ L n, in the case N = ⊥. -/
lemma upperCrossingTimeLT_bot_iff_ltUpcrossingsBefore [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hN : N ≤ ⊥) :
    upperCrossingTimeLT a b f N n ω ↔ ltUpcrossingsBefore a b f N n ω := by
  simp only [ltUpcrossingsBefore, hN, if_true]
  simp only [upperCrossingTimeLT, hN, if_true]

/-! The left implication: ∀ n, L n → P n, in the case N ≠ ⊥ -/
lemma upperCrossingTimeLT_of_ltUpcrossingsBefore [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (h : ¬ N ≤ ⊥) :
    ltUpcrossingsBefore a b f N n ω → upperCrossingTimeLT a b f N n ω := by
  simp only [ltUpcrossingsBefore, h, if_false]
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

/-!
  It remains to prove the right implication: ∀ n, P n → L n, in the case N ≠ ⊥.
-/

/-! Clearly, P n → Q n → L n, in the case N ≠ ⊥. -/
lemma ltUpcrossingsBefore_of_upcrossingsBeforeUpperCrossingTime_of_upperCrossingTimeLT
  [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hN : ¬ N ≤ ⊥) :
  upperCrossingTimeLT a b f N n ω →
    upcrossingsBeforeUpperCrossingTime a b f N n ω →
      ltUpcrossingsBefore a b f N n ω := by
  simp only [ltUpcrossingsBefore, upcrossingsBeforeUpperCrossingTime, hN, if_false]
  by_cases hnzero : n = 0
  · simp only [hnzero]
    grind
  · simp only [hnzero]
    intro h ⟨hseq, ht_le⟩
    use hseq
    simp only [upperCrossingTimeLT] at h
    refine lt_of_le_of_lt ht_le ?_
    grind

private lemma nondegenerate_of_hittingBtwn_lt [ConditionallyCompleteLinearOrderBot ι]
    [WellFoundedLT ι] (u : ι → Ω → ℝ) (s : Set ℝ) (n m : ι) (ω : Ω)
    (hl : hittingBtwn u s n m ω < m) :
    n < m := by
  have h := (hittingBtwn_lt_iff (i:=m) (le_refl m)).mp hl
  grind

/-! P n gives a pair of witnesses, useful for establishing Q n. -/
lemma upcrossingData_of_upperCrossingTimeLT [ConditionallyCompleteLinearOrderBot ι]
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
lemma upcrossingData_of_first_upperCrossingTimeLT [ConditionallyCompleteLinearOrderBot ι]
    [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) (hab : a < b) (hN : ¬ N ≤ ⊥) :
    upperCrossingTimeLT a b f N 1 ω → upcrossingsBeforeUpperCrossingTime a b f N 1 ω := by
  intro hup
  set m := upperCrossingTime a b f N 0 ω with hm
  have hm_bot : m = ⊥ := rfl
  rw [upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N 1 ω] at hup
  have ht_lt_N : hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f m N ω) N ω < N :=
    by simpa [upperCrossingTime] using hup
  rcases upcrossingData_of_upperCrossingTimeLT a b f m N ω ht_lt_N with
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
lemma upcrossingData_extend_of_upperCrossingTimeLT [ConditionallyCompleteLinearOrderBot ι]
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
  rcases upcrossingData_of_upperCrossingTimeLT a b f u' N ω hu_lt_N with
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

/-! P (n+1) → P n. -/
lemma upperCrossingTimeLT_of_upperCrossingTimeLT [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) :
  upperCrossingTimeLT a b f N (n+1) ω → upperCrossingTimeLT a b f N n ω := by
  intro hup
  rw [upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N (n+1) ω] at hup
  rw [upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N n ω]
  refine lt_of_le_of_lt ?_ hup
  exact upperCrossingTime_mono (Nat.le_succ n)

/-! ∀ n ≥ 1, P n → Q n, in the case N ≠ ⊥. -/
lemma upcrossingsBeforeUpperCrossingTime_of_upperCrossingTimeLT_all
  [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω)
  (hab : a < b) (hn : n ≥ 1) (hNbot : ¬ N ≤ ⊥) :
    upperCrossingTimeLT a b f N n ω → upcrossingsBeforeUpperCrossingTime a b f N n ω := by
  induction n with
  | zero =>
      intro h; linarith
  | succ n ih =>
      intro hup
      by_cases hn1 : n = 0
      · -- (n+1) = 1 case
        subst hn1
        exact upcrossingData_of_first_upperCrossingTimeLT a b f N ω hab hNbot hup
      · -- (n+1) ≥ 2 case
        have hn1 : n ≥ 1 := by grind
        -- have hn_succ : n + 1 ≥ 1 := by linarith
        simp only [hn1] at ih; simp at ih
        -- ih : P n → Q n
        -- hup : P (n+1); let's deduce P n
        have hPn := upperCrossingTimeLT_of_upperCrossingTimeLT a b f N n ω hup
        refine upcrossingData_extend_of_upperCrossingTimeLT a b f N ω hNbot n hn1 hup ?_
        grind

/-! The right implication: ∀ n, P n → L n, in the case N ≠ ⊥. -/
lemma ltUpcrossingsBefore_of_upperCrossingTimeLT [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b) (hN : ¬ N ≤ ⊥) :
    upperCrossingTimeLT a b f N n ω → ltUpcrossingsBefore a b f N n ω := by
  by_cases hnzero : n = 0
  · -- n = 0 case
    simp only [ltUpcrossingsBefore, hN]
    simp only [hnzero, if_true]; grind
  · -- n ≥ 1 case
    intro hup
    refine ltUpcrossingsBefore_of_upcrossingsBeforeUpperCrossingTime_of_upperCrossingTimeLT
      a b f N n ω hN hup ?_
    exact upcrossingsBeforeUpperCrossingTime_of_upperCrossingTimeLT_all
      a b f N n ω hab (by grind) (by grind) hup

/-! Finally, the equivalence ∀ n, P n ↔ L n. -/
theorem upperCrossingTimeLT_iff_ltUpcrossingsBefore [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b) :
    upperCrossingTimeLT a b f N n ω ↔ ltUpcrossingsBefore a b f N n ω := by
  by_cases hN : N ≤ ⊥
  · exact upperCrossingTimeLT_bot_iff_ltUpcrossingsBefore a b f N n ω hN
  · constructor
    · exact ltUpcrossingsBefore_of_upperCrossingTimeLT a b f N n ω hab hN
    · exact upperCrossingTimeLT_of_ltUpcrossingsBefore a b f N n ω hN

/-! Auxiliary lemma. -/
lemma upperCrossingTime_lt_iff_ltUpcrossingsBefore [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b) :
    upperCrossingTime a b f N n ω < N ↔ ltUpcrossingsBefore a b f N n ω := by
  rw [← upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N n ω]
  exact upperCrossingTimeLT_iff_ltUpcrossingsBefore a b f N n ω hab

/-! noncomputable def ltUpcrossingsBefore [LinearOrder ι] [OrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) : Prop :=
  if N ≤ ⊥ then False else
    if n = 0 then True else
      ∃ seq : UpcrossingData a b f n ω, seq.t (2 * n - 1) < N
-/

/-! noncomputable def upcrossingsBefore [Preorder ι] [OrderBot ι] [InfSet ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) : ℕ :=
    sSup {n | upperCrossingTime a b f N n ω < N}
-/

lemma upcrossingsBefore'_zero_of_N_bot [LinearOrder ι] [OrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) (hN : N ≤ ⊥) :
    upcrossingsBefore' a b f N ω = 0 := by
  simp only [upcrossingsBefore', ltUpcrossingsBefore, hN, if_true]
  simp

/-! The two definitions of upcrossingsBefore are equivalent. -/
theorem upcrossingsBefore_eq_upcrossingsBefore'
  [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (hab : a < b) :
    upcrossingsBefore a b f N = upcrossingsBefore' a b f N := by
  ext ω
  simp only [upcrossingsBefore, upcrossingsBefore']
  set A := {n | upperCrossingTime a b f N n ω < N} with hA
  set B := {n | ltUpcrossingsBefore a b f N n ω} with hB
  have : A = B := by
    ext n
    rw [hA, hB]
    exact upperCrossingTime_lt_iff_ltUpcrossingsBefore a b f N n ω hab
  grind

end UpperCrossingTimeEquivalence

/-! Suffices to show monotonicity for `Finite` index sets - the comparison with `NNRat`, as
  needed in the `theorem lintegral_iSup'`, is via `⊔`.
  -- Not really. We need to derive Doob's upcrossing inequality for finite index sets,
  from its version for Nat.
-/

section MonotonicityAndBoundedness

variable [LinearOrder ι]

/-! Given a finite {i | i < N}, size of UpcrossingData is bounded, assuming UpcrossingData < N. -/
lemma upcrossingData_bounded_of_finite (a b : ℝ) (f : ι → Ω → ℝ) (ω : Ω) (N : ι)
    (hfin : Finite {i | i < N}) :
    ∃ M : ℕ,  ∀ n : ℕ, ∀ hseq : UpcrossingData a b f n ω,
      hseq.t (2 * n - 1) < N → 2 * n ≤ M := by
  set s := {i | i < N} with hs
  have hfin := Fintype.ofFinite s
  use Fintype.card s
  intro n hseq ht_lt_N
  have h : ∀ i : Fin (2 * n), hseq.t i ∈ s := by
    intro i
    have : hseq.t i ≤ hseq.t (2 * n - 1) := hseq.mono (by grind)
    grind
  set F := hseq.t_on_Fin2n with hF
  set F' : Fin (2 * n) → s := Set.codRestrict F s h with ht'_def
  have hInj : Function.Injective F := hseq.t_strict_mono_on_Fin2n.injective
  have ht'Inj := hInj.codRestrict h
  calc
    Fintype.card s ≥ Fintype.card (Fin (2 * n)) :=
      Fintype.card_le_of_injective F' ht'Inj
    _ = 2 * n := Fintype.card_fin _

variable [OrderBot ι]
variable {κ : Type*} [LinearOrder κ] [OrderBot κ]

/-! (UNUSED NOW) Monotonicity of ltUpcrossingsBefore with respect to the index set. -/
/-!
lemma ltUpcrossingsBefore_mono_index_set (f : ι → κ) (hsmon : StrictMono f)
    (u : ι → Ω → ℝ) (v : κ → Ω → ℝ) (hv : ∀ i : ι, v (f i) = u i) -- u is a restriction of v to f(ι)
    (a b : ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b) :
    -- u has less upcrossings than v
    ltUpcrossingsBefore a b u N n ω → ltUpcrossingsBefore a b v (f N) n ω := by
  simp only [ltUpcrossingsBefore]
  by_cases hN : N ≤ ⊥
  · simp only [hN, if_true]; grind
  · simp only [hN, if_false]
    push_neg at hN
    have : f ⊥ < f N := hsmon hN
    have fbot : ⊥ ≤ f ⊥ := by exact OrderBot.bot_le (f ⊥)
    have hbot : ¬ f N ≤ ⊥ := by grind
    simp only [hbot, if_false]
    by_cases hnzero : n = 0
    · simp only [hnzero, if_true]
      grind
    · simp only [hnzero, if_false]
      rintro ⟨hseq, ht_lt_N⟩
      have hmon : Monotone f := hsmon.monotone
      let hseqv : UpcrossingData a b v n ω :=
        {
          hab := hab,
          t := fun i => f (hseq.t i),
          mono := by
            intro i j hij
            exact hsmon.monotone (hseq.mono hij)
          ft_le_a := by
            intro i hi heven
            rw [hv (hseq.t i)]
            exact hseq.ft_le_a i hi heven,
          ft_ge_b := by
            intro i hi hodd
            rw [hv (hseq.t i)]
            exact hseq.ft_ge_b i hi hodd
        }
      use hseqv
      have htv_lt_fN : hseqv.t (2 * n - 1) < f N := by
        simp only [hseqv]
        exact hsmon ht_lt_N
      exact htv_lt_fN
-/

/-! Monotonicity of ltUpcrossingsBefore with respect to the index set, on {i | i ≤ N}. -/
lemma ltUpcrossingsBefore_mono_index_set_before (f : ι → κ) (N : ι)
    (hsmon : StrictMonoOn f {i | i ≤ N})
    (u : ι → Ω → ℝ) (v : κ → Ω → ℝ) (hv : ∀ i ≤ N, v (f i) = u i) -- u is a restriction of v to f(ι)
    (a b : ℝ) (n : ℕ) (ω : Ω) (hab : a < b) :
    -- u has less upcrossings than v
    ltUpcrossingsBefore a b u N n ω → ltUpcrossingsBefore a b v (f N) n ω := by
  simp only [ltUpcrossingsBefore]
  by_cases hN : N ≤ ⊥
  · simp only [hN, if_true]; grind
  · simp only [hN, if_false]
    push_neg at hN -- hN : ⊥ < N
    have hBotIn : ⊥ ∈ {i | i ≤ N} := by simp
    have hNIn : N ∈ {i | i ≤ N} := by simp
    have : f ⊥ < f N := hsmon hBotIn hNIn hN
    have fbot : ⊥ ≤ f ⊥ := by exact OrderBot.bot_le (f ⊥)
    have hbot : ¬ f N ≤ ⊥ := by grind
    simp only [hbot, if_false]
    by_cases hnzero : n = 0
    · simp only [hnzero, if_true]
      grind
    · simp only [hnzero, if_false]
      rintro ⟨hseq, ht_lt_N⟩
      have hmon : MonotoneOn f {i | i ≤ N} := hsmon.monotoneOn
      have htIn : ∀ j < 2 * n, hseq.t j ∈ {i | i ≤ N} := by
        intro i hi
        have : hseq.t i ≤ hseq.t (2 * n - 1) := hseq.mono (by grind)
        grind
      let hseqv : UpcrossingData a b v n ω :=
        {
          hab := hab,
          t := fun i => if i < 2 * n then f (hseq.t i) else f N,
          mono := by
            intro i j hij
            by_cases hi : i < 2 * n
            · have hti := htIn i hi
              by_cases hj : j < 2 * n
              · -- both i and j are < 2 * n
                simp only [hi, hj, if_true]
                exact hmon hti (htIn j hj) (hseq.mono hij)
              · -- i < 2 * n but j ≥ 2 * n
                simp only [hi, hj, if_true, if_false]
                exact hmon hti hNIn (by grind)
            · -- i ≥ 2 * n, so j ≥ 2 * n too
              have hj : ¬ j < 2 * n := by grind
              simp only [hi, hj, if_false]
              rfl
          ft_le_a := by
            intro i hi heven
            simp only [hi, if_true]
            rw [hv (hseq.t i) (htIn i hi)]
            exact hseq.ft_le_a i hi heven
          ft_ge_b := by
            intro i hi hodd
            simp only [hi, if_true]
            rw [hv (hseq.t i) (htIn i hi)]
            exact hseq.ft_ge_b i hi hodd
        }
      use hseqv
      have htv_lt_fN : hseqv.t (2 * n - 1) < f N := by
        simp only [hseqv]
        have hnzero : 2 * n - 1 < 2 * n := by grind
        simp only [hnzero, if_true]
        exact hsmon (htIn (2 * n - 1) hnzero) hNIn ht_lt_N
      exact htv_lt_fN

/-! Given a finite index set, size of UpcrossingData is bounded. -/
/-!
-- lemma upcrossingData_bounded_size
--     [LinearOrder ι] [OrderBot ι] [Finite ι]
--     (a b : ℝ) (f : ι → Ω → ℝ) (ω : Ω)
--     : ∃ M : ℕ, ∀ n : ℕ, ∀ _ : UpcrossingData a b f n ω, 2 * n ≤ M := by
--   have hfin := Fintype.ofFinite ι
--   use Fintype.card ι
--   intro n hseq
--   exact hseq.index_set_card_ge_of_upcrossingData
-/

/-! Boundedness of ltUpcrossingsBefore, assuming {i | i < N} is finite. -/
lemma ltUpcrossingsBefore_bddAbove_of_finite (a b : ℝ) (f : ι → Ω → ℝ) (ω : Ω) (N : ι)
    (hfin : Finite {i | i < N}) :
    BddAbove {n | ltUpcrossingsBefore a b f N n ω} := by
  by_cases hN : N ≤ ⊥
  · simp only [ltUpcrossingsBefore, hN, if_true]
    use 0
    intro n hn
    grind
  · obtain ⟨M, hMsize⟩ := upcrossingData_bounded_of_finite a b f ω N hfin
    set A := {n | ltUpcrossingsBefore a b f N n ω} with hA
    have hbdd: BddAbove A := by
      use M
      intro n hn
      rw [hA] at hn;
      simp only [ltUpcrossingsBefore, hN, if_false] at hn
      by_cases hnzero : n = 0
      · simp only [hnzero]; grind
      · simp_all
        rcases hn with ⟨hseq, ht_lt_N⟩
        grind
    exact hbdd

/-! Monotonicity of upcrossingsBefore' in the index set, assuming ltUpcrossingsBefore is bounded. -/
lemma upcrossingsBefore'_mono_index_set_of_bounded (f : ι → κ)
    (N : ι) (hsmon : StrictMonoOn f {i | i ≤ N})
    (u : ι → Ω → ℝ) (v : κ → Ω → ℝ) (hv : ∀ i ≤ N, v (f i) = u i) -- u is a restriction of v to f(ι)
    (a b : ℝ) (ω : Ω) (hab : a < b)
    (hbdB : BddAbove {n | ltUpcrossingsBefore a b v (f N) n ω}) :
    -- u has less upcrossings than v
    upcrossingsBefore' a b u N ω ≤ upcrossingsBefore' a b v (f N) ω := by
  by_cases! hN : N ≤ ⊥
  · have hleftzero : upcrossingsBefore' a b u N ω = 0 := by
      exact upcrossingsBefore'_zero_of_N_bot a b u N ω hN
    rw [hleftzero]; grind
  · set A := {n | ltUpcrossingsBefore a b u N n ω} with hA
    set B := {n | ltUpcrossingsBefore a b v (f N) n ω} with hB
    have hAsubB : A ⊆ B := by
      intro n hn
      exact ltUpcrossingsBefore_mono_index_set_before f N hsmon u v hv a b n ω hab hn
    have hbdB : BddAbove B := hbdB
    have hnonempty : A.Nonempty := by
      use 0
      simp only [ltUpcrossingsBefore, hA]; simp; grind
    exact csSup_le_csSup hbdB hnonempty hAsubB

/-! Monotonicity of upcrossingsBefore' in the index set, assuming {i | i < f N} is finite. -/
theorem upcrossingsBefore'_mono_index_set_of_finite_till_N (f : ι → κ)
    (N : ι) (hsmon : StrictMonoOn f {i | i ≤ N})
    (u : ι → Ω → ℝ) (v : κ → Ω → ℝ) (hv : ∀ i ≤ N, v (f i) = u i) -- u is a restriction of v to f(ι)
    (a b : ℝ) (ω : Ω) (hab : a < b) (hfin : Finite {i | i < f N}) :
    -- u has less upcrossings than v
    upcrossingsBefore' a b u N ω ≤ upcrossingsBefore' a b v (f N) ω :=
  upcrossingsBefore'_mono_index_set_of_bounded f N hsmon u v hv a b ω hab <|
    ltUpcrossingsBefore_bddAbove_of_finite a b v ω (f N) hfin

/-! Monotonicity of upcrossingsBefore' in the index set, assuming its finiteness. -/
theorem upcrossingsBefore'_mono_index_set_of_finite [Finite κ] (f : ι → κ)
    (N : ι) (hsmon : StrictMonoOn f {i | i ≤ N})
    (u : ι → Ω → ℝ) (v : κ → Ω → ℝ) (hv : ∀ i ≤ N, v (f i) = u i) -- u is a restriction of v to f(ι)
    (a b : ℝ) (ω : Ω) (hab : a < b) :
    -- u has less upcrossings than v
    upcrossingsBefore' a b u N ω ≤ upcrossingsBefore' a b v (f N) ω :=
  upcrossingsBefore'_mono_index_set_of_finite_till_N f N hsmon u v hv a b ω hab <|
    inferInstance

end MonotonicityAndBoundedness

section Measurability

lemma measurable_zero_UpcrossingsBefore_lt [LinearOrder ι] [OrderBot ι]
    (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) :
    MeasurableSet ({ω | ltUpcrossingsBefore a b f N 0 ω}) := by
  simp only [ltUpcrossingsBefore]
  by_cases hN : N ≤ ⊥
  · simp only [hN, if_true]
    exact MeasurableSet.empty
  · simp only [hN, if_false, if_true]
    exact MeasurableSet.univ

lemma measurable_one_UpcrossingsBefore_lt [LinearOrder ι] [OrderBot ι] [Countable ι]
    {𝓕 : Filtration ι m0}
    (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (hf : Adapted 𝓕 f) (hab : a < b) :
    MeasurableSet ({ω | ltUpcrossingsBefore a b f N 1 ω}) := by
  by_cases hN : N ≤ ⊥
  · simp only [ltUpcrossingsBefore, hN, if_true]
    exact MeasurableSet.empty
  · -- simp only [hN, if_false]
    set S : Set Ω := {ω | ∃ s t : ι,
      f s ω ∈ Set.Iic a ∧ f t ω ∈ Set.Ici b ∧ s < t ∧ t < N} with hS
    have : {ω | ltUpcrossingsBefore a b f N 1 ω} = S := by
      ext ω
      simp only [ltUpcrossingsBefore, hN, if_false]
      simp only [Set.mem_setOf_eq]
      rw [Set.mem_setOf_eq]
      constructor
      · rintro ⟨seq, h_t1_lt_N⟩
        use seq.t 0, seq.t 1
        have ha : f (seq.t 0) ω ∈ Set.Iic a :=
          Set.mem_Iic.mpr (seq.ft_le_a 0 (by simp) Even.zero)
        have hb : f (seq.t 1) ω ∈ Set.Ici b :=
          Set.mem_Ici.mpr (seq.ft_ge_b 1 (by simp) (by grind))
        refine ⟨ha, hb, ?hs_lt_t, h_t1_lt_N⟩
        exact seq.t_strict_mono' (by simp) (by simp)
      · rintro ⟨s, t, hfs, hft, hs_lt_t, ht_lt_N⟩
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
        use hseq
        exact ht_lt_N
    rw [this]
    set A : ι → Set Ω := fun t => {ω | f t ω ∈ Set.Iic a} with hA
    set B : ι → Set Ω := fun t => {ω | f t ω ∈ Set.Ici b} with hB
    have hA_meas : ∀ t, MeasurableSet (A t) := fun t =>
        measurableSet_le ((hf t).mono (𝓕.le t)).measurable measurable_const
    have hB_meas : ∀ t, MeasurableSet (B t) := fun t =>
        measurableSet_le measurable_const ((hf t).mono (𝓕.le t)).measurable
    have hSconstr : S = ⋃ t < N, (B t ∩ ⋃ s < t, (A s)) := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, S, A, B]
      constructor
      · rintro ⟨s, t, hfs, hft, hst, htN⟩
        exact ⟨t, htN, hft, s, hst, hfs⟩
      · rintro ⟨t, htN, hft, s, hst, hfs⟩
        exact ⟨s, t, hfs, hft, hst, htN⟩
    rw [hSconstr]
    have huA_meas : ∀ t, MeasurableSet (⋃ s < t, (A s)) := fun t =>
      MeasurableSet.biUnion (Set.to_countable _) (fun s _ => hA_meas s)
    exact MeasurableSet.biUnion (Set.to_countable _) (fun t _ =>
      (hB_meas t).inter (huA_meas t))

lemma ltUpcrossingsBefore_of_ltUpcrossingsBefore [LinearOrder ι] [OrderBot ι]
    (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hN : ¬ N ≤ ⊥) :
    ltUpcrossingsBefore a b f N (n + 2) ω ↔
    (∃ seq' : UpcrossingData a b f (n + 1) ω, ∃ s t : ι,
      seq'.t (2 * n + 1) < s ∧
      s < t ∧
      t < N ∧
      f s ω ∈ Set.Iic a ∧
      f t ω ∈ Set.Ici b) := by
  simp only [ltUpcrossingsBefore]
  rw [if_neg hN]
  have h1 : n + 2 ≠ 0 := by grind
  simp only [h1, if_false]
  constructor
  · rintro ⟨seq, h_t1_lt_N⟩
    set seq' := seq.toShorter with hseq'_def
    set s := seq.t (2 * n + 2) with hs
    set t := seq.t (2 * n + 3) with ht
    have h_t1_lt_s : seq'.t (2 * n + 1) < s := seq.t_strict_mono' (by simp) (by grind)
    have h_s_lt_t : s < t := seq.t_strict_mono' (by grind) (by grind)
    have h_even : f s ω ∈ Set.Iic a :=
      Set.mem_Iic.mpr (seq.ft_le_a (2 * n + 2) (by grind) (by grind))
    have h_odd : f t ω ∈ Set.Ici b :=
      Set.mem_Ici.mpr (seq.ft_ge_b (2 * n + 3) (by grind) (by grind))
    exact ⟨seq', s, t, h_t1_lt_s, h_s_lt_t, h_t1_lt_N, h_even, h_odd⟩
  · rintro ⟨seq', s, t, h_t1_lt_s, h_s_lt_t, h_t_lt_N, hfs, hft⟩
    use (seq'.extend s t h_t1_lt_s.le h_s_lt_t.le hfs hft)
    have := seq'.extend_t s t h_t1_lt_s.le h_s_lt_t.le hfs hft
    rw [← this] at h_t_lt_N
    exact h_t_lt_N

lemma ltUpcrossingsBefore_of_ltUpcrossingsBefore' [LinearOrder ι] [OrderBot ι]
    (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hN : ¬ N ≤ ⊥) :
    ltUpcrossingsBefore a b f N (n + 2) ω ↔
    (∃ s t : ι, ltUpcrossingsBefore a b f s (n + 1) ω ∧
      s < t ∧
      t < N ∧
      f s ω ∈ Set.Iic a ∧
      f t ω ∈ Set.Ici b) := by
  rw [ltUpcrossingsBefore_of_ltUpcrossingsBefore a b f N n ω hN]
  simp only [ltUpcrossingsBefore]
  have hn1 : n + 1 ≠ 0 := by grind
  constructor
  · rintro ⟨seq', s, t, h_t1_lt_s, h_s_lt_t, h_t_lt_N, hfs, hft⟩
    use s, t
    have hsbot : ⊥ < s := lt_of_le_of_lt bot_le h_t1_lt_s
    have hsbot : ¬ s ≤ ⊥ := by grind
    simp only [hsbot, hn1, if_false]
    have hseq'_n1 : ∃ seq'' : UpcrossingData a b f (n + 1) ω, seq''.t (2 * n + 1) < s := by
      use seq'
    exact ⟨hseq'_n1, h_s_lt_t, h_t_lt_N, hfs, hft⟩
  · rintro ⟨s, t, h_ltUp_n1, h_s_lt_t, h_t_lt_N, hfs, hft⟩
    by_cases hsb : s ≤ ⊥
    · simp only [hsb, if_true] at h_ltUp_n1
    · simp only [hsb, if_false, hn1] at h_ltUp_n1
      rcases h_ltUp_n1 with ⟨seq', hseq'_n1⟩
      use seq', s, t
      exact ⟨hseq'_n1, h_s_lt_t, h_t_lt_N, hfs, hft⟩

lemma measurable_ltUpcrossingsBefore_of_Nbot [LinearOrder ι] [OrderBot ι]
    (a b : ℝ) (f : ι → Ω → ℝ) (n : ℕ) :
    MeasurableSet ({ω | ltUpcrossingsBefore a b f ⊥ n ω}) := by
  simp only [ltUpcrossingsBefore]; simp

/-! The set `{ω | ltUpcrossingsBefore a b f N n ω}` is measurable. -/
theorem Adapted.measurable_ltUpcrossingsBefore [LinearOrder ι] [OrderBot ι] [Countable ι]
    {𝓕 : Filtration ι m0}
    (a b : ℝ) (f : ι → Ω → ℝ) (n : ℕ) (hf : Adapted 𝓕 f) (hab : a < b) :
    ∀ N : ι, MeasurableSet ({ω | ltUpcrossingsBefore a b f N n ω}) := by
  by_cases! hnzero : n = 0
  · simp only [hnzero, if_true, ltUpcrossingsBefore]
    intro N
    simp_all
  · -- substitute n with n' + 1
    let n' := n - 1; have hn' : n = n' + 1 := by grind
    simp only [hn']
    induction n' with
    | zero =>
      intro N
      exact measurable_one_UpcrossingsBefore_lt a b f N hf hab
    | succ n'' ih =>
      intro N
      by_cases hN : N ≤ ⊥
      · simp only [ltUpcrossingsBefore, hN, if_true]
        exact MeasurableSet.empty
      · -- case N ≠ ⊥
        set S : ι → Set Ω := fun i => {ω | ltUpcrossingsBefore a b f i (n'' + 1) ω} with hS
        have hS_meas : ∀ i, MeasurableSet (S i) := fun i => ih i
        set S' : Set Ω := {ω | ltUpcrossingsBefore a b f N (n'' + 2) ω} with hS'
        set A : ι → Set Ω := fun t => {ω | f t ω ≤ a} with hA
        set B : ι → Set Ω := fun t => {ω | f t ω ≥ b} with hB
        have hA_meas : ∀ t, MeasurableSet (A t) := fun t =>
          measurableSet_le ((hf t).mono (𝓕.le t)).measurable measurable_const
        have hB_meas : ∀ t, MeasurableSet (B t) := fun t =>
          measurableSet_le measurable_const ((hf t).mono (𝓕.le t)).measurable
        have hSconstr : S' = ⋃ t < N, (B t ∩ ⋃ s < t, (A s ∩ S s)) := by
          ext ω
          simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, S', A, B]
          simp only [Set.mem_setOf_eq, S]
          rw [ltUpcrossingsBefore_of_ltUpcrossingsBefore' a b f N n'' ω hN]
          grind
        rw [hSconstr]
        have huA_meas : ∀ t, MeasurableSet (⋃ s < t, (A s ∩ S s)) := fun t =>
          MeasurableSet.biUnion (Set.to_countable _) (fun s _ =>
            (hA_meas s).inter (hS_meas s))
        exact MeasurableSet.biUnion (Set.to_countable _) (fun t _ => (hB_meas t).inter (huA_meas t))

lemma upcrossingsBefore'_eq_sum [LinearOrder ι] [OrderBot ι] [Finite ι]
    (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) (hab : a < b) : upcrossingsBefore' a b f N ω =
    ∑' i, {n | ltUpcrossingsBefore a b f N n ω}.indicator 1 i := by
  by_cases hN : N ≤ ⊥
  · simp only [upcrossingsBefore', ltUpcrossingsBefore, hN, if_true]
    simp_all
  · simp only [upcrossingsBefore']
    have hnonempty : {n | ltUpcrossingsBefore a b f N n ω}.Nonempty := by
      use 0
      simp only [ltUpcrossingsBefore, hN, if_false]
      grind
    set A : ℕ → Prop := (fun n => ltUpcrossingsBefore a b f N n ω) with hA
    have hbdd : BddAbove {n | A n} := by
      have hfin : Finite {i | i < N} := by infer_instance
      exact ltUpcrossingsBefore_bddAbove_of_finite a b f ω N hfin
    have huppbd : ∃ M : ℕ, ∀ n, A n → n ≤ M := by
      rcases hbdd with ⟨M, hM⟩
      exact ⟨M, fun n hn => hM hn⟩
    obtain ⟨M, hM⟩ := huppbd
    have hsub : {n | A n} ⊆ {n | n ≤ M} := by
      intro n hn
      grind
    have hleMfin : Finite {n | n ≤ M} := by infer_instance
    have hfin2 : Finite {n | A n} := Set.Finite.subset hleMfin hsub
    have hex : ∃ n : ℕ, upcrossingsBefore' a b f N ω ∈ {n | A n} := by
      use upcrossingsBefore' a b f N ω
      simp only [upcrossingsBefore']
      exact Set.Nonempty.csSup_mem hnonempty hfin2
    obtain ⟨n0, hn0⟩ := hex
    have : upcrossingsBefore' a b f N ω = sSup {n | A n} := rfl
    sorry



theorem Adapted.measurable_upcrossingsBefore' [LinearOrder ι] [OrderBot ι] [Finite ι]
    {𝓕 : Filtration ι m0}
    (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (hf : Adapted 𝓕 f) (hab : a < b) :
    Measurable (upcrossingsBefore' a b f N) := by
  have : upcrossingsBefore' a b f N = fun ω =>
      ∑' i, {n | ltUpcrossingsBefore a b f N n ω}.indicator 1 i := by
    ext ω
    exact upcrossingsBefore'_eq_sum a b f N ω hab
  rw [this]
  sorry
  -- refine Finset.measurable_fun_sum _ fun i _ => Measurable.indicator measurable_const <|
  --   𝓕.le N _ ?_
  -- simpa only [ENat.some_eq_coe, Nat.cast_lt] using
  --   hf.isStoppingTime_upperCrossingTime.measurableSet_lt_of_pred N

end Measurability

section DoobInequalityNat

variable {a b : ℝ}

theorem mul_integral_upcrossingsBefore_le_integral_pos_part_aux' [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0} (N : ℕ)
    (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    (b - a) * μ[upcrossingsBefore' a b f N] ≤ μ[fun ω => (f N ω - a)⁺] := by
  have hgeq : upcrossingsBefore a b f N = upcrossingsBefore' a b f N := by
    rw [upcrossingsBefore_eq_upcrossingsBefore' a b f N hab]
  have hequiv : (b - a) * μ[upcrossingsBefore a b f N] ≤ μ[fun ω => (f N ω - a)⁺] :=
    mul_integral_upcrossingsBefore_le_integral_pos_part_aux hf hab
  rw [← hgeq]
  assumption

/-!
  Doob's upcrossing inequality on `ℕ` for the alternative definition of `upcrossingsBefore`.
-/
theorem Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part' [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (a b : ℝ) (hf : Submartingale f 𝓕 μ) (N : ℕ) :
    (b - a) * μ[upcrossingsBefore' a b f N] ≤ μ[fun ω => (f N ω - a)⁺] := by
  by_cases! hab : a < b
  · exact mul_integral_upcrossingsBefore_le_integral_pos_part_aux' N hf hab
  · rw [← sub_nonpos] at hab
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hab (by positivity))
      (integral_nonneg fun ω => posPart_nonneg _)

end DoobInequalityNat

section FinToNat

variable {n : ℕ} [NeZero n] -- to avoid issues with `Fin 0`
variable {u : (Fin n) → Ω → ℝ} {N : Fin n}

def Fin.clamp (i : ℕ) (n : ℕ) [NeZero n] : Fin n :=
  ⟨min i (n - 1),
    Nat.lt_of_le_of_lt (Nat.min_le_right i (n - 1)) (Nat.sub_lt (NeZero.pos n) Nat.one_pos)⟩

lemma Fin.clamp_val (i : ℕ) (n : ℕ) [NeZero n] :
    (Fin.clamp i n).val = min i (n - 1) := rfl

lemma Fin.clamp.eq_of_fin (n : ℕ) [NeZero n] (i : Fin n) :
    Fin.clamp i.val n = i := by grind [Fin.clamp_val]

lemma Fin.clamp.monotone (i j : ℕ) (hij : i ≤ j) (n : ℕ) [NeZero n] :
    Fin.clamp i n ≤ Fin.clamp j n := by
  simp only [Fin.le_iff_val_le_val, Fin.clamp]
  exact min_le_min hij (Nat.le_refl _)

lemma Fin.clamp.StrictMonoOn {N n : ℕ} (hnN : N < n) [NeZero n] :
    StrictMonoOn (fun i => Fin.clamp i n) {i | i ≤ N} := by
  intro i hi j hj hij
  simp only [Fin.lt_iff_val_lt_val, Fin.clamp]
  grind

lemma Fin.val.StrictMonoOn {n : ℕ} (N : Fin n) :
    StrictMonoOn (fun k : Fin n => k.val) {k | k ≤ N} := by
  intro i hi j hj hij
  assumption

def Filtration.natOfFin (𝓕 : Filtration (Fin n) m0) : Filtration ℕ m0 :=
  { seq := fun i => 𝓕 (Fin.clamp i n)
    mono' := by
      intro i j hij
      refine 𝓕.mono ?_
      simp only [Fin.clamp, Fin.le_iff_val_le_val]
      exact min_le_min hij (Nat.le_refl _)
    le' := fun i => Filtration.le 𝓕 (Fin.clamp i n)
  }

variable {𝓕 : Filtration (Fin n) m0}

def Process.natOfFin (u : Fin n → Ω → ℝ) : ℕ → Ω → ℝ := fun k => u (Fin.clamp k n)

lemma Submartingale.natOfFin (hf : Submartingale u 𝓕 μ) :
    Submartingale (Process.natOfFin u) (Filtration.natOfFin 𝓕) μ := by
  set u' : ℕ → Ω → ℝ := Process.natOfFin u with hfNat
  set 𝓕' := Filtration.natOfFin 𝓕 with hFNat
  have hadapted' : Adapted 𝓕' u' := by
    intro i
    have hsm : StronglyMeasurable[𝓕 (Fin.clamp i n)] (u (Fin.clamp i n)) := by
      exact Submartingale.stronglyMeasurable hf (Fin.clamp i n)
    have hsm' : StronglyMeasurable[𝓕' i] (u' i) := by
      simp only [u', 𝓕']
      exact hsm
    exact hsm'
  have hsub' : (∀ i j, i ≤ j → u' i ≤ᵐ[μ] μ[u' j|𝓕' i]) := by
    intros i j hij
    simp only [u', 𝓕']
    refine Submartingale.ae_le_condExp hf ?_
    exact Fin.clamp.monotone i j hij n
  have hint' : ∀ i, Integrable (u' i) μ := by
    intro i
    simp only [u']
    exact Submartingale.integrable hf (Fin.clamp i n)
  exact ⟨ hadapted', hsub', hint' ⟩

lemma Process.natOfFin_eq (u : ℕ → Ω → ℝ) (v : Fin n → Ω → ℝ)
    (hNatOfFin : u = Process.natOfFin v) (N : ℕ) :
    ∀ i ≤ N, v (Fin.clamp i n) = u i := by
  intro i hi
  rw [hNatOfFin, Process.natOfFin]

lemma Process.natOfFin_eq' (u : Fin n → Ω → ℝ) (v : ℕ → Ω → ℝ)
    (hNatOfFin : v = Process.natOfFin u) (N : Fin n) :
    ∀ i ≤ N, v i.val = u i := by
  intro i hi
  rw [hNatOfFin, Process.natOfFin, Fin.clamp.eq_of_fin n i]

lemma Process.natOfFin.upcrossingsBefore'_le (u : ℕ → Ω → ℝ) (v : Fin n → Ω → ℝ)
    (hNatOfFin : u = Process.natOfFin v) (N : ℕ) (a b : ℝ) (ω : Ω) (hab : a < b) (hNn : N < n) :
    upcrossingsBefore' a b u N ω ≤ upcrossingsBefore' a b v (Fin.clamp N n) ω := by
  set f : ℕ → Fin n := fun i => Fin.clamp i n with hf
  have hsmon : StrictMonoOn f {i | i ≤ N} := Fin.clamp.StrictMonoOn hNn
  have hv : ∀ i ≤ N, v (f i) = u i := Process.natOfFin_eq u v hNatOfFin N
  have hfin : Finite {i | i < f N} := by infer_instance
  exact upcrossingsBefore'_mono_index_set_of_finite_till_N f N hsmon u v hv a b ω hab hfin

lemma Process.natOfFin.upcrossingsBefore'_ge (u : Fin n → Ω → ℝ) (v : ℕ → Ω → ℝ)
    (hNatOfFin : v = Process.natOfFin u) (N : Fin n) (a b : ℝ) (ω : Ω) (hab : a < b) :
    upcrossingsBefore' a b u N ω ≤ upcrossingsBefore' a b v N ω := by
  set f : Fin n → ℕ := fun i => i.val with hf
  have hsmon : StrictMonoOn f {i | i ≤ N} := Fin.val.StrictMonoOn N
  have hv : ∀ i ≤ N, v (f i) = u i := Process.natOfFin_eq' u v hNatOfFin N
  have hfin : Finite {i | i < f N} := by infer_instance
  exact upcrossingsBefore'_mono_index_set_of_finite_till_N f N hsmon u v hv a b ω hab hfin

theorem Process.natOfFin.upcrossingsBefore'_eq (u : Fin n → Ω → ℝ) (v : ℕ → Ω → ℝ)
    (hNatOfFin : v = Process.natOfFin u) (N : Fin n) (a b : ℝ) (ω : Ω) (hab : a < b) :
    upcrossingsBefore' a b u N ω = upcrossingsBefore' a b v N ω := by
  apply le_antisymm
  · exact Process.natOfFin.upcrossingsBefore'_ge u v hNatOfFin N a b ω hab
  · conv_rhs => rw [(Fin.clamp.eq_of_fin n N).symm]
    exact Process.natOfFin.upcrossingsBefore'_le v u hNatOfFin N a b ω hab (N.isLt)

end FinToNat

section DoobInequalityFin

variable {a b : ℝ}
 {n : ℕ} [NeZero n] -- to avoid issues with `Fin 0`
 {f : (Fin n) → Ω → ℝ} {N : Fin n}
 {𝓕 : Filtration (Fin n) m0}

theorem mul_integral_upcrossingsBefore_le_integral_pos_part_on_finite [IsFiniteMeasure μ]
    {u : (Fin n) → Ω → ℝ} {N : Fin n} {𝓕 : Filtration (Fin n) m0}
    (hu : Submartingale u 𝓕 μ) (hab : a < b) :
    (b - a) * μ[upcrossingsBefore' a b u N] ≤ μ[fun ω => (u N ω - a)⁺] := by
  -- We reduce to the `ℕ`-indexed case
  set 𝓕' := Filtration.natOfFin 𝓕 with hFiltr
  set v := Process.natOfFin u with hv
  have hvsub : Submartingale v 𝓕' μ := Submartingale.natOfFin hu
  -- The inclusion map from `Fin n` to `ℕ`
  set f : Fin n → ℕ := fun i => i.val with hmap
  set N' : ℕ := f N with hN'
  have hsmon : StrictMono f := by
    intro i j hij
    simp only [Fin.lt_iff_val_lt_val] at hij
    exact hij
  have hv : ∀ i : Fin n, v (f i) = u i := by
    intro i
    simp only [v, f]; unfold Process.natOfFin
    simp only [Fin.clamp.eq_of_fin n i]
  have hfin : Finite {i : ℕ | i < N'} := by infer_instance
  have hineq : upcrossingsBefore' a b u N ≤ upcrossingsBefore' a b v N' := by
    intro ω
    exact upcrossingsBefore'_mono_index_set_of_finite_till_N f hsmon u v hv a b N ω hab hfin
  -- TODO: finish, starting from measurability of upcrossingsBefore' (see another TODO, above)
  -- have hNpos : 0 < NNat + 1 := by exact Nat.lt_succ_of_le (Nat.zero_le NNat)
  sorry

end DoobInequalityFin

section Countable

variable [Countable ι]

theorem Countable.increasing_family_saturates_every_finite_subset :
    ∃ s : ℕ → Set ι,
    Monotone s ∧
    (∀ n, Finite (s n)) ∧
    (∀ t : Set ι, Finite t → ∃ n, t ⊆ s n) := by
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat ι
  let s : ℕ → Set ι := fun n => {i | f i < n}
  refine ⟨s, ?_, ?_, ?_⟩
  · -- Monotone s
    intro m n hmn i hi
    exact Nat.lt_of_lt_of_le hi hmn
  · -- ∀ n, Finite (s n)
    intro n
    let g : s n → Fin n := fun ⟨i, hi⟩ => ⟨f i, hi⟩
    have g_inj : Function.Injective g := fun ⟨x, _⟩ ⟨y, _⟩ h => Subtype.ext (hf (Fin.ext_iff.mp h))
    exact Finite.of_injective g g_inj
  · -- ∀ t, Finite t → ∃ n, t ⊆ s n
    intro t ht
    haveI : Fintype t := Set.Finite.fintype ht
    by_cases hempty : t = ∅
    · exact ⟨0, by simp [hempty]⟩
    · use (Finset.univ.image (fun i : t => f i)).sup id + 1
      intro i hi
      simp only [Set.mem_setOf_eq, s]
      have : f i ∈ Finset.univ.image (fun j : t => f j) :=
        Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
      exact Nat.lt_succ_of_le (Finset.le_sup (f := id) this)

variable [LinearOrder ι] [OrderBot ι]

variable (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (hab : a < b)

end Countable

end ProbabilityTheory
