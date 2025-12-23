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

/- The original definitions, valid for InfSet (hence not for NNRat), are:

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
  s : ℕ → ι
  t : ℕ → ι
  si_lt_ti  : ∀ i : ℕ, i < n → s i < t i
  fs_le_a  : ∀ i : ℕ, i < n → f (s i) ω ≤ a
  ft_ge_b  : ∀ i : ℕ, i < n → f (t i) ω ≥ b
  ti_lt_sj : ∀ i j : ℕ, i < j → j < n → t i < s j

/-! We already have (proved in Mathlib.Probability.Process.HittingTime):
theorem hittingBtwn_mem_set_of_hittingBtwn_lt [WellFoundedLT ι] {m : ι}
    (hl : hittingBtwn u s n m ω < m) :
    u (hittingBtwn u s n m ω) ω ∈ s
theorem hittingBtwn_le_of_mem {m : ι} (hin : n ≤ i) (him : i ≤ m) (his : u i ω ∈ s) :
    hittingBtwn u s n m ω ≤ i
-/

namespace UpcrossingData

variable {a b : ℝ} {f : ι → Ω → ℝ} {n : ℕ} {ω : Ω} [PartialOrder ι]
variable (h : UpcrossingData a b f n ω)

-- From hlt you get a ≤ version
lemma si_le_ti {i} (hi : i < n) : h.s i ≤ h.t i :=
  (h.si_lt_ti i hi).le

-- Repackage the side conditions as set membership
lemma fs_mem {i} (hi : i < n) : f (h.s i) ω ∈ Set.Iic a := h.fs_le_a i hi
lemma ft_mem {i} (hi : i < n) : f (h.t i) ω ∈ Set.Ici b := h.ft_ge_b i hi

-- Chain inequality as a non-strict version
lemma ti_le_sj {i j} (hij : i < j) (hj : j < n) : h.t i ≤ h.s j :=
  (h.ti_lt_sj i j hij hj).le

-- `s` is strictly increasing on indices below `n`
lemma s_lt_of_lt {i j} (hij : i < j) (hj : j < n) : h.s i < h.s j := by
  have hj' : j ≤ n := le_of_lt hj
  have hi : i < n := lt_of_lt_of_le hij hj'
  have hti : h.t i < h.s j := h.ti_lt_sj i j hij hj
  exact lt_trans (h.si_lt_ti i hi) hti

-- `t` is strictly increasing on indices below `n`
lemma t_lt_of_lt {i j} (hij : i < j) (hj : j < n) : h.t i < h.t j := by
  have hti : h.t i < h.s j := h.ti_lt_sj i j hij hj
  have hst : h.s j < h.t j := h.si_lt_ti j hj
  exact lt_trans hti hst

-- Convenient successors
lemma s_lt_succ {i} (hi : i + 1 < n) : h.s i < h.s (i + 1) :=
  h.s_lt_of_lt (Nat.lt_succ_self _) hi

lemma t_lt_succ {i} (hi : i + 1 < n) : h.t i < h.t (i + 1) :=
  h.t_lt_of_lt (Nat.lt_succ_self _) hi

def toShorter {a b : ℝ} {f : ι → Ω → ℝ} {n : ℕ} {ω : Ω} (h : UpcrossingData a b f (n + 1) ω) :
    UpcrossingData a b f n ω :=
{ s := h.s,
  t := h.t,
  si_lt_ti := fun i hi => h.si_lt_ti i (Nat.lt_trans hi (Nat.lt_succ_self _)),
  fs_le_a := fun i hi => h.fs_le_a i (Nat.lt_trans hi (Nat.lt_succ_self _)),
  ft_ge_b := fun i hi => h.ft_ge_b i (Nat.lt_trans hi (Nat.lt_succ_self _)),
  ti_lt_sj := fun i j hij hj =>
    h.ti_lt_sj i j hij (Nat.lt_trans hj (Nat.lt_succ_self _))
}

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
  ∀ n (hseq : UpcrossingData a b f (n+1) ω), hseq.t n ≤ N →
    upperCrossingTime a b f N (n+1) ω ≤ hseq.t n := by
  simp only [upperCrossingTime]
  -- motive depends on n and hseq
  refine Nat.rec (motive := fun n => ∀ hseq : UpcrossingData a b f (n+1) ω, hseq.t n ≤ N →
    upperCrossingTime a b f N (n+1) ω ≤ hseq.t n) ?base ?step
  · -- n = 0 case; hseq : UpcrossingData a b f 1 ω
    intro hseq h_t0_le_N
    simp only [upperCrossingTime];
    have h := Nat.zero_lt_succ 0
    exact upperCrossingTime_le_of_UpcrossingData' a b f ⊥ (hseq.s 0) (hseq.t 0) N ω
      bot_le (hseq.si_le_ti h) h_t0_le_N (hseq.fs_mem h) (hseq.ft_mem h)
  · -- succ case
    intro n ih hseq2 h_t_le_N
    set hseq1 := hseq2.toShorter with hseq_prev_def
    have h0 : hseq1.t n ≤ N := by
      calc
        hseq1.t n = hseq2.t n := rfl
        _ ≤ hseq2.t n.succ := le_of_lt (hseq2.t_lt_succ (by simp))
        _ ≤ N := h_t_le_N
    set u' := upperCrossingTime a b f N (n + 1) ω with hu'
    set s := hseq2.s n.succ with hs
    set t := hseq2.t n.succ with ht
    exact upperCrossingTime_le_of_UpcrossingData' a b f u' s t N ω
      (le_trans (ih hseq1 h0) (hseq2.ti_le_sj (Nat.lt_succ_self n) (by simp)))
      (hseq2.si_le_ti (by simp)) h_t_le_N (hseq2.fs_mem (by simp)) (hseq2.ft_mem (by simp))

noncomputable def ltUpcrossingsBefore [LinearOrder ι] [OrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) : Prop :=
  if N ≤ ⊥ then False else
    if n = 0 then True else
      ∃ seq : UpcrossingData a b f n ω, seq.t (n - 1) < N


lemma upperCrossingTime_lt_of_ltUpcrossingsBefore [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b) :
    ltUpcrossingsBefore a b f N n ω → upperCrossingTime a b f N n ω < N := by
  by_cases h : N ≤ ⊥
  · have : ⊥ ≤ N := OrderBot.bot_le N
    have hNbot : N = ⊥ := le_antisymm h this
    subst hNbot
    simp only [ltUpcrossingsBefore]; simp
  · simp only [ltUpcrossingsBefore, h, if_false]
    by_cases hnzero : n = 0
    · -- n = 0 case
      subst hnzero; simp; grind
    · -- n ≥ 1 case
      simp only [if_neg hnzero]
      rintro ⟨hseq, ht_lt_N⟩
      refine lt_of_le_of_lt ?_ ht_lt_N
      have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero    -- or however you know n≥1
      set m := n - 1 with hm
      have hnm : n = m + 1 := by grind
      subst hnm
      -- goal now has (m+1)
      refine upperCrossingTime_le_of_UpcrossingData a b f N ω m hseq ?_


/-
  Equivalent definition that skips `[InfSet ι]`:
  ltUpcrossingsBefore a b f N n ω ↔ upperCrossingTime a b f N n ω < N).
-/
noncomputable def upcrossingsBefore' [LinearOrder ι] [OrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) : ℕ := sSup {n | ltUpcrossingsBefore a b f N n ω}

lemma ltUpcrossingsBefore_iff_upperCrossingTime_lt [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b) :
    ltUpcrossingsBefore a b f N n ω ↔ upperCrossingTime a b f N n ω < N := by
  constructor
  · exact upperCrossingTime_lt_of_ltUpcrossingsBefore a b f N n ω hab
  · sorry
