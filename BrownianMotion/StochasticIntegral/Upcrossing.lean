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

-- -- A single step: if the (n+1)-st upcrossing happens before `N`, then the
-- -- intermediate lower and upper crossing times give the two witnesses between
-- -- the previous upper crossing time and `N`.
-- lemma upperCrossingTime_crossing_pair [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι]
--   (a b : ℝ) (hab : a < b) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω)
--   (hlt : upperCrossingTime a b f N (n + 1) ω < N) :
--   let s := lowerCrossingTimeAux a f (upperCrossingTime a b f N n ω) N ω
--   let t := upperCrossingTime a b f N (n + 1) ω
--   upperCrossingTime a b f N n ω ≤ s ∧ s < t ∧ t < N ∧
--     f s ω ∈ Set.Iic a ∧ f t ω ∈ Set.Ici b := by
--   classical
--   intro s t
--   have ht_mem : f t ω ∈ Set.Ici b :=
--     hittingBtwn_mem_set_of_hittingBtwn_lt (u := f) (s := Set.Ici b) (n := s) (m := N)
--       (ω := ω) hlt
--   have hs_le_N : s ≤ N := hittingBtwn_le (u := f) (s := Set.Iic a)
--     (n := upperCrossingTime a b f N n ω) (m := N) (ω := ω)
--   have hprev_le_N : upperCrossingTime a b f N n ω ≤ N :=
--     (upperCrossingTime_mono (Nat.le_succ n)).trans (le_of_lt hlt)
--   have hprev_le_s : upperCrossingTime a b f N n ω ≤ s :=
--     le_hittingBtwn (u := f) (s := Set.Iic a)
--       (n := upperCrossingTime a b f N n ω) (m := N) (ω := ω) hprev_le_N
--   have hs_mem : f s ω ∈ Set.Iic a :=
--     hittingBtwn_mem_set_of_hittingBtwn_lt (u := f) (s := Set.Iic a)
--       (n := upperCrossingTime a b f N n ω) (m := N) (ω := ω)
--       (lt_of_le_of_lt hs_le_N hlt)
--   have hs_le_t : s ≤ t :=
--     le_hittingBtwn (u := f) (s := Set.Ici b) (n := s) (m := N) (ω := ω) hs_le_N
--   have hs_lt_t : s < t := by
--     have hfa : f s ω ≤ a := by simpa [Set.mem_Iic] using hs_mem
--     have hfb : f t ω ≥ b := by simpa [Set.mem_Ici] using ht_mem
--     have hne : s ≠ t := by
--       intro hEq
--       have : b ≤ a := le_trans hfb (by simpa [hEq] using hfa)
--       exact (not_le_of_gt hab) this
--     exact lt_of_le_of_ne hs_le_t hne
--   refine ⟨hprev_le_s, hs_lt_t, lt_of_le_of_lt hs_le_t hlt, ?_, ht_mem⟩
--   simpa [Set.mem_Iic] using hs_mem

noncomputable def ltUpcrossingsBefore [LinearOrder ι] [OrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) : Prop :=
  if N ≤ ⊥ then False else
    if n = 0 then True else
      ∃ seq : UpcrossingData a b f n ω, seq.t (n - 1) < N


lemma upperCrossingTime_lt_of_ltUpcrossingsBefore [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) :
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
      cases n with
      | zero => contradiction
      | succ m =>
          have ht_le_N : hseq.t m ≤ N := le_of_lt ht_lt_N
          simpa using upperCrossingTime_le_of_UpcrossingData a b f N ω m hseq ht_le_N

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
  · exact upperCrossingTime_lt_of_ltUpcrossingsBefore a b f N n ω
  · intro hlt /-TODO: this could be streamlined by pointing witnesses s,t first. -/
    by_cases hNbot : N ≤ ⊥
    · simpa [ltUpcrossingsBefore, hNbot] using
        (not_lt_of_ge (bot_le : ⊥ ≤ upperCrossingTime a b f N n ω)
          (lt_of_lt_of_le hlt hNbot) : False)
    · simp only [ltUpcrossingsBefore, hNbot, if_false]
      cases n with
      | zero => simp
      | succ m =>
          have h_upper : upperCrossingTime a b f N (m + 1) ω < N := hlt
          have h_upper_le : ∀ k ≤ m + 1, upperCrossingTime a b f N k ω < N :=
            fun k hk => lt_of_le_of_lt (upperCrossingTime_mono hk) h_upper
          have h_lower_le : ∀ k ≤ m, lowerCrossingTime a b f N k ω < N :=
            fun k hk =>
              lt_of_le_of_lt
                (lowerCrossingTime_le_upperCrossingTime_succ (a:=a) (b:=b) (f:=f)
                  (N:=N) (n:=k) (ω:=ω))
                (h_upper_le (k + 1) (Nat.succ_le_succ hk))
          have h_s_mem : ∀ k < m + 1, f (lowerCrossingTime a b f N k ω) ω ∈ Set.Iic a :=
            fun k hk =>
              hittingBtwn_mem_set_of_hittingBtwn_lt
                (u := f) (s := Set.Iic a) (n := upperCrossingTime a b f N k ω)
                (m := N) (ω := ω) (h_lower_le k (Nat.lt_succ_iff.mp hk))
          have h_t_mem : ∀ k < m + 1, f (upperCrossingTime a b f N (k + 1) ω) ω ∈ Set.Ici b :=
            fun k hk =>
              hittingBtwn_mem_set_of_hittingBtwn_lt
                (u := f) (s := Set.Ici b)
                (n := lowerCrossingTimeAux a f (upperCrossingTime a b f N k ω) N ω)
                (m := N) (ω := ω)
                (h_upper_le (k + 1) (Nat.succ_le_succ (Nat.le_of_lt_succ hk)))
          let seq : UpcrossingData a b f (m + 1) ω :=
          { s := fun k => lowerCrossingTime a b f N k ω
            t := fun k => upperCrossingTime a b f N (k + 1) ω
            si_lt_ti := by
              intro k hk
              have hle : lowerCrossingTime a b f N k ω ≤
                  upperCrossingTime a b f N (k + 1) ω :=
                lowerCrossingTime_le_upperCrossingTime_succ (a:=a) (b:=b) (f:=f) (N:=N)
                  (n:=k) (ω:=ω)
              have hne : lowerCrossingTime a b f N k ω ≠ upperCrossingTime a b f N (k + 1) ω :=
                by
                  intro hEq
                  have hfa : f (upperCrossingTime a b f N (k + 1) ω) ω ≤ a := by
                    simpa [Set.mem_Iic, hEq] using (h_s_mem k hk)
                  have hfb : f (upperCrossingTime a b f N (k + 1) ω) ω ≥ b := by
                    simpa [Set.mem_Ici] using (h_t_mem k hk)
                  have : b ≤ a := le_trans hfb hfa
                  exact (not_le_of_gt hab) this
              exact lt_of_le_of_ne hle hne
            fs_le_a := fun k hk => by
              have h := h_s_mem k hk
              simpa [Set.mem_Iic] using h
            ft_ge_b := fun k hk => by
              have h := h_t_mem k hk
              simpa [Set.mem_Ici] using h
            ti_lt_sj := by
              intro i j hij hj
              have hi1_le_j : i + 1 ≤ j := Nat.succ_le_of_lt hij
              have hj_le_m : j ≤ m := Nat.lt_succ_iff.mp hj
              have hi1_le_m : i + 1 ≤ m := le_trans hi1_le_j hj_le_m
              have hti_le_si1 : upperCrossingTime a b f N (i + 1) ω ≤
                  lowerCrossingTime a b f N (i + 1) ω :=
                upperCrossingTime_le_lowerCrossingTime (a:=a) (b:=b) (f:=f) (N:=N)
                  (n:=i + 1) (ω:=ω)
              have hti_lt_si1 : upperCrossingTime a b f N (i + 1) ω <
                  lowerCrossingTime a b f N (i + 1) ω := by
                have hne : upperCrossingTime a b f N (i + 1) ω ≠
                    lowerCrossingTime a b f N (i + 1) ω := by
                  intro hEq
                  have hfa : f (lowerCrossingTime a b f N (i + 1) ω) ω ≤ a := by
                    have := h_s_mem (i + 1) (Nat.lt_succ_of_le hi1_le_m)
                    simpa [Set.mem_Iic, hEq] using this
                  have hfb : f (lowerCrossingTime a b f N (i + 1) ω) ω ≥ b := by
                    have hi_lt_m : i < m := lt_of_lt_of_le hij hj_le_m
                    have := h_t_mem i (lt_trans hi_lt_m (Nat.lt_succ_self m))
                    simpa [Set.mem_Ici, hEq, Nat.succ_eq_add_one] using this
                  have : b ≤ a := le_trans hfb hfa
                  exact (not_le_of_gt hab) this
                exact lt_of_le_of_ne hti_le_si1 hne
              have hsi1_le_sj : lowerCrossingTime a b f N (i + 1) ω ≤
                  lowerCrossingTime a b f N j ω :=
                lowerCrossingTime_mono hi1_le_j
              exact lt_of_lt_of_le hti_lt_si1 hsi1_le_sj }
          refine ⟨seq, ?_⟩
          simpa using h_upper
