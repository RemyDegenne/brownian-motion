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

noncomputable def ltUpcrossingsBefore [LinearOrder ι] [OrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) : Prop :=
  if N ≤ ⊥ then False else
    if n = 0 then True else
      ∃ seq : UpcrossingData a b f n ω, seq.t (2 * n - 1) < N

lemma upperCrossingTime_lt_bot_iff_ltUpcrossingsBefore [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hN : N ≤ ⊥) :
    ltUpcrossingsBefore a b f N n ω ↔ upperCrossingTime a b f N n ω < N := by
  simp only [ltUpcrossingsBefore, hN, if_true];
  have : upperCrossingTime a b f N n ω ≥ ⊥ := bot_le
  grind


lemma upperCrossingTime_lt_of_ltUpcrossingsBefore [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) :
    ltUpcrossingsBefore a b f N n ω → upperCrossingTime a b f N n ω < N := by
  by_cases h : N ≤ ⊥
  · exact (upperCrossingTime_lt_bot_iff_ltUpcrossingsBefore a b f N n ω h).mp
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
          have ht_le_N : hseq.t (2 * m + 1) ≤ N := le_of_lt ht_lt_N
          simpa using upperCrossingTime_le_of_UpcrossingData a b f N ω m hseq ht_le_N

private lemma nondegenerate_of_hittingBtwn_lt [ConditionallyCompleteLinearOrderBot ι]
    [WellFoundedLT ι] (u : ι → Ω → ℝ) (s : Set ℝ) (n m : ι) (ω : Ω)
    (hl : hittingBtwn u s n m ω < m) :
    n < m := by
  have h := (hittingBtwn_lt_iff (i:=m) (le_refl m)).mp hl
  grind

private lemma upcrossingData_of_upperCrossingTime_lt [ConditionallyCompleteLinearOrderBot ι]
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

lemma upcrossingData_extend_of_upperCrossingTime_lt [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) :
  ∀ n, upperCrossingTime a b f N (n+1) ω < N →
    ∀ (hseq : UpcrossingData a b f n ω),
      hseq.t (2 * n - 1) ≤ upperCrossingTime a b f N n ω →
      ∃ hseq' : UpcrossingData a b f (n+1) ω,
        -- hseq'.toShorter = hseq ∧
        hseq'.t (2 * n + 1) ≤ upperCrossingTime a b f N (n+1) ω := by
  intro n hup hseq htu'
  set u' := upperCrossingTime a b f N n ω with hu'
  set s := hseq.t (2 * n - 2) with hs
  set t := hseq.t (2 * n - 1) with ht
  set u := upperCrossingTime a b f N (n + 1) ω with hu
  have hu_lt_N : hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f u' N ω) N ω < N :=
    by simpa [upperCrossingTime] using hup
  rcases upcrossingData_of_upperCrossingTime_lt a b f u' N ω hu_lt_N with
    ⟨s', t', hu's', hs't', ht'u, hfs', hft'⟩
  let hseq' : UpcrossingData a b f (n + 1) ω :=
    hseq.extend s' t' (le_trans htu' hu's') hs't' hfs' hft'
  use hseq'
  have ht2n1 : hseq'.t (2 * n + 1) = t' := by
    simp only [hseq', UpcrossingData.extend_t]
  simp only [ht2n1];
  exact ht'u

lemma ltUpcrossingsBefore_of_upperCrossingTime_lt [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b) :
    upperCrossingTime a b f N n ω < N → ltUpcrossingsBefore a b f N n ω := by
  by_cases h : N ≤ ⊥
  · exact (upperCrossingTime_lt_bot_iff_ltUpcrossingsBefore a b f N n ω h).mpr
  · simp only [ltUpcrossingsBefore, h, if_false]
    by_cases hnzero : n = 0
    · -- n = 0 case
      subst hnzero; simp_all
    · -- n ≥ 1 case
      simp only [if_neg hnzero]
      intro hup




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
  · intro hlt
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
          { hab := hab,
            s := fun k => lowerCrossingTime a b f N k ω
            t := fun k => upperCrossingTime a b f N (k + 1) ω
            si_le_ti := by
              intro k hk
              have hle : lowerCrossingTime a b f N k ω ≤
                  upperCrossingTime a b f N (k + 1) ω :=
                lowerCrossingTime_le_upperCrossingTime_succ (a:=a) (b:=b) (f:=f) (N:=N)
                  (n:=k) (ω:=ω)
              exact hle
            fs_le_a := fun k hk => by
              have h := h_s_mem k hk
              simpa [Set.mem_Iic] using h
            ft_ge_b := fun k hk => by
              have h := h_t_mem k hk
              simpa [Set.mem_Ici] using h
            ti_le_sj := by
              intro i j hij hj
              have hi1_le_j : i + 1 ≤ j := Nat.succ_le_of_lt hij
              have hj_le_m : j ≤ m := Nat.lt_succ_iff.mp hj
              have hi1_le_m : i + 1 ≤ m := le_trans hi1_le_j hj_le_m
              have hti_le_si1 : upperCrossingTime a b f N (i + 1) ω ≤
                  lowerCrossingTime a b f N (i + 1) ω :=
                upperCrossingTime_le_lowerCrossingTime (a:=a) (b:=b) (f:=f) (N:=N) (n:=i+1) (ω:=ω)
              have hsi1_le_sj : lowerCrossingTime a b f N (i + 1) ω ≤
                  lowerCrossingTime a b f N j ω :=
                lowerCrossingTime_mono hi1_le_j
              exact le_trans hti_le_si1 hsi1_le_sj }
          refine ⟨seq, ?_⟩
          simpa using h_upper

/-!
TODO next:
  1) The upcrossingsBefore' - upcrossing number before N defined via sSup of ltUpcrossingsBefore,
  is equal to the original definition via sSup of upperCrossingTime < N.
  2) The upcrossingsBefore' is measurable (for ConditionallyCompleteLinearOrderBot ι), using
  the equivalence above and measurability of upperCrossingTime.
  3) The upcrossingsBefore' is monotone (weakly) in the index set, i.e.,
  for f : ι → κ monotone, upcrossingsBefore' a b u N ω ≤ upcrossingsBefore' a b v (f N) ω,
  where v (f i) = u i. On finite ι, this follows from the equivalence above and
  the upperCrossingTime_antimono_index_set proved in HittingTime.lean.
  But as we shall compare upcrossingsBefore' on finite and countable sets T ⊆ ι,
  we need to go through the UpcrossingData.
  4) For a countable set T of indices ι (T : Set ι), we can approximate the upcrossingsBefore'
  on T by upcrossingsBefore' on finite subsets of T; (monotone - by 3.) convergence.
  5) The above is the sketch of the proof of Doob's upcrossing inequality on countable index sets.
-/

-/
