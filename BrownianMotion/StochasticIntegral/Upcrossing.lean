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

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

-- structure UpcrossingData (a b : ℝ) (f : ι → Ω → ℝ) (n : ℕ) (ω : Ω) where
--   s t : ℕ → ι
--   hlt  : ∀ i : Fin n, s i < t i
--   hle  : ∀ i : Fin n, f (s i) ω ≤ a
--   hge  : ∀ i : Fin n, f (t i) ω ≥ b
--   chain : ∀ i j : Fin n, i < j → t i < s j

-- def nUpcrossings (a b : ℝ) (f : ι → Ω → ℝ) (n : ℕ) (ω : Ω) : Prop :=
--   ∃ d : UpcrossingData a b f n ω, True   -- or just `Nonempty (UpcrossingData …)`

-- def ltUpcrossingsBefore (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) : Prop :=
--   if N ≤ ⊥ then False else
--     if n = 0 then True else
--       ∃ d : UpcrossingData a b f n ω, d.t (n-1) < N

/-
  Equivalent definition that skips `[InfSet ι]`:
  ltUpcrossingsBefore a b f N n ω ↔ upperCrossingTime a b f N n ω < N).
-/
noncomputable def ltUpcrossingsBefore [LinearOrder ι] [OrderBot ι] (a b : ℝ) (f : ι → Ω → ℝ)
  (N : ι) (n : ℕ) (ω : Ω) : Prop :=
  if N ≤ ⊥ then False else
    if n = 0 then True else
      ∃ s t : Nat → ι,
        (∀ i : Fin n, s i < t i) ∧
        (∀ i : Fin n, f (s i) ω ≤ a) ∧
        (∀ i : Fin n, f (t i) ω ≥ b) ∧
        (∀ i j : Fin n, i < j → t i < s j) ∧
        t (n - 1) < N

noncomputable def upcrossingsBefore' [LinearOrder ι] [OrderBot ι] (a b : ℝ) (f : ι → Ω → ℝ)
  (N : ι) (ω : Ω) : ℕ :=
  sSup {n | ltUpcrossingsBefore a b f N n ω}

-- lemma ltUpcrossingsBefore_iff_upperCrossingTime_lt [ConditionallyCompleteLinearOrderBot ι]
--   [WellFoundedLT ι]
--   (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b)
--   (ltUpcrossingsBefore a b f N n ω):
--     upperCrossingTime a b f N n ω ≤ ltUpcrossingsBefore a b f N n ω   := by


lemma ltUpcrossingsBefore_iff_upperCrossingTime_lt [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b) :
    ltUpcrossingsBefore a b f N n ω ↔ upperCrossingTime a b f N n ω < N := by
  by_cases h : N ≤ ⊥
  · have : ⊥ ≤ N := OrderBot.bot_le N
    have hNbot : N = ⊥ := le_antisymm h this
    subst hNbot
    simp only [ltUpcrossingsBefore]; simp
  · simp only [ltUpcrossingsBefore, h, if_false]
    induction n
    case neg.zero => simp; grind
    case neg.succ n ih =>
      simp only [if_neg (Nat.succ_ne_zero n)]; simp
      by_cases hnzero : n = 0
      -- The induction step for n = 0:
      · subst hnzero; simp
        constructor
        · intro hupcross
          obtain ⟨s, t, hs0_lt_t0, hs0_le_a, ht0_ge_b, ht0_lt_N⟩ := hupcross
          set s0 : ι := s 0 with hs0
          set t0 : ι := t 0 with ht0
          have hs0_lt_N : s0 < N := by grind
          simp only [upperCrossingTime]; simp
          set pre_s0 := lowerCrossingTimeAux a f ⊥ N ω with hlower
          have h_lower : pre_s0 ≤ s0 := by
            simp only [pre_s0, lowerCrossingTimeAux]
            have h_exists : ∃ j ∈ Set.Icc ⊥ N, f j ω ∈ Set.Iic a := by
              use s0; simp; exact ⟨le_of_lt hs0_lt_N, hs0_le_a⟩
            simp only [hittingBtwn, h_exists, if_true]
            set s := Set.Icc ⊥ N ∩ { i | f i ω ∈ Set.Iic a } with hs
            have : s0 ∈ s := by simp [hs]; exact ⟨le_of_lt hs0_lt_N, hs0_le_a⟩
            exact csInf_le' this
          set pre_t0 := hittingBtwn f (Set.Ici b) pre_s0 N ω with hhit_lower
          set pre_t0' := hittingBtwn f (Set.Ici b) s0 N ω with hhit_s0
          have h_hit_mono : pre_t0 ≤ pre_t0' := by
            apply hittingBtwn_mono_left f (Set.Ici b) pre_s0 s0 N
            exact h_lower
          show pre_t0 < N
          have hpre_t0_lt_N : pre_t0' < N := by
            simp only [hhit_s0, hittingBtwn]
            have hs0t0 : s0 ≤ t0 ∧ t0 ≤ N := ⟨le_of_lt hs0_lt_t0, le_of_lt ht0_lt_N⟩
            have h_exists : ∃ j ∈ Set.Icc s0 N, f j ω ∈ Set.Ici b := by
              use t0; simp; exact ⟨hs0t0, ht0_ge_b⟩
            simp only [h_exists, if_true]
            set s := Set.Icc s0 N ∩ { i | f i ω ∈ Set.Ici b } with hs
            have : t0 ∈ s := by simp [hs]; exact ⟨hs0t0, ht0_ge_b⟩
            have := csInf_le' this
            grind
          exact Std.lt_of_le_of_lt h_hit_mono hpre_t0_lt_N
        · intro ht0_lt_N
          simp only [upperCrossingTime] at ht0_lt_N; simp at ht0_lt_N
          set s0 : ι := lowerCrossingTimeAux a f ⊥ N ω with hs0
          set t0 : ι := hittingBtwn f (Set.Ici b) s0 N ω with ht0
          have hs0_le_N : s0 ≤ N := by
            simp only [hs0, lowerCrossingTimeAux]
            exact hittingBtwn_le (u := f) (s := Set.Iic a) (n := ⊥) (m := N) (ω := ω)
          have hs0_le_t0 : s0 ≤ t0 := by
            simp only [ht0]
            exact le_hittingBtwn (u := f) (s := Set.Ici b) (n := s0) (m := N) hs0_le_N (ω := ω)
          have hf_t0_ge_b : f t0 ω ≥ b := by
            have hl : hittingBtwn f (Set.Ici b) s0 N ω < N := by grind
            exact hittingBtwn_mem_set_of_hittingBtwn_lt
              (u := f) (s := Set.Ici b) (n := s0) (ω := ω) (m := N) hl
          have hf_s0_le_a : f s0 ω ≤ a := by
            simp only [hs0, lowerCrossingTimeAux]
            rw [lowerCrossingTimeAux] at hs0
            exact hittingBtwn_mem_set_of_hittingBtwn_lt
              (u := f) (s := Set.Iic a) (n := ⊥) (ω := ω) (m := N) (lt_of_le_of_lt hs0_le_t0 ht0_lt_N)
          have hs0_lt_t0 : s0 < t0 := by grind
          let s : Nat → ι := fun i => if i = 0 then s0 else ⊥
          let t : Nat → ι := fun i => if i = 0 then t0 else ⊥
          use s, t
          exact ⟨hs0_lt_t0, hf_s0_le_a, hf_t0_ge_b, ht0_lt_N⟩
      · -- Now, n ≥ 1 and we show the induction step again:
        simp only [if_neg hnzero] at ih
        constructor
        · intro hupcross
          obtain ⟨s, t, hs_lt_t, hfs_le_a, hft_ge_b, hts, htn_lt_N⟩ := hupcross
          set sn : ι := s (Fin.last n) with hsn
          set tn : ι := t (Fin.last n) with htn
          sorry
