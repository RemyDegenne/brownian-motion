/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Wojciech Czernous
-/
import BrownianMotion.Auxiliary.Martingale
import BrownianMotion.StochasticIntegral.Cadlag
import Mathlib.Data.Finset.Sort
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Topology.Defs.Filter

/-! # Doob's upcrossing inequality on NNRat

-/

open MeasureTheory Filter Finset Function
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

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

structure UpcrossingData [PartialOrder ι] (a b : ℝ) (f : ι → Ω → ℝ) (n : ℕ) (ω : Ω) where
  hab : a < b
  t : ℕ → ι
  mono: Monotone t
  ft_le_a  : ∀ i : ℕ, i < 2 * n → Even i → f (t i) ω ≤ a
  ft_ge_b  : ∀ i : ℕ, i < 2 * n → Odd i → f (t i) ω ≥ b

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

lemma t_strict_mono' {i j} (hij : i < j) (hj : j < 2 * n) : h.t i < h.t j := by
  have hi1n : i + 1 < 2 * n := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hij) hj
  have hti : h.t i < h.t (i + 1) := lt_of_le_of_ne (h.mono (Nat.le_succ i)) (h.ti_ne_ti1 hi1n)
  exact lt_of_lt_of_le hti (h.mono (Nat.succ_le_of_lt hij))

def t_on_Fin2n : Fin (2 * n) → ι := fun x => h.t x.toNat

lemma t_strict_mono_on_Fin2n : StrictMono h.t_on_Fin2n := by
  intro x y hxy
  exact h.t_strict_mono' hxy y.isLt

def toShorter {a b : ℝ} {f : ι → Ω → ℝ} {n : ℕ} {ω : Ω} (h : UpcrossingData a b f (n + 1) ω) :
    UpcrossingData a b f n ω := ⟨ h.hab, h.t, h.mono,
    fun i hi hi_even => h.ft_le_a i (by grind) hi_even,
    fun i hi hi_odd => h.ft_ge_b i (by grind) hi_odd ⟩

def extend {a b : ℝ} {f : ι → Ω → ℝ} {n : ℕ} {ω : Ω}
    (h : UpcrossingData a b f n ω)
    (s t : ι)
    (hus : h.t (2 * n - 1) ≤ s)
    (hst : s ≤ t)
    (hfs : f s ω ∈ Set.Iic a)
    (hft : f t ω ∈ Set.Ici b) :
    UpcrossingData a b f (n + 1) ω :=
  ⟨h.hab, fun i => if i < 2 * n then h.t i else if i = 2 * n then s else t,
  by
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
  fun i hi he => if hn : i < 2 * n then by simp only [hn, if_true]; exact h.ft_le_a i (by grind) he
    else by simp only [hn, if_false]; grind,
  fun i hi ho => if hn : i < 2 * n then by simp only [hn, if_true]; exact h.ft_ge_b i (by grind) ho
    else by simp only [hn, if_false]; grind
  ⟩

lemma extend_t {a b : ℝ} {f : ι → Ω → ℝ} {n : ℕ} {ω : Ω}
    (h : UpcrossingData a b f n ω)
    (s t : ι)
    (hus : h.t (2 * n - 1) ≤ s)
    (hst : s ≤ t)
    (hfs : f s ω ∈ Set.Iic a)
    (hft : f t ω ∈ Set.Ici b) :
    (h.extend s t hus hst hfs hft).t (2 * n + 1) = t := by simp only [UpcrossingData.extend]; simp

end UpcrossingData

/-! The `ltUpcrossingsBefore a b f N n ω` is shortened as `L n`. -/
noncomputable def ltUpcrossingsBefore [LinearOrder ι] [OrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) : Prop :=
  if N ≤ ⊥ then False else -- to make {n | ...} empty when N = ⊥, same as in upperCrossingTime
    if n = 0 then True else
      ∃ seq : UpcrossingData a b f n ω, seq.t (2 * n - 1) < N

/-- The number of - alternatively defined - upcrossings (strictly) before time `N`. -/
noncomputable def upcrossingsBefore' [LinearOrder ι] [OrderBot ι] (a b : ℝ) (f : ι → Ω → ℝ)
    (N : ι) (ω : Ω) : ℕ :=
  sSup {n | ltUpcrossingsBefore a b f N n ω}

lemma upcrossingsBefore'_eq_zero_of_not_hab [LinearOrder ι] [OrderBot ι]
    {a b : ℝ} {f : ι → Ω → ℝ} {N : ι} {ω : Ω}
    (hab : ¬ a < b) : upcrossingsBefore' a b f N ω = 0 := by
  simp only [upcrossingsBefore', ltUpcrossingsBefore]
  rcases le_or_gt N ⊥ with hN | hN
  · simp_all
  · have : ¬ N ≤ ⊥ := by grind
    simp only [this, if_false]
    have : ∀ n, ¬ (∃ seq : UpcrossingData a b f n ω, seq.t (2 * n - 1) < N) :=
      fun _ ⟨seq, _⟩ => hab seq.hab
    simp only [this]; simp_all

/-! ltUpcrossingsBefore a b f N n ω ↔ upperCrossingTime a b f N n ω < N -/
section UpperCrossingTimeEquivalence

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
  rcases le_or_gt N ⊥ with hN | hN
  · simp only [upperCrossingTimeLT, hN, if_true]
    exact iff_of_false (fun h => h) (not_lt.mpr (le_trans hN bot_le))
  · simp only [upperCrossingTimeLT, not_le.mpr hN, if_false]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [upperCrossingTime, hN]
    · simp [hn]

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
  rcases eq_or_ne n 0 with rfl | hn
  · simp; grind
  · simp only [if_neg hn]
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
  rcases eq_or_ne n 0 with rfl | hn
  · simp_all
  · simp only [hn]
    intro h ⟨hseq, ht_le⟩
    use hseq
    simp only [upperCrossingTimeLT] at h
    refine lt_of_le_of_lt ht_le ?_
    simp_all


/-- Bundled properties of `hittingBtwn` that hold under `WellFoundedLT` but may also
be established under weaker assumptions (e.g., finiteness of the index set, or
right-continuity of trajectories for `ℝ≥0`). -/
structure HittingBtwnSpec [Preorder ι] [OrderBot ι] [InfSet ι]
    (f : ι → Ω → ℝ) (s : Set ℝ) (n m : ι) (ω : Ω) where
  /-- When the hitting time is strictly less than `m`, it actually hits the set. -/
  hitsSet : hittingBtwn f s n m ω < m → f (hittingBtwn f s n m ω) ω ∈ s

namespace HittingBtwnSpec

variable [ConditionallyCompleteLinearOrderBot ι]
variable {f : ι → Ω → ℝ} {s : Set ℝ} {n m : ι} {ω : Ω}

/-- If the hitting time is less than `i`, the hitting time itself is a witness in `[n, i)`. -/
lemma lt_exists_witness (hspec : HittingBtwnSpec f s n m ω) (i : ι) (hi : i ≤ m)
    (hlt : hittingBtwn f s n m ω < i) : ∃ j ∈ Set.Ico n i, f j ω ∈ s := by
  have htm : hittingBtwn f s n m ω < m := lt_of_lt_of_le hlt hi
  have hfhit : f (hittingBtwn f s n m ω) ω ∈ s := hspec.hitsSet htm
  set h := hittingBtwn f s n m ω with hdef
  have hle : h ≤ m := hittingBtwn_le ω
  -- If hittingBtwn < m, there must exist a hit in [n, m] (otherwise hittingBtwn = m)
  have h_exists : ∃ j ∈ Set.Icc n m, f j ω ∈ s := by
    by_contra h_neg
    simp only [hittingBtwn, h_neg, ↓reduceIte] at hdef
    exact (lt_irrefl m (hdef ▸ htm))
  exact ⟨h, ⟨le_hittingBtwn_of_exists h_exists, hlt⟩, hfhit⟩

end HittingBtwnSpec

/-- `WellFoundedLT` provides a `HittingBtwnSpec`. -/
lemma hittingBtwnSpec_of_wellFoundedLT [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι]
    (f : ι → Ω → ℝ) (s : Set ℝ) (n m : ι) (ω : Ω) : HittingBtwnSpec f s n m ω :=
  ⟨hittingBtwn_mem_set_of_hittingBtwn_lt⟩

private lemma nondegenerate_of_hittingBtwn_lt' [ConditionallyCompleteLinearOrderBot ι]
    (u : ι → Ω → ℝ) (s : Set ℝ) (n m : ι) (ω : Ω)
    (hspec : HittingBtwnSpec u s n m ω)
    (hl : hittingBtwn u s n m ω < m) :
    n < m := by
  have h := hspec.lt_exists_witness m (le_refl m) hl
  obtain ⟨j, hjIco, _⟩ := h
  exact lt_of_le_of_lt hjIco.1 hjIco.2

private lemma nondegenerate_of_hittingBtwn_lt [ConditionallyCompleteLinearOrderBot ι]
    [WellFoundedLT ι] (u : ι → Ω → ℝ) (s : Set ℝ) (n m : ι) (ω : Ω)
    (hl : hittingBtwn u s n m ω < m) :
    n < m :=
  nondegenerate_of_hittingBtwn_lt' u s n m ω (hittingBtwnSpec_of_wellFoundedLT u s n m ω) hl

/-! P n gives a pair of witnesses, useful for establishing Q n. -/
lemma upcrossingData_of_upperCrossingTimeLT' [ConditionallyCompleteLinearOrderBot ι]
    (a b : ℝ) (f : ι → Ω → ℝ) (m N : ι) (ω : Ω)
    (hspecIci : ∀ n, HittingBtwnSpec f (Set.Ici b) n N ω)
    (hspecIic : ∀ n, HittingBtwnSpec f (Set.Iic a) n N ω) :
    hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f m N ω) N ω < N →
    ∃ s t : ι, m ≤ s ∧ s ≤ t
    ∧ t ≤ hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f m N ω) N ω
    ∧ f s ω ∈ Set.Iic a ∧ f t ω ∈ Set.Ici b := by
  intro ht_lt_N
  set s := lowerCrossingTimeAux a f m N ω with hs
  set t := hittingBtwn f (Set.Ici b) s N ω with ht
  use s, t
  have hft : f t ω ∈ Set.Ici b := (hspecIci s).hitsSet ht_lt_N
  have hsN : s < N := nondegenerate_of_hittingBtwn_lt' f (Set.Ici b) s N ω (hspecIci s) ht_lt_N
  simp only [lowerCrossingTimeAux] at hs
  have hfs : f s ω ∈ Set.Iic a := (hspecIic m).hitsSet hsN
  have hms : m ≤ s := le_hittingBtwn
    (le_of_lt <| nondegenerate_of_hittingBtwn_lt' f (Set.Iic a) m N ω (hspecIic m) hsN) ω
  have hsltt : s ≤ t := le_hittingBtwn (le_of_lt hsN) ω
  simp_all

lemma upcrossingData_of_upperCrossingTimeLT [ConditionallyCompleteLinearOrderBot ι]
    [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (m N : ι) (ω : Ω) :
    hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f m N ω) N ω < N →
    ∃ s t : ι, m ≤ s ∧ s ≤ t
    ∧ t ≤ hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f m N ω) N ω
    ∧ f s ω ∈ Set.Iic a ∧ f t ω ∈ Set.Ici b :=
  upcrossingData_of_upperCrossingTimeLT' a b f m N ω
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Ici b) n N ω)
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Iic a) n N ω)

/-! P 1 → Q 1, in the case N ≠ ⊥. -/
lemma upcrossingData_of_first_upperCrossingTimeLT' [ConditionallyCompleteLinearOrderBot ι]
    (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) (hab : a < b) (hN : ¬ N ≤ ⊥)
    (hspecIci : ∀ n, HittingBtwnSpec f (Set.Ici b) n N ω)
    (hspecIic : ∀ n, HittingBtwnSpec f (Set.Iic a) n N ω) :
    upperCrossingTimeLT a b f N 1 ω → upcrossingsBeforeUpperCrossingTime a b f N 1 ω := by
  intro hup
  set m := upperCrossingTime a b f N 0 ω with hm
  have hm_bot : m = ⊥ := rfl
  rw [upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N 1 ω] at hup
  have : hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f m N ω) N ω < N :=
    by simpa [upperCrossingTime] using hup
  rcases upcrossingData_of_upperCrossingTimeLT' a b f m N ω hspecIci hspecIic this with
    ⟨s, t, hm_s, hs_t, ht_u, hfs, hft⟩
  let hseq : UpcrossingData a b f 1 ω := ⟨hab, fun i => if i = 0 then s else t,
    fun i j hij => if i = 0 then by grind else by grind, by grind, by grind⟩
  simp only [upcrossingsBeforeUpperCrossingTime, hN, if_false]
  use hseq
  have ht1 : hseq.t 1 = t := by simp only [hseq]; simp
  simp only [ht1]
  exact ht_u

lemma upcrossingData_of_first_upperCrossingTimeLT [ConditionallyCompleteLinearOrderBot ι]
    [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) (hab : a < b) (hN : ¬ N ≤ ⊥) :
    upperCrossingTimeLT a b f N 1 ω → upcrossingsBeforeUpperCrossingTime a b f N 1 ω :=
  upcrossingData_of_first_upperCrossingTimeLT' a b f N ω hab hN
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Ici b) n N ω)
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Iic a) n N ω)

/-! P (n+1) → Q n → Q (n+1), in the case N ≠ ⊥. -/
lemma upcrossingData_extend_of_upperCrossingTimeLT' [ConditionallyCompleteLinearOrderBot ι]
    (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) (hN : ¬ N ≤ ⊥)
    (hspecIci : ∀ n, HittingBtwnSpec f (Set.Ici b) n N ω)
    (hspecIic : ∀ n, HittingBtwnSpec f (Set.Iic a) n N ω) :
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
  rcases upcrossingData_of_upperCrossingTimeLT' a b f u' N ω hspecIci hspecIic hu_lt_N with
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

lemma upcrossingData_extend_of_upperCrossingTimeLT [ConditionallyCompleteLinearOrderBot ι]
    [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) (hN : ¬ N ≤ ⊥) :
  ∀ n ≥ 1, (upperCrossingTimeLT a b f N (n+1) ω →
    upcrossingsBeforeUpperCrossingTime a b f N n ω →
      upcrossingsBeforeUpperCrossingTime a b f N (n+1) ω) :=
  upcrossingData_extend_of_upperCrossingTimeLT' a b f N ω hN
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Ici b) n N ω)
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Iic a) n N ω)

/-! P (n+1) → P n. -/
lemma upperCrossingTimeLT_of_upperCrossingTimeLT [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) :
  upperCrossingTimeLT a b f N (n+1) ω → upperCrossingTimeLT a b f N n ω := by
  intro hup
  rw [upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N (n+1) ω] at hup
  rw [upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N n ω]
  refine lt_of_le_of_lt ?_ hup
  exact upperCrossingTime_mono (Nat.le_succ n)

/-! ∀ n ≥ 1, P n → Q n, in the case N ≠ ⊥. -/
lemma upcrossingsBeforeUpperCrossingTime_of_upperCrossingTimeLT_all'
  [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω)
  (hab : a < b) (hn : n ≥ 1) (hNbot : ¬ N ≤ ⊥)
  (hspecIci : ∀ n, HittingBtwnSpec f (Set.Ici b) n N ω)
  (hspecIic : ∀ n, HittingBtwnSpec f (Set.Iic a) n N ω) :
    upperCrossingTimeLT a b f N n ω → upcrossingsBeforeUpperCrossingTime a b f N n ω := by
  induction n with
  | zero =>
      intro h; linarith
  | succ n ih =>
      intro hup
      rcases eq_or_ne n 0 with rfl | hn
      · exact upcrossingData_of_first_upperCrossingTimeLT' a b f N ω hab hNbot hspecIci hspecIic hup
      · have hn1 : n ≥ 1 := by grind
        simp only [hn1] at ih; simp at ih
        have hPn := upperCrossingTimeLT_of_upperCrossingTimeLT a b f N n ω hup
        refine upcrossingData_extend_of_upperCrossingTimeLT'
          a b f N ω hNbot hspecIci hspecIic n hn1 hup ?_
        simp_all

lemma upcrossingsBeforeUpperCrossingTime_of_upperCrossingTimeLT_all
  [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω)
  (hab : a < b) (hn : n ≥ 1) (hNbot : ¬ N ≤ ⊥) :
    upperCrossingTimeLT a b f N n ω → upcrossingsBeforeUpperCrossingTime a b f N n ω :=
  upcrossingsBeforeUpperCrossingTime_of_upperCrossingTimeLT_all' a b f N n ω hab hn hNbot
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Ici b) n N ω)
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Iic a) n N ω)

/-! The right implication: ∀ n, P n → L n, in the case N ≠ ⊥. -/
lemma ltUpcrossingsBefore_of_upperCrossingTimeLT' [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b) (hN : ¬ N ≤ ⊥)
  (hspecIci : ∀ n, HittingBtwnSpec f (Set.Ici b) n N ω)
  (hspecIic : ∀ n, HittingBtwnSpec f (Set.Iic a) n N ω) :
    upperCrossingTimeLT a b f N n ω → ltUpcrossingsBefore a b f N n ω := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ltUpcrossingsBefore, hN]; simp_all
  · intro hup
    refine ltUpcrossingsBefore_of_upcrossingsBeforeUpperCrossingTime_of_upperCrossingTimeLT
      a b f N n ω hN hup ?_
    exact upcrossingsBeforeUpperCrossingTime_of_upperCrossingTimeLT_all'
      a b f N n ω hab (by grind) (by simp_all) hspecIci hspecIic hup

lemma ltUpcrossingsBefore_of_upperCrossingTimeLT [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b) (hN : ¬ N ≤ ⊥) :
    upperCrossingTimeLT a b f N n ω → ltUpcrossingsBefore a b f N n ω :=
  ltUpcrossingsBefore_of_upperCrossingTimeLT' a b f N n ω hab hN
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Ici b) n N ω)
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Iic a) n N ω)

/-! Finally, the equivalence ∀ n, P n ↔ L n. -/
theorem upperCrossingTimeLT_iff_ltUpcrossingsBefore' [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b)
  (hspecIci : ∀ n, HittingBtwnSpec f (Set.Ici b) n N ω)
  (hspecIic : ∀ n, HittingBtwnSpec f (Set.Iic a) n N ω) :
    upperCrossingTimeLT a b f N n ω ↔ ltUpcrossingsBefore a b f N n ω := by
  rcases le_or_gt N ⊥ with hN | hN
  · exact upperCrossingTimeLT_bot_iff_ltUpcrossingsBefore a b f N n ω hN
  · exact ⟨ltUpcrossingsBefore_of_upperCrossingTimeLT'
            a b f N n ω hab (not_le.mpr hN) hspecIci hspecIic,
            upperCrossingTimeLT_of_ltUpcrossingsBefore a b f N n ω (not_le.mpr hN)⟩

theorem upperCrossingTimeLT_iff_ltUpcrossingsBefore [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b) :
    upperCrossingTimeLT a b f N n ω ↔ ltUpcrossingsBefore a b f N n ω :=
  upperCrossingTimeLT_iff_ltUpcrossingsBefore' a b f N n ω hab
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Ici b) n N ω)
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Iic a) n N ω)

/-! Auxiliary lemma. -/
lemma upperCrossingTime_lt_iff_ltUpcrossingsBefore' [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b)
  (hspecIci : ∀ n, HittingBtwnSpec f (Set.Ici b) n N ω)
  (hspecIic : ∀ n, HittingBtwnSpec f (Set.Iic a) n N ω) :
    upperCrossingTime a b f N n ω < N ↔ ltUpcrossingsBefore a b f N n ω := by
  rw [← upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N n ω]
  exact upperCrossingTimeLT_iff_ltUpcrossingsBefore' a b f N n ω hab hspecIci hspecIic

lemma upperCrossingTime_lt_iff_ltUpcrossingsBefore [ConditionallyCompleteLinearOrderBot ι]
  [WellFoundedLT ι] (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b) :
    upperCrossingTime a b f N n ω < N ↔ ltUpcrossingsBefore a b f N n ω :=
  upperCrossingTime_lt_iff_ltUpcrossingsBefore' a b f N n ω hab
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Ici b) n N ω)
    (fun n => hittingBtwnSpec_of_wellFoundedLT f (Set.Iic a) n N ω)

lemma upcrossingsBefore'_zero_of_N_bot [LinearOrder ι] [OrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) (hN : N ≤ ⊥) :
    upcrossingsBefore' a b f N ω = 0 := by
  simp only [upcrossingsBefore', ltUpcrossingsBefore, hN, if_true]; simp

/-! The two definitions of upcrossingsBefore are equivalent. -/
theorem upcrossingsBefore_eq_upcrossingsBefore''
  [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (hab : a < b)
  (hspecIci : ∀ n ω, HittingBtwnSpec f (Set.Ici b) n N ω)
  (hspecIic : ∀ n ω, HittingBtwnSpec f (Set.Iic a) n N ω) :
    upcrossingsBefore a b f N = upcrossingsBefore' a b f N := by
  ext ω
  simp only [upcrossingsBefore, upcrossingsBefore']
  congr 1
  ext n
  exact upperCrossingTime_lt_iff_ltUpcrossingsBefore' a b f N n ω hab (hspecIci · ω) (hspecIic · ω)

theorem upcrossingsBefore_eq_upcrossingsBefore'
  [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (hab : a < b) :
    upcrossingsBefore a b f N = upcrossingsBefore' a b f N :=
  upcrossingsBefore_eq_upcrossingsBefore'' a b f N hab
    (fun n ω => hittingBtwnSpec_of_wellFoundedLT f (Set.Ici b) n N ω)
    (fun n ω => hittingBtwnSpec_of_wellFoundedLT f (Set.Iic a) n N ω)

end UpperCrossingTimeEquivalence

/-! Suffices to show monotonicity for `Finite` index sets - the comparison with `NNRat`, as
  needed in the `theorem lintegral_iSup'`, is via `⊔`.
  -- Not really. We need to derive Doob's upcrossing inequality for finite index sets,
  from its version for Nat. Besides, we need to compare with `NNRat` to establish convergence.
-/
section MonotonicityAndBoundedness

variable [LinearOrder ι]

/-! Given a finite {i | i < N}, size of UpcrossingData is bounded, assuming UpcrossingData < N. -/
lemma upcrossingData_bounded_of_finite (a b : ℝ) (f : ι → Ω → ℝ) (N : ι)
    (hfin : Finite {i | i < N}) :
    ∃ M : ℕ,  ∀ n ω, ∀ hseq : UpcrossingData a b f n ω,
      hseq.t (2 * n - 1) < N → 2 * n ≤ M := by
  set s := {i | i < N}
  letI := Fintype.ofFinite s
  refine ⟨Fintype.card s, fun n ω hseq ht_lt_N => ?_⟩
  have h : ∀ i : Fin (2 * n), hseq.t i ∈ s := fun i =>
    lt_of_le_of_lt (hseq.mono (by grind)) ht_lt_N
  calc Fintype.card s ≥ Fintype.card (Fin (2 * n)) :=
      Fintype.card_le_of_injective (Set.codRestrict hseq.t_on_Fin2n s h)
        (hseq.t_strict_mono_on_Fin2n.injective.codRestrict h)
    _ = 2 * n := Fintype.card_fin _

variable [OrderBot ι]
variable {κ : Type*} [LinearOrder κ] [OrderBot κ]

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
    have hNIn : N ∈ {i | i ≤ N} := by simp
    have : f ⊥ < f N := hsmon (by simp) hNIn hN
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
      let hseqv : UpcrossingData a b v n ω := ⟨
          hab,
          fun i => if i < 2 * n then f (hseq.t i) else f N,
          fun i j hij => by
            by_cases hi : i < 2 * n
            · by_cases hj : j < 2 * n
              · simp only [hi, hj, if_true]; exact hmon (htIn i hi) (htIn j hj) (hseq.mono hij)
              · simp only [hi, hj, if_true, if_false]; exact hmon (htIn i hi) hNIn (by grind)
            · simp only [hi, if_false]; grind,
          fun i hi heven => by
            simp only [hi, if_true]
            rw [hv (hseq.t i) (htIn i hi)]
            exact hseq.ft_le_a i hi heven,
          fun i hi hodd => by
            simp only [hi, if_true]
            rw [hv (hseq.t i) (htIn i hi)]
            exact hseq.ft_ge_b i hi hodd ⟩
      use hseqv
      have htv_lt_fN : hseqv.t (2 * n - 1) < f N := by
        simp only [hseqv]
        have hnzero : 2 * n - 1 < 2 * n := by grind
        simp only [hnzero, if_true]
        exact hsmon (htIn (2 * n - 1) hnzero) hNIn ht_lt_N
      exact htv_lt_fN

/-! Uniform boundedness of ltUpcrossingsBefore, assuming {i | i < N} is finite. -/
lemma ltUpcrossingsBefore_unif_bdd_of_finite (a b : ℝ) (f : ι → Ω → ℝ) (N : ι)
    (hfin : Finite {i | i < N}) :
    ∃ M, ∀ n ω, ltUpcrossingsBefore a b f N n ω → n ≤ M := by
  by_cases hN : N ≤ ⊥
  · simp only [ltUpcrossingsBefore, hN, if_true]
    use 0
    intro n hn
    grind
  · obtain ⟨M, hMsize⟩ := upcrossingData_bounded_of_finite a b f N hfin
    use M
    intro n ω hn
    simp only [ltUpcrossingsBefore, hN, if_false] at hn
    by_cases hnzero : n = 0
    · simp only [hnzero]; grind
    · simp_all
      rcases hn with ⟨hseq, ht_lt_N⟩
      grind

lemma upcrossingsBefore'_bounded_of_finite (a b : ℝ) (f : ι → Ω → ℝ) (N : ι)
    (hfin : Finite {i | i < N}) :
    ∃ M, ∀ ω, upcrossingsBefore' a b f N ω ≤ M := by
  obtain ⟨M, hMsize⟩ := ltUpcrossingsBefore_unif_bdd_of_finite a b f N hfin
  use M
  intro ω
  simp only [upcrossingsBefore']
  exact csSup_le' fun n => hMsize n ω

/-! Boundedness of ltUpcrossingsBefore, assuming {i | i < N} is finite. -/
lemma ltUpcrossingsBefore_bddAbove_of_finite (a b : ℝ) (f : ι → Ω → ℝ) (ω : Ω) (N : ι)
    (hfin : Finite {i | i < N}) :
    BddAbove {n | ltUpcrossingsBefore a b f N n ω} := by
  obtain ⟨M, hMsize⟩ := ltUpcrossingsBefore_unif_bdd_of_finite a b f N hfin
  use M
  intro n hn
  grind

/-! Monotonicity of upcrossingsBefore' in the index set, assuming finitely many upcrossings. -/
lemma upcrossingsBefore'_mono_index_set_of_bounded (f : ι → κ)
    (N : ι) (hsmon : StrictMonoOn f {i | i ≤ N})
    (u : ι → Ω → ℝ) (v : κ → Ω → ℝ) (hv : ∀ i ≤ N, v (f i) = u i) -- u is a restriction of v to f(ι)
    (a b : ℝ) (ω : Ω) (hab : a < b)
    (hbdB : BddAbove {n | ltUpcrossingsBefore a b v (f N) n ω}) :
    -- u has less upcrossings than v, and (v · ω) has finitely many upcrossings before f N
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
    -- u has less upcrossings than v, and (v · ω) has finitely many points before f N
    upcrossingsBefore' a b u N ω ≤ upcrossingsBefore' a b v (f N) ω :=
  upcrossingsBefore'_mono_index_set_of_bounded f N hsmon u v hv a b ω hab <|
    ltUpcrossingsBefore_bddAbove_of_finite a b v ω (f N) hfin

end MonotonicityAndBoundedness

/-! To compare upcrossingsBefore' between NNRat and its finsets (with ⊥) and between them. -/
section UpcrossingsOnFinset

variable {κ : Type*} [LinearOrder κ] [OrderBot κ]
    {s : Finset κ} (hbot : ⊥ ∈ s)

/-! Assuming finitely many upcrossings along a trajectory, a subset of index set admits less. -/
theorem upcrossingsBefore'_ge_finset_of_bounded (N : s) (u : s → Ω → ℝ) (v : κ → Ω → ℝ)
    (hv : ∀ i : s, v i = u i) -- u is a restriction of v to s
    (a b : ℝ) (ω : Ω) (hab : a < b)
    (hfin : BddAbove {n | ltUpcrossingsBefore a b v N n ω}) :
    -- u has less upcrossings than v, and (v · ω) has finitely many upcrossings before f N
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    upcrossingsBefore' a b u N ω ≤ upcrossingsBefore' a b v N ω := by
  set f : s → κ := fun i => (i : κ) with hf
  have hsmon : StrictMonoOn f {i | i ≤ N} := by
    intro i hi j hj hij
    exact hij
  have hv' : ∀ i ≤ N, v (f i) = u i := by
    intro i hi
    rw [hf]
    exact hv i
  have hfN : f N = N := rfl
  rw [← hfN]
  convert upcrossingsBefore'_mono_index_set_of_bounded f N hsmon u v hv' a b ω hab hfin using 1

theorem upcrossingsBefore'_ge_finset {t : Finset κ} (hbots : ⊥ ∈ s) (hbott : ⊥ ∈ t) (hst : s ⊆ t)
    (N : s) (u : s → Ω → ℝ) (v : t → Ω → ℝ)
    (hv : ∀ i : s, v ⟨i, hst i.prop⟩ = u i) -- u is a restriction of v to s
    (a b : ℝ) (ω : Ω) (hab : a < b) :
    -- u has less upcrossings than v, and v has finite index set
    letI : OrderBot s := { bot := ⟨⊥, hbots⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    letI : OrderBot t := { bot := ⟨⊥, hbott⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    upcrossingsBefore' a b u N ω ≤ upcrossingsBefore' a b v ⟨N, hst N.prop⟩ ω := by
  letI : OrderBot s := { bot := ⟨⊥, hbots⟩, bot_le := fun ⟨_, _⟩ => bot_le }
  letI : OrderBot t := { bot := ⟨⊥, hbott⟩, bot_le := fun ⟨_, _⟩ => bot_le }
  -- The inclusion map from s into t
  set f : s → t := fun i => ⟨i, hst i.prop⟩ with hf
  have hsmon : StrictMonoOn f {i | i ≤ N} := by
    intro i _ j _ hij
    exact hij
  have hv' : ∀ i ≤ N, v (f i) = u i := fun i _ => hv i
  have hfN : f N = ⟨N, hst N.prop⟩ := rfl
  rw [← hfN]
  exact upcrossingsBefore'_mono_index_set_of_finite_till_N f N hsmon u v hv' a b ω hab inferInstance

end UpcrossingsOnFinset

section DoobInequalityNat

variable {a b : ℝ}

theorem mul_integral_upcrossingsBefore'_le_integral_pos_part_aux [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0} (N : ℕ)
    (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    (b - a) * μ[upcrossingsBefore' a b f N] ≤ μ[fun ω => (f N ω - a)⁺] := by
  have hgeq : upcrossingsBefore a b f N = upcrossingsBefore' a b f N := by
    rw [upcrossingsBefore_eq_upcrossingsBefore' a b f N hab]
  have hequiv : (b - a) * μ[upcrossingsBefore a b f N] ≤ μ[fun ω => (f N ω - a)⁺] :=
    mul_integral_upcrossingsBefore_le_integral_pos_part_aux hf hab
  rw [← hgeq]
  assumption

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
  ⟨ fun i => 𝓕 (Fin.clamp i n),
    fun i j hij => by
      refine 𝓕.mono ?_
      simp only [Fin.clamp, Fin.le_iff_val_le_val]
      exact min_le_min hij (Nat.le_refl _),
    fun i => Filtration.le 𝓕 (Fin.clamp i n) ⟩

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
    ∀ i ≤ N, v (Fin.clamp i n) = u i := fun i _ => by rw [hNatOfFin, Process.natOfFin]

lemma Process.natOfFin_eq' (u : Fin n → Ω → ℝ) (v : ℕ → Ω → ℝ)
    (hNatOfFin : v = Process.natOfFin u) (N : Fin n) :
    ∀ i ≤ N, v i.val = u i := fun i _ => by
  rw [hNatOfFin, Process.natOfFin, Fin.clamp.eq_of_fin n i]

lemma Process.natOfFin.upcrossingsBefore'_le (u : ℕ → Ω → ℝ) (v : Fin n → Ω → ℝ)
    (hNatOfFin : u = Process.natOfFin v) (N : ℕ) (a b : ℝ) (hab : a < b) (hNn : N < n) :
    upcrossingsBefore' a b u N ≤ upcrossingsBefore' a b v (Fin.clamp N n) := by
  set f : ℕ → Fin n := fun i => Fin.clamp i n with hf
  have hsmon : StrictMonoOn f {i | i ≤ N} := Fin.clamp.StrictMonoOn hNn
  have hv : ∀ i ≤ N, v (f i) = u i := Process.natOfFin_eq u v hNatOfFin N
  have hfin : Finite {i | i < f N} := by infer_instance
  intro ω
  exact upcrossingsBefore'_mono_index_set_of_finite_till_N f N hsmon u v hv a b ω hab hfin

lemma Process.natOfFin.upcrossingsBefore'_ge (u : Fin n → Ω → ℝ) (v : ℕ → Ω → ℝ)
    (hNatOfFin : v = Process.natOfFin u) (N : Fin n) (a b : ℝ) (hab : a < b) :
    upcrossingsBefore' a b u N ≤ upcrossingsBefore' a b v N := by
  set f : Fin n → ℕ := fun i => i.val with hf
  have hsmon : StrictMonoOn f {i | i ≤ N} := Fin.val.StrictMonoOn N
  have hv : ∀ i ≤ N, v (f i) = u i := Process.natOfFin_eq' u v hNatOfFin N
  have hfin : Finite {i | i < f N} := by infer_instance
  intro ω
  exact upcrossingsBefore'_mono_index_set_of_finite_till_N f N hsmon u v hv a b ω hab hfin

theorem Process.natOfFin.upcrossingsBefore'_eq (u : Fin n → Ω → ℝ) (v : ℕ → Ω → ℝ)
    (hNatOfFin : v = Process.natOfFin u) (N : Fin n) (a b : ℝ) (hab : a < b) :
    upcrossingsBefore' a b u N = upcrossingsBefore' a b v N := by
  apply le_antisymm
  · exact Process.natOfFin.upcrossingsBefore'_ge u v hNatOfFin N a b hab
  · conv_rhs => rw [(Fin.clamp.eq_of_fin n N).symm]
    exact Process.natOfFin.upcrossingsBefore'_le v u hNatOfFin N a b hab (N.isLt)

end FinToNat

section FinsetToFin

variable [LinearOrder ι]

variable {s : Finset ι} {k : ℕ} (hne : s.Nonempty) (hk : #s = k) -- (hbot : ⊥ ∈ s)

def Finset.orderIso : Fin k ≃o s := by exact Finset.orderIsoOfFin s hk

def Finset.FromFin : Fin k → s := fun n => Finset.orderIso hk n

def Finset.ToFin : s → Fin k := fun i => (Finset.orderIso hk).symm i

lemma Finset.FromFin.StrictMono : StrictMono (Finset.FromFin hk) :=
  OrderIso.strictMono (Finset.orderIso hk)

lemma Finset.ToFin.StrictMono : StrictMono (Finset.ToFin hk) :=
  OrderIso.strictMono (Finset.orderIso hk).symm

lemma Finset.FromFin.StrictMonoOn (N : Fin k) : StrictMonoOn (Finset.FromFin hk) {i | i ≤ N} :=
  (Finset.FromFin.StrictMono hk).strictMonoOn {i | i ≤ N}

lemma Finset.ToFin.StrictMonoOn (N : s) : StrictMonoOn (Finset.ToFin hk) {i | i ≤ N} :=
  (Finset.ToFin.StrictMono hk).strictMonoOn {i | i ≤ N}

lemma Finset.FromFin.ToFin_eq (i : s) :
    Finset.FromFin hk (Finset.ToFin hk i) = i := by
  rw [Finset.ToFin, Finset.FromFin]
  exact OrderIso.apply_symm_apply (Finset.orderIso hk) i

def Filtration.finOfFinset (𝓕 : Filtration s m0) : Filtration (Fin k) m0 :=
  ⟨ fun i => 𝓕 (Finset.FromFin hk i),
    fun i j hij => by refine 𝓕.mono ?_; exact (Finset.FromFin.StrictMono hk).monotone hij,
    fun i => Filtration.le 𝓕 (Finset.FromFin hk i) ⟩

variable {𝓕 : Filtration s m0}

def Process.finOfFinset (u : s → Ω → ℝ) : Fin k → Ω → ℝ := fun i => u (Finset.FromFin hk i)

variable {u : s → Ω → ℝ} {N : s}

lemma Submartingale.finOfFinset (hf : Submartingale u 𝓕 μ) :
    Submartingale (Process.finOfFinset hk u) (Filtration.finOfFinset hk 𝓕) μ := by
  set u' : Fin k → Ω → ℝ := Process.finOfFinset hk u with hfFin
  set 𝓕' := Filtration.finOfFinset hk 𝓕
  have hadapted' : Adapted 𝓕' u' := fun i => by
    have hsm : StronglyMeasurable[𝓕 (Finset.FromFin hk i)] (u (Finset.FromFin hk i)) := by
      exact Submartingale.stronglyMeasurable hf (Finset.FromFin hk i)
    have hsm' : StronglyMeasurable[𝓕' i] (u' i) := by simp only [u', 𝓕']; exact hsm
    exact hsm'
  have hsub' : (∀ i j, i ≤ j → u' i ≤ᵐ[μ] μ[u' j|𝓕' i]) := fun i j hij => by
    simp only [u', 𝓕']
    refine Submartingale.ae_le_condExp hf ?_
    exact (Finset.FromFin.StrictMono hk).monotone hij
  have hint' : ∀ i, Integrable (u' i) μ := fun i => by
    simp only [u']
    exact Submartingale.integrable hf (Finset.FromFin hk i)
  exact ⟨ hadapted', hsub', hint' ⟩

lemma Process.finOfFinset_eq (u : s → Ω → ℝ) (v : Fin k → Ω → ℝ)
    (hFinOfFinset : v = Process.finOfFinset hk u) (N : s) :
    ∀ i ≤ N, v (Finset.ToFin hk i) = u i := fun i _ => by
  rw [hFinOfFinset, Process.finOfFinset, (Finset.FromFin.ToFin_eq hk i)]

lemma Process.finOfFinset_eq' (u : Fin k → Ω → ℝ) (v : s → Ω → ℝ)
    (hFinOfFinset : u = Process.finOfFinset hk v) (N : Fin k) :
    ∀ i ≤ N, v (Finset.FromFin hk i) = u i := fun i _ => by rw [hFinOfFinset, Process.finOfFinset]

variable [OrderBot ι] (hbot : ⊥ ∈ s) [NeZero k] -- to avoid issues with `Fin 0`

lemma Process.finOfFinset.upcrossingsBefore'_le (u : Fin k → Ω → ℝ) (v : s → Ω → ℝ)
    (hFinOfFinset : u = Process.finOfFinset hk v) (N : Fin k) (a b : ℝ) (hab : a < b) :
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    upcrossingsBefore' a b u N ≤ upcrossingsBefore' a b v (Finset.FromFin hk N) := by
  set f : Fin k → s := fun i => Finset.FromFin hk i with hf
  have hsmon : StrictMonoOn f {i | i ≤ N} := Finset.FromFin.StrictMonoOn hk N
  have hv : ∀ i ≤ N, v (f i) = u i := Process.finOfFinset_eq' hk u v hFinOfFinset N
  have hfin : Finite {i | i < f N} := by infer_instance
  intro ω
  convert upcrossingsBefore'_mono_index_set_of_finite_till_N f N hsmon u v hv a b ω hab hfin using 1

lemma Process.finOfFinset.upcrossingsBefore'_ge (u : s → Ω → ℝ) (v : Fin k → Ω → ℝ)
    (hFinOfFinset : v = Process.finOfFinset hk u) (N : s) (a b : ℝ) (hab : a < b) :
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    upcrossingsBefore' a b u N ≤ upcrossingsBefore' a b v (Finset.ToFin hk N) := by
  set f : s → Fin k := fun i => Finset.ToFin hk i with hf
  have hsmon : StrictMonoOn f {i | i ≤ N} := Finset.ToFin.StrictMonoOn hk N
  have hv : ∀ i ≤ N, v (f i) = u i := Process.finOfFinset_eq hk u v hFinOfFinset N
  have hfin : Finite {i | i < f N} := by infer_instance
  intro ω
  convert upcrossingsBefore'_mono_index_set_of_finite_till_N f N hsmon u v hv a b ω hab hfin using 1

theorem Process.finOfFinset.upcrossingsBefore'_eq (u : s → Ω → ℝ) (v : Fin k → Ω → ℝ)
    (hFinOfFinset : v = Process.finOfFinset hk u) (N : s) (a b : ℝ) (hab : a < b) :
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    upcrossingsBefore' a b u N = upcrossingsBefore' a b v (Finset.ToFin hk N) := by
  apply le_antisymm
  · exact Process.finOfFinset.upcrossingsBefore'_ge hk hbot u v hFinOfFinset N a b hab
  · set N' := Finset.ToFin hk N with hN'
    have hN : Finset.FromFin hk N' = N := by rw [hN']; exact Finset.FromFin.ToFin_eq hk N
    rw [← hN]
    exact Process.finOfFinset.upcrossingsBefore'_le hk hbot v u hFinOfFinset N' a b hab

end FinsetToFin

section Measurability
/-!
We use the following, which assumes ι = ℕ :
theorem Adapted.measurable_upcrossingsBefore (hf : Adapted ℱ f) (hab : a < b) :
    Measurable (upcrossingsBefore a b f N)
-/

theorem Adapted.measurable_upcrossingsBefore'_Nat {f : ℕ → Ω → ℝ} {N : ℕ} {a b : ℝ}
    {𝓕 : Filtration ℕ m0} (hf : Adapted 𝓕 f) (hab : a < b) :
    Measurable (upcrossingsBefore' a b f N) := by
  have hgeq : upcrossingsBefore a b f N = upcrossingsBefore' a b f N := by
    rw [upcrossingsBefore_eq_upcrossingsBefore' a b f N hab]
  rw [← hgeq]
  exact Adapted.measurable_upcrossingsBefore hf hab

variable {n : ℕ} [NeZero n] -- to avoid issues with `Fin 0`

theorem Adapted.measurable_upcrossingsBefore'_Fin {u : (Fin n) → Ω → ℝ} {N : Fin n} {a b : ℝ}
    {𝓕 : Filtration (Fin n) m0} (hf : Adapted 𝓕 u) (hab : a < b) :
    Measurable (upcrossingsBefore' a b u N) := by
  set 𝓕' := Filtration.natOfFin 𝓕 with hFiltr
  set v := Process.natOfFin u with hv
  have hadapted' : Adapted 𝓕' v := fun i => by
    have hsm : StronglyMeasurable[𝓕 (Fin.clamp i n)] (u (Fin.clamp i n)) := by
      exact hf (Fin.clamp i n)
    simp only [v, 𝓕']
    assumption
  have hNatOfFin : v = Process.natOfFin u := rfl
  have hfin : Finite (Fin n) := by infer_instance
  have hmeas_nat : Measurable (upcrossingsBefore' a b v N.val) :=
    Adapted.measurable_upcrossingsBefore'_Nat hadapted' hab
  have heq : upcrossingsBefore' a b u N = upcrossingsBefore' a b v N := by
    exact Process.natOfFin.upcrossingsBefore'_eq u v hNatOfFin N a b hab
  rw [heq]
  exact hmeas_nat

theorem Adapted.measurable_upcrossingsBefore'_Finset [LinearOrder ι] [OrderBot ι]
    {s : Finset ι} {k : ℕ} (hk : #s = k) (hbot : ⊥ ∈ s) [NeZero k]
    {u : s → Ω → ℝ} {N : s} {a b : ℝ} {𝓕 : Filtration s m0}
    (hf : Adapted 𝓕 u) (hab : a < b) :
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    Measurable (upcrossingsBefore' a b u N) := by
  set 𝓕' := Filtration.finOfFinset hk 𝓕 with hFiltr
  set v := Process.finOfFinset hk u with hv
  have hadapted' : Adapted 𝓕' v := fun i => by
    have hsm : StronglyMeasurable[𝓕 (Finset.FromFin hk i)] (u (Finset.FromFin hk i)) := by
      exact hf (Finset.FromFin hk i)
    simp only [v, 𝓕']
    assumption
  have hFinOfFinset : v = Process.finOfFinset hk u := rfl
  rw [Process.finOfFinset.upcrossingsBefore'_eq hk hbot u v hFinOfFinset N a b hab]
  exact Adapted.measurable_upcrossingsBefore'_Fin hadapted' hab

end Measurability

section DoobInequalityFin

variable {n : ℕ} [NeZero n] -- to avoid issues with `Fin 0`
  {u : (Fin n) → Ω → ℝ} {N : Fin n} {𝓕 : Filtration (Fin n) m0} {a b : ℝ}

theorem mul_integral_upcrossingsBefore'_Fin_le_integral_pos_part_aux [IsFiniteMeasure μ]
    (hu : Submartingale u 𝓕 μ) (hab : a < b) :
    (b - a) * μ[upcrossingsBefore' a b u N] ≤ μ[fun ω => (u N ω - a)⁺] := by
  -- We reduce to the `ℕ`-indexed case
  set 𝓕' := Filtration.natOfFin 𝓕 with hFiltr
  set v := Process.natOfFin u with hv
  have hvsub : Submartingale v 𝓕' μ := Submartingale.natOfFin hu
  have hNatOfFin : v = Process.natOfFin u := rfl
  have heq : upcrossingsBefore' a b u N = upcrossingsBefore' a b v N := by
    exact Process.natOfFin.upcrossingsBefore'_eq u v hNatOfFin N a b hab
  rw [heq]
  have huNvN : v N = u N := Process.natOfFin_eq' u v hNatOfFin N N le_rfl
  rw [← huNvN]
  exact mul_integral_upcrossingsBefore'_le_integral_pos_part_aux N hvsub hab

end DoobInequalityFin

section DoobInequalityFinset

variable [LinearOrder ι] [OrderBot ι]
  {s : Finset ι} {k : ℕ} (hne : s.Nonempty) (hk : #s = k) (hbot : ⊥ ∈ s) [NeZero k]
  {𝓕 : Filtration s m0} {f : s → Ω → ℝ} {N : s} {a b : ℝ}

theorem mul_integral_upcrossingsBefore'_Finset_le_integral_pos_part_aux [IsFiniteMeasure μ]
    (hk : #s = k) (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    (b - a) * μ[upcrossingsBefore' a b f N] ≤ μ[fun ω => (f N ω - a)⁺] := by
  -- We reduce to the `Fin k`-indexed case
  set 𝓕' := Filtration.finOfFinset hk 𝓕
  set v := Process.finOfFinset hk f
  have hvsub : Submartingale v 𝓕' μ := Submartingale.finOfFinset hk hf
  have hFinOfFinset : v = Process.finOfFinset hk f := rfl
  have heq := Process.finOfFinset.upcrossingsBefore'_eq hk hbot f v hFinOfFinset N a b hab
  rw [heq]
  have huNvN : v (Finset.ToFin hk N) = f N := Process.finOfFinset_eq hk f v hFinOfFinset N N le_rfl
  rw [← huNvN]
  exact mul_integral_upcrossingsBefore'_Fin_le_integral_pos_part_aux hvsub hab

theorem Adapted.integrable_upcrossingsBefore' [IsFiniteMeasure μ] (hk : #s = k)
    (hf : Adapted 𝓕 f) (hab : a < b) :
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    Integrable (fun ω => (upcrossingsBefore' a b f N ω : ℝ)) μ := by
  letI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
  obtain ⟨M, hM⟩ := upcrossingsBefore'_bounded_of_finite a b f N (by infer_instance)
  have hbdd : ∀ᵐ ω ∂μ, ‖(upcrossingsBefore' a b f N ω : ℝ)‖ ≤ M := by
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    simp only [Nat.cast_le, Nat.abs_cast]
    grind
  have meas0 := Adapted.measurable_upcrossingsBefore'_Finset hk hbot (N:=N) hf hab
  have meas : AEStronglyMeasurable (fun ω => (upcrossingsBefore' a b f N ω : ℝ)) μ :=
    Measurable.aestronglyMeasurable (measurable_from_top.comp meas0)
  exact ⟨meas, .of_bounded hbdd⟩

end DoobInequalityFinset

section Countable

variable [Countable ι] [LinearOrder ι] [OrderBot ι]

/-! Approximating `Set.Iic N` by finite sets that always contain ⊥ and N. -/

theorem Countable.increasing_family_saturates_Iic (N : ι) :
    ∃ s : ℕ → Set ι,
    Monotone s ∧
    (∀ n, Finite (s n)) ∧
    (∀ n, ⊥ ∈ s n) ∧
    (∀ n, N ∈ s n) ∧
    (∀ t : Set ι, Finite t → t ⊆ Set.Iic N → ∃ n, t ⊆ s n ∧ s n ⊆ Set.Iic N) := by
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat ι
  -- f enumerates elements of ι, but not all natural numbers must be present
  let s₀ : ℕ → Set ι := fun n => {i | f i < n}
  -- Augment each s₀ n with ⊥ and N, and intersect with Set.Iic N
  let s : ℕ → Set ι := fun n => (s₀ n ∩ Set.Iic N) ∪ {⊥, N}
  refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
  · -- Monotone s
    intro m n hmn x hx
    simp only [s, Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_setOf_eq, s₀] at hx ⊢
    cases hx with
    | inl h =>
      left
      constructor
      · exact Nat.lt_of_lt_of_le h.1 hmn
      · exact h.2
    | inr h => right; exact h
  · -- ∀ n, Finite (s n)
    intro n
    apply Set.Finite.union
    · apply Set.Finite.inter_of_left
      let g : s₀ n → Fin n := fun ⟨i, hi⟩ => ⟨f i, hi⟩
      have g_inj : Function.Injective g := fun ⟨x, _⟩ ⟨y, _⟩ h =>
        Subtype.ext (hf (Fin.ext_iff.mp h))
      exact Finite.of_injective g g_inj
    · exact Set.finite_singleton N |>.insert ⊥
  · -- ∀ n, ⊥ ∈ s n
    intro n
    simp only [s, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    right; left; trivial
  · -- ∀ n, N ∈ s n
    intro n
    simp only [s, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    right; right; trivial
  · -- saturation
    intro t ht htIcc
    haveI : Fintype t := Set.Finite.fintype ht
    by_cases hempty : t = ∅
    · use 0
      constructor
      · simp [hempty, Set.empty_subset]
      · intro x hx
        simp only [s, Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx
        cases hx with
        | inl h => exact h.2
        | inr h =>
          cases h with
          | inl h => subst h; simp
          | inr h => subst h; simp
    · use (Finset.univ.image (fun i : t => f i)).sup id + 1
      constructor
      · intro x hx
        simp only [s, Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_insert_iff,
          Set.mem_singleton_iff, Set.mem_setOf_eq, s₀]
        left
        constructor
        · have : f x ∈ Finset.univ.image (fun j : t => f j) :=
            Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
          exact Nat.lt_succ_of_le (Finset.le_sup (f := id) this)
        · exact htIcc hx
      · intro x hx
        simp only [s, Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx
        cases hx with
        | inl h => exact h.2
        | inr h =>
          cases h with
          | inl h => subst h; simp
          | inr h => subst h; simp

theorem Countable.increasing_finset_family_saturates_Iic (N : ι) :
    ∃ s : ℕ → Finset ι,
    Monotone s ∧
    (∀ n, ⊥ ∈ s n) ∧
    (∀ n, N ∈ s n) ∧
    (∀ t : Set ι, Finite t → t ⊆ Set.Iic N → ∃ n, t ⊆ s n ∧ ↑(s n) ⊆ Set.Iic N) := by
  obtain ⟨s, hsmon, hsfin, hsbot, hsN, hsaturate⟩ :=
    Countable.increasing_family_saturates_Iic (ι := ι) N
  -- Convert Set to Finset
  have fintype_s : ∀ n, Fintype (s n) := fun n => Fintype.ofFinite (s n)
  let s' : ℕ → Finset ι := fun n => @Set.toFinset ι (s n) (fintype_s n)
  refine ⟨s', ?_, ?_, ?_, ?_⟩
  · -- Monotone s'
    intro m n hmn
    simp only [s', Finset.le_iff_subset]
    intro x hx
    simp only [Set.mem_toFinset] at hx ⊢
    exact hsmon hmn hx
  · -- ∀ n, ⊥ ∈ s' n
    intro n
    simp only [s', Set.mem_toFinset]
    exact hsbot n
  · -- ∀ n, N ∈ s' n
    intro n
    simp only [s', Set.mem_toFinset]
    exact hsN n
  · -- saturation
    intro t ht htIcc
    obtain ⟨n, hn, hnIcc⟩ := hsaturate t ht htIcc
    use n
    constructor
    · intro x hx
      change x ∈ @Set.toFinset ι (s n) (fintype_s n)
      rw [Set.mem_toFinset]
      exact hn hx
    · intro x hx
      simp only [Finset.mem_coe, s', Set.mem_toFinset] at hx
      exact hnIcc hx

variable (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (hab : a < b)

end Countable

/-- Helper definition for `upcrossingsBefore'` on a finset, bundling the `OrderBot` instance.
    This avoids repeating `letI : OrderBot (s n) := { bot := ⟨⊥, hbot n⟩, ... }` throughout
    theorem statements and proofs. -/
noncomputable def upcrossingsBefore'_finset [LinearOrder ι] [OrderBot ι] {N : ι}
    {s : ℕ → Finset ι} (hbot : ∀ n, ⊥ ∈ s n) (hN : ∀ n, N ∈ s n)
    (a b : ℝ) (f : ι → Ω → ℝ) (n : ℕ) (ω : Ω) : ℕ :=
  letI : OrderBot (s n) := { bot := ⟨⊥, hbot n⟩, bot_le := fun ⟨_, _⟩ => bot_le }
  upcrossingsBefore' a b (fun i : s n => f i) ⟨N, hN n⟩ ω

section Approximation

variable [LinearOrder ι] [OrderBot ι]
  {a b : ℝ} {f : ι → Ω → ℝ} {N : ι} {ω : Ω}

/-- If we have K upcrossings, witnessed by UpcrossingDat a, and a finset contains all
    the witness points, then the finset also has at least K upcrossings. -/
lemma upcrossingsBefore'_finset_ge_of_witness
    {s : Finset ι} (hbot : ⊥ ∈ s) (hN : N ∈ s)
    {K : ℕ} (hKpos : K ≥ 1)
    (hseq : UpcrossingData a b f K ω)
    (ht_lt_N : hseq.t (2 * K - 1) < N)
    (ht_in_s : ∀ i < 2 * K, hseq.t i ∈ s) :
    letI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    K ≤ upcrossingsBefore' a b (fun i : s => f i) ⟨N, hN⟩ ω := by
  letI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
  have hNbot : ¬ N ≤ ⊥ := fun h => not_lt_bot (lt_of_lt_of_le ht_lt_N h)
  -- Build UpcrossingData on s from hseq
  have ht_lt_N_s : ⟨hseq.t (2 * K - 1), ht_in_s (2 * K - 1) (by omega)⟩ < (⟨N, hN⟩ : s) := ht_lt_N
  let hseq' : UpcrossingData a b (fun i : s => f i) K ω := ⟨
    hseq.hab,
    fun i => if h : i < 2 * K then ⟨hseq.t i, ht_in_s i h⟩ else ⟨N, hN⟩,
    fun i j hij => by
      simp only
      split_ifs with hi hj
      · exact hseq.mono hij
      · have hmono : hseq.t i ≤ hseq.t (2 * K - 1) := hseq.mono (by omega)
        exact le_of_lt (lt_of_le_of_lt hmono ht_lt_N_s)
      · omega
      · exact le_rfl,
    fun i hi heven => by simp only [hi, dif_pos]; exact hseq.ft_le_a i hi heven,
    fun i hi hodd => by simp only [hi, dif_pos]; exact hseq.ft_ge_b i hi hodd ⟩
  -- hseq' witnesses K upcrossings before ⟨N, hN⟩
  have hlt : ltUpcrossingsBefore a b (fun i : s => f i) ⟨N, hN⟩ K ω := by
    simp only [ltUpcrossingsBefore]
    have hNbot' : ¬ (⟨N, hN⟩ : s) ≤ ⊥ := fun h => hNbot h
    simp only [hNbot', ↓reduceIte, Nat.one_le_iff_ne_zero.mp hKpos]
    use hseq'
    simp only [hseq', dif_pos (by omega : 2 * K - 1 < 2 * K)]
    exact ht_lt_N
  -- Therefore upcrossingsBefore' on s is at least K
  have hmem : K ∈ {n | ltUpcrossingsBefore a b (fun i : s => f i) ⟨N, hN⟩ n ω} :=
    Set.mem_setOf.mpr hlt
  have hbdd' : BddAbove {n | ltUpcrossingsBefore a b (fun i : s => f i) ⟨N, hN⟩ n ω} :=
    ltUpcrossingsBefore_bddAbove_of_finite a b (fun i : s => f i) ω ⟨N, hN⟩ inferInstance
  exact le_csSup hbdd' hmem

/-- Given a monotone family of finsets saturating `Set.Iic N`, assuming bounded upcrossings,
    the upcrossings on `ι` eventually equal the upcrossings on the finsets. -/
theorem upcrossingsBefore'_eventually_eq_of_saturating_finsets
    {s : ℕ → Finset ι}
    (hmon : Monotone s)
    (hbot : ∀ n, ⊥ ∈ s n)
    (hN : ∀ n, N ∈ s n)
    (hsaturate : ∀ t : Set ι, Finite t → t ⊆ Set.Iic N →
      ∃ n, t ⊆ s n ∧ ↑(s n) ⊆ Set.Iic N)
    (hab : a < b)
    (hbdd : BddAbove {n | ltUpcrossingsBefore a b f N n ω}) :
    ∃ M, ∀ m ≥ M,
      letI : OrderBot (s m) := { bot := ⟨⊥, hbot m⟩, bot_le := fun ⟨_, _⟩ => bot_le }
      upcrossingsBefore' a b (fun i : s m => f i) ⟨N, hN m⟩ ω =
        upcrossingsBefore' a b f N ω := by
  set K := upcrossingsBefore' a b f N ω with hKdef
  by_cases hKzero : K = 0
  · -- K = 0: any finset works
    use 0
    intro m _
    apply le_antisymm
    · exact upcrossingsBefore'_ge_finset_of_bounded (hbot m) ⟨N, hN m⟩
        (fun i : s m => f i) f (fun _ => rfl) a b ω hab hbdd
    · rw [hKzero]; exact Nat.zero_le _
  · -- K ≥ 1: we need to find the witness and ensure the finset contains it
    have hKpos : K ≥ 1 := Nat.one_le_iff_ne_zero.mpr hKzero
    -- N is not ⊥ (otherwise K = 0)
    have hNbot : ¬ N ≤ ⊥ := by
      intro h
      have hzero : upcrossingsBefore' a b f N ω = 0 := upcrossingsBefore'_zero_of_N_bot a b f N ω h
      simp only [← hKdef] at hzero
      exact hKzero hzero
    -- K is in the set of ltUpcrossingsBefore
    have hne : {n | ltUpcrossingsBefore a b f N n ω}.Nonempty := by
      use 0
      simp only [Set.mem_setOf, ltUpcrossingsBefore, hNbot, ↓reduceIte]
    have hKmem : K ∈ {n | ltUpcrossingsBefore a b f N n ω} := by
      simp only [hKdef, upcrossingsBefore']
      exact Nat.sSup_mem hne hbdd
    -- Extract the UpcrossingData from K being in the set
    simp only [Set.mem_setOf, ltUpcrossingsBefore, hNbot, ↓reduceIte,
      Nat.one_le_iff_ne_zero.mp hKpos] at hKmem
    obtain ⟨hseq, ht_lt_N⟩ := hKmem
    -- The witness set
    set witness : Set ι := Set.range (fun i : Fin (2 * K) => hseq.t i) with hwit
    have hwit_finite : Finite witness := Set.finite_range _
    have hwit_Icc : witness ⊆ Set.Iic N := by
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      have : hseq.t i ≤ hseq.t (2 * K - 1) := hseq.mono (by omega)
      exact le_of_lt (lt_of_le_of_lt this ht_lt_N)
    -- Find M such that witness ⊆ s M
    obtain ⟨M', hM'_wit, _⟩ := hsaturate witness hwit_finite hwit_Icc
    use M'
    intro m hm
    apply le_antisymm
    · exact upcrossingsBefore'_ge_finset_of_bounded (hbot m) ⟨N, hN m⟩
        (fun i : s m => f i) f (fun _ => rfl) a b ω hab hbdd
    · -- witness ⊆ s m
      have hwit_in_sm : witness ⊆ s m := fun x hx => hmon hm (hM'_wit hx)
      have ht_in_sm : ∀ i < 2 * K, hseq.t i ∈ s m := fun i hi =>
        hwit_in_sm (Set.mem_range.mpr ⟨⟨i, hi⟩, rfl⟩)
      simp only [hKdef]
      exact upcrossingsBefore'_finset_ge_of_witness (hbot m) (hN m) hKpos hseq ht_lt_N ht_in_sm

/-! In the above setting, hbdd may be replaced by a finite supremum of upcrossingsBefore'. -/
theorem upcrossingsBefore'_finite_of_saturating_finsets_finite_sup
    {s : ℕ → Finset ι}
    (hbot : ∀ n, ⊥ ∈ s n)
    (hN : ∀ n, N ∈ s n)
    (hsaturate : ∀ t : Set ι, Finite t → t ⊆ Set.Iic N →
      ∃ n, t ⊆ s n ∧ ↑(s n) ⊆ Set.Iic N)
    (hfinite_sup : ∃ C, ∀ n, upcrossingsBefore'_finset hbot hN a b f n ω ≤ C) :
    BddAbove {n | ltUpcrossingsBefore a b f N n ω} := by
  obtain ⟨C, hCbound⟩ := hfinite_sup
  by_cases hNbot : N ≤ ⊥
  · -- N ≤ ⊥ implies {n | ltUpcrossingsBefore a b f N n ω} is empty
    simp only [ltUpcrossingsBefore]; simp_all
  · -- Use the finite supremum C to bound
    use C
    intro K hK
    simp only [Set.mem_setOf, ltUpcrossingsBefore, hNbot] at hK
    classical
    -- assume K > C, that is, exist UpcrosingData with > C upcrossings
    by_contra hnot
    have hKpos : ¬ K = 0 := by grind
    simp only [hKpos] at hK
    obtain ⟨hseq, ht_lt_N⟩ := hK
    -- The witness set
    set witness : Set ι := Set.range (fun i : Fin (2 * K) => hseq.t i) with hwit
    have hwit_finite : Finite witness := Set.finite_range _
    have hwit_Icc : witness ⊆ Set.Iic N := by
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      have : hseq.t i ≤ hseq.t (2 * K - 1) := hseq.mono (by omega)
      exact le_of_lt (lt_of_le_of_lt this ht_lt_N)
    -- Find n₀ such that witness ⊆ s n₀
    obtain ⟨n₀, hn₀_wit, _⟩ := hsaturate witness hwit_finite hwit_Icc
    /- We have K upcrossings and s n₀ contains all the witness points, hence ≥ K upcrossings. -/
    letI : OrderBot (s n₀) := { bot := ⟨⊥, hbot n₀⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    have h_upcrossings_ge : K ≤ upcrossingsBefore' a b (fun i : s n₀ => f i) ⟨N, hN n₀⟩ ω :=
      upcrossingsBefore'_finset_ge_of_witness (hbot n₀) (hN n₀) (Nat.one_le_iff_ne_zero.mpr hKpos)
        hseq ht_lt_N (fun i hi => hn₀_wit (Set.mem_range.mpr ⟨⟨i, hi⟩, rfl⟩))
    -- This contradicts the bound by C
    have hbound := hCbound n₀
    simp only [upcrossingsBefore'_finset] at hbound
    linarith

/-! The above two theorems merge into the following. -/
lemma upcrossingsBefore'_eventually_eq_of_saturating_finsets_finite_sup_aux
    {s : ℕ → Finset ι}
    (hmon : Monotone s)
    (hbot : ∀ n, ⊥ ∈ s n)
    (hN : ∀ n, N ∈ s n)
    (hsaturate : ∀ t : Set ι, Finite t → t ⊆ Set.Iic N →
      ∃ n, t ⊆ s n ∧ ↑(s n) ⊆ Set.Iic N)
    (hab : a < b)
    (hfinite_sup : ∃ C, ∀ n, upcrossingsBefore'_finset hbot hN a b f n ω ≤ C) :
    ∃ M, ∀ m ≥ M, upcrossingsBefore'_finset hbot hN a b f m ω = upcrossingsBefore' a b f N ω := by
  have hbdd : BddAbove {n | ltUpcrossingsBefore a b f N n ω} :=
    upcrossingsBefore'_finite_of_saturating_finsets_finite_sup hbot hN hsaturate hfinite_sup
  exact upcrossingsBefore'_eventually_eq_of_saturating_finsets hmon hbot hN hsaturate hab hbdd

/-- The upcrossings count on the full index set equals the supremum of upcrossings counts
    on the approximating finsets, when the latter is bounded. This version provides an
    equality in ℝ (with coercions from ℕ). -/
theorem upcrossingsBefore'_eq_iSup_finset_real
    {s : ℕ → Finset ι}
    (hmon : Monotone s)
    (hbot : ∀ n, ⊥ ∈ s n)
    (hN : ∀ n, N ∈ s n)
    (hsaturate : ∀ t : Set ι, Finite t → t ⊆ Set.Iic N →
      ∃ n, t ⊆ s n ∧ ↑(s n) ⊆ Set.Iic N)
    (hab : a < b)
    (ω : Ω) (hfinite_sup : ∃ C : ℝ, ∀ n, (upcrossingsBefore'_finset hbot hN a b f n ω : ℝ) ≤ C) :
    (upcrossingsBefore' a b f N ω : ℝ) =
      ⨆ n, (upcrossingsBefore'_finset hbot hN a b f n ω : ℝ) := by
  -- Convert real bound to nat bound
  obtain ⟨C', hCbound'⟩ := hfinite_sup
  let C := Nat.ceil C'
  have hCC : C' ≤ C := Nat.le_ceil C'
  have hCbound : ∃ C, ∀ n, upcrossingsBefore'_finset hbot hN a b f n ω ≤ C := by
    use C
    intro n
    exact_mod_cast (hCbound' n).trans hCC
  -- Get the stabilization point M
  obtain ⟨M, hM⟩ := upcrossingsBefore'_eventually_eq_of_saturating_finsets_finite_sup_aux
    hmon hbot hN hsaturate hab hCbound
  -- The sequence is monotone in ℝ
  have hU_mono : Monotone (fun n => (upcrossingsBefore'_finset hbot hN a b f n ω : ℝ)) := by
    intro n m hnm
    simp only [upcrossingsBefore'_finset]
    exact Nat.cast_le.mpr (upcrossingsBefore'_ge_finset (hbot n) (hbot m) (hmon hnm) ⟨N, hN n⟩
      (fun i : s n => f i) (fun i : s m => f i) (fun _ => rfl) a b ω hab)
  -- LHS equals value at M
  have heq1 : (upcrossingsBefore' a b f N ω : ℝ) =
      (upcrossingsBefore'_finset hbot hN a b f M ω : ℝ) := by
    exact_mod_cast (hM M le_rfl).symm
  -- RHS (ℝ-supremum) equals value at M
  have heq2 : ⨆ n, (upcrossingsBefore'_finset hbot hN a b f n ω : ℝ) =
      (upcrossingsBefore'_finset hbot hN a b f M ω : ℝ) := by
    apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
    · intro n
      by_cases hnM : n ≤ M
      · exact hU_mono hnM
      · push_neg at hnM
        simp only [upcrossingsBefore'_finset]
        exact_mod_cast le_of_eq (hM n (le_of_lt hnM) ▸ (hM M le_rfl).symm)
    · intro w hw
      exact ⟨M, hw⟩
  rw [heq1, heq2]

end Approximation

section ConvergenceBochner

lemma integrable_lim_of_mono_L1_bounded {f : ℕ → Ω → ℝ} {F : Ω → ℝ}
    (h_pos : ∀ n, 0 ≤ᵐ[μ] f n)
    (hf : ∀ n, Integrable (f n) μ)
    {c : ℝ}
    (hF : AEStronglyMeasurable F μ)
    (h_bound : ∀ n, μ[f n] ≤ c)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (nhds (F x))) :
    Integrable F μ := by
  -- F ≥ 0 a.e. since f n ≥ 0 a.e. and f n → F monotonically
  have hF_pos : 0 ≤ᵐ[μ] F := by
    filter_upwards [h_pos 0, h_mono, h_tendsto] with x hf0 hmono htends
    exact ge_of_tendsto' htends fun n => le_trans hf0 (hmono (Nat.zero_le n))
  -- Convert lintegral to integral for f n (since f n ≥ 0 a.e.)
  have hlint_eq : ∀ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂μ = ENNReal.ofReal (μ[f n]) :=
    fun n => (ofReal_integral_eq_lintegral_ofReal (hf n) (h_pos n)).symm
  -- The lintegral of f n is bounded by c
  have hlint_bound : ∀ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂μ ≤ ENNReal.ofReal c :=
    fun n => (hlint_eq n).symm ▸ ENNReal.ofReal_le_ofReal (h_bound n)
  -- Monotonicity of f n in ENNReal
  have h_mono_ennreal : ∀ᵐ x ∂μ, Monotone fun n => ENNReal.ofReal (f n x) := by
    filter_upwards [h_mono] with x hx n m hnm; exact ENNReal.ofReal_le_ofReal (hx hnm)
  -- Convergence of f n to F in ENNReal
  have h_tendsto_ennreal : ∀ᵐ x ∂μ, Tendsto (fun n => ENNReal.ofReal (f n x)) atTop
      (nhds (ENNReal.ofReal (F x))) := by
    filter_upwards [h_tendsto] with x hx; exact (ENNReal.continuous_ofReal.tendsto _).comp hx
  -- AEMeasurable for ENNReal.ofReal ∘ f n
  have h_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (f n x)) μ :=
    fun n => (hf n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  -- By monotone convergence, lintegral of F equals limit of lintegrals
  have h_lintegral_tendsto :
      Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) atTop
        (nhds (∫⁻ x, ENNReal.ofReal (F x) ∂μ)) :=
    lintegral_tendsto_of_tendsto_of_monotone h_meas h_mono_ennreal h_tendsto_ennreal
  -- The limit of a sequence bounded by c is at most c
  have h_lintegral_bound : ∫⁻ x, ENNReal.ofReal (F x) ∂μ ≤ ENNReal.ofReal c :=
    le_of_tendsto' h_lintegral_tendsto hlint_bound
  -- HasFiniteIntegral since lintegral is finite
  have hfi : HasFiniteIntegral F μ := by
    rw [hasFiniteIntegral_iff_ofReal hF_pos]
    exact lt_of_le_of_lt h_lintegral_bound ENNReal.ofReal_lt_top
  exact ⟨hF, hfi⟩

lemma bounded_integral_lim_of_mono_L1_bounded {f : ℕ → Ω → ℝ} {F : Ω → ℝ}
    (h_pos : ∀ n, 0 ≤ᵐ[μ] f n)
    (hf : ∀ n, Integrable (f n) μ)
    {c : ℝ}
    (hF : AEStronglyMeasurable F μ)
    (h_bound : ∀ n, μ[f n] ≤ c)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (nhds (F x))) :
    μ[F] ≤ c := by
  have hF_int : Integrable F μ :=
    integrable_lim_of_mono_L1_bounded h_pos hf hF h_bound h_mono h_tendsto
  have h_int_tendsto : Tendsto (fun n => μ[f n]) atTop (nhds μ[F]) :=
    integral_tendsto_of_tendsto_of_monotone hf hF_int h_mono h_tendsto
  exact le_of_tendsto' h_int_tendsto h_bound

lemma bounded_integral_sup_of_mono_L1_bounded {f : ℕ → Ω → ℝ} {F : Ω → ℝ}
    (h_pos : ∀ n, 0 ≤ᵐ[μ] f n)
    (h_int : ∀ n, Integrable (f n) μ)
    {c : ℝ}
    (h_bound : ∀ n, μ[f n] ≤ c)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x)
    (h_sup : ∀ x, (∃ M, ∀ n, f n x ≤ M) → F x = ⨆ n, f n x) :
    Integrable F μ ∧ μ[F] ≤ c := by
  -- Show that a.e. the sequence is bounded above (key step)
  have h_ae_bdd : ∀ᵐ x ∂μ, ∃ M, ∀ n, f n x ≤ M := by
    have h_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (f n x)) μ :=
      fun n => (h_int n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have h_mono_ennreal : ∀ᵐ x ∂μ, Monotone fun n => ENNReal.ofReal (f n x) := by
      filter_upwards [h_mono] with x hx n m hnm
      exact ENNReal.ofReal_le_ofReal (hx hnm)
    have h_lintegral_bdd : ∀ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂μ ≤ ENNReal.ofReal c := by
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (h_int n) (h_pos n)]
      exact ENNReal.ofReal_le_ofReal (h_bound n)
    have h_sup_lintegral : ∫⁻ x, ⨆ n, ENNReal.ofReal (f n x) ∂μ ≤ ENNReal.ofReal c := by
      calc ∫⁻ x, ⨆ n, ENNReal.ofReal (f n x) ∂μ
          = ⨆ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂μ := lintegral_iSup' h_meas h_mono_ennreal
        _ ≤ ENNReal.ofReal c := iSup_le h_lintegral_bdd
    have h_sup_lt_top : ∀ᵐ x ∂μ, ⨆ n, ENNReal.ofReal (f n x) < ⊤ := by
      have hne : ∫⁻ x, ⨆ n, ENNReal.ofReal (f n x) ∂μ ≠ ⊤ :=
        (lt_of_le_of_lt h_sup_lintegral ENNReal.ofReal_lt_top).ne
      have hmeas : AEMeasurable (fun x => ⨆ n, ENNReal.ofReal (f n x)) μ :=
        AEMeasurable.iSup h_meas
      exact ae_lt_top' hmeas hne
    filter_upwards [h_sup_lt_top, h_mono, h_pos 0] with x hx_lt_top hx_mono hf0
    have hsup_ne_top : ⨆ n, ENNReal.ofReal (f n x) ≠ ⊤ := hx_lt_top.ne
    refine ⟨(⨆ n, ENNReal.ofReal (f n x)).toReal, fun n => ?_⟩
    by_cases hfn : 0 ≤ f n x
    · calc f n x = (ENNReal.ofReal (f n x)).toReal := (ENNReal.toReal_ofReal hfn).symm
        _ ≤ (⨆ n, ENNReal.ofReal (f n x)).toReal := by
            apply ENNReal.toReal_mono hsup_ne_top
            exact le_iSup (fun n => ENNReal.ofReal (f n x)) n
    · push_neg at hfn
      have h0le : 0 ≤ (⨆ n, ENNReal.ofReal (f n x)).toReal := ENNReal.toReal_nonneg
      exact le_trans (le_of_lt hfn) h0le
  -- Now we have a.e. boundedness, so a.e. F = ⨆ n, f n x and f n → F
  have h_ae_sup : ∀ᵐ x ∂μ, F x = ⨆ n, f n x := by
    filter_upwards [h_ae_bdd] with x hx; exact h_sup x hx
  have h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (nhds (F x)) := by
    filter_upwards [h_ae_bdd, h_mono, h_ae_sup] with x hx_bdd hx_mono hx_sup
    rw [hx_sup]
    exact tendsto_atTop_ciSup hx_mono ⟨_, Set.forall_mem_range.mpr hx_bdd.choose_spec⟩
  have hF : AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (h_int n).aestronglyMeasurable) h_tendsto
  have hF_int : Integrable F μ :=
    integrable_lim_of_mono_L1_bounded h_pos h_int hF h_bound h_mono h_tendsto
  exact ⟨hF_int, bounded_integral_lim_of_mono_L1_bounded h_pos h_int hF h_bound h_mono h_tendsto⟩

end ConvergenceBochner

section DoobInequalityCountable

variable [LinearOrder ι] {f : ι → Ω → ℝ} {𝓕 : Filtration ι m0}

/-- Restrict a filtration on ι to a finset s. -/
def Filtration.restrictFinset (𝓕 : Filtration ι m0) (s : Finset ι) :
    Filtration s m0 := ⟨fun i => 𝓕 i.val, fun _ _ hij => 𝓕.mono hij, fun i => 𝓕.le i.val⟩

/-- Restrict a submartingale on ι to a finset s. -/
lemma Submartingale.restrictFinset (𝓕 : Filtration ι m0) (s : Finset ι)
    (hf : Submartingale f 𝓕 μ) :
    Submartingale (fun i : s => f i) (Filtration.restrictFinset 𝓕 s) μ :=
  ⟨fun i => hf.adapted i.val, fun i j hij => hf.2.1 i.val j.val hij, fun i => hf.integrable i.val⟩

variable [Countable ι] [OrderBot ι] {N : ι} {a b : ℝ}

theorem mul_integral_upcrossingsBefore'_Countable_le_integral_pos_part_aux [IsFiniteMeasure μ]
    (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    Integrable (fun ω => (upcrossingsBefore' a b f N ω : ℝ)) μ ∧
    μ[upcrossingsBefore' a b f N] ≤ μ[fun ω => (f N ω - a)⁺] / (b - a) := by
  -- We approximate Set.Iic N by an increasing family of finsets
  obtain ⟨s, hsmon, hsbot, hsN, hsaturate⟩ := Countable.increasing_finset_family_saturates_Iic N
  -- For each n, define U_n as upcrossings on s n
  let U : ℕ → Ω → ℝ := fun n ω => upcrossingsBefore'_finset hsbot hsN a b f n ω
  -- The bound c is the same for all n (since f N appears in each finset)
  set c := μ[fun ω => (f N ω - a)⁺] / (b - a) with hc
  set F : Ω → ℝ := fun ω => upcrossingsBefore' a b f N ω with hF
  have hk : ∀ n, #(s n) = Finset.card (s n) := by intro n; rfl
  have hne : ∀ n, (s n).Nonempty := by intro n; use ⊥; exact hsbot n
  have hnz : ∀ n, #(s n) ≠ 0 := by intro n; exact Finset.card_ne_zero.mpr (hne n)
  have hNZ : ∀ n, NeZero #(s n) := by intro n; exact ⟨hnz n⟩
  let hFiltr := fun n => Filtration.restrictFinset 𝓕 (s n)
  have hsub : ∀ n, Submartingale (fun i : s n => f i) (hFiltr n) μ :=
    fun n => Submartingale.restrictFinset 𝓕 (s n) hf
  refine bounded_integral_sup_of_mono_L1_bounded (f:=U) ?h_pos ?h_int ?h_bound ?h_mono ?h_sup
  · intro n; filter_upwards with ω; simp only [U]; simp
  · exact fun n =>
      Adapted.integrable_upcrossingsBefore' (μ := μ) (hsbot n) (hk n) (hsub n).adapted hab
  · intro n
    simp only [hc, le_div_iff₀' (sub_pos.mpr hab)]
    exact mul_integral_upcrossingsBefore'_Finset_le_integral_pos_part_aux
      (hbot := hsbot n) (hk := rfl) (hf := hsub n) (N := ⟨N, hsN n⟩) hab
  · filter_upwards with ω n m hnm
    simp only [U, upcrossingsBefore'_finset]
    exact_mod_cast upcrossingsBefore'_ge_finset (hsbot n) (hsbot m) (hsmon hnm) ⟨N, hsN n⟩
      (fun i : s n => f i) (fun i : s m => f i) (fun _ => rfl) a b ω hab
  · intro ω hω_bdd; simp only [hF, U]
    exact upcrossingsBefore'_eq_iSup_finset_real hsmon hsbot hsN hsaturate hab ω hω_bdd

theorem Submartingale.mul_integral_upcrossingsBefore'_Countable_le_integral_pos_part
    [IsFiniteMeasure μ]
    (hf : Submartingale f 𝓕 μ) :
    (b - a) * μ[upcrossingsBefore' a b f N] ≤ μ[fun ω => (f N ω - a)⁺] := by
  by_cases! hab : a < b
  · simp only [← le_div_iff₀' (sub_pos.mpr hab)]
    exact (mul_integral_upcrossingsBefore'_Countable_le_integral_pos_part_aux hf hab).2
  · rw [← sub_nonpos] at hab
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hab (by positivity))
      (integral_nonneg fun ω => posPart_nonneg _)

theorem Submartingale.integrable_upcrossingsBefore'_Countable
    [IsFiniteMeasure μ]
    (hf : Submartingale f 𝓕 μ) :
    Integrable (fun ω => (upcrossingsBefore' a b f N ω : ℝ)) μ := by
  by_cases hab : a < b
  · exact (mul_integral_upcrossingsBefore'_Countable_le_integral_pos_part_aux hf hab).1
  · -- simp only [← sub_nonpos] at hab
    have h_nonpos : (fun ω => (upcrossingsBefore' a b f N ω : ℝ)) =ᵐ[μ] 0 := by
      filter_upwards with ω
      have := upcrossingsBefore'_eq_zero_of_not_hab (a:=a) (b:=b) (f:=f) (N:=N) (ω:=ω) hab
      simp_all
    rw [integrable_congr h_nonpos]
    exact integrable_zero Ω ℝ μ

end DoobInequalityCountable

section DoobInequalityNNReal

variable {f : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 m0} [IsFiniteMeasure μ]
  {N : ℝ≥0} {a b : ℝ}

/-!
/-- `WellFoundedLT` provides a `HittingBtwnSpec`. -/
lemma hittingBtwnSpec_of_wellFoundedLT [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι]
    (f : ι → Ω → ℝ) (s : Set ℝ) (n m : ι) (ω : Ω) : HittingBtwnSpec f s n m ω :=
  ⟨hittingBtwn_mem_set_of_hittingBtwn_lt, fun i hi => hittingBtwn_lt_iff (i := i) hi⟩
-/

/-- For `ℝ≥0`, right continuity of trajectories provides `HittingBtwnSpec`.
This requires showing that hitting times actually hit closed sets for right-continuous functions. -/
lemma hittingBtwnSpec_of_right_continuous (s : Set ℝ) (n m : ℝ≥0) (ω : Ω)
    (hs : IsClosed s) (hRC : Function.RightContinuous (f · ω)) :
    HittingBtwnSpec f s n m ω := by
  constructor
  -- hitsSet: hittingBtwn f s n m ω < m → f (hittingBtwn f s n m ω) ω ∈ s
  intro ht
  -- Since hittingBtwn < m, there exists a hit in [n, m]
  have h_exists : ∃ j ∈ Set.Icc n m, f j ω ∈ s := by
    by_contra h_neg
    simp only [hittingBtwn, h_neg, ↓reduceIte] at ht
    exact lt_irrefl m ht
  -- The hitting time is the infimum of hitting points in [n, m]
  set S := Set.Icc n m ∩ {i | f i ω ∈ s} with Sdef
  have h_eq : hittingBtwn f s n m ω = sInf S := by
    simp only [hittingBtwn, h_exists, ↓reduceIte, Sdef]
  -- The set of hitting points is nonempty
  have hne : S.Nonempty := by
    obtain ⟨j, hj_Icc, hj_s⟩ := h_exists
    exact ⟨j, hj_Icc, hj_s⟩
  -- S is bounded below
  have hbdd : BddBelow S := ⟨n, fun x hx => hx.1.1⟩
  -- Get a sequence in S converging to sInf S from above
  obtain ⟨u, hu_anti, hu_tendsto, hu_mem⟩ := exists_seq_tendsto_sInf hne hbdd
  -- The sequence elements are in S, so f u n ω ∈ s
  have hu_in_s : ∀ n, f (u n) ω ∈ s := fun n => (hu_mem n).2
  -- Since u is antitone and converges to sInf S from above, we have u n ≥ sInf S
  have hu_ge : ∀ n, u n ≥ sInf S := fun n => csInf_le hbdd (hu_mem n)
  -- Case split: either sInf S ∈ S (then done), or sInf S is a strict limit from the right
  rw [h_eq]
  by_cases h_mem_S : sInf S ∈ S
  · -- sInf S ∈ S, so f (sInf S) ω ∈ s directly
    exact h_mem_S.2
  · -- sInf S ∉ S, so all u n > sInf S strictly
    have hu_gt : ∀ n, u n > sInf S := fun n => lt_of_le_of_ne (hu_ge n) (fun heq =>
      h_mem_S (heq ▸ hu_mem n))
    -- u n ∈ Ioi (sInf S), so we can use right-continuity
    have hu_Ioi : ∀ n, u n ∈ Set.Ioi (sInf S) := fun n => hu_gt n
    -- Right-continuity gives tendsto (f · ω) (nhdsWithin h (Ioi h)) (nhds (f h ω))
    -- The sequence u, which stays in Ioi h, induces a filter map to nhdsWithin
    have h_tendsto_within : Tendsto u atTop (nhdsWithin (sInf S) (Set.Ioi (sInf S))) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hu_tendsto, Filter.Eventually.of_forall hu_Ioi⟩
    -- Compose with right-continuity
    have h_f_tendsto : Tendsto (fun n => f (u n) ω) atTop (nhds (f (sInf S) ω)) :=
      (hRC (sInf S)).tendsto.comp h_tendsto_within
    -- Apply IsClosed.mem_of_tendsto
    exact hs.mem_of_tendsto h_f_tendsto (Filter.Eventually.of_forall hu_in_s)

theorem upcrossingsBefore_eq_upcrossingsBefore'_NNReal (hab : a < b) :
    upcrossingsBefore a b f N = upcrossingsBefore' a b f N := by
  

theorem mul_integral_upcrossingsBefore'_NNReal_le_integral_pos_part_aux
    (hf : Submartingale f 𝓕 μ) {N : ℝ≥0} {a b : ℝ} (hab : a < b)
    (hRC : ∀ ω, RightContinuous (f · ω)) :
    (b - a) * μ[upcrossingsBefore' a b f N] ≤ μ[fun ω => (f N ω - a)⁺] := by
  sorry

end DoobInequalityNNReal

end ProbabilityTheory
