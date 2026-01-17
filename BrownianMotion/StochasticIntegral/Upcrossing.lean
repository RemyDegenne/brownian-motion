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

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {a b : ℝ}

/- Upcrossings number that is infinite when optional times accumulate before N. -/
noncomputable def upcrossingsBeforeENat [Preorder ι] [OrderBot ι] [InfSet ι]
    (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : upperCrossingTime a b f N n ω < N), (n : ℕ∞)

/-- `upcrossingsBeforeENat` agrees with `upcrossingsBefore` whenever the set of crossing indices
is bounded above. -/
lemma upcrossingsBeforeENat_eq_upcrossingsBefore_of_finite [Preorder ι] [OrderBot ι] [InfSet ι]
    {f : ι → Ω → ℝ} {N : ι} {ω : Ω}
    (hbdd : BddAbove {n | upperCrossingTime a b f N n ω < N}) :
    upcrossingsBeforeENat a b f N ω = (upcrossingsBefore a b f N ω : ℕ∞) := by
  simp only [upcrossingsBeforeENat, upcrossingsBefore]
  rw [ENat.coe_sSup hbdd]
  simp only [Set.mem_setOf_eq]

/-- `upcrossingsBeforeENat` agrees with `upcrossingsBefore` on `ℕ` index set when `a < b`. -/
theorem upcrossingsBeforeENat_eq_upcrossingsBefore_Nat {f : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω}
    (hab : a < b) :
    upcrossingsBeforeENat a b f N ω = (upcrossingsBefore a b f N ω : ℕ∞) :=
  upcrossingsBeforeENat_eq_upcrossingsBefore_of_finite (upperCrossingTime_lt_bddAbove hab)

/-! Let's use:
theorem mul_integral_upcrossingsBefore_le_integral_pos_part_aux [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hab : a < b) :
    (b - a) * μ[upcrossingsBefore a b f N] ≤ μ[fun ω => (f N ω - a)⁺]
-/
theorem mul_lintegral_upcrossingsBefore_le_lintegral_pos_part_aux [IsFiniteMeasure μ]
    {𝓕 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ}
    (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingsBefore a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
  have hint : Integrable (fun ω => (upcrossingsBefore a b f N ω : ℝ)) μ :=
    hf.adapted.integrable_upcrossingsBefore hab
  have hnn : 0 ≤ᵐ[μ] (fun ω => (upcrossingsBefore a b f N ω : ℝ)) :=
    ae_of_all μ (fun ω => Nat.cast_nonneg _)
  -- The coercion ℕ → ℝ≥0∞ equals ENNReal.ofReal ∘ (↑ : ℕ → ℝ)
  have hlint_eq : ∫⁻ ω, (upcrossingsBefore a b f N ω : ℝ≥0∞) ∂μ =
      ENNReal.ofReal (∫ ω, (upcrossingsBefore a b f N ω : ℝ) ∂μ) := by
    have h1 : ∫⁻ ω, (upcrossingsBefore a b f N ω : ℝ≥0∞) ∂μ =
        ∫⁻ ω, ENNReal.ofReal (upcrossingsBefore a b f N ω : ℝ) ∂μ := by
      congr 1 with ω
      simp only [ENNReal.ofReal_natCast]
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint hnn]
  rw [hlint_eq]
  -- Also convert RHS
  have hpos_nn : 0 ≤ᵐ[μ] (fun ω => (f N ω - a)⁺) :=
    ae_of_all μ (fun ω => posPart_nonneg _)
  have hpos_int : Integrable (fun ω => (f N ω - a)⁺) μ :=
    ((hf.integrable N).sub (integrable_const a)).pos_part
  have hrhs_eq : ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ =
      ENNReal.ofReal (∫ ω, (f N ω - a)⁺ ∂μ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hpos_int hpos_nn]
  rw [hrhs_eq]
  have hDoob := mul_integral_upcrossingsBefore_le_integral_pos_part_aux (N := N) hf hab
  have hba_pos : 0 ≤ b - a := le_of_lt (sub_pos.mpr hab)
  rw [← ENNReal.ofReal_mul hba_pos]
  apply ENNReal.ofReal_le_ofReal
  exact hDoob

theorem mul_lintegral_upcrossingsBeforeENat_le_lintegral_pos_part_aux [IsFiniteMeasure μ]
    {𝓕 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ}
    (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingsBeforeENat a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
  simp_rw [upcrossingsBeforeENat_eq_upcrossingsBefore_Nat hab, ENat.toENNReal_coe]
  exact mul_lintegral_upcrossingsBefore_le_lintegral_pos_part_aux hf hab

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

/-! The `ltUpcrossingData a b f N n ω` is shortened as `L n`. -/
noncomputable def ltUpcrossingData [LinearOrder ι] [OrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) : Prop :=
  if N ≤ ⊥ then False else -- to make {n | ...} empty when N = ⊥, same as in upperCrossingTime
    if n = 0 then True else
      ∃ seq : UpcrossingData a b f n ω, seq.t (2 * n - 1) < N

/-- The maximal length of upcrossing sequence (strictly) before time `N`. Suitable for MCT proof. -/
noncomputable def upcrossingSequenceENat [LinearOrder ι] [OrderBot ι] (a b : ℝ) (f : ι → Ω → ℝ)
    (N : ι) (ω : Ω) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ltUpcrossingData a b f N n ω), (n : ℕ∞)


lemma upcrossingSequenceENat_eq_zero_of_not_hab [LinearOrder ι] [OrderBot ι]
    {a b : ℝ} {f : ι → Ω → ℝ} {N : ι} {ω : Ω}
    (hab : ¬ a < b) : upcrossingSequenceENat a b f N ω = 0 := by
  simp only [upcrossingSequenceENat, ltUpcrossingData]
  rcases le_or_gt N ⊥ with hN | hN
  · simp_all
  · have : ¬ N ≤ ⊥ := by grind
    simp only [this, if_false]
    have : ∀ n, ¬ (∃ seq : UpcrossingData a b f n ω, seq.t (2 * n - 1) < N) :=
      fun _ ⟨seq, _⟩ => hab seq.hab
    simp only [this]; simp_all

/-! ltUpcrossingData a b f N n ω ↔ upperCrossingTime a b f N n ω < N -/
section DefsEquivalence

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
lemma upperCrossingTimeLT_bot_iff_ltUpcrossingData [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hN : N ≤ ⊥) :
    upperCrossingTimeLT a b f N n ω ↔ ltUpcrossingData a b f N n ω := by
  simp only [ltUpcrossingData, hN, if_true]
  simp only [upperCrossingTimeLT, hN, if_true]

/-! The left implication: ∀ n, L n → P n, in the case N ≠ ⊥ -/
lemma upperCrossingTimeLT_of_ltUpcrossingData [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (h : ¬ N ≤ ⊥) :
    ltUpcrossingData a b f N n ω → upperCrossingTimeLT a b f N n ω := by
  simp only [ltUpcrossingData, h, if_false]
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
lemma ltUpcrossingData_of_upcrossingsBeforeUpperCrossingTime_of_upperCrossingTimeLT
  [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hN : ¬ N ≤ ⊥) :
  upperCrossingTimeLT a b f N n ω →
    upcrossingsBeforeUpperCrossingTime a b f N n ω →
      ltUpcrossingData a b f N n ω := by
  simp only [ltUpcrossingData, upcrossingsBeforeUpperCrossingTime, hN, if_false]
  rcases eq_or_ne n 0 with rfl | hn
  · simp_all
  · simp only [hn]
    intro h ⟨hseq, ht_le⟩
    use hseq
    simp only [upperCrossingTimeLT] at h
    refine lt_of_le_of_lt ht_le ?_
    simp_all


/-- Bundled properties of `hittingBtwn` that may be established under various assumptions
(e.g., finiteness of the index set, or right-continuity of trajectories for `ℝ≥0`). -/
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

/-- In a well-founded order, `HittingBtwnSpec` is automatic since infima of nonempty sets
are attained. -/
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

/-! The right implication: ∀ n, P n → L n, in the case N ≠ ⊥. -/
lemma ltUpcrossingData_of_upperCrossingTimeLT' [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b) (hN : ¬ N ≤ ⊥)
  (hspecIci : ∀ n, HittingBtwnSpec f (Set.Ici b) n N ω)
  (hspecIic : ∀ n, HittingBtwnSpec f (Set.Iic a) n N ω) :
    upperCrossingTimeLT a b f N n ω → ltUpcrossingData a b f N n ω := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ltUpcrossingData, hN]; simp_all
  · intro hup
    refine ltUpcrossingData_of_upcrossingsBeforeUpperCrossingTime_of_upperCrossingTimeLT
      a b f N n ω hN hup ?_
    exact upcrossingsBeforeUpperCrossingTime_of_upperCrossingTimeLT_all'
      a b f N n ω hab (by grind) (by simp_all) hspecIci hspecIic hup

/-! Finally, the equivalence ∀ n, P n ↔ L n. -/
theorem upperCrossingTimeLT_iff_ltUpcrossingData' [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b)
  (hspecIci : ∀ n, HittingBtwnSpec f (Set.Ici b) n N ω)
  (hspecIic : ∀ n, HittingBtwnSpec f (Set.Iic a) n N ω) :
    upperCrossingTimeLT a b f N n ω ↔ ltUpcrossingData a b f N n ω := by
  rcases le_or_gt N ⊥ with hN | hN
  · exact upperCrossingTimeLT_bot_iff_ltUpcrossingData a b f N n ω hN
  · exact ⟨ltUpcrossingData_of_upperCrossingTimeLT'
            a b f N n ω hab (not_le.mpr hN) hspecIci hspecIic,
            upperCrossingTimeLT_of_ltUpcrossingData a b f N n ω (not_le.mpr hN)⟩

/-! Auxiliary lemma. -/
lemma upperCrossingTime_lt_iff_ltUpcrossingData' [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hab : a < b)
  (hspecIci : ∀ n, HittingBtwnSpec f (Set.Ici b) n N ω)
  (hspecIic : ∀ n, HittingBtwnSpec f (Set.Iic a) n N ω) :
    upperCrossingTime a b f N n ω < N ↔ ltUpcrossingData a b f N n ω := by
  rw [← upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N n ω]
  exact upperCrossingTimeLT_iff_ltUpcrossingData' a b f N n ω hab hspecIci hspecIic

lemma upcrossingSequenceENat_zero_of_N_bot [LinearOrder ι] [OrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (ω : Ω) (hN : N ≤ ⊥) :
    upcrossingSequenceENat a b f N ω = 0 := by
  simp only [upcrossingSequenceENat, ltUpcrossingData, hN, if_true]; simp

/-! The two definitions of upcrossing*ENat are equivalent; measurable via `upcrossingsBeforeENat`.-/
theorem upcrossingsBeforeENat_eq_upcrossingSequenceENat
  [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (hab : a < b)
  (hspecIci : ∀ n ω, HittingBtwnSpec f (Set.Ici b) n N ω)
  (hspecIic : ∀ n ω, HittingBtwnSpec f (Set.Iic a) n N ω) :
    upcrossingsBeforeENat a b f N = upcrossingSequenceENat a b f N := by
  ext ω
  simp only [upcrossingsBeforeENat, upcrossingSequenceENat]
  congr 1
  ext n
  rw [upperCrossingTime_lt_iff_ltUpcrossingData' a b f N n ω hab (hspecIci · ω) (hspecIic · ω)]

/-- `upcrossingsBeforeENat` agrees with `upcrossingSequenceENat` on `ℕ` index set when `a < b`. -/
theorem upcrossingsBeforeENat_eq_upcrossingSequenceENat_Nat {f : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω}
    (hab : a < b) :
    upcrossingsBeforeENat a b f N ω = upcrossingSequenceENat a b f N ω :=
  congrFun (upcrossingsBeforeENat_eq_upcrossingSequenceENat a b f N hab
    (fun n ω => hittingBtwnSpec_of_wellFoundedLT f (Set.Ici b) n N ω)
    (fun n ω => hittingBtwnSpec_of_wellFoundedLT f (Set.Iic a) n N ω)) ω

/-- `upcrossingSequenceENat` agrees with `upcrossingsBefore` on `ℕ` index set when `a < b`. -/
theorem upcrossingSequenceENat_eq_upcrossingsBefore_Nat {f : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω}
    (hab : a < b) :
    upcrossingSequenceENat a b f N ω = (upcrossingsBefore a b f N ω : ℕ∞) := by
  rw [← upcrossingsBeforeENat_eq_upcrossingSequenceENat_Nat hab]
  exact upcrossingsBeforeENat_eq_upcrossingsBefore_Nat hab

/-- `BddAbove` for `ltUpcrossingData` on `ℕ`, derived from `upperCrossingTime_lt_bddAbove`. -/
lemma ltUpcrossingData_bddAbove_Nat {f : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω} (hab : a < b) :
    BddAbove {n | ltUpcrossingData a b f N n ω} := by
  have heq : {n | ltUpcrossingData a b f N n ω} = {n | upperCrossingTime a b f N n ω < N} := by
    ext n
    rw [Set.mem_setOf, Set.mem_setOf,
        upperCrossingTime_lt_iff_ltUpcrossingData' a b f N n ω hab
          (fun m => hittingBtwnSpec_of_wellFoundedLT f (Set.Ici b) m N ω)
          (fun m => hittingBtwnSpec_of_wellFoundedLT f (Set.Iic a) m N ω)]
  rw [heq]
  exact upperCrossingTime_lt_bddAbove hab

/-- Finiteness for `upcrossingSequenceENat` on `ℕ`, derived from `upperCrossingTime_lt_bddAbove`. -/
lemma upcrossingSequenceENat_finite_Nat {f : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω} (hab : a < b) :
    upcrossingSequenceENat a b f N ω < ⊤ := by
  simp only [upcrossingSequenceENat]
  have hbd : BddAbove {n | ltUpcrossingData a b f N n ω} := ltUpcrossingData_bddAbove_Nat hab
  obtain ⟨M, hM⟩ := hbd
  simp_rw [upperBounds, Set.mem_setOf_eq] at hM
  exact lt_of_le_of_lt (iSup₂_le fun n h => by exact_mod_cast hM h) (ENat.coe_lt_top M)

end DefsEquivalence

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

/-! Monotonicity of ltUpcrossingData with respect to the index set, on {i | i ≤ N}. -/
lemma ltUpcrossingData_mono_index_set_before (f : ι → κ) (N : ι)
    (hsmon : StrictMonoOn f {i | i ≤ N})
    (u : ι → Ω → ℝ) (v : κ → Ω → ℝ) (hv : ∀ i ≤ N, v (f i) = u i) -- u is a restriction of v to f(ι)
    (a b : ℝ) (n : ℕ) (ω : Ω) (hab : a < b) :
    -- u has less upcrossings than v
    ltUpcrossingData a b u N n ω → ltUpcrossingData a b v (f N) n ω := by
  simp only [ltUpcrossingData]
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

/-! Uniform boundedness of ltUpcrossingData, assuming {i | i < N} is finite. -/
lemma ltUpcrossingData_unif_bdd_of_finite (a b : ℝ) (f : ι → Ω → ℝ) (N : ι)
    (hfin : Finite {i | i < N}) :
    ∃ M, ∀ n ω, ltUpcrossingData a b f N n ω → n ≤ M := by
  by_cases hN : N ≤ ⊥
  · simp only [ltUpcrossingData, hN, if_true]
    use 0
    intro n hn
    grind
  · obtain ⟨M, hMsize⟩ := upcrossingData_bounded_of_finite a b f N hfin
    use M
    intro n ω hn
    simp only [ltUpcrossingData, hN, if_false] at hn
    by_cases hnzero : n = 0
    · simp only [hnzero]; grind
    · simp_all
      rcases hn with ⟨hseq, ht_lt_N⟩
      grind

lemma upcrossingSequenceENat_bounded_of_finite (a b : ℝ) (f : ι → Ω → ℝ) (N : ι)
    (hfin : Finite {i | i < N}) :
    ∃ M, ∀ ω, upcrossingSequenceENat a b f N ω ≤ M := by
  obtain ⟨M, hMsize⟩ := ltUpcrossingData_unif_bdd_of_finite a b f N hfin
  use M
  intro ω
  simp only [upcrossingSequenceENat]
  exact iSup₂_le fun n hn => Nat.cast_le.mpr (hMsize n ω hn)

/-! Boundedness of ltUpcrossingData, assuming {i | i < N} is finite. -/
lemma ltUpcrossingData_bddAbove_of_finite (a b : ℝ) (f : ι → Ω → ℝ) (ω : Ω) (N : ι)
    (hfin : Finite {i | i < N}) :
    BddAbove {n | ltUpcrossingData a b f N n ω} := by
  obtain ⟨M, hMsize⟩ := ltUpcrossingData_unif_bdd_of_finite a b f N hfin
  use M
  intro n hn
  grind

/-- `BddAbove` for `ltUpcrossingData` from `upcrossingSequenceENat < ⊤`. -/
lemma ltUpcrossingData_bddAbove_of_upcrossingSequenceENat_lt_top
    {a b : ℝ} {f : ι → Ω → ℝ} {N : ι} {ω : Ω}
    (hfin : upcrossingSequenceENat a b f N ω < ⊤) :
    BddAbove {n | ltUpcrossingData a b f N n ω} := by
  simp only [upcrossingSequenceENat] at hfin
  -- The biSup is < ⊤, so there exists a bound M
  rw [lt_top_iff_ne_top] at hfin
  obtain ⟨M, hM⟩ := WithTop.ne_top_iff_exists.mp hfin
  use M
  intro n hn
  by_contra hcon
  push_neg at hcon
  have h : (n : ℕ∞) ≤ ⨆ k, ⨆ (_ : ltUpcrossingData a b f N k ω), (k : ℕ∞) := by
    apply le_ciSup_of_le (OrderTop.bddAbove _) n
    exact le_iSup_of_le hn le_rfl
  have h' : (n : ℕ∞) ≤ M := le_trans h (le_of_eq hM.symm)
  have h'' : n ≤ M := Nat.cast_le.mp h'
  omega



/-- `upcrossingSequenceENat < ⊤` from `BddAbove` for `ltUpcrossingData`. -/
lemma upcrossingSequenceENat_lt_top_of_bddAbove
    {a b : ℝ} {f : ι → Ω → ℝ} {N : ι} {ω : Ω}
    (hbdd : BddAbove {n | ltUpcrossingData a b f N n ω}) :
    upcrossingSequenceENat a b f N ω < ⊤ := by
  obtain ⟨M, hM⟩ := hbdd
  simp only [upcrossingSequenceENat]
  calc ⨆ n, ⨆ (_ : ltUpcrossingData a b f N n ω), (n : ℕ∞)
      ≤ (M : ℕ∞) := iSup₂_le fun n hn => Nat.cast_le.mpr (hM hn)
    _ < ⊤ := ENat.coe_lt_top M

/-! Monotonicity of upcrossingSequenceENat in the index set, assuming finitely many upcrossings. -/
lemma upcrossingSequenceENat_mono_index_set (f : ι → κ)
    (N : ι) (hsmon : StrictMonoOn f {i | i ≤ N})
    (u : ι → Ω → ℝ) (v : κ → Ω → ℝ) (hv : ∀ i ≤ N, v (f i) = u i) -- u is a restriction of v to f(ι)
    (a b : ℝ) (ω : Ω) (hab : a < b) :
    -- u has less upcrossings than v
    upcrossingSequenceENat a b u N ω ≤ upcrossingSequenceENat a b v (f N) ω := by
  by_cases! hN : N ≤ ⊥
  · have hleftzero : upcrossingSequenceENat a b u N ω = 0 := by
      exact upcrossingSequenceENat_zero_of_N_bot a b u N ω hN
    rw [hleftzero]; simp_all
  · set A := {n | ltUpcrossingData a b u N n ω} with hA
    set B := {n | ltUpcrossingData a b v (f N) n ω} with hB
    have hAsubB : A ⊆ B := by
      intro n hn
      exact ltUpcrossingData_mono_index_set_before f N hsmon u v hv a b n ω hab hn
    exact biSup_mono fun n hn => hAsubB hn

@[deprecated upcrossingSequenceENat_mono_index_set (since := "2025-01-16")]
theorem upcrossingSequenceENat_mono_index_set_of_finite_till_N (f : ι → κ)
    (N : ι) (hsmon : StrictMonoOn f {i | i ≤ N})
    (u : ι → Ω → ℝ) (v : κ → Ω → ℝ) (hv : ∀ i ≤ N, v (f i) = u i) -- u is a restriction of v to f(ι)
    (a b : ℝ) (ω : Ω) (hab : a < b) (_hfin : Finite {i | i < f N}) :
    -- u has less upcrossings than v
    upcrossingSequenceENat a b u N ω ≤ upcrossingSequenceENat a b v (f N) ω :=
  upcrossingSequenceENat_mono_index_set f N hsmon u v hv a b ω hab

end MonotonicityAndBoundedness

/-! To compare upcrossingSequenceENat between NNRat and its finsets (with ⊥) and between them. -/
section UpcrossingsOnFinset

variable {κ : Type*} [LinearOrder κ] [OrderBot κ]
    {s : Finset κ} (hbot : ⊥ ∈ s)

/-! A subset of the index set admits less upcrossings. -/
theorem upcrossingSequenceENat_ge_finset_of_subset (N : s) (u : s → Ω → ℝ) (v : κ → Ω → ℝ)
    (hv : ∀ i : s, v i = u i) -- u is a restriction of v to s
    (a b : ℝ) (ω : Ω) (hab : a < b) :
    -- u has less upcrossings than v
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    upcrossingSequenceENat a b u N ω ≤ upcrossingSequenceENat a b v N ω := by
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
  convert upcrossingSequenceENat_mono_index_set f N hsmon u v hv' a b ω hab using 1

theorem upcrossingSequenceENat_ge_finset {t : Finset κ}
    (hbots : ⊥ ∈ s) (hbott : ⊥ ∈ t) (hst : s ⊆ t)
    (N : s) (u : s → Ω → ℝ) (v : t → Ω → ℝ)
    (hv : ∀ i : s, v ⟨i, hst i.prop⟩ = u i) -- u is a restriction of v to s
    (a b : ℝ) (ω : Ω) (hab : a < b) :
    -- u has less upcrossings than v, and v has finite index set
    letI : OrderBot s := { bot := ⟨⊥, hbots⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    letI : OrderBot t := { bot := ⟨⊥, hbott⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    upcrossingSequenceENat a b u N ω ≤ upcrossingSequenceENat a b v ⟨N, hst N.prop⟩ ω := by
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
  exact upcrossingSequenceENat_mono_index_set f N hsmon u v hv' a b ω hab

end UpcrossingsOnFinset

section DoobInequalityNat

variable {a b : ℝ}

theorem mul_lintegral_upcrossingSequenceENat_le_lintegral_pos_part_aux [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0} (N : ℕ)
    (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
  have hgeq : upcrossingsBeforeENat a b f N = upcrossingSequenceENat a b f N := by
    rw [upcrossingsBeforeENat_eq_upcrossingSequenceENat a b f N hab
      (fun n ω => hittingBtwnSpec_of_wellFoundedLT f (Set.Ici b) n N ω)
      (fun n ω => hittingBtwnSpec_of_wellFoundedLT f (Set.Iic a) n N ω)]
  simp_rw [← hgeq]
  exact mul_lintegral_upcrossingsBeforeENat_le_lintegral_pos_part_aux hf hab

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
    Submartingale (Process.natOfFin u) (Filtration.natOfFin 𝓕) μ :=
  ⟨ fun i => by
      have hsm : StronglyMeasurable[𝓕 (Fin.clamp i n)] (u (Fin.clamp i n)) := by
        exact Submartingale.stronglyMeasurable hf (Fin.clamp i n)
      have hsm' : StronglyMeasurable[Filtration.natOfFin 𝓕 i] (Process.natOfFin u i) := by
        simp only [Process.natOfFin, Filtration.natOfFin]
        exact hsm
      exact hsm',
    fun i j hij => by
      simp only [Process.natOfFin, Filtration.natOfFin]
      refine Submartingale.ae_le_condExp hf ?_
      exact Fin.clamp.monotone i j hij n,
    fun i => by
      simp only [Process.natOfFin]
      exact Submartingale.integrable hf (Fin.clamp i n) ⟩

lemma Process.natOfFin_eq (u : ℕ → Ω → ℝ) (v : Fin n → Ω → ℝ)
    (hNatOfFin : u = Process.natOfFin v) (N : ℕ) :
    ∀ i ≤ N, v (Fin.clamp i n) = u i := fun i _ => by rw [hNatOfFin, Process.natOfFin]

lemma Process.natOfFin_eq' (u : Fin n → Ω → ℝ) (v : ℕ → Ω → ℝ)
    (hNatOfFin : v = Process.natOfFin u) (N : Fin n) :
    ∀ i ≤ N, v i.val = u i := fun i _ => by
  rw [hNatOfFin, Process.natOfFin, Fin.clamp.eq_of_fin n i]

lemma Process.natOfFin.upcrossingSequenceENat_le (u : ℕ → Ω → ℝ) (v : Fin n → Ω → ℝ)
    (hNatOfFin : u = Process.natOfFin v) (N : ℕ) (a b : ℝ) (hab : a < b) (hNn : N < n) :
    upcrossingSequenceENat a b u N ≤ upcrossingSequenceENat a b v (Fin.clamp N n) := by
  set f : ℕ → Fin n := fun i => Fin.clamp i n with hf
  have hsmon : StrictMonoOn f {i | i ≤ N} := Fin.clamp.StrictMonoOn hNn
  have hv : ∀ i ≤ N, v (f i) = u i := Process.natOfFin_eq u v hNatOfFin N
  intro ω
  exact upcrossingSequenceENat_mono_index_set f N hsmon u v hv a b ω hab

lemma Process.natOfFin.upcrossingSequenceENat_ge (u : Fin n → Ω → ℝ) (v : ℕ → Ω → ℝ)
    (hNatOfFin : v = Process.natOfFin u) (N : Fin n) (a b : ℝ) (hab : a < b) :
    upcrossingSequenceENat a b u N ≤ upcrossingSequenceENat a b v N := by
  set f : Fin n → ℕ := fun i => i.val with hf
  have hsmon : StrictMonoOn f {i | i ≤ N} := Fin.val.StrictMonoOn N
  have hv : ∀ i ≤ N, v (f i) = u i := Process.natOfFin_eq' u v hNatOfFin N
  intro ω
  exact upcrossingSequenceENat_mono_index_set f N hsmon u v hv a b ω hab

theorem Process.natOfFin.upcrossingSequenceENat_eq (u : Fin n → Ω → ℝ) (v : ℕ → Ω → ℝ)
    (hNatOfFin : v = Process.natOfFin u) (N : Fin n) (a b : ℝ) (hab : a < b) :
    upcrossingSequenceENat a b u N = upcrossingSequenceENat a b v N := by
  apply le_antisymm
  · exact Process.natOfFin.upcrossingSequenceENat_ge u v hNatOfFin N a b hab
  · conv_rhs => rw [(Fin.clamp.eq_of_fin n N).symm]
    exact Process.natOfFin.upcrossingSequenceENat_le v u hNatOfFin N a b hab (N.isLt)

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
    Submartingale (Process.finOfFinset hk u) (Filtration.finOfFinset hk 𝓕) μ :=
  ⟨ fun i => hf.adapted (Finset.FromFin hk i),
    fun i j hij => by
      simp only [Process.finOfFinset, Filtration.finOfFinset]
      refine Submartingale.ae_le_condExp hf ?_
      exact (Finset.FromFin.StrictMono hk).monotone hij,
    fun i => hf.integrable (Finset.FromFin hk i) ⟩

lemma Process.finOfFinset_eq (u : s → Ω → ℝ) (v : Fin k → Ω → ℝ)
    (hFinOfFinset : v = Process.finOfFinset hk u) (N : s) :
    ∀ i ≤ N, v (Finset.ToFin hk i) = u i := fun i _ => by
  rw [hFinOfFinset, Process.finOfFinset, (Finset.FromFin.ToFin_eq hk i)]

lemma Process.finOfFinset_eq' (u : Fin k → Ω → ℝ) (v : s → Ω → ℝ)
    (hFinOfFinset : u = Process.finOfFinset hk v) (N : Fin k) :
    ∀ i ≤ N, v (Finset.FromFin hk i) = u i := fun i _ => by rw [hFinOfFinset, Process.finOfFinset]

variable [OrderBot ι] (hbot : ⊥ ∈ s) [NeZero k] -- to avoid issues with `Fin 0`

lemma Process.finOfFinset.upcrossingSequenceENat_le (u : Fin k → Ω → ℝ) (v : s → Ω → ℝ)
    (hFinOfFinset : u = Process.finOfFinset hk v) (N : Fin k) (a b : ℝ) (hab : a < b) :
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    upcrossingSequenceENat a b u N ≤ upcrossingSequenceENat a b v (Finset.FromFin hk N) := by
  set f : Fin k → s := fun i => Finset.FromFin hk i with hf
  have hsmon : StrictMonoOn f {i | i ≤ N} := Finset.FromFin.StrictMonoOn hk N
  have hv : ∀ i ≤ N, v (f i) = u i := Process.finOfFinset_eq' hk u v hFinOfFinset N
  intro ω
  convert upcrossingSequenceENat_mono_index_set f N hsmon u v hv a b ω hab using 1

lemma Process.finOfFinset.upcrossingSequenceENat_ge (u : s → Ω → ℝ) (v : Fin k → Ω → ℝ)
    (hFinOfFinset : v = Process.finOfFinset hk u) (N : s) (a b : ℝ) (hab : a < b) :
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    upcrossingSequenceENat a b u N ≤ upcrossingSequenceENat a b v (Finset.ToFin hk N) := by
  set f : s → Fin k := fun i => Finset.ToFin hk i with hf
  have hsmon : StrictMonoOn f {i | i ≤ N} := Finset.ToFin.StrictMonoOn hk N
  have hv : ∀ i ≤ N, v (f i) = u i := Process.finOfFinset_eq hk u v hFinOfFinset N
  intro ω
  convert upcrossingSequenceENat_mono_index_set f N hsmon u v hv a b ω hab using 1

theorem Process.finOfFinset.upcrossingSequenceENat_eq (u : s → Ω → ℝ) (v : Fin k → Ω → ℝ)
    (hFinOfFinset : v = Process.finOfFinset hk u) (N : s) (a b : ℝ) (hab : a < b) :
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    upcrossingSequenceENat a b u N = upcrossingSequenceENat a b v (Finset.ToFin hk N) := by
  apply le_antisymm
  · exact Process.finOfFinset.upcrossingSequenceENat_ge hk hbot u v hFinOfFinset N a b hab
  · set N' := Finset.ToFin hk N with hN'
    have hN : Finset.FromFin hk N' = N := by rw [hN']; exact Finset.FromFin.ToFin_eq hk N
    rw [← hN]
    exact Process.finOfFinset.upcrossingSequenceENat_le hk hbot v u hFinOfFinset N' a b hab

end FinsetToFin

section Measurability
/-!
We use the following, which assumes ι = ℕ :
theorem Adapted.measurable_upcrossingsBefore (hf : Adapted ℱ f) (hab : a < b) :
    Measurable (upcrossingsBefore a b f N)
-/

theorem Adapted.measurable_upcrossingSequenceENat_Nat {f : ℕ → Ω → ℝ} {N : ℕ} {a b : ℝ}
    {𝓕 : Filtration ℕ m0} (hf : Adapted 𝓕 f) (hab : a < b) :
    Measurable (fun ω => (upcrossingSequenceENat a b f N ω : ℝ≥0∞)) := by
  simp_rw [upcrossingSequenceENat_eq_upcrossingsBefore_Nat hab]
  exact measurable_from_top.comp (measurable_from_top.comp (hf.measurable_upcrossingsBefore hab))

variable {n : ℕ} [NeZero n] -- to avoid issues with `Fin 0`

theorem Adapted.measurable_upcrossingSequenceENat_Fin {u : (Fin n) → Ω → ℝ} {N : Fin n} {a b : ℝ}
    {𝓕 : Filtration (Fin n) m0} (hf : Adapted 𝓕 u) (hab : a < b) :
    Measurable (fun ω => (upcrossingSequenceENat a b u N ω : ℝ≥0∞)) := by
  set 𝓕' := Filtration.natOfFin 𝓕 with hFiltr
  set v := Process.natOfFin u with hv
  have hadapted' : Adapted 𝓕' v := fun i => by
    have hsm : StronglyMeasurable[𝓕 (Fin.clamp i n)] (u (Fin.clamp i n)) := by
      exact hf (Fin.clamp i n)
    simp only [v, 𝓕']
    assumption
  have hNatOfFin : v = Process.natOfFin u := rfl
  have hmeas_nat : Measurable (fun ω => (upcrossingSequenceENat a b v N.val ω : ℝ≥0∞)) :=
    Adapted.measurable_upcrossingSequenceENat_Nat hadapted' hab
  have heq : upcrossingSequenceENat a b u N = upcrossingSequenceENat a b v N := by
    exact Process.natOfFin.upcrossingSequenceENat_eq u v hNatOfFin N a b hab
  simp_rw [heq]
  exact hmeas_nat

theorem Adapted.measurable_upcrossingSequenceENat_Finset [LinearOrder ι] [OrderBot ι]
    {s : Finset ι} {k : ℕ} (hk : #s = k) (hbot : ⊥ ∈ s) [NeZero k]
    {u : s → Ω → ℝ} {N : s} {a b : ℝ} {𝓕 : Filtration s m0}
    (hf : Adapted 𝓕 u) (hab : a < b) :
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    Measurable (fun ω => (upcrossingSequenceENat a b u N ω : ℝ≥0∞)) := by
  set 𝓕' := Filtration.finOfFinset hk 𝓕 with hFiltr
  set v := Process.finOfFinset hk u with hv
  have hadapted' : Adapted 𝓕' v := fun i => by
    have hsm : StronglyMeasurable[𝓕 (Finset.FromFin hk i)] (u (Finset.FromFin hk i)) := by
      exact hf (Finset.FromFin hk i)
    simp only [v, 𝓕']
    assumption
  have hFinOfFinset : v = Process.finOfFinset hk u := rfl
  simp_rw [Process.finOfFinset.upcrossingSequenceENat_eq hk hbot u v hFinOfFinset N a b hab]
  exact Adapted.measurable_upcrossingSequenceENat_Fin hadapted' hab

end Measurability

section DoobInequalityFin

variable {n : ℕ} [NeZero n] -- to avoid issues with `Fin 0`
  {u : (Fin n) → Ω → ℝ} {N : Fin n} {𝓕 : Filtration (Fin n) m0} {a b : ℝ}

theorem mul_lintegral_upcrossingSequenceENat_Fin_le_lintegral_pos_part_aux [IsFiniteMeasure μ]
    (hu : Submartingale u 𝓕 μ) (hab : a < b) :
    ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingSequenceENat a b u N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((u N ω - a)⁺) ∂μ := by
  -- We reduce to the `ℕ`-indexed case
  set 𝓕' := Filtration.natOfFin 𝓕 with hFiltr
  set v := Process.natOfFin u with hv
  have hvsub : Submartingale v 𝓕' μ := Submartingale.natOfFin hu
  have hNatOfFin : v = Process.natOfFin u := rfl
  have heq : upcrossingSequenceENat a b u N = upcrossingSequenceENat a b v N := by
    exact Process.natOfFin.upcrossingSequenceENat_eq u v hNatOfFin N a b hab
  rw [heq]
  have huNvN : v N = u N := Process.natOfFin_eq' u v hNatOfFin N N le_rfl
  rw [← huNvN]
  exact mul_lintegral_upcrossingSequenceENat_le_lintegral_pos_part_aux N hvsub hab

end DoobInequalityFin

section DoobInequalityFinset

variable [LinearOrder ι] [OrderBot ι]
  {s : Finset ι} {k : ℕ} (hne : s.Nonempty) (hk : #s = k) (hbot : ⊥ ∈ s) [NeZero k]
  {𝓕 : Filtration s m0} {f : s → Ω → ℝ} {N : s} {a b : ℝ}

theorem mul_lintegral_upcrossingSequenceENat_Finset_le_lintegral_pos_part_aux [IsFiniteMeasure μ]
    (hk : #s = k) (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
  -- We reduce to the `Fin k`-indexed case
  set 𝓕' := Filtration.finOfFinset hk 𝓕
  set v := Process.finOfFinset hk f
  have hvsub : Submartingale v 𝓕' μ := Submartingale.finOfFinset hk hf
  have hFinOfFinset : v = Process.finOfFinset hk f := rfl
  have heq := Process.finOfFinset.upcrossingSequenceENat_eq hk hbot f v hFinOfFinset N a b hab
  rw [heq]
  have huNvN : v (Finset.ToFin hk N) = f N := Process.finOfFinset_eq hk f v hFinOfFinset N N le_rfl
  rw [← huNvN]
  exact mul_lintegral_upcrossingSequenceENat_Fin_le_lintegral_pos_part_aux hvsub hab

theorem Adapted.measurable_upcrossingSequenceENat_Finset' (hk : #s = k)
    (hf : Adapted 𝓕 f) (hab : a < b) :
    haveI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    Measurable (fun ω => (upcrossingSequenceENat a b f N ω : ℝ≥0∞)) := by
  letI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
  exact Adapted.measurable_upcrossingSequenceENat_Finset hk hbot hf hab

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

/-- Helper definition for `upcrossingSequenceENat` on a finset, bundling the `OrderBot` instance.
    This avoids repeating `letI : OrderBot (s n) := { bot := ⟨⊥, hbot n⟩, ... }` throughout
    theorem statements and proofs. -/
noncomputable def upcrossingSequenceENat_finset [LinearOrder ι] [OrderBot ι] {N : ι}
    {s : ℕ → Finset ι} (hbot : ∀ n, ⊥ ∈ s n) (hN : ∀ n, N ∈ s n)
    (a b : ℝ) (f : ι → Ω → ℝ) (n : ℕ) (ω : Ω) : ℕ∞ :=
  letI : OrderBot (s n) := { bot := ⟨⊥, hbot n⟩, bot_le := fun ⟨_, _⟩ => bot_le }
  upcrossingSequenceENat a b (fun i : s n => f i) ⟨N, hN n⟩ ω

section Approximation

variable [LinearOrder ι] [OrderBot ι]
  {a b : ℝ} {f : ι → Ω → ℝ} {N : ι} {ω : Ω}

/-- ι-UpcrossingData of length K, contained in s : Finset ι, yield s-upcrossingSequenceENat ≥ K. -/
lemma upcrossingSequenceENat_finset_ge_of_witness
    {s : Finset ι} (hbot : ⊥ ∈ s) (hN : N ∈ s)
    {K : ℕ} (hKpos : K ≥ 1)
    (hseq : UpcrossingData a b f K ω)
    (ht_lt_N : hseq.t (2 * K - 1) < N)
    (ht_in_s : ∀ i < 2 * K, hseq.t i ∈ s) :
    letI : OrderBot s := { bot := ⟨⊥, hbot⟩, bot_le := fun ⟨_, _⟩ => bot_le }
    K ≤ upcrossingSequenceENat a b (fun i : s => f i) ⟨N, hN⟩ ω := by
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
  have hlt : ltUpcrossingData a b (fun i : s => f i) ⟨N, hN⟩ K ω := by
    simp only [ltUpcrossingData]
    have hNbot' : ¬ (⟨N, hN⟩ : s) ≤ ⊥ := fun h => hNbot h
    simp only [hNbot', ↓reduceIte, Nat.one_le_iff_ne_zero.mp hKpos]
    use hseq'
    simp only [hseq', dif_pos (by omega : 2 * K - 1 < 2 * K)]
    exact ht_lt_N
  -- Therefore upcrossingSequenceENat on s is at least K
  simp only [upcrossingSequenceENat]
  have hbdd : BddAbove (Set.range fun n =>
      ⨆ (_ : ltUpcrossingData a b (fun i : s => f i) ⟨N, hN⟩ n ω), (n : ℕ∞)) := OrderTop.bddAbove _
  exact le_ciSup_of_le hbdd K (le_iSup_of_le hlt le_rfl)

/-- Given a monotone family of finsets saturating `Set.Iic N`, assuming bounded upcrossings,
    the upcrossings on `ι` eventually equal the upcrossings on the finsets. -/
theorem upcrossingSequenceENat_eventually_eq_of_saturating_finsets
    {s : ℕ → Finset ι}
    (hmon : Monotone s)
    (hbot : ∀ n, ⊥ ∈ s n)
    (hN : ∀ n, N ∈ s n)
    (hsaturate : ∀ t : Set ι, Finite t → t ⊆ Set.Iic N →
      ∃ n, t ⊆ s n ∧ ↑(s n) ⊆ Set.Iic N)
    (hab : a < b)
    (hfin : upcrossingSequenceENat a b f N ω < ⊤) :
    ∃ M, ∀ m ≥ M,
      letI : OrderBot (s m) := { bot := ⟨⊥, hbot m⟩, bot_le := fun ⟨_, _⟩ => bot_le }
      upcrossingSequenceENat a b (fun i : s m => f i) ⟨N, hN m⟩ ω =
        upcrossingSequenceENat a b f N ω := by
  -- Derive BddAbove from finiteness
  have hbdd : BddAbove {n | ltUpcrossingData a b f N n ω} :=
    ltUpcrossingData_bddAbove_of_upcrossingSequenceENat_lt_top hfin
  -- Extract natural number K' = sSup
  set K' := sSup {n | ltUpcrossingData a b f N n ω} with hK'def
  have hKeq : upcrossingSequenceENat a b f N ω = (K' : ℕ∞) := by
    simp only [upcrossingSequenceENat]
    exact (ENat.coe_sSup hbdd).symm
  by_cases hK'zero : K' = 0
  · -- K' = 0: any finset works
    use 0
    intro m _
    apply le_antisymm
    · exact upcrossingSequenceENat_ge_finset_of_subset (hbot m) ⟨N, hN m⟩
        (fun i : s m => f i) f (fun _ => rfl) a b ω hab
    · rw [hKeq, hK'zero]; exact zero_le _
  · -- K' ≥ 1: we need to find the witness and ensure the finset contains it
    have hK'pos : K' ≥ 1 := Nat.one_le_iff_ne_zero.mpr hK'zero
    -- N is not ⊥ (otherwise K' = 0)
    have hNbot : ¬ N ≤ ⊥ := by
      intro h
      have hzero : upcrossingSequenceENat a b f N ω = 0 :=
        upcrossingSequenceENat_zero_of_N_bot a b f N ω h
      simp only [hKeq, Nat.cast_eq_zero] at hzero
      exact hK'zero hzero
    -- K' is in the set of ltUpcrossingData
    have hne : {n | ltUpcrossingData a b f N n ω}.Nonempty := by
      use 0
      simp only [Set.mem_setOf, ltUpcrossingData, hNbot, ↓reduceIte]
    have hK'mem : ltUpcrossingData a b f N K' ω := Nat.sSup_mem hne hbdd
    -- Extract the UpcrossingData from K' being in the set
    simp only [ltUpcrossingData, hNbot, ↓reduceIte, hK'zero] at hK'mem
    obtain ⟨hseq, ht_lt_N⟩ := hK'mem
    -- The witness set
    set witness : Set ι := Set.range (fun i : Fin (2 * K') => hseq.t i) with hwit
    have hwit_finite : Finite witness := Set.finite_range _
    have hwit_Icc : witness ⊆ Set.Iic N := by
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      have : hseq.t i ≤ hseq.t (2 * K' - 1) := hseq.mono (by omega)
      exact le_of_lt (lt_of_le_of_lt this ht_lt_N)
    -- Find M such that witness ⊆ s M
    obtain ⟨M', hM'_wit, _⟩ := hsaturate witness hwit_finite hwit_Icc
    use M'
    intro m hm
    apply le_antisymm
    · exact upcrossingSequenceENat_ge_finset_of_subset (hbot m) ⟨N, hN m⟩
        (fun i : s m => f i) f (fun _ => rfl) a b ω hab
    · -- witness ⊆ s m
      have hwit_in_sm : witness ⊆ s m := fun x hx => hmon hm (hM'_wit hx)
      have ht_in_sm : ∀ i < 2 * K', hseq.t i ∈ s m := fun i hi =>
        hwit_in_sm (Set.mem_range.mpr ⟨⟨i, hi⟩, rfl⟩)
      rw [hKeq]
      exact upcrossingSequenceENat_finset_ge_of_witness (hbot m) (hN m) hK'pos hseq ht_lt_N ht_in_sm

/-! In the above setting, hbdd may be replaced by a finite supremum of upcrossingSequenceENat. -/
theorem upcrossingSequenceENat_finite_of_saturating_finsets_finite_sup
    {s : ℕ → Finset ι}
    (hbot : ∀ n, ⊥ ∈ s n)
    (hN : ∀ n, N ∈ s n)
    (hsaturate : ∀ t : Set ι, Finite t → t ⊆ Set.Iic N →
      ∃ n, t ⊆ s n ∧ ↑(s n) ⊆ Set.Iic N)
    (hfinite_sup : ∃ C < ⊤, ∀ n, upcrossingSequenceENat_finset hbot hN a b f n ω ≤ C) :
    upcrossingSequenceENat a b f N ω < ⊤ := by
  -- First establish BddAbove, then convert to < ⊤
  suffices hbdd : BddAbove {n | ltUpcrossingData a b f N n ω} by
    exact upcrossingSequenceENat_lt_top_of_bddAbove hbdd
  obtain ⟨C, hClt, hCbound⟩ := hfinite_sup
  by_cases hNbot : N ≤ ⊥
  · -- N ≤ ⊥ implies {n | ltUpcrossingData a b f N n ω} is empty
    use 0
    intro n hn
    simp only [ltUpcrossingData, hNbot, ↓reduceIte] at hn
    exact absurd hn id
  · -- Use the finite supremum C to bound
    -- First get a natural number bound from C
    rw [lt_top_iff_ne_top] at hClt
    obtain ⟨C', hC'eq⟩ := WithTop.ne_top_iff_exists.mp hClt
    use C'
    intro K hK
    simp only [Set.mem_setOf, ltUpcrossingData, hNbot, ↓reduceIte] at hK
    -- K is positive
    by_cases hKzero : K = 0
    · omega
    · simp only [hKzero, ↓reduceIte] at hK
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
      letI : OrderBot (s n₀) := { bot := ⟨⊥, hbot n₀⟩, bot_le := fun ⟨_, _⟩ => bot_le }
      have h_upcrossings_ge : (K : ℕ∞)
        ≤ upcrossingSequenceENat a b (fun i : s n₀ => f i) ⟨N, hN n₀⟩ ω :=
        upcrossingSequenceENat_finset_ge_of_witness (hbot n₀) (hN n₀)
          (Nat.one_le_iff_ne_zero.mpr hKzero) hseq ht_lt_N
          (fun i hi => hn₀_wit (Set.mem_range.mpr ⟨⟨i, hi⟩, rfl⟩))
      -- This gives K ≤ C'
      have hbound := hCbound n₀
      simp only [upcrossingSequenceENat_finset] at hbound
      rw [← hC'eq] at hbound
      exact ENat.coe_le_coe.mp (le_trans h_upcrossings_ge hbound)


/-! The above two theorems merge into the following. -/
lemma upcrossingSequenceENat_eventually_eq_of_saturating_finsets_finite_sup_aux
    {s : ℕ → Finset ι}
    (hmon : Monotone s)
    (hbot : ∀ n, ⊥ ∈ s n)
    (hN : ∀ n, N ∈ s n)
    (hsaturate : ∀ t : Set ι, Finite t → t ⊆ Set.Iic N →
      ∃ n, t ⊆ s n ∧ ↑(s n) ⊆ Set.Iic N)
    (hab : a < b)
    (hfinite_sup : ∃ C < ⊤, ∀ n, upcrossingSequenceENat_finset hbot hN a b f n ω ≤ C) :
    ∃ M, ∀ m ≥ M, upcrossingSequenceENat_finset hbot hN a b f m ω
      = upcrossingSequenceENat a b f N ω := by
  have hfin : upcrossingSequenceENat a b f N ω < ⊤ :=
    upcrossingSequenceENat_finite_of_saturating_finsets_finite_sup hbot hN hsaturate hfinite_sup
  exact upcrossingSequenceENat_eventually_eq_of_saturating_finsets hmon hbot hN hsaturate hab hfin

/-- The upcrossings count on the full index set equals the supremum of upcrossings counts
    on the approximating finsets, when the latter is bounded. This version provides an
    equality in ℝ (with coercions from ℕ). -/
theorem upcrossingSequenceENat_eq_iSup_finset_real
    {s : ℕ → Finset ι}
    (hmon : Monotone s)
    (hbot : ∀ n, ⊥ ∈ s n)
    (hN : ∀ n, N ∈ s n)
    (hsaturate : ∀ t : Set ι, Finite t → t ⊆ Set.Iic N →
      ∃ n, t ⊆ s n ∧ ↑(s n) ⊆ Set.Iic N)
    (hab : a < b)
    (ω : Ω) (hfinite_sup : ∃ C : ℝ, ∀ n, (upcrossingSequenceENat_finset hbot hN a b f n ω : ℝ) ≤ C) :
    (upcrossingSequenceENat a b f N ω : ℝ) =
      ⨆ n, (upcrossingSequenceENat_finset hbot hN a b f n ω : ℝ) := by
  -- Convert real bound to nat bound
  obtain ⟨C', hCbound'⟩ := hfinite_sup
  let C := Nat.ceil C'
  have hCC : C' ≤ C := Nat.le_ceil C'
  have hCbound : ∃ C, ∀ n, upcrossingSequenceENat_finset hbot hN a b f n ω ≤ C := by
    use C
    intro n
    exact_mod_cast (hCbound' n).trans hCC
  -- Get the stabilization point M
  obtain ⟨M, hM⟩ := upcrossingSequenceENat_eventually_eq_of_saturating_finsets_finite_sup_aux
    hmon hbot hN hsaturate hab hCbound
  -- The sequence is monotone in ℝ
  have hU_mono : Monotone (fun n => (upcrossingSequenceENat_finset hbot hN a b f n ω : ℝ)) := by
    intro n m hnm
    simp only [upcrossingSequenceENat_finset]
    exact Nat.cast_le.mpr (upcrossingSequenceENat_ge_finset (hbot n) (hbot m) (hmon hnm) ⟨N, hN n⟩
      (fun i : s n => f i) (fun i : s m => f i) (fun _ => rfl) a b ω hab)
  -- LHS equals value at M
  have heq1 : (upcrossingSequenceENat a b f N ω : ℝ) =
      (upcrossingSequenceENat_finset hbot hN a b f M ω : ℝ) := by
    exact_mod_cast (hM M le_rfl).symm
  -- RHS (ℝ-supremum) equals value at M
  have heq2 : ⨆ n, (upcrossingSequenceENat_finset hbot hN a b f n ω : ℝ) =
      (upcrossingSequenceENat_finset hbot hN a b f M ω : ℝ) := by
    apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
    · intro n
      by_cases hnM : n ≤ M
      · exact hU_mono hnM
      · push_neg at hnM
        simp only [upcrossingSequenceENat_finset]
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
    (h_pos : ∀ n, 0 ≤ᵐ[μ] f n) (h_int : ∀ n, Integrable (f n) μ) {c : ℝ}
    (h_bound : ∀ n, μ[f n] ≤ c) (h_mono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x)
    (h_sup : ∀ x, (∃ M, ∀ n, f n x ≤ M) → F x = ⨆ n, f n x) :
    Integrable F μ ∧ μ[F] ≤ c := by
  have h_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (f n x)) μ :=
    fun n => (h_int n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have h_mono_ennreal : ∀ᵐ x ∂μ, Monotone fun n => ENNReal.ofReal (f n x) := by
    filter_upwards [h_mono] with x hx n m hnm; exact ENNReal.ofReal_le_ofReal (hx hnm)
  have h_lintegral_bdd n : ∫⁻ x, ENNReal.ofReal (f n x) ∂μ ≤ ENNReal.ofReal c := by
    rw [← ofReal_integral_eq_lintegral_ofReal (h_int n) (h_pos n)]
    exact ENNReal.ofReal_le_ofReal (h_bound n)
  have h_sup_lintegral : ∫⁻ x, ⨆ n, ENNReal.ofReal (f n x) ∂μ ≤ ENNReal.ofReal c :=
    (lintegral_iSup' h_meas h_mono_ennreal).trans_le (iSup_le h_lintegral_bdd)
  have h_sup_lt_top : ∀ᵐ x ∂μ, ⨆ n, ENNReal.ofReal (f n x) < ⊤ :=
    ae_lt_top' (AEMeasurable.iSup h_meas) (h_sup_lintegral.trans_lt ENNReal.ofReal_lt_top).ne
  have h_ae_bdd : ∀ᵐ x ∂μ, ∃ M, ∀ n, f n x ≤ M := by
    filter_upwards [h_sup_lt_top, h_mono, h_pos 0] with x hx_lt_top hx_mono hf0
    refine ⟨(⨆ n, ENNReal.ofReal (f n x)).toReal, fun n => ?_⟩
    by_cases hfn : 0 ≤ f n x
    · calc f n x = (ENNReal.ofReal (f n x)).toReal := (ENNReal.toReal_ofReal hfn).symm
        _ ≤ _ := ENNReal.toReal_mono hx_lt_top.ne (le_iSup (fun n => ENNReal.ofReal (f n x)) n)
    · exact (lt_of_not_ge hfn).le.trans ENNReal.toReal_nonneg
  have h_ae_sup : ∀ᵐ x ∂μ, F x = ⨆ n, f n x := by
    filter_upwards [h_ae_bdd] with x hx; exact h_sup x hx
  have h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (nhds (F x)) := by
    filter_upwards [h_ae_bdd, h_mono, h_ae_sup] with x hx_bdd hx_mono hx_sup
    exact hx_sup ▸ tendsto_atTop_ciSup hx_mono ⟨_, Set.forall_mem_range.mpr hx_bdd.choose_spec⟩
  have hF : AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (h_int n).aestronglyMeasurable) h_tendsto
  have hF_int := integrable_lim_of_mono_L1_bounded h_pos h_int hF h_bound h_mono h_tendsto
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

theorem mul_integral_upcrossingSequenceENat_Countable_le_integral_pos_part_aux [IsFiniteMeasure μ]
    (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    Integrable (fun ω => (upcrossingSequenceENat a b f N ω : ℝ)) μ ∧
    μ[upcrossingSequenceENat a b f N] ≤ μ[fun ω => (f N ω - a)⁺] / (b - a) := by
  -- We approximate Set.Iic N by an increasing family of finsets
  obtain ⟨s, hsmon, hsbot, hsN, hsaturate⟩ := Countable.increasing_finset_family_saturates_Iic N
  -- For each n, define U_n as upcrossings on s n
  let U : ℕ → Ω → ℝ := fun n ω => upcrossingSequenceENat_finset hsbot hsN a b f n ω
  -- The bound c is the same for all n (since f N appears in each finset)
  set c := μ[fun ω => (f N ω - a)⁺] / (b - a) with hc
  set F : Ω → ℝ := fun ω => upcrossingSequenceENat a b f N ω with hF
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
      Adapted.integrable_upcrossingSequenceENat (μ := μ) (hsbot n) (hk n) (hsub n).adapted hab
  · intro n
    simp only [hc, le_div_iff₀' (sub_pos.mpr hab)]
    exact mul_integral_upcrossingSequenceENat_Finset_le_integral_pos_part_aux
      (hbot := hsbot n) (hk := rfl) (hf := hsub n) (N := ⟨N, hsN n⟩) hab
  · filter_upwards with ω n m hnm
    simp only [U, upcrossingSequenceENat_finset]
    exact_mod_cast upcrossingSequenceENat_ge_finset (hsbot n) (hsbot m) (hsmon hnm) ⟨N, hsN n⟩
      (fun i : s n => f i) (fun i : s m => f i) (fun _ => rfl) a b ω hab
  · intro ω hω_bdd; simp only [hF, U]
    exact upcrossingSequenceENat_eq_iSup_finset_real hsmon hsbot hsN hsaturate hab ω hω_bdd

theorem Submartingale.mul_integral_upcrossingSequenceENat_Countable_le_integral_pos_part
    [IsFiniteMeasure μ]
    (hf : Submartingale f 𝓕 μ) :
    (b - a) * μ[upcrossingSequenceENat a b f N] ≤ μ[fun ω => (f N ω - a)⁺] := by
  by_cases! hab : a < b
  · simp only [← le_div_iff₀' (sub_pos.mpr hab)]
    exact (mul_integral_upcrossingSequenceENat_Countable_le_integral_pos_part_aux hf hab).2
  · rw [← sub_nonpos] at hab
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hab (by positivity))
      (integral_nonneg fun ω => posPart_nonneg _)

theorem Submartingale.integrable_upcrossingSequenceENat_Countable
    [IsFiniteMeasure μ]
    (hf : Submartingale f 𝓕 μ) :
    Integrable (fun ω => (upcrossingSequenceENat a b f N ω : ℝ)) μ := by
  by_cases hab : a < b
  · exact (mul_integral_upcrossingSequenceENat_Countable_le_integral_pos_part_aux hf hab).1
  · -- simp only [← sub_nonpos] at hab
    have h_nonpos : (fun ω => (upcrossingSequenceENat a b f N ω : ℝ)) =ᵐ[μ] 0 := by
      filter_upwards with ω
      have := upcrossingSequenceENat_eq_zero_of_not_hab (a:=a) (b:=b) (f:=f) (N:=N) (ω:=ω) hab
      simp_all
    rw [integrable_congr h_nonpos]
    exact integrable_zero Ω ℝ μ

end DoobInequalityCountable

section DoobInequalityNNReal

variable {f : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 m0} [IsFiniteMeasure μ]
  {N : ℝ≥0} {a b : ℝ}

/-!
Let $U_a^b(f,N)$ denote the number of $[a,b]$-crossings of $f$ up to time $N$;
its measurability is ensured by the debut theorem.

For a fixed $N\in R_+$, let $D=Q_+\cup\{N\}$.

For $0<ε<(b-a)/2$,
\[
  EU_a^b(f,N) \le EU_{a+ε}^{b-ε}(f|_D,N) \le \frac{E(f_t-a-ε)^+}{b-a-2ε},
\]
where the latter inequality is the Doob upcrossing inequality applied to $f|_D$, $D$ countable.
Indeed, let us fix a right-continuous trajectory $f · (\omega)$ and denote it by $f$, again;
by continuity,
\begin{align*}
  f_s\le a  &\implies (f|_D)_{s_n}\le a+ε \tekst{for some} s_n\downarrow s, \\
  f_s\ge b  &\implies (f|_D)_{s_n}\ge b-ε \tekst{for some} s_n\downarrow s,
\end{align*}
which yields
$
  U_a^b(f,N) \le U_{a+ε}^{b-ε}(f|_D,N)
$.
The sequence $(s_n)\subset D$; if $s=N$, we take $s_n=N\in D$.
Now, letting $ε\to0$ gives our claim, by monotone convergence in numerator.
-/
lemma disturbed_crossing_le_close_of_crossing (hRC : ∀ ω, RightContinuous (f · ω)) {ε : ℝ}
    (hεpos : 0 < ε) {s t : ℝ≥0} (hst : s < t) {ω : Ω} (ha : f s ω ≤ a) :
    ∃ s' : ℚ≥0, (s' : ℝ≥0) < t ∧ (s' : ℝ≥0) > s ∧ f s' ω ≤ a + ε := by
  have hRC_s : ContinuousWithinAt (f · ω) (Set.Ioi s) s := hRC ω s
  rw [Metric.continuousWithinAt_iff] at hRC_s
  obtain ⟨δ, hδpos, hδ⟩ := hRC_s ε hεpos
  have hts_pos : (0 : ℝ) < t - s := sub_pos.mpr hst
  set δ' : ℝ≥0 := ⟨min (δ / 2) ((t - s) / 2), by positivity⟩
  have hδ'pos : (0 : ℝ≥0) < δ' := (lt_min (by linarith) (by linarith) : (0 : ℝ) < _)
  -- Pick a rational in (s, s + δ')
  obtain ⟨q, hqs, hqδ⟩ := exists_rat_btwn
    (show (s : ℝ) < s + δ' by exact_mod_cast lt_add_of_pos_right s hδ'pos)
  have hq_pos : 0 ≤ q := Rat.cast_nonneg.mp ((NNReal.coe_nonneg s).trans (le_of_lt hqs))
  set s' : ℚ≥0 := ⟨q, hq_pos⟩
  have hs'_val : (s' : ℝ) = q := rfl
  have hs'_gt_s : (s : ℝ) < s' := hqs
  have hs'_lt_δ : (s' : ℝ) < s + δ' := hqδ
  refine ⟨s', ?_, ?_, ?_⟩
  · -- s' < t
    have : (δ' : ℝ) < t - s := (min_le_right _ _).trans_lt (by linarith)
    calc (s' : ℝ) < s + δ' := hs'_lt_δ
      _ < s + (t - s) := add_lt_add_left this s
      _ = t := by ring
  · -- s' > s
    exact hs'_gt_s
  · have hs'_lt_δ' : dist (s' : ℝ≥0) s < δ := by
      have : ((s' : ℝ≥0) : ℝ) = (s' : ℝ) := rfl
      simp only [NNReal.dist_eq, this]
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hs'_gt_s))]
      calc (s' : ℝ) - s < s + δ' - s := by linarith
        _ = δ' := by ring
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    have hdist : dist (f s' ω) (f s ω) < ε := hδ hs'_gt_s hs'_lt_δ'
    linarith [abs_sub_lt_iff.mp (Real.dist_eq _ _ ▸ hdist)]

lemma disturbed_crossing_ge_close_of_crossing (hRC : ∀ ω, RightContinuous (f · ω)) {ε : ℝ}
    (hεpos : 0 < ε) {s t : ℝ≥0} (hst : s < t) {ω : Ω} (hb : f s ω ≥ b) :
    ∃ s' : ℚ≥0, (s' : ℝ≥0) < t ∧ (s' : ℝ≥0) > s ∧ f s' ω ≥ b - ε := by
  obtain ⟨s', h1, h2, h3⟩ := disturbed_crossing_le_close_of_crossing (f := -f) (a := -b)
    (fun ω x => (hRC ω x).neg) hεpos hst (neg_le_neg hb)
  exact ⟨s', h1, h2, by simp only [Pi.neg_apply] at h3; linarith⟩

/-- Given `UpcrossingData a b f K ω` with witness times ending before `N`, and `0 < ε < (b-a)/2`,
    we can construct `UpcrossingData (a + ε) (b - ε) f K ω` with witness times in `ℚ≥0` before `N`.
    This uses right-continuity to "push" each crossing time slightly forward while staying
    within the ε-disturbed thresholds. -/
lemma UpcrossingData.disturb (hRC : ∀ ω, RightContinuous (f · ω)) {K : ℕ} (hKpos : K ≥ 1) {ω : Ω}
    (hseq : UpcrossingData a b f K ω) (ht_lt_N : hseq.t (2 * K - 1) < N) {ε : ℝ} (hεpos : 0 < ε)
    (hε_small : 2 * ε < b - a) :
    ∃ (t' : ℕ → ℚ≥0) (hseq' : UpcrossingData (a + ε) (b - ε) f K ω),
      hseq'.t = (fun i => (t' i : ℝ≥0)) ∧ (t' (2 * K - 1) : ℝ≥0) < N := by
  let bound : ℕ → ℝ≥0 := fun i => if i + 1 < 2 * K then hseq.t (i + 1) else N
  have hbound_gt i (hi : i < 2 * K) : hseq.t i < bound i := by
    simp only [bound]; split_ifs with h
    · exact hseq.t_strict_mono' (Nat.lt_succ_self i) h
    · exact (by omega : i = 2 * K - 1) ▸ ht_lt_N
  have hexists i (hi : i < 2 * K) : ∃ t'_i : ℚ≥0, hseq.t i < t'_i ∧ (t'_i : ℝ≥0) < bound i ∧
      (Even i → f t'_i ω ≤ a + ε) ∧ (Odd i → f t'_i ω ≥ b - ε) := by
    by_cases heven : Even i
    · obtain ⟨s', h1, h2, h3⟩ := disturbed_crossing_le_close_of_crossing hRC hεpos
        (hbound_gt i hi) (hseq.ft_le_a i hi heven)
      exact ⟨s', h2, h1, fun _ => h3, fun ho => absurd heven (Nat.not_even_iff_odd.mpr ho)⟩
    · obtain ⟨s', h1, h2, h3⟩ := disturbed_crossing_ge_close_of_crossing hRC hεpos
        (hbound_gt i hi) (hseq.ft_ge_b i hi (Nat.not_even_iff_odd.mp heven))
      exact ⟨s', h2, h1, fun he => absurd he heven, fun _ => h3⟩
  choose t' ht'_gt ht'_lt ht'_le_a ht'_ge_b using hexists
  let t'' : ℕ → ℚ≥0 := fun i => if h : i < 2 * K then t' i h else t' (2 * K - 1) (by omega)
  have hmono : Monotone (fun i => (t'' i : ℝ≥0)) := fun i j hij => by
    simp only [t'']; split_ifs with hi hj
    · rcases eq_or_lt_of_le hij with rfl | hij_lt; · rfl
      have h2 : bound i ≤ hseq.t j := by
        simp only [bound]
        split_ifs with hi' <;> [exact hseq.mono (Nat.succ_le_of_lt hij_lt); omega]
      exact le_of_lt ((ht'_lt i hi).trans_le (h2.trans (le_of_lt (ht'_gt j hj))))
    · by_cases hi_eq : i = 2 * K - 1
      · subst hi_eq; rfl
      · have h2 : bound i ≤ hseq.t (2 * K - 1) := by
          have : i + 1 < 2 * K := by omega
          simp only [bound, this, ↓reduceIte]; exact hseq.mono (by omega)
        exact le_of_lt ((ht'_lt i hi).trans_le (h2.trans (le_of_lt (ht'_gt _ _))))
    · omega
    · rfl
  refine ⟨t'', ⟨by linarith, fun i => t'' i, hmono,
    fun i hi he => by simp only [t'', hi, ↓reduceDIte]; exact ht'_le_a i hi he,
    fun i hi ho => by simp only [t'', hi, ↓reduceDIte]; exact ht'_ge_b i hi ho⟩, rfl, ?_⟩
  simp only [t'', (by omega : 2 * K - 1 < 2 * K), ↓reduceDIte]
  calc (t' (2 * K - 1) _ : ℝ≥0) < bound (2 * K - 1) := ht'_lt _ _
    _ = N := by simp only [bound]; split_ifs <;> [omega; rfl]

/-- The set `D = ℚ≥0 ∪ {N}` used in the discretization argument for Doob's inequality. -/
def DSet (N : ℝ≥0) : Set ℝ≥0 := {q | ∃ r : ℚ≥0, (r : ℝ≥0) = q} ∪ {N}

lemma DSet_countable (N : ℝ≥0) : (DSet N).Countable := by
  apply Set.Countable.union _ (Set.countable_singleton N)
  have : {q : ℝ≥0 | ∃ r : ℚ≥0, (r : ℝ≥0) = q} = Set.range (fun q : ℚ≥0 => (q : ℝ≥0)) := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_range]
  rw [this]
  have : Countable ℚ≥0 := Subtype.countable
  exact Set.countable_range _

lemma mem_DSet_of_NNRat {N : ℝ≥0} (q : ℚ≥0) : (q : ℝ≥0) ∈ DSet N :=
  Or.inl ⟨q, rfl⟩

lemma zero_mem_DSet (N : ℝ≥0) : (0 : ℝ≥0) ∈ DSet N := by
  convert mem_DSet_of_NNRat (0 : ℚ≥0)
  simp

lemma N_mem_DSet (N : ℝ≥0) : N ∈ DSet N := Or.inr rfl

instance DSet_orderBot (N : ℝ≥0) : OrderBot (DSet N) where
  bot := ⟨0, zero_mem_DSet N⟩
  bot_le := fun ⟨x, _⟩ => zero_le x

instance DSet_countable_inst (N : ℝ≥0) : Countable (DSet N) := (DSet_countable N).to_subtype

/-- When `f` is right-continuous, upcrossings from `a` to `b` in `f` are bounded by
    upcrossings from `(a + ε)` to `(b - ε)` in the restriction of `f` to `D = ℚ≥0 ∪ {N}`. -/
lemma upcrossingSequenceENat_le_upcrossingSequenceENat_restrict_DSet
    (hRC : ∀ ω, RightContinuous (f · ω)) {ε : ℝ} (hεpos : 0 < ε) (hε_small : 2 * ε < b - a)
    (ω : Ω) (hBdd : BddAbove {n | ltUpcrossingData (a + ε) (b - ε) (fun d : DSet N => f d)
      ⟨N, N_mem_DSet N⟩ n ω}) :
    upcrossingSequenceENat a b f N ω ≤
      upcrossingSequenceENat (a + ε) (b - ε) (fun d : DSet N => f d) ⟨N, N_mem_DSet N⟩ ω := by
  set DN := DSet N
  set Nelem : DN := ⟨N, N_mem_DSet N⟩
  haveI : Countable DN := DSet_countable_inst N
  have hNelem_bot : Nelem ≤ ⊥ ↔ N ≤ ⊥ := by simp only [le_bot_iff, Nelem, Subtype.ext_iff]; rfl
  -- If N ≤ ⊥, then LHS = 0 ≤ RHS
  by_cases hNbot : N ≤ ⊥
  · have : {n | ltUpcrossingData a b f N n ω} = ∅ := by
      ext n; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, ltUpcrossingData,
        hNbot, ↓reduceIte]
    simp only [upcrossingSequenceENat, this, csSup_empty]
    exact Nat.zero_le _
  -- Now N > ⊥, so the set is nonempty (contains 0)
  apply csSup_le_csSup
  -- The D-indexed version is bounded (assumed)
  · exact hBdd
  -- The set of K with upcrossings in f is nonempty (0 is always in it when N > ⊥)
  · use 0
    simp only [Set.mem_setOf_eq, ltUpcrossingData, hNbot, ↓reduceIte]
  -- Main inclusion: if K upcrossings exist in f, then K upcrossings exist in f|D
  · intro K hK
    simp only [Set.mem_setOf_eq, ltUpcrossingData, hNelem_bot, hNbot, ↓reduceIte] at hK ⊢
    rcases K with _ | K
    · trivial
    · -- K ≥ 1, so hK : ∃ seq, seq.t (2 * (K+1) - 1) < N
      obtain ⟨hseq, ht_lt_N⟩ := hK
      -- Use disturb to get rational times
      obtain ⟨t', hseq', ht'_eq, ht'_lt_N⟩ := hseq.disturb hRC (by omega : K + 1 ≥ 1)
        ht_lt_N hεpos hε_small
      -- Build UpcrossingData for f|D using the rational times t' (which are in D)
      let t'' : ℕ → DN := fun i => ⟨t' i, mem_DSet_of_NNRat (t' i)⟩
      have ht'_eq' : ∀ i, hseq'.t i = t' i := fun i => congrFun ht'_eq i
      refine ⟨⟨hseq'.hab, t'', ?_, ?_, ?_⟩, ?_⟩
      · -- Monotonicity of t''
        intro i j hij
        simp only [t'', Subtype.mk_le_mk]
        rw [← ht'_eq' i, ← ht'_eq' j]
        exact hseq'.mono hij
      · -- f(t'' i) ≤ a + ε for even i
        intro i hi he
        simp only [t'']
        rw [← ht'_eq' i]
        exact hseq'.ft_le_a i hi he
      · -- f(t'' i) ≥ b - ε for odd i
        intro i hi ho
        simp only [t'']
        rw [← ht'_eq' i]
        exact hseq'.ft_ge_b i hi ho
      · -- t'' (2 * (K+1) - 1) < Nelem
        simp only [t'']
        exact ht'_lt_N

/-- Restrict a filtration on ℝ≥0 to DSet N. -/
def Filtration.restrictDSet (𝓕 : Filtration ℝ≥0 m0) (N : ℝ≥0) :
    Filtration (DSet N) m0 :=
  ⟨fun i => 𝓕 i.val, fun _ _ hij => 𝓕.mono hij, fun i => 𝓕.le i.val⟩

omit [IsFiniteMeasure μ] in
/-- Restrict a submartingale on ℝ≥0 to DSet N. -/
lemma submartingale_restrictDSet (hf : Submartingale f 𝓕 μ) (N : ℝ≥0) :
    Submartingale (fun d : DSet N => f d) (Filtration.restrictDSet 𝓕 N) μ :=
  ⟨fun i => hf.adapted i.val, fun i j hij => hf.2.1 i.val j.val hij, fun i => hf.integrable i.val⟩

/-- The restriction of f to DSet N is integrable in upcrossings. -/
lemma integrable_upcrossingSequenceENat_restrict_DSet (hf : Submartingale f 𝓕 μ)
    {ε : ℝ} (hε_small : 2 * ε < b - a) :
    Integrable (fun ω => (upcrossingSequenceENat (a + ε) (b - ε)
        (fun d : DSet N => f d) ⟨N, N_mem_DSet N⟩ ω : ℝ)) μ := by
  have hab' : a + ε < b - ε := by linarith
  exact (mul_integral_upcrossingSequenceENat_Countable_le_integral_pos_part_aux
    (submartingale_restrictDSet hf N) hab').1

/-- For $0<ε<(b-a)/2$, $EU_a^b(f,N) \le EU_{a+ε}^{b-ε}(f|_D,N)$. -/
lemma integral_upcrossingSequenceENat_le_of_restrict_DSet (hf : Submartingale f 𝓕 μ)
    (hRC : ∀ ω, RightContinuous (f · ω)) {ε : ℝ} (hεpos : 0 < ε)
    (hε_small : 2 * ε < b - a)
    (hBdd : ∀ᵐ ω ∂μ, BddAbove {n | ltUpcrossingData (a + ε) (b - ε) (fun d : DSet N => f d)
      ⟨N, N_mem_DSet N⟩ n ω})
    (hInt : Integrable (fun ω => (upcrossingSequenceENat a b f N ω : ℝ)) μ) :
    μ[fun ω => (upcrossingSequenceENat a b f N ω : ℝ)] ≤
      μ[fun ω => (upcrossingSequenceENat (a + ε) (b - ε)
        (fun d : DSet N => f d) ⟨N, N_mem_DSet N⟩ ω : ℝ)] := by
  apply integral_mono_ae
  · exact hInt
  · exact integrable_upcrossingSequenceENat_restrict_DSet hf hε_small
  · filter_upwards [hBdd] with ω hBdd_ω
    exact Nat.cast_le.mpr
      (upcrossingSequenceENat_le_upcrossingSequenceENat_restrict_DSet hRC hεpos hε_small ω hBdd_ω)

/-- For $0<ε<(b-a)/2$, $EU_{a+ε}^{b-ε}(f|_D,N) \le \frac{E(f_N-a-ε)^+}{b-a-2ε}$.
    This follows from the discrete Doob inequality applied to the restriction of f to D. -/
lemma mul_integral_upcrossingSequenceENat_restrict_DSet_le (hf : Submartingale f 𝓕 μ)
    {ε : ℝ} (hε_small : 2 * ε < b - a) :
    (b - a - 2 * ε) * μ[fun ω => (upcrossingSequenceENat (a + ε) (b - ε)
        (fun d : DSet N => f d) ⟨N, N_mem_DSet N⟩ ω : ℝ)] ≤
      μ[fun ω => (f N ω - (a + ε))⁺] := by
  have hab' : a + ε < b - ε := by linarith
  have hba : b - ε - (a + ε) = b - a - 2 * ε := by ring
  rw [← hba]
  exact Submartingale.mul_integral_upcrossingSequenceENat_Countable_le_integral_pos_part
    (submartingale_restrictDSet hf N)



theorem mul_integral_upcrossingSequenceENat_NNReal_le_integral_pos_part_aux (hf : Submartingale f 𝓕 μ)
    (hRC : ∀ ω, RightContinuous (f · ω)) (hab : a < b) :
    (b - a) * μ[upcrossingSequenceENat a b f N] ≤ μ[fun ω => (f N ω - a)⁺] := by
  sorry



/-- Right-continuous process hits the closed set at the corresponding hitting time. -/
lemma hittingBtwnSpec_of_right_continuous (s : Set ℝ) (n m : ℝ≥0) (ω : Ω)
    (hs : IsClosed s) (hRC : Function.RightContinuous (f · ω)) :
    HittingBtwnSpec f s n m ω := by
  constructor
  intro ht
  have h_exists : ∃ j ∈ Set.Icc n m, f j ω ∈ s := by
    by_contra h_neg; simp only [hittingBtwn, h_neg, ↓reduceIte] at ht; exact lt_irrefl m ht
  set S := Set.Icc n m ∩ {i | f i ω ∈ s}
  have h_eq : hittingBtwn f s n m ω = sInf S := by simp only [hittingBtwn, h_exists, ↓reduceIte, S]
  have hne : S.Nonempty := h_exists
  have hbdd : BddBelow S := ⟨n, fun x hx => hx.1.1⟩
  obtain ⟨u, -, hu_tendsto, hu_mem⟩ := exists_seq_tendsto_sInf hne hbdd
  rw [h_eq]
  by_cases h_mem_S : sInf S ∈ S
  · exact h_mem_S.2
  · have hu_Ioi : ∀ n, u n ∈ Set.Ioi (sInf S) := fun n =>
      lt_of_le_of_ne (csInf_le hbdd (hu_mem n)) (fun heq => h_mem_S (heq ▸ hu_mem n))
    have h_tendsto_within : Tendsto u atTop (nhdsWithin (sInf S) (Set.Ioi (sInf S))) :=
      tendsto_nhdsWithin_iff.mpr ⟨hu_tendsto, Filter.Eventually.of_forall hu_Ioi⟩
    exact hs.mem_of_tendsto ((hRC (sInf S)).tendsto.comp h_tendsto_within)
      (Filter.Eventually.of_forall fun n => (hu_mem n).2)

theorem upcrossingsBeforeENat_eq_upcrossingSequenceENat (hRC : ∀ ω, RightContinuous (f · ω))
    (hab : a < b) :
    upcrossingsBeforeENat a b f N = upcrossingSequenceENat a b f N :=
  upcrossingsBeforeENat_eq_upcrossingSequenceENat a b f N hab
    (fun n ω => hittingBtwnSpec_of_right_continuous (Set.Ici b) n N ω isClosed_Ici (hRC ω))
    (fun n ω => hittingBtwnSpec_of_right_continuous (Set.Iic a) n N ω isClosed_Iic (hRC ω))

theorem mul_integral_upcrossingsBeforeENat_NNReal_le_integral_pos_part_aux (hf : Submartingale f 𝓕 μ)
    (hRC : ∀ ω, RightContinuous (f · ω)) (hab : a < b) :
    (b - a) * μ[upcrossingsBeforeENat a b f N] ≤ μ[fun ω => (f N ω - a)⁺] := by
  rw [upcrossingsBeforeENat_eq_upcrossingSequenceENat hRC hab]
  exact mul_integral_upcrossingSequenceENat_NNReal_le_integral_pos_part_aux hf hRC hab

theorem Submartingale.mul_integral_upcrossingsBeforeENat_NNReal_le_integral_pos_part
    (hf : Submartingale f 𝓕 μ)
    (hRC : ∀ ω, RightContinuous (f · ω)) :
    (b - a) * μ[upcrossingsBeforeENat a b f N] ≤ μ[fun ω => (f N ω - a)⁺] := by
  by_cases! hab : a < b
  · exact mul_integral_upcrossingsBeforeENat_NNReal_le_integral_pos_part_aux hf hRC hab
  · rw [← sub_nonpos] at hab
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hab (by positivity))
      (integral_nonneg fun ω => posPart_nonneg _)

end DoobInequalityNNReal


/-- Rationale for ⨆ instead of sSup in the definitions. -/
example : sSup (Set.univ : Set ℕ) = 0 := by
  have h : ¬ BddAbove (Set.univ : Set ℕ) := by
    intro ⟨M, hM⟩
    have : M + 1 ≤ M := hM (Set.mem_univ (M + 1))
    omega
  rw [csSup_of_not_bddAbove h, csSup_empty]
  rfl

/-- Submartingale has integrable t-values and our RHS in DUI is thus finite. -/
example {f : ℕ → Ω → ℝ} {N : ℕ} {a : ℝ} (hInt : Integrable (fun ω => (f N ω - a)⁺) μ) :
    ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ < ∞ := by
  rw [← hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ => posPart_nonneg _))]
  exact hInt.hasFiniteIntegral

/-- Since the LHS in DUI is finite, the integral of upcrossingsBefore is finite. -/
example {f : Ω → ℝ≥0∞} {ω : Ω} (hab : a < b)
    (hmeas : AEMeasurable f μ)
    (h : ENNReal.ofReal (b - a) * ∫⁻ ω, f ω ∂μ < ⊤) :
    ∀ᵐ ω ∂μ, f ω < ⊤ := by
  have hba_ne_zero : ENNReal.ofReal (b - a) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hlint : ∫⁻ ω, f ω ∂μ ≠ ⊤ := by
    intro hcontra
    simp only [hcontra] at h
    rw [ENNReal.mul_top] at h
    simp_all
  exact_mod_cast ae_lt_top' hmeas hlint



end ProbabilityTheory
