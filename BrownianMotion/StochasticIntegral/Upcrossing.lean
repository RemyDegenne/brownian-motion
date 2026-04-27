/-
Copyright (c) 2025 Wojciech Czernous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Czernous
-/
module

public import BrownianMotion.Auxiliary.ENNReal
public import BrownianMotion.StochasticIntegral.Cadlag
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Probability.Martingale.Upcrossing

@[expose] public section

/-! # Doob's upcrossing inequality on NNRat

-/

open MeasureTheory Filter Finset Function
open scoped ENNReal NNReal

namespace MeasureTheory

/-! The original definitions, valid for `InfSet` (hence not for `NNRat`), are:

noncomputable def upperCrossingTime [Preorder ι] [OrderBot ι] [InfSet ι] (a b : ℝ) (f : ι → Ω → ℝ)
    (N : ι) : ℕ → Ω → ι
  | 0 => ⊥
  | n + 1 => fun ω =>
    hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f (upperCrossingTime a b f N n ω) N ω) N ω

noncomputable def upcrossingsBefore [Preorder ι] [OrderBot ι] [InfSet ι] (a b : ℝ) (f : ι → Ω → ℝ)
    (N : ι) (ω : Ω) : ℕ :=
  sSup {n | upperCrossingTime a b f N n ω < N}

-- BUT:

example : sSup (Set.univ : Set ℕ) = 0 := by
  have h : ¬ BddAbove (Set.univ : Set ℕ) := by
    intro ⟨M, hM⟩
    have : M + 1 ≤ M := hM (Set.mem_univ (M + 1))
    omega
  rw [csSup_of_not_bddAbove h, csSup_empty]
  rfl

-- which is why we use ⨆ instead of sSup in the following definitions.
-/

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {a b : ℝ}

/-- Upcrossings number that is infinite when optional times accumulate before N. -/
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

/-- Doob's upcrossing inequality on ℕ, with `upcrossingsBefore` and Lebesgue integral. -/
theorem mul_lintegral_upcrossingsBefore_le_lintegral_pos_part [IsFiniteMeasure μ]
    {𝓕 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ}
    (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingsBefore a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
  have hint : Integrable (fun ω => (upcrossingsBefore a b f N ω : ℝ)) μ :=
    hf.stronglyAdapted.integrable_upcrossingsBefore hab
  have hpos_int : Integrable (fun ω => (f N ω - a)⁺) μ :=
    ((hf.integrable N).sub (integrable_const a)).pos_part
  have hcast : ∫⁻ ω, (upcrossingsBefore a b f N ω : ℝ≥0∞) ∂μ
      = ENNReal.ofReal (∫ ω, (upcrossingsBefore a b f N ω : ℝ) ∂μ) := by
    rw [lintegral_congr fun ω => (ENNReal.ofReal_natCast _).symm,
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => Nat.cast_nonneg _)]
  rw [hcast,
    ← ofReal_integral_eq_lintegral_ofReal hpos_int (ae_of_all _ fun _ => posPart_nonneg _),
    ← ENNReal.ofReal_mul (sub_pos.mpr hab).le]
  exact ENNReal.ofReal_le_ofReal
    (mul_integral_upcrossingsBefore_le_integral_pos_part_aux (N := N) hf hab)

/-- Doob's upcrossing inequality on ℕ, with `upcrossingsBeforeENat` and Lebesgue integral. -/
theorem mul_lintegral_upcrossingsBeforeENat_le_lintegral_pos_part [IsFiniteMeasure μ]
    {𝓕 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ}
    (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingsBeforeENat a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
  simp_rw [upcrossingsBeforeENat_eq_upcrossingsBefore_Nat hab, ENat.toENNReal_coe]
  exact mul_lintegral_upcrossingsBefore_le_lintegral_pos_part hf hab

/-- Data structure representing an upcrossing sequence for a stochastic process. -/
structure UpcrossingData [PartialOrder ι] (a b : ℝ) (f : ι → Ω → ℝ) (n : ℕ) (ω : Ω) where
  hab : a < b
  /-- Sequence `s_1 < t_1 < s_2 < t_2 < ... < s_n < t_n ≤ ...`, see blueprint;
      renamed as `t_0 < t_1 < ...`. -/
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

/-- Restricts the infinite sequence to the finite set `Fin (2 * n)`. -/
def t_on_Fin2n : Fin (2 * n) → ι := fun x => h.t x.toNat

lemma t_strict_mono_on_Fin2n : StrictMono h.t_on_Fin2n := by
  intro x y hxy
  exact h.t_strict_mono' hxy y.isLt

/-- Shortens an upcrossing sequence by removing the last two points,
    so that the length decreases by one. -/
def toShorter {a b : ℝ} {f : ι → Ω → ℝ} {n : ℕ} {ω : Ω} (h : UpcrossingData a b f (n + 1) ω) :
    UpcrossingData a b f n ω := ⟨ h.hab, h.t, h.mono,
    fun i hi hi_even => h.ft_le_a i (by grind) hi_even,
    fun i hi hi_odd => h.ft_ge_b i (by grind) hi_odd ⟩

/-- An extension of an upcrossing sequence by adding two more points `s` and `t`. -/
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

/-- The term `ltUpcrossingData a b f N n ω` is abbreviated as `L n`; see the blueprint. -/
noncomputable def ltUpcrossingData [LinearOrder ι] [OrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) : Prop :=
  if N ≤ ⊥ then False else -- to make {n | ...} empty when N = ⊥, same as in upperCrossingTime
    if n = 0 then True else
      ∃ seq : UpcrossingData a b f n ω, seq.t (2 * n - 1) < N

/-- The maximal length of upcrossing sequence (strictly) before time `N`. Suitable for MCT proof. -/
noncomputable def upcrossingSequenceENat [LinearOrder ι] [OrderBot ι] (a b : ℝ) (f : ι → Ω → ℝ)
    (N : ι) (ω : Ω) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ltUpcrossingData a b f N n ω), (n : ℕ∞)

/-! `ltUpcrossingData a b f N n ω ↔ upperCrossingTime a b f N n ω < N` -/
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
  refine Nat.rec (motive := fun n => ∀ hseq : UpcrossingData a b f (n+1) ω, hseq.t (2 * n + 1) ≤ N →
    upperCrossingTime a b f N (n+1) ω ≤ hseq.t (2 * n + 1)) ?base ?step
  · intro hseq h_t1_le_N
    simp only [upperCrossingTime]
    exact upperCrossingTime_le_of_UpcrossingData' a b f ⊥ (hseq.t 0) (hseq.t 1) N ω
      bot_le (hseq.mono (by simp)) h_t1_le_N
      (hseq.ft_le_a 0 (by simp) Even.zero) (hseq.ft_ge_b 1 (by simp) (by grind))
  · intro n ih hseq2 htN
    have ht's : hseq2.t (2 * n + 1) ≤ hseq2.t (2 * n + 2) := hseq2.mono (Nat.le_succ _)
    have hst : hseq2.t (2 * n + 2) ≤ hseq2.t (2 * n + 3) := hseq2.mono (Nat.le_succ _)
    exact upperCrossingTime_le_of_UpcrossingData' a b f _ _ _ N ω
      ((ih hseq2.toShorter (ht's.trans (hst.trans htN))).trans ht's) hst htN
      (hseq2.ft_le_a (2 * n + 2) (by grind) (by grind))
      (hseq2.ft_ge_b (2 * n + 3) (by grind) (by grind))

/-- The term `upcrossingsBeforeUpperCrossingTime a b f N n ω` is abbreviated as `Q n`;
    see the blueprint. -/
noncomputable def upcrossingsBeforeUpperCrossingTime [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) : Prop :=
  if N ≤ ⊥ then False else
    if n = 0 then True else
      ∃ seq : UpcrossingData a b f n ω, seq.t (2 * n - 1) ≤ upperCrossingTime a b f N n ω

/-- The term `upperCrossingTimeLT a b f N n ω` is abbreviated as `P n`; see the blueprint. -/
noncomputable def upperCrossingTimeLT [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) : Prop :=
  if N ≤ ⊥ then False else
    if n = 0 then True else
      upperCrossingTime a b f N n ω < N

/-!
  The current aim is to establish `∀ n, P n ↔ L n`.
-/

/-! Auxiliary equivalence lemma. -/
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

/-! The equivalence `P n ↔ L n` in the case `N = ⊥`. -/
lemma upperCrossingTimeLT_bot_iff_ltUpcrossingData [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) (hN : N ≤ ⊥) :
    upperCrossingTimeLT a b f N n ω ↔ ltUpcrossingData a b f N n ω := by
  simp only [ltUpcrossingData, hN, if_true]
  simp only [upperCrossingTimeLT, hN, if_true]

/-! The left implication `∀ n, L n → P n` in the case `N ≠ ⊥`. -/
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
  It remains to prove the right implication `∀ n, P n → L n` in the case `N ≠ ⊥`.
-/

/-! Clearly, `P n → Q n → L n` in the case `N ≠ ⊥`. -/
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

/-! `P n` gives a pair of witnesses, useful for establishing `Q n`. -/
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

/-! `P 1 → Q 1` in the case `N ≠ ⊥`. -/
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

/-! `P (n+1) → Q n → Q (n+1)` in the case `N ≠ ⊥`. -/
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

/-! `P (n+1) → P n`. -/
lemma upperCrossingTimeLT_of_upperCrossingTimeLT [ConditionallyCompleteLinearOrderBot ι]
  (a b : ℝ) (f : ι → Ω → ℝ) (N : ι) (n : ℕ) (ω : Ω) :
  upperCrossingTimeLT a b f N (n+1) ω → upperCrossingTimeLT a b f N n ω := by
  intro hup
  rw [upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N (n+1) ω] at hup
  rw [upperCrossingTimeLT_iff_upperCrossingTime_lt a b f N n ω]
  refine lt_of_le_of_lt ?_ hup
  exact upperCrossingTime_mono (Nat.le_succ n)

/-! `∀ n ≥ 1, P n → Q n` in the case `N ≠ ⊥`. -/
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

/-! The right implication `∀ n, P n → L n` in the case `N ≠ ⊥`. -/
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

/-! Finally, the equivalence `∀ n, P n ↔ L n`. -/
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

/-! Auxiliary lemma for converting between `upperCrossingTime` and `ltUpcrossingData`. -/
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

/-! The two definitions of `upcrossing*ENat` are equivalent; measurability follows via
    `upcrossingsBeforeENat`. -/
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

/-! `BddAbove` for `ltUpcrossingData` on `ℕ`, derived from `upperCrossingTime_lt_bddAbove`. -/
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

end DefsEquivalence

section MonotonicityAndBoundedness

variable [LinearOrder ι]

/-! Given a finite `{i | i < N}`, the size of `UpcrossingData` is bounded,
    assuming `UpcrossingData < N`. -/
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

/-! Monotonicity of `ltUpcrossingData` with respect to the index set on `{i | i ≤ N}`. -/
lemma ltUpcrossingData_mono_index_set_before (f : ι → κ) (N : ι)
    (hsmon : StrictMonoOn f {i | i ≤ N})
    (u : ι → Ω → ℝ) (v : κ → Ω → ℝ) (hv : ∀ i ≤ N, v (f i) = u i) -- u is a restriction of v to f(ι)
    (a b : ℝ) (n : ℕ) (ω : Ω) (hab : a < b) :
    -- u has less upcrossings than v
    ltUpcrossingData a b u N n ω → ltUpcrossingData a b v (f N) n ω := by
  simp only [ltUpcrossingData]
  by_cases hN : N ≤ ⊥
  · simp only [hN, ↓reduceIte, false_implies]
  · simp only [hN, ↓reduceIte]
    push Not at hN
    have hbot : ¬ f N ≤ ⊥ :=
      not_le.mpr (lt_of_le_of_lt (OrderBot.bot_le _) (hsmon bot_le le_rfl hN))
    simp only [hbot, ↓reduceIte]
    by_cases hnzero : n = 0
    · simp only [hnzero, ↓reduceIte, true_implies]
    · simp only [hnzero, ↓reduceIte]
      rintro ⟨hseq, ht_lt_N⟩
      have hmon : MonotoneOn f {i | i ≤ N} := hsmon.monotoneOn
      have htIn (j : ℕ) (hj : j < 2 * n) : hseq.t j ∈ {i | i ≤ N} :=
        (hseq.mono (by grind : j ≤ 2 * n - 1)).trans (le_of_lt ht_lt_N)
      refine ⟨⟨hab, fun i => if i < 2 * n then f (hseq.t i) else f N,
        fun i j hij => ?_, fun i hi heven => ?_, fun i hi hodd => ?_⟩, ?_⟩
      · by_cases hi : i < 2 * n <;> by_cases hj : j < 2 * n <;> simp only [*, ↓reduceIte]
        · exact hmon (htIn _ hi) (htIn _ hj) (hseq.mono hij)
        · exact hmon (htIn _ hi) le_rfl (by grind)
        · grind
        · rfl
      · simp only [hi, ↓reduceIte, hv _ (htIn i hi)]; exact hseq.ft_le_a i hi heven
      · simp only [hi, ↓reduceIte, hv _ (htIn i hi)]; exact hseq.ft_ge_b i hi hodd
      · simp only [(by grind : 2 * n - 1 < 2 * n), ↓reduceIte]
        exact hsmon (htIn _ (by grind)) le_rfl ht_lt_N

/-! Uniform boundedness of `ltUpcrossingData`, assuming `{i | i < N}` is finite. -/
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

/-! Monotonicity of `upcrossingSequenceENat` with respect to the index set. -/
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

end MonotonicityAndBoundedness

/-- Helper: a `Finset` containing `⊥` inherits an `OrderBot` instance via the inclusion. -/
abbrev Finset.orderBotOfBotMem {ι : Type*} [LE ι] [OrderBot ι] {s : Finset ι} (hbot : ⊥ ∈ s) :
    OrderBot s where
  bot := ⟨⊥, hbot⟩
  bot_le _ := bot_le

/-! To compare upcrossingSequenceENat between NNRat and its finsets (with ⊥) and between them. -/
section UpcrossingsOnFinset

variable {κ : Type*} [LinearOrder κ] [OrderBot κ]
    {s : Finset κ} (hbot : ⊥ ∈ s)

/-! A subset of the index set admits less upcrossings. -/
theorem upcrossingSequenceENat_ge_finset_of_subset (N : s) (u : s → Ω → ℝ) (v : κ → Ω → ℝ)
    (hv : ∀ i : s, v i = u i) -- u is a restriction of v to s
    (a b : ℝ) (ω : Ω) (hab : a < b) :
    -- u has less upcrossings than v
    haveI : OrderBot s := Finset.orderBotOfBotMem hbot
    upcrossingSequenceENat a b u N ω ≤ upcrossingSequenceENat a b v N ω := by
  set f : s → κ := fun i => (i : κ)
  have hsmon : StrictMonoOn f {i | i ≤ N} := fun _ _ _ _ hij => hij
  have hv' : ∀ i ≤ N, v (f i) = u i := fun i _ => hv i
  have hfN : f N = N := rfl
  rw [← hfN]
  convert upcrossingSequenceENat_mono_index_set f N hsmon u v hv' a b ω hab using 1

theorem upcrossingSequenceENat_ge_finset {t : Finset κ}
    (hbots : ⊥ ∈ s) (hbott : ⊥ ∈ t) (hst : s ⊆ t)
    (N : s) (u : s → Ω → ℝ) (v : t → Ω → ℝ)
    (hv : ∀ i : s, v ⟨i, hst i.prop⟩ = u i) -- u is a restriction of v to s
    (a b : ℝ) (ω : Ω) (hab : a < b) :
    -- u has less upcrossings than v, and v has finite index set
    letI : OrderBot s := Finset.orderBotOfBotMem hbots
    letI : OrderBot t := Finset.orderBotOfBotMem hbott
    upcrossingSequenceENat a b u N ω ≤ upcrossingSequenceENat a b v ⟨N, hst N.prop⟩ ω := by
  letI : OrderBot s := Finset.orderBotOfBotMem hbots
  letI : OrderBot t := Finset.orderBotOfBotMem hbott
  -- The inclusion map from s into t
  set f : s → t := fun i => ⟨i, hst i.prop⟩ with hf
  have hsmon : StrictMonoOn f {i | i ≤ N} := fun _ _ _ _ hij => hij
  have hfN : f N = ⟨N, hst N.prop⟩ := rfl
  rw [← hfN]
  exact upcrossingSequenceENat_mono_index_set f N hsmon u v (fun i _ => hv i) a b ω hab

end UpcrossingsOnFinset

section DoobInequalityNat

variable {a b : ℝ}

theorem mul_lintegral_upcrossingSequenceENat_le_lintegral_pos_part [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0} (N : ℕ)
    (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
  have hgeq : upcrossingsBeforeENat a b f N = upcrossingSequenceENat a b f N := by
    rw [upcrossingsBeforeENat_eq_upcrossingSequenceENat a b f N hab
      (fun n ω => hittingBtwnSpec_of_wellFoundedLT f (Set.Ici b) n N ω)
      (fun n ω => hittingBtwnSpec_of_wellFoundedLT f (Set.Iic a) n N ω)]
  simp_rw [← hgeq]
  exact mul_lintegral_upcrossingsBeforeENat_le_lintegral_pos_part hf hab

end DoobInequalityNat

section FinToNat

variable {n : ℕ} [NeZero n] -- to avoid issues with `Fin 0`
variable {u : (Fin n) → Ω → ℝ} {N : Fin n}

/-- Clamps a natural number to the range of `Fin n`. -/
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
  simp only [Fin.lt_def, Fin.clamp]
  grind

/-- Embedding of a filtration defined on `Fin n` into a filtration defined on `ℕ`. -/
def Filtration.natOfFin (𝓕 : Filtration (Fin n) m0) : Filtration ℕ m0 :=
  ⟨ fun i => 𝓕 (Fin.clamp i n),
    fun i j hij => by
      refine 𝓕.mono ?_
      simp only [Fin.clamp, Fin.le_iff_val_le_val]
      exact min_le_min hij (Nat.le_refl _),
    fun i => Filtration.le 𝓕 (Fin.clamp i n) ⟩

variable {𝓕 : Filtration (Fin n) m0}

/-- Embedding of a process defined on `Fin n` into a process defined on `ℕ`. -/
def Process.natOfFin (u : Fin n → Ω → ℝ) : ℕ → Ω → ℝ := fun k => u (Fin.clamp k n)

lemma Submartingale.natOfFin (hf : Submartingale u 𝓕 μ) :
    Submartingale (Process.natOfFin u) (Filtration.natOfFin 𝓕) μ :=
  ⟨ fun i => by
      have hsm : StronglyMeasurable[𝓕 (Fin.clamp i n)] (u (Fin.clamp i n)) := by
        exact Submartingale.stronglyMeasurable hf (Fin.clamp i n)
      have hsm' : StronglyMeasurable[Filtration.natOfFin 𝓕 i] (Process.natOfFin u i) := by
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
    (hNatOfFin : u = Process.natOfFin v) :
    ∀ i, v (Fin.clamp i n) = u i := fun i => by rw [hNatOfFin, Process.natOfFin]

lemma Process.natOfFin_eq' (u : Fin n → Ω → ℝ) (v : ℕ → Ω → ℝ)
    (hNatOfFin : v = Process.natOfFin u) :
    ∀ i, v i.val = u i := fun i => by
  rw [hNatOfFin, Process.natOfFin, Fin.clamp.eq_of_fin n i]

lemma Process.natOfFin.upcrossingSequenceENat_le (u : ℕ → Ω → ℝ) (v : Fin n → Ω → ℝ)
    (hNatOfFin : u = Process.natOfFin v) (N : ℕ) (a b : ℝ) (hab : a < b) (hNn : N < n) :
    upcrossingSequenceENat a b u N ≤ upcrossingSequenceENat a b v (Fin.clamp N n) := by
  set f : ℕ → Fin n := fun i => Fin.clamp i n
  have hsmon : StrictMonoOn f {i | i ≤ N} := Fin.clamp.StrictMonoOn hNn
  have hv : ∀ i ≤ N, v (f i) = u i :=  fun i _ => Process.natOfFin_eq u v hNatOfFin i
  intro ω
  exact upcrossingSequenceENat_mono_index_set f N hsmon u v hv a b ω hab

lemma Process.natOfFin.upcrossingSequenceENat_ge (u : Fin n → Ω → ℝ) (v : ℕ → Ω → ℝ)
    (hNatOfFin : v = Process.natOfFin u) (N : Fin n) (a b : ℝ) (hab : a < b) :
    upcrossingSequenceENat a b u N ≤ upcrossingSequenceENat a b v N := by
  set f : Fin n → ℕ := fun i => i.val
  have hsmon : StrictMonoOn f {i | i ≤ N} := fun _ _ _ _ hij => hij
  have hv : ∀ i ≤ N, v (f i) = u i := fun i _ => Process.natOfFin_eq' u v hNatOfFin i
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

/-- Order isomorphism between `Fin k` and a finite set. -/
def Finset.orderIso : Fin k ≃o s := by exact Finset.orderIsoOfFin s hk

/-- Order embedding from `Fin k` to a finite set, constructed from `Finset.orderIso`. -/
def Finset.FromFin : Fin k → s := fun n => Finset.orderIso hk n

/-- Order embedding from a finite set to `Fin k`, the inverse of `Finset.FromFin`. -/
def Finset.ToFin : s → Fin k := fun i => (Finset.orderIso hk).symm i

lemma Finset.FromFin.ToFin_eq (i : s) :
    Finset.FromFin hk (Finset.ToFin hk i) = i := by
  rw [Finset.ToFin, Finset.FromFin]
  exact OrderIso.apply_symm_apply (Finset.orderIso hk) i

/-- Filtration defined on a finite set converted to a filtration on `Fin k`. -/
def Filtration.finOfFinset (𝓕 : Filtration s m0) : Filtration (Fin k) m0 :=
  ⟨ fun i => 𝓕 (Finset.FromFin hk i),
    fun i j hij => by refine 𝓕.mono ?_; exact (Finset.orderIso hk).strictMono.monotone hij,
    fun i => Filtration.le 𝓕 (Finset.FromFin hk i) ⟩

variable {𝓕 : Filtration s m0}

/-- Process defined on a finite set converted to a process on `Fin k`. -/
def Process.finOfFinset (u : s → Ω → ℝ) : Fin k → Ω → ℝ := fun i => u (Finset.FromFin hk i)

variable {u : s → Ω → ℝ} {N : s}

lemma Submartingale.finOfFinset (hf : Submartingale u 𝓕 μ) :
    Submartingale (Process.finOfFinset hk u) (Filtration.finOfFinset hk 𝓕) μ :=
  ⟨ fun i => hf.stronglyAdapted (Finset.FromFin hk i),
    fun i j hij => by
      simp only [Process.finOfFinset, Filtration.finOfFinset]
      refine Submartingale.ae_le_condExp hf ?_
      exact (Finset.orderIso hk).strictMono.monotone hij,
    fun i => hf.integrable (Finset.FromFin hk i) ⟩

lemma Process.finOfFinset_eq (u : s → Ω → ℝ) (v : Fin k → Ω → ℝ)
    (hFinOfFinset : v = Process.finOfFinset hk u) :
    ∀ i, v (Finset.ToFin hk i) = u i := fun i => by
  rw [hFinOfFinset, Process.finOfFinset, (Finset.FromFin.ToFin_eq hk i)]

lemma Process.finOfFinset_eq' (u : Fin k → Ω → ℝ) (v : s → Ω → ℝ)
    (hFinOfFinset : u = Process.finOfFinset hk v) :
    ∀ i, v (Finset.FromFin hk i) = u i := fun i => by rw [hFinOfFinset, Process.finOfFinset]

variable [OrderBot ι] (hbot : ⊥ ∈ s) [NeZero k] -- to avoid issues with `Fin 0`

lemma Process.finOfFinset.upcrossingSequenceENat_le (u : Fin k → Ω → ℝ) (v : s → Ω → ℝ)
    (hFinOfFinset : u = Process.finOfFinset hk v) (N : Fin k) (a b : ℝ) (hab : a < b) :
    haveI : OrderBot s := Finset.orderBotOfBotMem hbot
    upcrossingSequenceENat a b u N ≤ upcrossingSequenceENat a b v (Finset.FromFin hk N) := by
  set f : Fin k → s := fun i => Finset.FromFin hk i
  have hsmon : StrictMonoOn f {i | i ≤ N} :=
    (Finset.orderIso hk).strictMono.strictMonoOn _
  have hv : ∀ i ≤ N, v (f i) = u i := fun i _ => Process.finOfFinset_eq' hk u v hFinOfFinset i
  intro ω
  convert upcrossingSequenceENat_mono_index_set f N hsmon u v hv a b ω hab using 1

lemma Process.finOfFinset.upcrossingSequenceENat_ge (u : s → Ω → ℝ) (v : Fin k → Ω → ℝ)
    (hFinOfFinset : v = Process.finOfFinset hk u) (N : s) (a b : ℝ) (hab : a < b) :
    haveI : OrderBot s := Finset.orderBotOfBotMem hbot
    upcrossingSequenceENat a b u N ≤ upcrossingSequenceENat a b v (Finset.ToFin hk N) := by
  set f : s → Fin k := fun i => Finset.ToFin hk i
  have hsmon : StrictMonoOn f {i | i ≤ N} :=
    (Finset.orderIso hk).symm.strictMono.strictMonoOn _
  have hv : ∀ i ≤ N, v (f i) = u i := fun i _ => Process.finOfFinset_eq hk u v hFinOfFinset i
  intro ω
  convert upcrossingSequenceENat_mono_index_set f N hsmon u v hv a b ω hab using 1

theorem Process.finOfFinset.upcrossingSequenceENat_eq (u : s → Ω → ℝ) (v : Fin k → Ω → ℝ)
    (hFinOfFinset : v = Process.finOfFinset hk u) (N : s) (a b : ℝ) (hab : a < b) :
    haveI : OrderBot s := Finset.orderBotOfBotMem hbot
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
theorem StronglyAdapted.measurable_upcrossingsBefore (hf : StronglyAdapted ℱ f) (hab : a < b) :
    Measurable (upcrossingsBefore a b f N)
-/

theorem StronglyAdapted.measurable_upcrossingSequenceENat_Nat {f : ℕ → Ω → ℝ} {N : ℕ} {a b : ℝ}
    {𝓕 : Filtration ℕ m0} (hf : StronglyAdapted 𝓕 f) (hab : a < b) :
    Measurable (fun ω => (upcrossingSequenceENat a b f N ω : ℝ≥0∞)) := by
  simp_rw [upcrossingSequenceENat_eq_upcrossingsBefore_Nat hab]
  exact measurable_from_top.comp (measurable_from_top.comp (hf.measurable_upcrossingsBefore hab))

variable {n : ℕ} [NeZero n] -- to avoid issues with `Fin 0`

theorem StronglyAdapted.measurable_upcrossingSequenceENat_Fin
    {u : (Fin n) → Ω → ℝ} {N : Fin n} {a b : ℝ}
    {𝓕 : Filtration (Fin n) m0} (hf : StronglyAdapted 𝓕 u) (hab : a < b) :
    Measurable (fun ω => (upcrossingSequenceENat a b u N ω : ℝ≥0∞)) := by
  set 𝓕' := Filtration.natOfFin 𝓕 with hFiltr
  set v := Process.natOfFin u with hv
  have hadapted' : StronglyAdapted 𝓕' v := fun i => by
    have hsm : StronglyMeasurable[𝓕 (Fin.clamp i n)] (u (Fin.clamp i n)) := hf (Fin.clamp i n)
    exact hsm
  have hNatOfFin : v = Process.natOfFin u := rfl
  have hmeas_nat : Measurable (fun ω => (upcrossingSequenceENat a b v N.val ω : ℝ≥0∞)) :=
    StronglyAdapted.measurable_upcrossingSequenceENat_Nat hadapted' hab
  have heq : upcrossingSequenceENat a b u N = upcrossingSequenceENat a b v N := by
    exact Process.natOfFin.upcrossingSequenceENat_eq u v hNatOfFin N a b hab
  simp_rw [heq]
  exact hmeas_nat

theorem StronglyAdapted.measurable_upcrossingSequenceENat_Finset [LinearOrder ι] [OrderBot ι]
    {s : Finset ι} {k : ℕ} (hk : #s = k) (hbot : ⊥ ∈ s) [NeZero k]
    {u : s → Ω → ℝ} {N : s} {a b : ℝ} {𝓕 : Filtration s m0}
    (hf : StronglyAdapted 𝓕 u) (hab : a < b) :
    haveI : OrderBot s := Finset.orderBotOfBotMem hbot
    Measurable (fun ω => (upcrossingSequenceENat a b u N ω : ℝ≥0∞)) := by
  set 𝓕' := Filtration.finOfFinset hk 𝓕 with hFiltr
  set v := Process.finOfFinset hk u with hv
  have hadapted' : StronglyAdapted 𝓕' v := fun i => by
    exact hf (Finset.FromFin hk i)
  have hFinOfFinset : v = Process.finOfFinset hk u := rfl
  simp_rw [Process.finOfFinset.upcrossingSequenceENat_eq hk hbot u v hFinOfFinset N a b hab]
  exact StronglyAdapted.measurable_upcrossingSequenceENat_Fin hadapted' hab

end Measurability

section DoobInequalityFin

variable {n : ℕ} [NeZero n] -- to avoid issues with `Fin 0`
  {u : (Fin n) → Ω → ℝ} {N : Fin n} {𝓕 : Filtration (Fin n) m0} {a b : ℝ}

theorem mul_lintegral_upcrossingSequenceENat_Fin_le_lintegral_pos_part [IsFiniteMeasure μ]
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
  have huNvN : v N = u N := Process.natOfFin_eq' u v hNatOfFin N
  rw [← huNvN]
  exact mul_lintegral_upcrossingSequenceENat_le_lintegral_pos_part N hvsub hab

end DoobInequalityFin

section DoobInequalityFinset

variable [LinearOrder ι] [OrderBot ι]
  {s : Finset ι} {k : ℕ} (hne : s.Nonempty) (hk : #s = k) (hbot : ⊥ ∈ s) [NeZero k]
  {𝓕 : Filtration s m0} {f : s → Ω → ℝ} {N : s} {a b : ℝ}

theorem mul_lintegral_upcrossingSequenceENat_Finset_le_lintegral_pos_part [IsFiniteMeasure μ]
    (hk : #s = k) (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    haveI : OrderBot s := Finset.orderBotOfBotMem hbot
    ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
  -- We reduce to the `Fin k`-indexed case
  set 𝓕' := Filtration.finOfFinset hk 𝓕
  set v := Process.finOfFinset hk f
  have hvsub : Submartingale v 𝓕' μ := Submartingale.finOfFinset hk hf
  have hFinOfFinset : v = Process.finOfFinset hk f := rfl
  have heq := Process.finOfFinset.upcrossingSequenceENat_eq hk hbot f v hFinOfFinset N a b hab
  rw [heq]
  have huNvN : v (Finset.ToFin hk N) = f N := Process.finOfFinset_eq hk f v hFinOfFinset N
  rw [← huNvN]
  exact mul_lintegral_upcrossingSequenceENat_Fin_le_lintegral_pos_part hvsub hab

theorem StronglyAdapted.measurable_upcrossingSequenceENat_Finset' (hk : #s = k)
    (hf : StronglyAdapted 𝓕 f) (hab : a < b) :
    haveI : OrderBot s := Finset.orderBotOfBotMem hbot
    Measurable (fun ω => (upcrossingSequenceENat a b f N ω : ℝ≥0∞)) := by
  letI : OrderBot s := Finset.orderBotOfBotMem hbot
  exact StronglyAdapted.measurable_upcrossingSequenceENat_Finset hk hbot hf hab

end DoobInequalityFinset

section Countable

variable [Countable ι] [LinearOrder ι] [OrderBot ι]

/-! Approximating `Set.Iic N` by finite sets that always contain `⊥` and `N`. -/

theorem Countable.increasing_family_saturates_Iic (N : ι) :
    ∃ s : ℕ → Set ι,
    Monotone s ∧
    (∀ n, Finite (s n)) ∧
    (∀ n, ⊥ ∈ s n) ∧
    (∀ n, N ∈ s n) ∧
    (∀ t : Set ι, Finite t → t ⊆ Set.Iic N → ∃ n, t ⊆ s n ∧ s n ⊆ Set.Iic N) := by
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat ι
  let s₀ : ℕ → Set ι := fun n => {i | f i < n}
  let s : ℕ → Set ι := fun n => (s₀ n ∩ Set.Iic N) ∪ {⊥, N}
  have hs_subset n : s n ⊆ Set.Iic N := fun x hx => by
    simp only [s, Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨-, h⟩ | rfl | rfl <;> simp_all
  refine ⟨s, fun m n hmn x hx => ?_, fun n => ?_, fun n => ?_, fun n => ?_, fun t ht htIic => ?_⟩
  · simp only [s, Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_setOf_eq, s₀] at hx ⊢
    rcases hx with ⟨h1, h2⟩ | h
    · left; exact ⟨h1.trans_le hmn, h2⟩
    · right; exact h
  · exact (Set.Finite.inter_of_left (Finite.of_injective (fun ⟨i, hi⟩ => (⟨f i, hi⟩ : Fin n))
      (fun ⟨_, _⟩ ⟨_, _⟩ h => Subtype.ext (hf (Fin.ext_iff.mp h)))) _).union (Set.toFinite _)
  · simp only [s, Set.mem_union, Set.mem_insert_iff]; right; left; trivial
  · simp only [s, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]; right; right; trivial
  · haveI : Fintype t := Set.Finite.fintype ht
    use (Finset.univ.image (fun i : t => f i)).sup id + 1
    refine ⟨fun x hx => ?_, hs_subset _⟩
    simp only [s, Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_setOf_eq, s₀]
    exact .inl ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id)
      (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩)), htIic hx⟩

theorem Countable.increasing_finset_family_saturates_Iic (N : ι) :
    ∃ s : ℕ → Finset ι,
    Monotone s ∧
    (∀ n, ⊥ ∈ s n) ∧
    (∀ n, N ∈ s n) ∧
    (∀ t : Set ι, Finite t → t ⊆ Set.Iic N → ∃ n, t ⊆ s n ∧ ↑(s n) ⊆ Set.Iic N) := by
  obtain ⟨s, hsmon, hsfin, hsbot, hsN, hsaturate⟩ :=
    Countable.increasing_family_saturates_Iic (ι := ι) N
  have fintype_s n : Fintype (s n) := Fintype.ofFinite (s n)
  refine ⟨fun n => (s n).toFinset,
    fun m n hmn => ?_, fun n => ?_, fun n => ?_, fun t ht htIic => ?_⟩
  · simp only [Finset.le_iff_subset]
    exact fun x hx => Set.mem_toFinset.mpr (hsmon hmn (Set.mem_toFinset.mp hx))
  · simp only [Set.mem_toFinset]; exact hsbot n
  · simp only [Set.mem_toFinset]; exact hsN n
  · obtain ⟨n, hn, hnIic⟩ := hsaturate t ht htIic
    exact ⟨n, fun x hx => Set.mem_toFinset.mpr (hn hx), fun x hx => hnIic (Set.mem_toFinset.mp hx)⟩

end Countable

/-- Helper definition for `upcrossingSequenceENat` on a finset, bundling the `OrderBot` instance.
    This avoids repeating `letI : OrderBot (s n) := { bot := ⟨⊥, hbot n⟩, ... }` in theorem
    statements and proofs. -/
noncomputable def upcrossingSequenceENat_finset [LinearOrder ι] [OrderBot ι] {N : ι}
    {s : ℕ → Finset ι} (hbot : ∀ n, ⊥ ∈ s n) (hN : ∀ n, N ∈ s n)
    (a b : ℝ) (f : ι → Ω → ℝ) (n : ℕ) (ω : Ω) : ℕ∞ :=
  letI : OrderBot (s n) := Finset.orderBotOfBotMem (hbot n)
  upcrossingSequenceENat a b (fun i : s n => f i) ⟨N, hN n⟩ ω

section Approximation

variable [LinearOrder ι] [OrderBot ι]
  {a b : ℝ} {f : ι → Ω → ℝ} {N : ι} {ω : Ω}

/-- An `ι`-valued `UpcrossingData` of length `K`, contained in `s : Finset ι`,
    yields `s`-indexed `upcrossingSequenceENat ≥ K`. -/
lemma upcrossingSequenceENat_finset_ge_of_witness
    {s : Finset ι} (hbot : ⊥ ∈ s) (hN : N ∈ s)
    {K : ℕ} (hKpos : K ≥ 1)
    (hseq : UpcrossingData a b f K ω)
    (ht_lt_N : hseq.t (2 * K - 1) < N)
    (ht_in_s : ∀ i < 2 * K, hseq.t i ∈ s) :
    letI : OrderBot s := Finset.orderBotOfBotMem hbot
    K ≤ upcrossingSequenceENat a b (fun i : s => f i) ⟨N, hN⟩ ω := by
  letI : OrderBot s := Finset.orderBotOfBotMem hbot
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

/-- The upcrossings count on the full countable index set equals the supremum of upcrossings
    counts on the approximating finsets. This holds unconditionally—both when the supremum
    is finite and when it is infinite. This is the main approximation theorem for upcrossings
    on countable index sets. -/
theorem upcrossingSequenceENat_eq_iSup_finset
    {s : ℕ → Finset ι}
    (hbot : ∀ n, ⊥ ∈ s n)
    (hN : ∀ n, N ∈ s n)
    (hsaturate : ∀ t : Set ι, Finite t → t ⊆ Set.Iic N →
      ∃ n, t ⊆ s n ∧ ↑(s n) ⊆ Set.Iic N)
    (hab : a < b) :
    upcrossingSequenceENat a b f N ω = ⨆ n, upcrossingSequenceENat_finset hbot hN a b f n ω := by
  apply le_antisymm
  · by_cases hNbot : N ≤ ⊥
    · simp only [upcrossingSequenceENat_zero_of_N_bot a b f N ω hNbot]; exact zero_le _
    · simp only [upcrossingSequenceENat]; apply iSup₂_le; intro K hK
      simp only [ltUpcrossingData, hNbot, ↓reduceIte] at hK
      by_cases hKzero : K = 0
      · simp only [hKzero, Nat.cast_zero]; exact zero_le _
      · simp only [hKzero, ↓reduceIte] at hK; obtain ⟨hseq, ht_lt_N⟩ := hK
        set witness : Set ι := Set.range (fun i : Fin (2 * K) => hseq.t i)
        have hwit_Iic : witness ⊆ Set.Iic N := fun x ⟨i, hi⟩ =>
          le_of_lt (hi ▸ (hseq.mono (by omega : i ≤ 2 * K - 1)).trans_lt ht_lt_N)
        obtain ⟨n₀, hn₀_wit, _⟩ := hsaturate witness (Set.finite_range _) hwit_Iic
        calc (K : ℕ∞) ≤ upcrossingSequenceENat_finset hbot hN a b f n₀ ω :=
              upcrossingSequenceENat_finset_ge_of_witness (hbot n₀) (hN n₀)
                (Nat.one_le_iff_ne_zero.mpr hKzero) hseq ht_lt_N
                (fun i hi => hn₀_wit ⟨⟨i, hi⟩, rfl⟩)
          _ ≤ ⨆ n, upcrossingSequenceENat_finset hbot hN a b f n ω :=
              le_iSup (fun n => upcrossingSequenceENat_finset hbot hN a b f n ω) n₀
  · exact iSup_le fun n => upcrossingSequenceENat_ge_finset_of_subset (hbot n) ⟨N, hN n⟩
      (fun i : s n => f i) f (fun _ => rfl) a b ω hab

end Approximation

section DoobInequalityCountable

variable [LinearOrder ι] {f : ι → Ω → ℝ} {𝓕 : Filtration ι m0}

/-- Restrict a filtration on ι to a finset s. -/
def Filtration.restrictFinset (𝓕 : Filtration ι m0) (s : Finset ι) :
    Filtration s m0 := ⟨fun i => 𝓕 i.val, fun _ _ hij => 𝓕.mono hij, fun i => 𝓕.le i.val⟩

/-- Restrict a submartingale on ι to a finset s. -/
lemma Submartingale.restrictFinset (𝓕 : Filtration ι m0) (s : Finset ι)
    (hf : Submartingale f 𝓕 μ) :
    Submartingale (fun i : s => f i) (Filtration.restrictFinset 𝓕 s) μ :=
  ⟨fun i => hf.stronglyAdapted i.val,
    fun i j hij => hf.2.1 i.val j.val hij,
    fun i => hf.integrable i.val⟩

variable [OrderBot ι] {N : ι} {a b : ℝ}

/-- Measurability of `upcrossingSequenceENat_finset` as `ℝ≥0∞`. -/
theorem StronglyAdapted.measurable_upcrossingSequenceENat_finset
    {s : ℕ → Finset ι} (hbot : ∀ n, ⊥ ∈ s n) (hN : ∀ n, N ∈ s n)
    (hf : StronglyAdapted 𝓕 f) (hab : a < b) (n : ℕ) :
    Measurable (fun ω => (upcrossingSequenceENat_finset hbot hN a b f n ω : ℝ≥0∞)) := by
  simp only [upcrossingSequenceENat_finset]
  have hne : (s n).Nonempty := ⟨⊥, hbot n⟩
  have hnz : #(s n) ≠ 0 := Finset.card_ne_zero.mpr hne
  haveI : NeZero #(s n) := ⟨hnz⟩
  letI : OrderBot (s n) := Finset.orderBotOfBotMem (hbot n)
  let 𝓕' := Filtration.restrictFinset 𝓕 (s n)
  have hadapted : StronglyAdapted 𝓕' (fun i : s n => f i) := fun i => hf i.val
  exact StronglyAdapted.measurable_upcrossingSequenceENat_Finset' (hbot := hbot n) rfl hadapted hab

variable [Countable ι]

theorem mul_lintegral_upcrossingSequenceENat_Countable_le_lintegral_pos_part [IsFiniteMeasure μ]
    (hf : Submartingale f 𝓕 μ) (hab : a < b) :
    ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
  obtain ⟨s, hsmon, hsbot, hsN, hsaturate⟩ := Countable.increasing_finset_family_saturates_Iic N
  let g : ℕ → Ω → ℝ≥0∞ := fun n ω => (upcrossingSequenceENat_finset hsbot hsN a b f n ω : ℝ≥0∞)
  set c := ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ
  have hNZ n : NeZero #(s n) := ⟨Finset.card_ne_zero.mpr ⟨⊥, hsbot n⟩⟩
  have hsub n : Submartingale (fun i : s n => f i) (Filtration.restrictFinset 𝓕 (s n)) μ :=
    Submartingale.restrictFinset 𝓕 (s n) hf
  have hg_meas n : Measurable (g n) :=
    StronglyAdapted.measurable_upcrossingSequenceENat_finset hsbot hsN hf.stronglyAdapted hab n
  have hg_mono n : ∀ᵐ ω ∂μ, g n ω ≤ g n.succ ω := by
    filter_upwards with ω; simp only [g, ENat.toENNReal_le]
    exact upcrossingSequenceENat_ge_finset (hsbot n) (hsbot n.succ) (hsmon (Nat.le_succ n))
      ⟨N, hsN n⟩ (fun i : s n => f i) (fun i : s n.succ => f i) (fun _ => rfl) a b ω hab
  have hg_bound n : ENNReal.ofReal (b - a) * ∫⁻ ω, g n ω ∂μ ≤ c := by
    simp only [g, upcrossingSequenceENat_finset]; haveI := hNZ n
    exact mul_lintegral_upcrossingSequenceENat_Finset_le_lintegral_pos_part
      (hbot := hsbot n) (hk := rfl) (hf := hsub n) (N := ⟨N, hsN n⟩) hab
  have hiSup_eq ω : (upcrossingSequenceENat a b f N ω : ℝ≥0∞) = ⨆ n, g n ω := by
    simp only [g, upcrossingSequenceENat_eq_iSup_finset hsbot hsN hsaturate hab,
      ENat.toENNReal_iSup]
  have hba_pos : ENNReal.ofReal (b - a) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos]; exact hab
  have hg_int_bound : ∫⁻ ω, ⨆ n, g n ω ∂μ ≤ c / ENNReal.ofReal (b - a) :=
    calc ∫⁻ ω, ⨆ n, g n ω ∂μ = ⨆ n, ∫⁻ ω, g n ω ∂μ := lintegral_iSup_ae hg_meas hg_mono
      _ ≤ c / ENNReal.ofReal (b - a) := iSup_le fun n => by
          rw [ENNReal.le_div_iff_mul_le (.inl hba_pos) (.inl (by simp)), mul_comm]
          exact hg_bound n
  calc ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ
      = ENNReal.ofReal (b - a) * ∫⁻ ω, ⨆ n, g n ω ∂μ := by simp only [hiSup_eq]
    _ ≤ ENNReal.ofReal (b - a) * (c / ENNReal.ofReal (b - a)) := mul_le_mul_right hg_int_bound _
    _ = c := ENNReal.mul_div_cancel hba_pos (by simp)

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
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp (hRC ω s) ε hεpos
  have hts_pos : (0 : ℝ) < t - s := sub_pos.mpr hst
  set δ' : ℝ≥0 := ⟨min (δ / 2) ((t - s) / 2), by positivity⟩
  have hδ'pos : (0 : ℝ≥0) < δ' := (lt_min (by linarith) (by linarith) : (0 : ℝ) < _)
  obtain ⟨q, hqs, hqδ⟩ := exists_rat_btwn
    (show (s : ℝ) < s + δ' by exact_mod_cast lt_add_of_pos_right s hδ'pos)
  have hq_pos : 0 ≤ q := Rat.cast_nonneg.mp ((NNReal.coe_nonneg s).trans (le_of_lt hqs))
  set s' : ℚ≥0 := ⟨q, hq_pos⟩
  refine ⟨s', ?_, hqs, ?_⟩
  · have : (δ' : ℝ) < t - s := (min_le_right _ _).trans_lt (by linarith)
    calc (s' : ℝ) < s + δ' := hqδ
      _ < s + (t - s) := by linarith
      _ = t := by ring
  · have hs'_lt_δ : dist (s' : ℝ≥0) s < δ := by
      have hsq : ((s' : ℝ≥0) : ℝ) = (q : ℝ) := rfl
      simp only [NNReal.dist_eq, hsq, abs_of_nonneg (sub_nonneg.mpr (le_of_lt hqs))]
      calc (q : ℝ) - s < δ' := by linarith
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    linarith [abs_sub_lt_iff.mp (Real.dist_eq _ _ ▸ hδ hqs hs'_lt_δ)]

lemma disturbed_crossing_ge_close_of_crossing (hRC : ∀ ω, RightContinuous (f · ω)) {ε : ℝ}
    (hεpos : 0 < ε) {s t : ℝ≥0} (hst : s < t) {ω : Ω} (hb : f s ω ≥ b) :
    ∃ s' : ℚ≥0, (s' : ℝ≥0) < t ∧ (s' : ℝ≥0) > s ∧ f s' ω ≥ b - ε := by
  obtain ⟨s', h1, h2, h3⟩ := disturbed_crossing_le_close_of_crossing (f := -f) (a := -b)
    (fun ω x => (hRC ω x).neg) hεpos hst (neg_le_neg hb)
  exact ⟨s', h1, h2, by linarith [show -f s' ω ≤ -b + ε from h3]⟩

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
    (ω : Ω) :
    upcrossingSequenceENat a b f N ω ≤
      upcrossingSequenceENat (a + ε) (b - ε) (fun d : DSet N => f d) ⟨N, N_mem_DSet N⟩ ω := by
  set DN := DSet N; set Nelem : DN := ⟨N, N_mem_DSet N⟩
  simp only [upcrossingSequenceENat]; apply biSup_mono; intro K hK
  simp only [ltUpcrossingData] at hK ⊢
  by_cases hNbot : N ≤ ⊥
  · simp only [hNbot, ↓reduceIte] at hK
  · have hNelem_bot : Nelem ≤ ⊥ ↔ N ≤ ⊥ := by simp only [le_bot_iff, Nelem, Subtype.ext_iff]; rfl
    simp only [hNbot, hNelem_bot, ↓reduceIte] at hK ⊢
    rcases K with _ | K; · trivial
    obtain ⟨hseq, ht_lt_N⟩ := hK
    obtain ⟨t', hseq', ht'_eq, ht'_lt_N⟩ := hseq.disturb hRC (by omega : K + 1 ≥ 1)
      ht_lt_N hεpos hε_small
    let t'' : ℕ → DN := fun i => ⟨t' i, mem_DSet_of_NNRat (t' i)⟩
    have ht'_eq' i : hseq'.t i = t' i := congrFun ht'_eq i
    refine ⟨⟨hseq'.hab, t'', fun i j hij => ?_, fun i hi he => ?_, fun i hi ho => ?_⟩, ht'_lt_N⟩
    · simp only [t'', Subtype.mk_le_mk, ← ht'_eq' i, ← ht'_eq' j]; exact hseq'.mono hij
    · simp only [t'']; rw [← ht'_eq' i]; exact hseq'.ft_le_a i hi he
    · simp only [t'']; rw [← ht'_eq' i]; exact hseq'.ft_ge_b i hi ho

/-- Restrict a filtration on ℝ≥0 to DSet N. -/
def Filtration.restrictDSet (𝓕 : Filtration ℝ≥0 m0) (N : ℝ≥0) :
    Filtration (DSet N) m0 :=
  ⟨fun i => 𝓕 i.val, fun _ _ hij => 𝓕.mono hij, fun i => 𝓕.le i.val⟩

omit [IsFiniteMeasure μ] in
/-- Restrict a submartingale on ℝ≥0 to DSet N. -/
lemma submartingale_restrictDSet (hf : Submartingale f 𝓕 μ) (N : ℝ≥0) :
    Submartingale (fun d : DSet N => f d) (Filtration.restrictDSet 𝓕 N) μ :=
  ⟨fun i => hf.stronglyAdapted i.val,
    fun i j hij => hf.2.1 i.val j.val hij,
    fun i => hf.integrable i.val⟩

omit [IsFiniteMeasure μ] in
/-- For $0<ε<(b-a)/2$, $E[U_a^b(f,N)] \le E[U_{a+ε}^{b-ε}(f|_D,N)]$.
    Uses `upcrossingSequenceENat_le_upcrossingSequenceENat_restrict_DSet`. -/
lemma lintegral_upcrossingSequenceENat_le_of_restrict_DSet
    (hRC : ∀ ω, RightContinuous (f · ω)) {ε : ℝ} (hεpos : 0 < ε)
    (hε_small : 2 * ε < b - a) :
    ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, (upcrossingSequenceENat (a + ε) (b - ε)
        (fun d : DSet N => f d) ⟨N, N_mem_DSet N⟩ ω : ℝ≥0∞) ∂μ := by
  apply lintegral_mono
  intro ω
  exact ENat.toENNReal_le.mpr
    (upcrossingSequenceENat_le_upcrossingSequenceENat_restrict_DSet hRC hεpos hε_small ω)

/-- For $0<ε<(b-a)/2$, $(b-a-2ε) E[U_{a+ε}^{b-ε}(f|_D,N)] \le E[(f_N-a-ε)^+]$ in lintegral form.
    This follows from the discrete Doob inequality applied to the restriction of f to D. -/
lemma mul_lintegral_upcrossingSequenceENat_restrict_DSet_le (hf : Submartingale f 𝓕 μ)
    {ε : ℝ} (hε_small : 2 * ε < b - a) :
    ENNReal.ofReal (b - a - 2 * ε) * ∫⁻ ω, (upcrossingSequenceENat (a + ε) (b - ε)
        (fun d : DSet N => f d) ⟨N, N_mem_DSet N⟩ ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - (a + ε))⁺) ∂μ := by
  have hab' : a + ε < b - ε := by linarith
  have hba : b - ε - (a + ε) = b - a - 2 * ε := by ring
  rw [← hba]
  exact mul_lintegral_upcrossingSequenceENat_Countable_le_lintegral_pos_part
    (submartingale_restrictDSet hf N) hab'

/-- For all ε with 2ε < b - a, we have (b-a-2ε) * E[U_a^b(f,N)] ≤ E[(f_N - a)^+]. -/
lemma mul_lintegral_upcrossingSequenceENat_NNReal_eps (hf : Submartingale f 𝓕 μ)
    (hRC : ∀ ω, RightContinuous (f · ω)) {ε : ℝ} (hεpos : 0 < ε)
    (hε_small : 2 * ε < b - a) :
    ENNReal.ofReal (b - a - 2 * ε) * ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
  -- Step 1: LHS_integral ≤ DSet_integral
  have h1 : ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, (upcrossingSequenceENat (a + ε) (b - ε)
        (fun d : DSet N => f d) ⟨N, N_mem_DSet N⟩ ω : ℝ≥0∞) ∂μ :=
    lintegral_upcrossingSequenceENat_le_of_restrict_DSet hRC hεpos hε_small
  -- Step 2: Doob on DSet
  have h2 : ENNReal.ofReal (b - a - 2 * ε) *
      ∫⁻ ω, (upcrossingSequenceENat (a + ε) (b - ε)
        (fun d : DSet N => f d) ⟨N, N_mem_DSet N⟩ ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - (a + ε))⁺) ∂μ :=
    mul_lintegral_upcrossingSequenceENat_restrict_DSet_le hf hε_small
  -- Step 3: (f_N - a - ε)^+ ≤ (f_N - a)^+
  have h3 : ∫⁻ ω, ENNReal.ofReal ((f N ω - (a + ε))⁺) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
    apply lintegral_mono
    intro ω
    apply ENNReal.ofReal_le_ofReal
    apply posPart_mono
    linarith
  calc ENNReal.ofReal (b - a - 2 * ε) * ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ
      ≤ ENNReal.ofReal (b - a - 2 * ε) *
        ∫⁻ ω, (upcrossingSequenceENat (a + ε) (b - ε)
          (fun d : DSet N => f d) ⟨N, N_mem_DSet N⟩ ω : ℝ≥0∞) ∂μ :=
        mul_le_mul_right h1 _
      _ ≤ ∫⁻ ω, ENNReal.ofReal ((f N ω - (a + ε))⁺) ∂μ := h2
      _ ≤ ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := h3

/-- Doob's upcrossing inequality for right-continuous submartingales indexed by ℝ≥0:
    $(b-a) \cdot E[U_a^b(f,N)] \le E[(f_N - a)^+]$ -/
theorem mul_lintegral_upcrossingSequenceENat_NNReal_le_lintegral_pos_part (hf : Submartingale f 𝓕 μ)
    (hRC : ∀ ω, RightContinuous (f · ω)) (hab : a < b) :
    ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
  set L := ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ
  set R := ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ
  have hba_pos : 0 < b - a := sub_pos.mpr hab
  -- For each n, ε_n = (b-a)/(2*(n+2)) yields (b-a-2ε_n) = (b-a)*(n+1)/(n+2)
  have h_coeff (n : ℕ) : b - a - 2 * ((b - a) / (2 * ((n : ℝ) + 2))) =
      (b - a) * (((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
    have hn2_ne : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp; ring
  have h_eps_n' (n : ℕ) : ENNReal.ofReal ((b - a) * (((n : ℝ) + 1) / ((n : ℝ) + 2))) * L ≤ R := by
    rw [← h_coeff n]
    have hn2_pos : 0 < (n : ℝ) + 2 := by positivity
    have hε_small : 2 * ((b - a) / (2 * ((n : ℝ) + 2))) < b - a := by
      rw [show 2 * ((b - a) / (2 * ((n : ℝ) + 2))) = (b - a) / ((n : ℝ) + 2) by field_simp,
        div_lt_iff₀ hn2_pos]; nlinarith
    exact mul_lintegral_upcrossingSequenceENat_NNReal_eps hf hRC (by positivity) hε_small
  -- sup_n (b-a)*(n+1)/(n+2) = (b-a) by monotone limit
  have h_mono (n m : ℕ) (hnm : n ≤ m) : (b - a) * (((n : ℝ) + 1) / ((n : ℝ) + 2)) ≤
      (b - a) * (((m : ℝ) + 1) / ((m : ℝ) + 2)) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hba_pos)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h_cast : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
    nlinarith
  have h_tendsto_frac : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) atTop (nhds 1) := by
    have h (n : ℕ) : ((n : ℝ) + 1) / ((n : ℝ) + 2) = 1 - 1 / ((n : ℝ) + 2) := by field_simp; ring
    simp_rw [h]
    have htend : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (nhds 0) := by
      have : (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) = (fun n : ℕ => 1 / ((n + 1 : ℕ) + 1 : ℝ)) := by
        ext n; simp only [Nat.cast_add, Nat.cast_one]; ring
      rw [this]; exact (tendsto_add_atTop_iff_nat 1).mpr tendsto_one_div_add_atTop_nhds_zero_nat
    convert Tendsto.sub tendsto_const_nhds htend using 1; ring_nf
  have h_sup : ⨆ n : ℕ, ENNReal.ofReal ((b - a) * (((n : ℝ) + 1) / ((n : ℝ) + 2))) =
      ENNReal.ofReal (b - a) := by
    apply le_antisymm
    · exact iSup_le fun n => ENNReal.ofReal_le_ofReal <|
        mul_le_of_le_one_right (le_of_lt hba_pos) (div_le_one_of_le₀ (by linarith) (by positivity))
    · have h_tendsto := ENNReal.tendsto_ofReal (h_tendsto_frac.const_mul (b - a))
      simp only [mul_one] at h_tendsto
      rw [h_tendsto.limUnder_eq.symm.trans (tendsto_atTop_iSup fun n m hnm =>
        ENNReal.ofReal_le_ofReal (h_mono n m hnm)).limUnder_eq]
  rw [← h_sup, ENNReal.iSup_mul]
  exact iSup_le h_eps_n'

/-- A right-continuous process hits the closed set at the corresponding hitting time. -/
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

/-- For right-continuous processes, `upcrossingsBeforeENat` agrees with `upcrossingSequenceENat`.
    This is important for measurability of the latter. -/
theorem upcrossingsBeforeENat_eq_upcrossingSequenceENat_NNReal (hRC : ∀ ω, RightContinuous (f · ω))
    (hab : a < b) :
    upcrossingsBeforeENat a b f N = upcrossingSequenceENat a b f N :=
  upcrossingsBeforeENat_eq_upcrossingSequenceENat a b f N hab
    (fun n ω => hittingBtwnSpec_of_right_continuous (Set.Ici b) n N ω isClosed_Ici (hRC ω))
    (fun n ω => hittingBtwnSpec_of_right_continuous (Set.Iic a) n N ω isClosed_Iic (hRC ω))

/-- Integrability of a submartingale yields a finite RHS in Doob's upcrossing inequality. -/
lemma pos_sub_integrable_of_submartingale (hf : Submartingale f 𝓕 μ) :
    ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ < ⊤ := by
  rw [← hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ => posPart_nonneg _))]
  -- Show that (f N - a)⁺ is integrable
  have hInt_sub : Integrable (fun ω => f N ω - a) μ := (hf.integrable N).sub (integrable_const a)
  have h_bound : ∀ x, ‖(f N x - a)⁺‖ ≤ ‖f N x - a‖ := fun x => by
    simp only [Real.norm_eq_abs, abs_of_nonneg (posPart_nonneg _)]
    rw [posPart_def]
    exact sup_le (le_abs_self _) (abs_nonneg _)
  have h_meas : AEStronglyMeasurable (fun ω => (f N ω - a)⁺) μ := by
    have h1 : (fun ω => (f N ω - a)⁺) = (fun ω => (f N ω - a) ⊔ 0) := by ext; rfl
    rw [h1]
    exact hInt_sub.aestronglyMeasurable.sup aestronglyMeasurable_const
  exact (hInt_sub.mono h_meas (Filter.Eventually.of_forall h_bound)).hasFiniteIntegral

/-- The `upcrossingSequenceENat` is a.s. finite, assuming it is `AEMeasurable`
    (which follows from the début theorem). -/
theorem upcrossingSequenceENat_ae_lt_top (hf : Submartingale f 𝓕 μ)
    (hRC : ∀ ω, RightContinuous (f · ω)) (hab : a < b)
    (hmeas : AEMeasurable (fun ω => (upcrossingSequenceENat a b f N ω : ℝ≥0∞)) μ) :
    ∀ᵐ ω ∂μ, upcrossingSequenceENat a b f N ω < ⊤ := by
  -- The RHS of Doob inequality is finite
  have hRHS : ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ < ⊤ := pos_sub_integrable_of_submartingale hf
  -- The LHS of Doob inequality is ≤ RHS
  have hDoob : ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ :=
    mul_lintegral_upcrossingSequenceENat_NNReal_le_lintegral_pos_part hf hRC hab
  -- So LHS < ⊤
  have hba_ne_zero : ENNReal.ofReal (b - a) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hLHS_lt : ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ < ⊤ :=
    lt_of_le_of_lt hDoob hRHS
  have hlint_ne_top : ∫⁻ ω, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) ∂μ ≠ ⊤ := by
    intro hcontra
    rw [hcontra, ENNReal.mul_top hba_ne_zero] at hLHS_lt
    exact absurd hLHS_lt (not_lt.mpr le_top)
  -- ae_lt_top' gives us (↑(upcrossingSequenceENat ...) : ℝ≥0∞) < ⊤ a.e.
  -- We need to convert to ℕ∞ < ⊤
  have h_ae_ennreal : ∀ᵐ ω ∂μ, (upcrossingSequenceENat a b f N ω : ℝ≥0∞) < ⊤ :=
    ae_lt_top' hmeas hlint_ne_top
  filter_upwards [h_ae_ennreal] with ω hω
  exact ENat.toENNReal_lt_top.mp hω

end DoobInequalityNNReal

end MeasureTheory
