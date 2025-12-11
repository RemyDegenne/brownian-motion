/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Wojciech Czernous
-/
import BrownianMotion.Auxiliary.Martingale
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Data.Finset.Sort

/-! # Doob's upcrossing inequality

-/

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

#check Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part

variable {ι Ω E : Type*} [ConditionallyCompleteLinearOrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
  {Y : ι → Ω → ℝ}

/-- **Doob's upcrossing estimate**: given a real-valued discrete submartingale `f` and real
values `a` and `b`, we have `(b - a) * 𝔼[upcrossingsBefore a b f N] ≤ 𝔼[(f N - a)⁺]` where
`upcrossingsBefore a b f N` is the number of times the process `f` crossed from below `a` to above
`b` before the time `N`. -/
-- This is the version for countable time index. The original version for natural time index is in
--  .lake/packages/mathlib/Mathlib/Probability/Martingale/Upcrossing.lean
-- We shall extend the result "mul_integral_upcrossingsBefore_le_integral_pos_part",
-- which works for `ℕ` as time index, i.e., finite time index - as it is up to the time `N`.
-- By repeating the claim on a finite time index,
-- for denser and denser finite subsets of `Iic N`, we get the result for countable time index.
-- The result then follows thanks to monotone convergence theorem.
-- The point is to show that the number of upcrossings is:
-- - growing when we add more time points,
-- - converging to the number of upcrossings on the whole countable index set.
-- By inductively densening the time index, we mean adding one time point at a time.

def restriction_to_Fin (n k : ℕ) (hn : n ≠ 0) : Fin n := ⟨min k (n-1), by grind⟩

lemma restriction_to_Fin.mono (n k1 k2 : ℕ) (hn : n ≠ 0) (h : k1 ≤ k2) :
  restriction_to_Fin n k1 hn ≤ restriction_to_Fin n k2 hn := by
  simp only [restriction_to_Fin]
  refine Fin.mk_le_mk.mpr ?_
  exact inf_le_inf_right (n-1) h

lemma restriction_to_Fin.eq_of_lt (n k : ℕ) (hn : n ≠ 0) (hk : k < n) :
  restriction_to_Fin n k hn = k := by
  simp only [restriction_to_Fin]
  grind

lemma restriction_to_Fin.strict_of_lt (n k1 k2 : ℕ) (hn : n ≠ 0)
    (h : k1 < k2) (h2 : k2 < n) :
  restriction_to_Fin n k1 hn < restriction_to_Fin n k2 hn := by
  have h1 : k1 < n := lt_of_lt_of_le h (le_of_lt h2)
  simp only [restriction_to_Fin, Fin.lt_iff_val_lt_val]
  grind

lemma restriction_to_Fin.map_le_map_iff (n i j : ℕ) (hn : n ≠ 0)
  (hi : i < n) (hj : j < n) :
    restriction_to_Fin n i hn ≤ restriction_to_Fin n j hn ↔ i ≤ j := by
  have h1 : restriction_to_Fin n i hn = i := restriction_to_Fin.eq_of_lt n i hn hi
  have h2 : restriction_to_Fin n j hn = j := restriction_to_Fin.eq_of_lt n j hn hj
  grind

lemma restriction_to_Fin.map_lt_map_iff (n i j : ℕ) (hn : n ≠ 0)
  (hi : i < n) (hj : j < n) :
    restriction_to_Fin n i hn < restriction_to_Fin n j hn ↔ i < j := by
  have h1 : restriction_to_Fin n i hn = i := restriction_to_Fin.eq_of_lt n i hn hi
  have h2 : restriction_to_Fin n j hn = j := restriction_to_Fin.eq_of_lt n j hn hj
  grind

theorem Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part_finite
    [Finite ι] [Nonempty ι] [IsFiniteMeasure P]
    (a b : ℝ) (hf : Submartingale X 𝓕 P) (N : ι) :
    (b - a) * P[upcrossingsBefore a b X N] ≤ P[fun ω => (X N ω - a)⁺] := by
  -- We reduce to the case where `ι = Fin n` for some `n : ℕ`.
  -- get an order isomorphism
  have hfin := Fintype.ofFinite ι
  let n := Fintype.card ι
  have hn : n ≠ 0 := Fintype.card_ne_zero
  let i2N : ι ≃o Fin n := (Fintype.orderIsoFinOfCardEq ι (rfl)).symm

  -- define a monotone map from `ℕ` to `ι` covering all
  let N2i : ℕ → ι := fun k => i2N.symm (restriction_to_Fin n k hn)
  have hN2imono : Monotone N2i := by
    intro i j hij
    refine i2N.symm.monotone ?_
    exact restriction_to_Fin.mono n i j hn hij
  -- define a filtration and a submartingale on `Fin n`
  let 𝓕' : Filtration ℕ mΩ :=
    { seq := fun i => 𝓕 (N2i i)
      mono' := by
        intro i j hij
        refine 𝓕.mono ?_
        exact hN2imono hij
      le' := by
        exact fun i ↦ Filtration.le 𝓕 (N2i i)
    }
  let X' : ℕ → Ω → ℝ := fun i ω => X (N2i i) ω
  have hf' : Submartingale X' 𝓕' P := by
    have hadapted' : Adapted 𝓕' X' := by
      intro i
      have hsm : StronglyMeasurable[𝓕 (N2i i)] (X (N2i i)) := by
        exact Submartingale.stronglyMeasurable hf (N2i i)
      have hsm' : StronglyMeasurable[𝓕' i] (X' i) := by
        simp only [X', 𝓕']
        exact hsm
      exact hsm'
    have hsub' : (∀ i j, i ≤ j → X' i ≤ᵐ[P] P[X' j|𝓕' i]) := by
      intros i j hij
      simp only [X', 𝓕']
      refine Submartingale.ae_le_condExp hf ?_
      exact hN2imono hij
    have hint' : ∀ i, Integrable (X' i) P := by
      intro i
      simp only [X']
      exact Submartingale.integrable hf (N2i i)
    exact ⟨ hadapted', hsub', hint' ⟩

  -- now apply the known result on `Fin n`

  let N' : ℕ := i2N N


  have hnn : N = N2i (i2N N) := by
    refine (OrderIso.apply_eq_iff_eq_symm_apply i2N N (restriction_to_Fin n (↑(i2N N)) hn)).mp ?_
    simp only [restriction_to_Fin]
    ext
    simp
    grind

  have hXN : X N = X' N' := by
    ext ω
    simp only [N', X']
    rw[← hnn]

  have hN2iltiff2 : ∀ i j : ℕ, i < n → j < n → (i < j ↔ N2i i < N2i j) := by
    intro i j hi hj
    simp only [N2i]
    have h1 : i < j ↔ restriction_to_Fin n i hn < restriction_to_Fin n j hn := by
      exact Iff.symm (restriction_to_Fin.map_lt_map_iff n i j hn hi hj)
    have h2 : restriction_to_Fin n i hn < restriction_to_Fin n j hn ↔
        i2N.symm (restriction_to_Fin n i hn) < i2N.symm (restriction_to_Fin n j hn) := by
      exact Iff.symm (i2N.symm.lt_iff_lt)
    grind

  have hN2iltiff1 : ∀ i j : ℕ, j < n → (i < j ↔ N2i i < N2i j) := by
    intro i j hj
    constructor
    · intro hij
      grind
    · contrapose!
      exact fun a ↦ hN2imono a

  have hNlt : i2N N < n := by grind

  have hupton : ∀ i : ι, ∀ k : ℕ, i = N2i k → (i < N ↔ k < N') := by
    intro i k hik
    rw[hnn, hik]
    simp only [N']
    exact iff_comm.mp (hN2iltiff1 k (↑(i2N N)) hNlt)

  have hN2ii2Nid {t : ι} : N2i (i2N t) = t := by
    have ht : (i2N t) < n := by grind
    refine (OrderIso.symm_apply_eq i2N).mpr ?_
    have := restriction_to_Fin.eq_of_lt n (i2N t) hn ht
    grind

  have hi2NN2iid {k : ℕ} (hk : k < n) : i2N (N2i k) = k := by
    grind

  have hi2Neqbot : i2N ⊥ = 0 := by
    apply le_antisymm
    · -- i2N ⊥ ≤ 0 because ⊥ ≤ i2N.symm 0
      have h : (⊥ : ι) ≤ i2N.symm 0 := bot_le
      exact (OrderIso.symm_apply_le (Fintype.orderIsoFinOfCardEq ι rfl)).mpr h
    · -- 0 ≤ i2N ⊥ since 0 is the minimum in Fin n
      exact Fin.zero_le _

  have hSetIcceq :
    ∀ i j x : ι, x ∈ Set.Icc i j ↔ (i2N x) ∈ Set.Icc (i2N i) (i2N j) := by
    intro i j x
    constructor
    · intro hx
      simp only [Set.mem_Icc] at *
      have h1 : i2N i ≤ i2N x := by
        grind
      have h2 : i2N x ≤ i2N j := by
        grind
      exact ⟨h1, h2⟩
    · intro hy
      simp only [Set.mem_Icc] at *
      have h1 : i ≤ x := by
        grind
      have h2 : x ≤ j := by
        grind
      exact ⟨h1, h2⟩

  have hXhiteq : ∀ i j ω, ∀ s : Set ℝ,
      (∃ j_1 ∈ Set.Icc i j, X j_1 ω ∈ s)
    ↔ (∃ j_2 ∈ Set.Icc (i2N i : ℕ) (i2N j), X' j_2 ω ∈ s) := by
    intro i j ω s
    constructor
    · intro hhit1
      obtain ⟨j_1, hij1, hx1⟩ := hhit1
      use i2N j_1
      constructor
      · exact (hSetIcceq i j j_1).mp hij1
      · simp only [X', hN2ii2Nid]
        exact hx1
    · intro hhit2
      obtain ⟨j_2, hij2, hx2⟩ := hhit2
      use N2i j_2
      have hj_2lt : j_2 < n := by grind
      have hj_2eq : i2N (N2i j_2) = j_2 := by grind
      constructor
      · apply (hSetIcceq i j (N2i j_2)).mpr
        rw [← hj_2eq] at hij2
        exact hij2
      · simp only [X'] at hx2
        exact hx2

  #check Set.Nonempty.csInf_mem

  have hsfin : ∀ s : Set ι, s.Finite := by
    intro s
    exact Set.toFinite s

  have hsSupeq : ∀ s : Set ι, ∀ t : Set ℕ,
  -- t is the preimage of s through N2i
  -- Even if s is {y} = {N2i (n-1)}, so that t is {n-1, n, n+1, ...},
  -- we get sInf s = y, sInf t = (n-1), and N2i (sInf t) = N2i (n-1) = y.
  /-
  If f is monotone (but not necessarily injective),
  inf A = f (inf f^{-1}(A)) ?
  -/
    s.Nonempty ∧ (∀ x, (N2i x) ∈ s ↔ x ∈ t)
      → sInf s = N2i (sInf t) := by
    intro s t hst
    have hsnem : s.Nonempty := hst.left
    have hsinfmem : sInf s ∈ s := Set.Nonempty.csInf_mem hsnem (hsfin s)
    have hinfsrep : sInf s = N2i (i2N (sInf s)) := by
      grind
    have htpreims : ∀ x, (N2i x) ∈ s ↔ x ∈ t := hst.right
    have haux1 : BddBelow t := by
      refine ⟨0, ?_⟩
      intro x hx
      grind
    have haux2 : (i2N (sInf s)).val ∈ t := by
      grind
    have haux3 : sInf t ≤ (i2N (sInf s)).val := by
      exact csInf_le haux1 haux2
    have haux4 : N2i (sInf t) ≤ sInf s := by
      grind
    have htnem : t.Nonempty := by
      use (i2N (sInf s)).val
    -- We can't repeat the argument, t is not known to be finite.
    have haux42 : sInf s ≤ N2i (sInf t) := by
      have haux41 : ∀ x, x ∈ t → N2i x ∈ s := by
        intro x hx
        exact (htpreims x).mpr hx
      have haux411 : ∀ x, x ∈ t → sInf s ≤ N2i x := by
        intro x hx
        have hn2ixins : N2i x ∈ s := haux41 x hx
        exact csInf_le (hsfin s).bddBelow hn2ixins
      sorry

    exact le_antisymm haux42 haux4

  have hhitBtw : ∀ s i j ω, hittingBtwn X s i j ω = N2i (hittingBtwn X' s (i2N i) (i2N j) ω) := by
    intro s i j ω
    simp only [hittingBtwn]
    have hcondeq : ∀ s : Set ℝ, ∀ i ω, (X i ω ∈ s) ↔ (X' (i2N i) ω ∈ s) := by
      grind
    rw [hXhiteq]
    sorry
    -- split_ifs with h1

    -- have hSetIcccapeq :
    --   Set.Icc i j ∩ {i | X i ω ∈ s}
    --   = N2i (sInf (Set.Icc ↑(i2N i) ↑(i2N j) ∩ {i | X' i ω ∈ s}))
    -- by_cases -- h1 : ∃ j_1 ∈ Set.Icc i j, X j_1 ω ∈ s
    --   -- h1 : ∃ j_1 ∈ Set.Icc i j, X j_1 ω ∈ s
    --   have h1rhs : ∃ j_1 ∈ Set.Icc (i2N i) (i2N j), X' j_1 ω ∈ s := by
    --     simp only [X']
    --     obtain ⟨j_1, hij, hx⟩ := h1
    --     use i2N j_1
    --     constructor
    --     · refine Set.mem_Icc.mpr ?_








  have huppercrossings :
    ∀ k ω, upperCrossingTime a b X N k ω = N2i (upperCrossingTime a b X' N' k ω)
  := by
    intro k; induction k with
    | zero =>
        intro ω; simp only [upperCrossingTime, N2i]          -- both are ⊥
        have hX0_lt : 0 < n := by grind
        have h0_eq := restriction_to_Fin.eq_of_lt n 0 hn hX0_lt
        have h00 : ⊥ = i2N.symm 0 := by
          exact (OrderIso.apply_eq_iff_eq_symm_apply i2N ⊥ 0).mp hi2Neqbot
        sorry
        -- rw [h00]
        -- simp
        -- exact Fin.eq_of_val_eq (id (Eq.symm h0_eq))
    | succ k ih =>
        intro ω
        sorry
        -- -- bounds: both upperCrossingTimes ≤ N, so their Fin reps are < n
        -- have hX_le  := upperCrossingTime_le (a:=a) (b:=b) (f:=X)  (N:=N)  (n:=k) ω
        -- have hX'_le := upperCrossingTime_le (a:=a) (b:=b) (f:=X') (N:=N') (n:=k) ω
        -- have hX_lt  : upperCrossingTime a b X  N  k ω < n := lt_of_le_of_lt hX_le  hNlt
        -- have hX'_lt : upperCrossingTime a b X' N' k ω < n := lt_of_le_of_lt hX'_le hNlt

        -- -- unfold the succ step and transport hittingBtwn through N2i using ih
        -- simp [upperCrossingTime_succ, ih, hittingBtwn, N2i, hN2i_id hX_lt, hN2i_id hX'_lt]

  have hupcrossings :
    upcrossingsBefore a b X N = upcrossingsBefore a b X' N' := by
      ext ω
      simp only [upcrossingsBefore, huppercrossings]
      apply congr_arg sSup
      ext n
      exact hupton (N2i (upperCrossingTime a b X' N' n ω)) (upperCrossingTime a b X' N' n ω) rfl

  have hintegral :
    P[fun ω => (X N ω - a)⁺] = P[fun ω => (X' N' ω - a)⁺] := by
    rw[hXN]

  rw [hupcrossings, hintegral]

  exact Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part a b hf' (N' : ℕ)
