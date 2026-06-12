/-
Copyright (c) 2026 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import BrownianMotion.StochasticIntegral.Cadlag
public import BrownianMotion.StochasticIntegral.SimpleProcess
public import BrownianMotion.StochasticIntegral.OptionalSampling
public import Mathlib.Probability.Notation
public import Mathlib.Probability.Martingale.Upcrossing

/-! # Cadlag modification stochastic processes -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [TopologicalSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTopology ι]
  [FirstCountableTopology ι] -- required for ∀ t : ι, (𝓝[>] t).IsCountablyGenerated
  [DenselyOrdered ι] [NoMaxOrder ι] -- required for ∀ t : ι, (𝓝[>] t).NeBot)
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

local notation:25 V " ● " X => SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ) V X

/-! ### Discrete upcrossing helpers

Pathwise upcrossing estimates for `ℕ`-indexed processes. These supply the quantitative core of
the regularization argument: the number of upcrossings of `X` along a finite subset of the time
domain is controlled by an elementary stochastic integral. -/

section DiscreteUpcrossing

variable {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}

/-- `hittingBtwn` only depends on the hitting predicate. -/
lemma hittingBtwn_congr {u v : ℕ → Ω → ℝ} {s : Set ℝ}
    (h : ∀ i ω, u i ω ∈ s ↔ v i ω ∈ s) (n m : ℕ) :
    hittingBtwn u s n m = hittingBtwn v s n m := by
  ext ω
  have hs : {i : ℕ | u i ω ∈ s} = {i : ℕ | v i ω ∈ s} := Set.ext fun i ↦ h i ω
  have hex : (∃ j ∈ Set.Icc n m, u j ω ∈ s) = (∃ j ∈ Set.Icc n m, v j ω ∈ s) :=
    propext (exists_congr fun j ↦ and_congr_right fun _ ↦ h j ω)
  unfold hittingBtwn
  rw [hs, hex]

/-- Upper crossing times only depend on the position of the process relative to `a` and `b`. -/
lemma upperCrossingTime_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) (n : ℕ) :
    upperCrossingTime a b f N n = upperCrossingTime a b g N n := by
  have hIic' : ∀ i ω, f i ω ∈ Set.Iic a ↔ g i ω ∈ Set.Iic a := hIic
  have hIci' : ∀ i ω, f i ω ∈ Set.Ici b ↔ g i ω ∈ Set.Ici b := hIci
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ω
    rw [upperCrossingTime_succ_eq, upperCrossingTime_succ_eq, lowerCrossingTime,
      lowerCrossingTime, ih, hittingBtwn_congr hIic', hittingBtwn_congr hIci']

/-- Lower crossing times only depend on the position of the process relative to `a` and `b`. -/
lemma lowerCrossingTime_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) (n : ℕ) :
    lowerCrossingTime a b f N n = lowerCrossingTime a b g N n := by
  have hIic' : ∀ i ω, f i ω ∈ Set.Iic a ↔ g i ω ∈ Set.Iic a := hIic
  funext ω
  rw [lowerCrossingTime, lowerCrossingTime, upperCrossingTime_congr hIic hIci,
    hittingBtwn_congr hIic']

lemma upcrossingStrat_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) (n : ℕ) :
    upcrossingStrat a b f N n = upcrossingStrat a b g N n := by
  funext ω
  unfold upcrossingStrat
  simp_rw [upperCrossingTime_congr hIic hIci, lowerCrossingTime_congr hIic hIci]

lemma upcrossingsBefore_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) :
    upcrossingsBefore a b f N ω = upcrossingsBefore a b g N ω := by
  unfold upcrossingsBefore
  simp_rw [upperCrossingTime_congr hIic hIci]

/-- Pathwise upcrossing inequality with correction term: unlike
`MeasureTheory.mul_upcrossingsBefore_le`, this requires no assumption `a ≤ f N ω`, at the price
of the extra term `max (a - f N ω) 0`. -/
lemma mul_upcrossingsBefore_le_sum_add_max (hab : a < b) :
    (b - a) * upcrossingsBefore a b f N ω ≤
      (∑ k ∈ Finset.range N, upcrossingStrat a b f N k ω * (f (k + 1) - f k) ω)
        + max (a - f N ω) 0 := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [upcrossingsBefore_zero]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos hN).symm⟩
  set g : ℕ → Ω → ℝ := fun k ω' => if k = M + 1 then max (f k ω') a else f k ω' with hg
  have hIic : ∀ i ω', g i ω' ≤ a ↔ f i ω' ≤ a := by
    intro i ω'
    simp only [hg]
    split_ifs with h
    · simp
    · rfl
  have hIci : ∀ i ω', b ≤ g i ω' ↔ b ≤ f i ω' := by
    intro i ω'
    simp only [hg]
    split_ifs with h
    · rw [le_max_iff]
      simp only [or_iff_left_iff_imp]
      exact fun hba ↦ absurd (hba.trans_lt hab) (lt_irrefl b)
    · rfl
  have hga : a ≤ g (M + 1) ω := by simp [hg]
  have key := mul_upcrossingsBefore_le (f := g) (N := M + 1) (ω := ω) hga hab
  rw [upcrossingsBefore_congr hIic hIci] at key
  simp only [upcrossingStrat_congr hIic hIci] at key
  refine key.trans ?_
  rw [Finset.sum_range_succ, Finset.sum_range_succ
    (f := fun k ↦ upcrossingStrat a b f (M + 1) k ω * (f (k + 1) - f k) ω)]
  have hsum : ∀ k ∈ Finset.range M,
      upcrossingStrat a b f (M + 1) k ω * (g (k + 1) - g k) ω
        = upcrossingStrat a b f (M + 1) k ω * (f (k + 1) - f k) ω := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h1 : g (k + 1) = f (k + 1) := by
      simp only [hg, if_neg (Nat.succ_lt_succ hk).ne]
    have h2 : g k = f k := by
      simp only [hg, if_neg (hk.trans M.lt_succ_self).ne]
    rw [h1, h2]
  rw [Finset.sum_congr rfl hsum, add_assoc]
  gcongr
  have hgM : g M = f M := by simp only [hg, if_neg M.lt_succ_self.ne]
  have hgM1 : g (M + 1) ω = f (M + 1) ω + max (a - f (M + 1) ω) 0 := by
    simp only [hg, if_pos rfl]
    rcases le_total a (f (M + 1) ω) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
  rw [Pi.sub_apply, hgM, hgM1]
  have h01 : 0 ≤ upcrossingStrat a b f (M + 1) M ω := upcrossingStrat_nonneg
  have h11 : upcrossingStrat a b f (M + 1) M ω ≤ 1 := upcrossingStrat_le_one
  have hmax : 0 ≤ max (a - f (M + 1) ω) 0 := le_max_right _ _
  calc upcrossingStrat a b f (M + 1) M ω * (f (M + 1) ω + max (a - f (M + 1) ω) 0 - f M ω)
      = upcrossingStrat a b f (M + 1) M ω * (f (M + 1) - f M) ω
        + upcrossingStrat a b f (M + 1) M ω * max (a - f (M + 1) ω) 0 := by
        rw [Pi.sub_apply]; ring
    _ ≤ upcrossingStrat a b f (M + 1) M ω * (f (M + 1) - f M) ω + max (a - f (M + 1) ω) 0 := by
        gcongr
        calc upcrossingStrat a b f (M + 1) M ω * max (a - f (M + 1) ω) 0
            ≤ 1 * max (a - f (M + 1) ω) 0 := by gcongr
          _ = max (a - f (M + 1) ω) 0 := one_mul _

/-- Alternations force upcrossings: if there are `m` pairs of (strictly increasing) times below
`N` at which `f` is alternately strictly below `a` and strictly above `b`, then `f` has at least
`m` upcrossings of `[a, b]` before `N`. -/
lemma le_upcrossingsBefore_of_alternating (hab : a < b) {m : ℕ} {c : ℕ → ℕ}
    (hmono : ∀ i, i + 1 < 2 * m → c i < c (i + 1))
    (hN : ∀ i < 2 * m, c i < N)
    (ha : ∀ i < m, f (c (2 * i)) ω < a)
    (hb : ∀ i < m, b < f (c (2 * i + 1)) ω) :
    m ≤ upcrossingsBefore a b f N ω := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  -- key step: `i + 1 ≤ upcrossingsBefore a b f (c (2 * i + 1) + 1) ω` for all `i < m`
  have key : ∀ i, i < m → i + 1 ≤ upcrossingsBefore a b f (c (2 * i + 1) + 1) ω := by
    intro i
    induction i with
    | zero =>
      intro h0
      have := upcrossingsBefore_lt_of_exists_upcrossing (f := f) (ω := ω) (N := 0) hab
        (Nat.zero_le (c 0)) (ha 0 h0) (hmono 0 (by omega)).le (hb 0 h0)
      simpa [upcrossingsBefore_zero] using this
    | succ i ih =>
      intro hi
      have h1 : i + 1 ≤ upcrossingsBefore a b f (c (2 * i + 1) + 1) ω := ih (by omega)
      have h2 := upcrossingsBefore_lt_of_exists_upcrossing (f := f) (ω := ω)
        (N := c (2 * i + 1) + 1) hab
        (show c (2 * i + 1) + 1 ≤ c (2 * (i + 1)) from hmono (2 * i + 1) (by omega))
        (ha (i + 1) hi)
        (show c (2 * (i + 1)) ≤ c (2 * (i + 1) + 1) from (hmono (2 * (i + 1)) (by omega)).le)
        (hb (i + 1) hi)
      omega
  have hlast := key (m - 1) (by omega)
  have hmono' := upcrossingsBefore_mono (f := f) hab
    (show c (2 * (m - 1) + 1) + 1 ≤ N from hN (2 * (m - 1) + 1) (by omega))
  have hm1 : m - 1 + 1 = m := by omega
  rw [hm1] at hlast
  exact hlast.trans (hmono' ω)

end DiscreteUpcrossing

/-! ### Finite skeletons and the elementary integral bridge

Discrete data along a monotone sequence of times is converted into elementary predictable sets,
whose elementary stochastic integrals compute weighted sums of increments of `X`. -/

section Bridge

set_option linter.unusedSectionVars false

/-- The filtration on `ℕ` obtained by pulling back `𝓕` along a monotone sequence of times. -/
def pullbackFiltration (𝓕 : Filtration ι mΩ) {idx : ℕ → ι} (hidx : Monotone idx) :
    Filtration ℕ mΩ where
  seq k := 𝓕 (idx k)
  mono' _ _ h := 𝓕.mono (hidx h)
  le' _ := 𝓕.le _

@[simp] lemma pullbackFiltration_apply {idx : ℕ → ι} (hidx : Monotone idx) (k : ℕ) :
    pullbackFiltration 𝓕 hidx k = 𝓕 (idx k) := rfl

/-- The monotone enumeration of a finite set of times, extended by the constant `t` at indices
beyond `F.card`. -/
noncomputable def finIdx (F : Finset ι) (t : ι) : ℕ → ι := fun k ↦
  if h : k < F.card then (F.orderIsoOfFin rfl ⟨k, h⟩ : ι) else t

lemma finIdx_mem {F : Finset ι} {t : ι} {k : ℕ} (h : k < F.card) : finIdx F t k ∈ F := by
  rw [finIdx, dif_pos h]
  exact (F.orderIsoOfFin rfl ⟨k, h⟩).2

lemma finIdx_eq_of_card_le {F : Finset ι} {t : ι} {k : ℕ} (h : F.card ≤ k) :
    finIdx F t k = t := by
  rw [finIdx, dif_neg (by omega)]

lemma finIdx_le {F : Finset ι} {t : ι} (hF : ∀ s ∈ F, s ≤ t) (k : ℕ) : finIdx F t k ≤ t := by
  rcases lt_or_ge k F.card with h | h
  · exact hF _ (finIdx_mem h)
  · exact (finIdx_eq_of_card_le h).le

lemma finIdx_lt_of_lt {F : Finset ι} {t : ι} {k l : ℕ} (hkl : k < l) (hl : l < F.card) :
    finIdx F t k < finIdx F t l := by
  rw [finIdx, finIdx, dif_pos (hkl.trans hl), dif_pos hl]
  exact_mod_cast (F.orderIsoOfFin rfl).strictMono (by exact_mod_cast hkl)

lemma finIdx_monotone {F : Finset ι} {t : ι} (hF : ∀ s ∈ F, s ≤ t) : Monotone (finIdx F t) := by
  intro k l hkl
  rcases eq_or_lt_of_le hkl with rfl | hkl
  · exact le_rfl
  rcases lt_or_ge l F.card with h | h
  · exact (finIdx_lt_of_lt hkl h).le
  · rw [finIdx_eq_of_card_le h]
    exact finIdx_le hF k

lemma exists_finIdx_eq {F : Finset ι} {t : ι} {s : ι} (hs : s ∈ F) :
    ∃ k, k < F.card ∧ finIdx F t k = s := by
  obtain ⟨k, hk⟩ := (F.orderIsoOfFin rfl).surjective ⟨s, hs⟩
  exact ⟨k, k.2, by rw [finIdx, dif_pos k.2, Fin.eta, hk]⟩

/-- **Bridge lemma**: a finite collection of `{0,1}`-valued adapted weights along a monotone
sequence of times below `t` is realized by an elementary predictable set whose elementary
stochastic integral at time `t` is the weighted sum of increments of `X`. -/
lemma exists_elementaryPredictableSet_integral_eq {t : ι} (n : ℕ) {idx : ℕ → ι}
    (hidx : Monotone idx) (hidxt : ∀ k, idx k ≤ t) {W : ℕ → Ω → ℝ}
    (hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) :
    ∃ S : ElementaryPredictableSet 𝓕, ∀ ω,
      (S.indicator (1 : ℝ) ● X) t ω
        = ∑ k ∈ Finset.range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω) := by
  classical
  set K : Finset ℕ := {k ∈ Finset.range n | idx k < idx (k + 1)} with hK
  have hKmem : ∀ {k}, k ∈ K → k < n ∧ idx k < idx (k + 1) := by
    intro k hk
    simpa [hK] using hk
  have hinj : Set.InjOn (fun k ↦ (idx k, idx (k + 1))) K := by
    intro k hk l hl hkl
    simp only [Prod.mk.injEq] at hkl
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd ((hidx (Nat.succ_le_of_lt h)).trans_eq hkl.1.symm) (hKmem hk).2.not_ge
    · exact absurd ((hidx (Nat.succ_le_of_lt h)).trans_eq hkl.1) (hKmem hl).2.not_ge
  refine ⟨⟨∅, K.image fun k ↦ (idx k, idx (k + 1)),
    fun p ↦ if h : ∃ k ∈ K, (idx k, idx (k + 1)) = p then W h.choose ⁻¹' {1} else ∅,
    ?_, @MeasurableSet.empty _ (𝓕 ⊥), ?_, ?_⟩, ?_⟩
  · -- le_of_mem_I
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
    exact (hKmem hk).2.le
  · -- measurableSet_set
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
    have hex : ∃ k' ∈ K, (idx k', idx (k' + 1)) = (idx k, idx (k + 1)) := ⟨k, hk, rfl⟩
    simp only [dif_pos hex]
    obtain ⟨hcK, hceq⟩ := hex.choose_spec
    have h1 : idx hex.choose = idx k := (Prod.ext_iff.1 hceq).1
    have h2 : MeasurableSet[𝓕 (idx hex.choose)] (W hex.choose ⁻¹' {1}) :=
      hWmeas _ (hKmem hcK).1 (measurableSet_singleton 1)
    rwa [h1] at h2
  · -- pairwiseDisjoint
    intro p hp q hq hpq
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp hq
    obtain ⟨k, hk, rfl⟩ := hp
    obtain ⟨l, hl, rfl⟩ := hq
    have hkl : k ≠ l := fun h ↦ hpq (by rw [h])
    have hIoc : Disjoint (Set.Ioc (idx k) (idx (k + 1))) (Set.Ioc (idx l) (idx (l + 1))) := by
      rcases lt_or_gt_of_ne hkl with h | h
      · exact Set.Ioc_disjoint_Ioc_of_le (hidx (Nat.succ_le_of_lt h))
      · exact (Set.Ioc_disjoint_Ioc_of_le (hidx (Nat.succ_le_of_lt h))).symm
    exact Set.disjoint_left.2 fun x hx hx' ↦
      Set.disjoint_left.1 hIoc hx.1 hx'.1
  · -- the integral computation
    intro ω
    rw [ElementaryPredictableSet.integral_indicator_apply,
      Finset.sum_image fun k hk l hl h ↦ hinj hk hl h]
    refine (Finset.sum_congr rfl fun k hk ↦ ?_).trans
      (Finset.sum_subset (Finset.filter_subset _ _) fun k hk hkK ↦ ?_)
    · -- per-term equality on K
      have hex : ∃ k' ∈ K, (idx k', idx (k' + 1)) = (idx k, idx (k + 1)) := ⟨k, hk, rfl⟩
      have hchoose : hex.choose = k := hinj hex.choose_spec.1 hk hex.choose_spec.2
      have hst : ∀ j, stoppedProcess X (fun _ ↦ (t : WithTop ι)) (idx j) ω = X (idx j) ω :=
        fun j ↦ stoppedProcess_eq_of_le (by exact_mod_cast hidxt j)
      simp only [dif_pos hex, hchoose]
      rcases hW01 k (hKmem hk).1 ω with h0 | h1
      · rw [Set.indicator_of_notMem (by simp [h0]), h0, zero_mul]
      · rw [Set.indicator_of_mem (by simp [h1]), h1, one_mul]
        simp [ContinuousLinearMap.mul_apply', hst]
    · -- terms outside K vanish
      have hno : ¬ idx k < idx (k + 1) := fun h ↦ hkK (by simp [hK, Finset.mem_range.1 hk, h])
      have heq : idx (k + 1) = idx k :=
        le_antisymm (not_lt.1 hno) (hidx k.le_succ)
      rw [heq, sub_self, mul_zero]

end Bridge

/-! ### Upcrossing and alternation bounds along finite time sets -/

section UpcrossingBound

set_option linter.unusedSectionVars false

variable {a b : ℝ} {t : ι} {F : Finset ι} {m : ℕ}

/-- `upcrossingStrat` takes only the values `0` and `1`. -/
lemma upcrossingStrat_eq_zero_or_one (a b : ℝ) (f : ℕ → Ω → ℝ) (N n : ℕ) (ω : Ω) :
    upcrossingStrat a b f N n ω = 0 ∨ upcrossingStrat a b f N n ω = 1 := by
  classical
  rw [upcrossingStrat, ← Finset.indicator_biUnion_apply]
  · rw [Set.indicator_apply]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  intro i _ j _ hij
  simp only [Set.Ico_disjoint_Ico]
  obtain hij' | hij' := lt_or_gt_of_ne hij
  · rw [min_eq_left (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω ≤ upperCrossingTime a b f N _ ω),
      max_eq_right (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ ≤ lowerCrossingTime _ _ _ _ _ _)]
    exact le_trans upperCrossingTime_le_lowerCrossingTime
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))
  · rw [min_eq_right (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω ≤ upperCrossingTime a b f N _ ω),
      max_eq_left (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ ≤ lowerCrossingTime _ _ _ _ _ _)]
    exact le_trans upperCrossingTime_le_lowerCrossingTime
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))

/-- Expectation bound on the number of upcrossings along a finite set of times `F ⊆ Iic t`,
from the boundedness of elementary stochastic integrals at time `t`. -/
lemma mul_integral_upcrossingsBefore_finIdx_le [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hab : a < b) (hF : ∀ s ∈ F, s ≤ t) :
    (b - a) * ∫ ω, (upcrossingsBefore a b (fun k ↦ X (finIdx F t k)) F.card ω : ℝ) ∂μ
      ≤ C + ∫ ω, max (a - X t ω) 0 ∂μ := by
  classical
  set f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω with hf
  set n := F.card with hn
  have hadapt : StronglyAdapted (pullbackFiltration 𝓕 (finIdx_monotone hF)) f :=
    fun j ↦ hX (finIdx F t j)
  obtain ⟨S, hS⟩ := exists_elementaryPredictableSet_integral_eq (𝓕 := 𝓕) (X := X) n
    (finIdx_monotone hF) (finIdx_le hF) (W := upcrossingStrat a b f n)
    (fun k _ ω ↦ upcrossingStrat_eq_zero_or_one a b f n k ω)
    (fun k _ ↦ (hadapt.upcrossingStrat k).measurable)
  have hpath : ∀ ω, (b - a) * (upcrossingsBefore a b f n ω : ℝ)
      ≤ (S.indicator (1 : ℝ) ● X) t ω + max (a - X t ω) 0 := by
    intro ω
    have h1 := mul_upcrossingsBefore_le_sum_add_max (f := f) (N := n) (ω := ω) hab
    have hfn : f n ω = X t ω := by
      change X (finIdx F t n) ω = X t ω
      rw [finIdx_eq_of_card_le hn.ge]
    rw [hfn] at h1
    have h2 : (S.indicator (1 : ℝ) ● X) t ω
        = ∑ k ∈ Finset.range n, upcrossingStrat a b f n k ω * (f (k + 1) - f k) ω := hS ω
    rwa [← h2] at h1
  -- integrability of the elementary integral at `t`
  have hWmeas : ∀ k, Measurable (upcrossingStrat a b f n k) := fun k ↦
    ((hadapt.upcrossingStrat k).measurable).mono (𝓕.le _) le_rfl
  have hintS : Integrable ((S.indicator (1 : ℝ) ● X) t) μ := by
    have hSfun : ((S.indicator (1 : ℝ) ● X) t)
        = fun ω ↦ ∑ k ∈ Finset.range n,
          upcrossingStrat a b f n k ω * (X (finIdx F t (k + 1)) ω - X (finIdx F t k) ω) :=
      funext hS
    rw [hSfun]
    refine integrable_finsetSum _ fun k _ ↦ Integrable.bdd_mul
      (((hXint _).sub (hXint _)))
      (hWmeas k).aestronglyMeasurable (c := 1) (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg upcrossingStrat_nonneg]
    exact upcrossingStrat_le_one
  have hintmax : Integrable (fun ω ↦ max (a - X t ω) 0) μ :=
    (((integrable_const a).sub (hXint t))).pos_part
  have hintcount : Integrable (fun ω ↦ (upcrossingsBefore a b f n ω : ℝ)) μ :=
    hadapt.integrable_upcrossingsBefore hab
  calc (b - a) * ∫ ω, (upcrossingsBefore a b f n ω : ℝ) ∂μ
      = ∫ ω, (b - a) * (upcrossingsBefore a b f n ω : ℝ) ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ ω, ((S.indicator (1 : ℝ) ● X) t ω + max (a - X t ω) 0) ∂μ :=
        integral_mono (hintcount.const_mul _) (hintS.add hintmax) hpath
    _ = μ[(S.indicator (1 : ℝ) ● X) t] + ∫ ω, max (a - X t ω) 0 ∂μ :=
        integral_add hintS hintmax
    _ ≤ C + ∫ ω, max (a - X t ω) 0 ∂μ := by gcongr; exact hC S

variable (X) in
/-- The event that `X` makes `m` alternations from strictly below `a` to strictly above `b` at
increasing times inside the finite time set `F`. -/
def altSet (F : Finset ι) (a b : ℝ) (m : ℕ) : Set Ω :=
  {ω | ∃ c : ℕ → ι, (∀ i, i + 1 < 2 * m → c i < c (i + 1)) ∧ (∀ i < 2 * m, c i ∈ F)
    ∧ (∀ i < m, X (c (2 * i)) ω < a) ∧ (∀ i < m, b < X (c (2 * i + 1)) ω)}

lemma altSet_mono {F G : Finset ι} (h : F ⊆ G) : altSet X F a b m ⊆ altSet X G a b m :=
  fun _ ⟨c, hc1, hc2, hca, hcb⟩ ↦ ⟨c, hc1, fun i hi ↦ h (hc2 i hi), hca, hcb⟩

lemma finIdx_lt_finIdx_iff {k l : ℕ} (hk : k < F.card) (hl : l < F.card) :
    finIdx F t k < finIdx F t l ↔ k < l := by
  rw [finIdx, finIdx, dif_pos hk, dif_pos hl, Subtype.coe_lt_coe,
    OrderIso.lt_iff_lt, Fin.mk_lt_mk]

/-- On the event `altSet X F a b m`, the process `X` has at least `m` upcrossings along the
enumeration of `F`. -/
lemma altSet_subset_upcrossingsBefore (hab : a < b) :
    altSet X F a b m
      ⊆ {ω | m ≤ upcrossingsBefore a b (fun k ↦ X (finIdx F t k)) F.card ω} := by
  classical
  rintro ω ⟨c, hc1, hc2, hca, hcb⟩
  have hex : ∀ i, i < 2 * m → ∃ k, k < F.card ∧ finIdx F t k = c i :=
    fun i hi ↦ exists_finIdx_eq (hc2 i hi)
  set c' : ℕ → ℕ := fun i ↦ if hi : i < 2 * m then (hex i hi).choose else 0 with hc'
  have hc'spec : ∀ i (hi : i < 2 * m),
      c' i < F.card ∧ finIdx F t (c' i) = c i := by
    intro i hi
    rw [hc']
    simp only [dif_pos hi]
    exact (hex i hi).choose_spec
  refine le_upcrossingsBefore_of_alternating hab (c := c') ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨hlt1, heq1⟩ := hc'spec i (by omega)
    obtain ⟨hlt2, heq2⟩ := hc'spec (i + 1) hi
    rw [← finIdx_lt_finIdx_iff (t := t) hlt1 hlt2, heq1, heq2]
    exact hc1 i hi
  · exact fun i hi ↦ (hc'spec i hi).1
  · intro i hi
    rw [(hc'spec (2 * i) (by omega)).2]
    exact hca i hi
  · intro i hi
    rw [(hc'spec (2 * i + 1) (by omega)).2]
    exact hcb i hi

/-- Quantitative alternation bound: the probability of `m` alternations along any finite
`F ⊆ Iic t` is at most `K / m` with `K` independent of `F` and `m`. -/
lemma measureReal_altSet_le [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hab : a < b) (hm : 0 < m) (hF : ∀ s ∈ F, s ≤ t) :
    μ.real (altSet X F a b m)
      ≤ (C + ∫ ω, max (a - X t ω) 0 ∂μ) / (b - a) / m := by
  classical
  set f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω with hf
  have hadapt : StronglyAdapted (pullbackFiltration 𝓕 (finIdx_monotone hF)) f :=
    fun j ↦ hX (finIdx F t j)
  have hsub : altSet X F a b m
      ⊆ {ω | (m : ℝ) ≤ (upcrossingsBefore a b f F.card ω : ℝ)} := by
    refine (altSet_subset_upcrossingsBefore (t := t) hab).trans ?_
    intro ω hω
    exact_mod_cast hω
  have hmono : μ.real (altSet X F a b m)
      ≤ μ.real {ω | (m : ℝ) ≤ (upcrossingsBefore a b f F.card ω : ℝ)} :=
    measureReal_mono hsub
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun ω ↦ (upcrossingsBefore a b f F.card ω : ℝ))
    (ae_of_all _ fun ω ↦ by positivity)
    (hadapt.integrable_upcrossingsBefore hab) (m : ℝ)
  have hbound := mul_integral_upcrossingsBefore_finIdx_le
    (μ := μ) hX hXint hC hab hF
  have hbpos : (0 : ℝ) < b - a := sub_pos.2 hab
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  refine hmono.trans ?_
  rw [div_div, le_div_iff₀ (by positivity)]
  calc μ.real {ω | (m : ℝ) ≤ (upcrossingsBefore a b f F.card ω : ℝ)} * ((b - a) * m)
      = (b - a) * ((m : ℝ) * μ.real {ω | (m : ℝ) ≤ (upcrossingsBefore a b f F.card ω : ℝ)}) := by
        ring
    _ ≤ (b - a) * ∫ ω, (upcrossingsBefore a b f F.card ω : ℝ) ∂μ := by gcongr
    _ ≤ C + ∫ ω, max (a - X t ω) 0 ∂μ := hbound

end UpcrossingBound

/-! ### Maximal inequality along finite time sets -/

section Maximal

set_option linter.unusedSectionVars false

variable {t : ι} {F : Finset ι} {lam : ℝ}

/-- Discrete stopped telescoping identity: weighting the increments of `f` by the indicator of
"not yet above `lam`" telescopes to the value at the first time `f` exceeds `lam`. -/
lemma sum_indicator_mul_sub_eq_stopped (f : ℕ → Ω → ℝ) (lam : ℝ) (n : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range n,
        ({ω' | ∀ j ≤ k, f j ω' ≤ lam}.indicator 1 ω : ℝ) * (f (k + 1) ω - f k ω)
      = f (hittingBtwn f (Set.Ioi lam) 0 n ω) ω - f 0 ω := by
  classical
  induction n with
  | zero =>
    have h0 : hittingBtwn f (Set.Ioi lam) 0 0 ω = 0 := Nat.le_zero.1 (hittingBtwn_le ω)
    simp [h0]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hhit : ∃ j ∈ Set.Icc 0 n, f j ω ∈ Set.Ioi lam
    · -- already hit by time `n`: the hitting time stabilizes and the last weight vanishes
      have hstab : hittingBtwn f (Set.Ioi lam) 0 n ω = hittingBtwn f (Set.Ioi lam) 0 (n + 1) ω :=
        hittingBtwn_eq_hittingBtwn_of_exists (Nat.le_succ n) hhit
      obtain ⟨j, hj, hjs⟩ := hhit
      have hnotmem : ω ∉ {ω' | ∀ j' ≤ n, f j' ω' ≤ lam} :=
        fun hmem ↦ absurd (hmem j hj.2) (not_le.2 hjs)
      rw [Set.indicator_of_notMem hnotmem, hstab]
      ring
    · -- no hit yet: all weights up to `n` equal one and the hitting time is the horizon
      have hno : ∀ j, j ≤ n → f j ω ≤ lam :=
        fun j hj ↦ not_lt.1 fun hlt ↦ hhit ⟨j, ⟨Nat.zero_le j, hj⟩, hlt⟩
      have h1 : hittingBtwn f (Set.Ioi lam) 0 n ω = n := by
        refine le_antisymm (hittingBtwn_le ω) (not_lt.1 fun hlt ↦ ?_)
        obtain ⟨j, hj, hjs⟩ := (hittingBtwn_lt_iff n le_rfl).1 hlt
        exact absurd hjs (not_lt.2 (hno j hj.2.le))
      have h2 : hittingBtwn f (Set.Ioi lam) 0 (n + 1) ω = n + 1 := by
        refine le_antisymm (hittingBtwn_le ω) (not_lt.1 fun hlt ↦ ?_)
        obtain ⟨j, hj, hjs⟩ := (hittingBtwn_lt_iff (n + 1) le_rfl).1 hlt
        exact absurd hjs (not_lt.2 (hno j (Nat.lt_succ_iff.1 hj.2)))
      have hmem : ω ∈ {ω' | ∀ j' ≤ n, f j' ω' ≤ lam} := hno
      rw [Set.indicator_of_mem hmem, h1, h2]
      simp only [Pi.one_apply]
      ring

/-- Integrability of bounded-weight increment sums. -/
lemma integrable_sum_weight_increments {g : ι → Ω → ℝ} (hgint : ∀ s, Integrable (g s) μ)
    {n : ℕ} {idx : ℕ → ι} {W : ℕ → Ω → ℝ}
    (hWmeas : ∀ k, k < n → AEStronglyMeasurable (W k) μ)
    (hWb : ∀ k, k < n → ∀ ω, ‖W k ω‖ ≤ 1) :
    Integrable (fun ω ↦ ∑ k ∈ Finset.range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) μ :=
  integrable_finsetSum _ fun k hk ↦ Integrable.bdd_mul ((hgint _).sub (hgint _))
    (hWmeas k (Finset.mem_range.1 hk)) (ae_of_all _ (hWb k (Finset.mem_range.1 hk)))

/-- Two-sided expectation bound for adapted `{0,1}`-weighted increment sums of `X`, from the
boundedness of elementary stochastic integrals at time `t`. The lower bound uses the
complementary weights `1 - W`. -/
lemma integral_sum_weight_increments_mem_Icc [IsFiniteMeasure μ]
    (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    {n : ℕ} {idx : ℕ → ι} (hidx : Monotone idx) (hidxt : ∀ k, idx k ≤ t)
    {W : ℕ → Ω → ℝ} (hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) :
    ∫ ω, (∑ k ∈ Finset.range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
        ∈ Set.Icc (-(C + ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)) C := by
  classical
  have hb01 : ∀ (V : ℕ → Ω → ℝ), (∀ k, k < n → ∀ ω, V k ω = 0 ∨ V k ω = 1) →
      ∀ k, k < n → ∀ ω, ‖V k ω‖ ≤ 1 := by
    intro V hV k hk ω
    rcases hV k hk ω with h | h <;> simp [h]
  have hupper : ∀ (V : ℕ → Ω → ℝ), (∀ k, k < n → ∀ ω, V k ω = 0 ∨ V k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (V k)) →
      ∫ ω, (∑ k ∈ Finset.range n, V k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ ≤ C := by
    intro V hV01 hVmeas
    obtain ⟨S, hS⟩ := exists_elementaryPredictableSet_integral_eq (𝓕 := 𝓕) (X := X) n
      hidx hidxt (W := V) hV01 hVmeas
    have : (fun ω ↦ ∑ k ∈ Finset.range n, V k ω * (X (idx (k + 1)) ω - X (idx k) ω))
        = ((S.indicator (1 : ℝ) ● X) t) := (funext hS).symm
    rw [this]
    exact hC S
  constructor
  · -- lower bound via the complementary weights
    have hW1 : ∀ k, k < n → ∀ ω, (1 - W k ω) = 0 ∨ (1 - W k ω) = 1 := by
      intro k hk ω
      rcases hW01 k hk ω with h | h <;> simp [h]
    have hW1meas : ∀ k, k < n → Measurable[𝓕 (idx k)] (fun ω ↦ 1 - W k ω) :=
      fun k hk ↦ (measurable_const.sub (hWmeas k hk))
    have hco := hupper (fun k ω ↦ 1 - W k ω) hW1 hW1meas
    have hsplit : ∀ ω, (∑ k ∈ Finset.range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω))
        = (X (idx n) ω - X (idx 0) ω)
          - ∑ k ∈ Finset.range n, (1 - W k ω) * (X (idx (k + 1)) ω - X (idx k) ω) := by
      intro ω
      have htel : ∑ k ∈ Finset.range n, (X (idx (k + 1)) ω - X (idx k) ω)
          = X (idx n) ω - X (idx 0) ω := Finset.sum_range_sub (fun k ↦ X (idx k) ω) n
      rw [← htel, ← Finset.sum_sub_distrib]
      congr 1 with k
      ring
    have hint1 : Integrable
        (fun ω ↦ ∑ k ∈ Finset.range n, (1 - W k ω) * (X (idx (k + 1)) ω - X (idx k) ω)) μ :=
      integrable_sum_weight_increments hXint
        (fun k hk ↦ ((hW1meas k hk).mono (𝓕.le _) le_rfl).aestronglyMeasurable)
        (hb01 _ hW1)
    have hintsub : Integrable (fun ω ↦ X (idx n) ω - X (idx 0) ω) μ :=
      (hXint _).sub (hXint _)
    have hI : ∫ ω, (∑ k ∈ Finset.range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
        = (∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ)
          - ∫ ω, (∑ k ∈ Finset.range n, (1 - W k ω) * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ := by
      rw [integral_congr_ae (μ := μ) (ae_of_all _ hsplit), integral_sub hintsub hint1]
    have hT : -(∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)
        ≤ ∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ := by
      rw [neg_le]
      calc -∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ
          ≤ |∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ| := neg_le_abs _
        _ ≤ ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ := abs_integral_le_integral_abs
    rw [hI]
    linarith [hco]
  · exact hupper W hW01 hWmeas

/-- One-sided maximal inequality along a finite skeleton for an adapted, integrable process `g`
whose adapted `{0,1}`-weighted increment sums along `idx` have expectation at most `K`. -/
lemma mul_measureReal_exists_lt_le [IsFiniteMeasure μ]
    {g : ι → Ω → ℝ} (hg : StronglyAdapted 𝓕 g) (hgint : ∀ s, Integrable (g s) μ)
    {n : ℕ} {idx : ℕ → ι} (hidx : Monotone idx) {K : ℝ}
    (hK : ∀ W : ℕ → Ω → ℝ, (∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) →
      ∫ ω, (∑ k ∈ Finset.range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) ∂μ ≤ K) :
    lam * μ.real {ω | ∃ k ≤ n, lam < g (idx k) ω}
      ≤ K + ∫ ω, |g (idx 0) ω| ∂μ + ∫ ω, |g (idx n) ω| ∂μ := by
  classical
  set f : ℕ → Ω → ℝ := fun k ω ↦ g (idx k) ω with hf
  set W : ℕ → Ω → ℝ := fun k ↦ {ω' | ∀ j ≤ k, f j ω' ≤ lam}.indicator 1 with hW
  have hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1 := by
    intro k _ ω
    by_cases h : ω ∈ {ω' | ∀ j ≤ k, f j ω' ≤ lam}
    · exact Or.inr (by rw [hW]; simp [Set.indicator_of_mem h])
    · exact Or.inl (by rw [hW]; simp [Set.indicator_of_notMem h])
  have hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k) := by
    intro k _
    have hset : MeasurableSet[𝓕 (idx k)] {ω' | ∀ j ≤ k, f j ω' ≤ lam} := by
      have : {ω' | ∀ j ≤ k, f j ω' ≤ lam} = ⋂ j ∈ Finset.Iic k, f j ⁻¹' Set.Iic lam := by
        ext ω'
        simp [Set.mem_iInter]
      rw [this]
      refine MeasurableSet.biInter (Finset.Iic k).countable_toSet fun j hj ↦ ?_
      have hj' : j ≤ k := Finset.mem_Iic.1 hj
      exact (𝓕.mono (hidx hj')) _ ((hg (idx j)).measurable measurableSet_Iic)
    exact (measurable_const.indicator hset)
  have hWb : ∀ k, k < n → ∀ ω, ‖W k ω‖ ≤ 1 := by
    intro k hk ω
    rcases hW01 k hk ω with h | h <;> simp [h]
  -- the stopped value
  set tau : Ω → ℕ := fun ω ↦ hittingBtwn f (Set.Ioi lam) 0 n ω with htau
  set ftau : Ω → ℝ := fun ω ↦ f (tau ω) ω with hftau
  have htel : ∀ ω, ftau ω = f 0 ω
      + ∑ k ∈ Finset.range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω) := by
    intro ω
    have := sum_indicator_mul_sub_eq_stopped f lam n ω
    rw [hftau, htau]
    have hterm : ∀ k, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)
        = ({ω' | ∀ j ≤ k, f j ω' ≤ lam}.indicator 1 ω : ℝ) * (f (k + 1) ω - f k ω) := by
      intro k
      rfl
    simp_rw [hterm]
    rw [this]
    ring
  have hint_sum : Integrable
      (fun ω ↦ ∑ k ∈ Finset.range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) μ :=
    integrable_sum_weight_increments hgint
      (fun k hk ↦ ((hWmeas k hk).mono (𝓕.le _) le_rfl).aestronglyMeasurable) hWb
  have hint_ftau : Integrable ftau μ := by
    have : ftau = fun ω ↦ f 0 ω
        + ∑ k ∈ Finset.range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω) := funext htel
    rw [this]
    exact (hgint _).add hint_sum
  -- the event
  set H : Set Ω := {ω | ∃ k ≤ n, lam < g (idx k) ω} with hH
  have hHmeas : MeasurableSet H := by
    have : H = ⋃ k ∈ Finset.Iic n, (g (idx k)) ⁻¹' Set.Ioi lam := by
      ext ω
      simp [hH]
    rw [this]
    exact MeasurableSet.biUnion (Finset.Iic n).countable_toSet fun k _ ↦
      (𝓕.le _) _ ((hg (idx k)).measurable measurableSet_Ioi)
  -- on `H`, the stopped value exceeds `lam`
  have hHval : ∀ ω ∈ H, lam < ftau ω := by
    intro ω hω
    obtain ⟨k, hk, hkval⟩ := hω
    have hexists : ∃ j ∈ Set.Icc 0 n, f j ω ∈ Set.Ioi lam := ⟨k, ⟨Nat.zero_le k, hk⟩, hkval⟩
    exact hittingBtwn_mem_set hexists
  -- off `H`, the stopped value is the terminal value
  have hHcval : ∀ ω ∉ H, ftau ω = f n ω := by
    intro ω hω
    have hno : ∀ j, j ≤ n → f j ω ≤ lam := by
      intro j hj
      by_contra hlt
      exact hω ⟨j, hj, not_le.1 hlt⟩
    have h1 : tau ω = n := by
      refine le_antisymm (hittingBtwn_le ω) (not_lt.1 fun hlt ↦ ?_)
      obtain ⟨j, hj, hjs⟩ := (hittingBtwn_lt_iff n le_rfl).1 hlt
      exact absurd hjs (not_lt.2 (hno j hj.2.le))
    change f (tau ω) ω = f n ω
    rw [h1]
  -- assemble
  have hsplit : ∫ ω, ftau ω ∂μ = (∫ ω in H, ftau ω ∂μ) + ∫ ω in Hᶜ, ftau ω ∂μ :=
    (integral_add_compl hHmeas hint_ftau).symm
  have hlower : lam * μ.real H ≤ ∫ ω in H, ftau ω ∂μ := by
    calc lam * μ.real H = ∫ _ in H, lam ∂μ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ ω in H, ftau ω ∂μ := by
          refine setIntegral_mono_on (integrable_const lam).integrableOn
            hint_ftau.integrableOn hHmeas fun ω hω ↦ (hHval ω hω).le
  have hcompl : -(∫ ω, |g (idx n) ω| ∂μ) ≤ ∫ ω in Hᶜ, ftau ω ∂μ := by
    have heq : ∫ ω in Hᶜ, ftau ω ∂μ = ∫ ω in Hᶜ, f n ω ∂μ :=
      setIntegral_congr_fun hHmeas.compl fun ω hω ↦ hHcval ω hω
    rw [heq, neg_le]
    calc -∫ ω in Hᶜ, f n ω ∂μ ≤ |∫ ω in Hᶜ, f n ω ∂μ| := neg_le_abs _
      _ ≤ ∫ ω in Hᶜ, |f n ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, |g (idx n) ω| ∂μ :=
          setIntegral_le_integral (hgint _).abs (ae_of_all _ fun ω ↦ abs_nonneg _)
  have htotal : ∫ ω, ftau ω ∂μ ≤ K + ∫ ω, |g (idx 0) ω| ∂μ := by
    have : ∫ ω, ftau ω ∂μ = (∫ ω, f 0 ω ∂μ)
        + ∫ ω, (∑ k ∈ Finset.range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) ∂μ := by
      rw [← integral_add (hgint _) hint_sum]
      exact integral_congr_ae (ae_of_all _ htel)
    rw [this]
    have h0 : ∫ ω, f 0 ω ∂μ ≤ ∫ ω, |g (idx 0) ω| ∂μ :=
      integral_mono (hgint _) (hgint _).abs fun ω ↦ le_abs_self _
    have hsum := hK W hW01 hWmeas
    linarith
  linarith [hsplit, hlower, hcompl, htotal]

lemma finIdx_zero_eq_bot {F : Finset ι} {t : ι} (hbot : ⊥ ∈ F) : finIdx F t 0 = ⊥ := by
  have hcard : 0 < F.card := Finset.card_pos.2 ⟨⊥, hbot⟩
  obtain ⟨k, hk, hkeq⟩ := exists_finIdx_eq (t := t) hbot
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact hkeq
  · exact le_bot_iff.1 (hkeq ▸ (finIdx_lt_of_lt hkpos hk).le)

/-- **Maximal inequality**: the probability that `|X|` exceeds `lam` somewhere on a finite set
`F ⊆ Iic t` is at most `K / lam`, with `K` independent of `F`. -/
lemma measureReal_exists_abs_lt_le [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hlam : 0 < lam) (hF : ∀ s ∈ F, s ≤ t) :
    μ.real {ω | ∃ s ∈ F, lam < |X s ω|}
      ≤ 2 * (C + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ + ∫ ω, |X t ω| ∂μ) / lam := by
  classical
  set G : Finset ι := insert ⊥ F with hG
  have hGF : F ⊆ G := Finset.subset_insert _ _
  have hGle : ∀ s ∈ G, s ≤ t := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact bot_le
    · exact hF s hs
  set n : ℕ := G.card with hn
  set idx : ℕ → ι := finIdx G t with hidx
  have hmono : Monotone idx := finIdx_monotone hGle
  have hidx0 : idx 0 = ⊥ := finIdx_zero_eq_bot (Finset.mem_insert_self _ _)
  have hidxn : idx n = t := finIdx_eq_of_card_le hn.ge
  -- two-sided expectation bound for adapted 0/1 weights along `idx`
  have hbdd : ∀ W : ℕ → Ω → ℝ, (∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) →
      ∫ ω, (∑ k ∈ Finset.range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
        ∈ Set.Icc (-(C + ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)) C :=
    fun W hW01 hWmeas ↦ integral_sum_weight_increments_mem_Icc (t := t) hXint hC hmono
      (finIdx_le hGle) hW01 hWmeas
  -- apply the one-sided maximal inequality to `X`
  have hpos := mul_measureReal_exists_lt_le (lam := lam) hX hXint (n := n) hmono (K := C)
    (fun W hW01 hWmeas ↦ (hbdd W hW01 hWmeas).2)
  -- and to `-X`
  have hnegX : StronglyAdapted 𝓕 (fun s ω ↦ -X s ω) := fun s ↦ (hX s).neg
  have hnegint : ∀ s, Integrable ((fun s ω ↦ -X s ω) s) μ := fun s ↦ (hXint s).neg
  have hneg := mul_measureReal_exists_lt_le (lam := lam) hnegX hnegint (n := n) hmono
    (K := C + ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)
    (fun W hW01 hWmeas ↦ by
      have h1 := (hbdd W hW01 hWmeas).1
      have h2 : ∫ ω, (∑ k ∈ Finset.range n, W k ω * (-X (idx (k + 1)) ω - -X (idx k) ω)) ∂μ
          = -∫ ω, (∑ k ∈ Finset.range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ := by
        rw [← integral_neg]
        congr 1 with ω
        rw [← Finset.sum_neg_distrib]
        congr 1 with k
        ring
      rw [h2]
      linarith)
  -- combine the two events
  have hsub : {ω | ∃ s ∈ F, lam < |X s ω|}
      ⊆ {ω | ∃ k ≤ n, lam < X (idx k) ω} ∪ {ω | ∃ k ≤ n, lam < -X (idx k) ω} := by
    rintro ω ⟨s, hs, habs⟩
    obtain ⟨k, hk, hkeq⟩ := exists_finIdx_eq (t := t) (hGF hs)
    have hkeq' : idx k = s := hkeq
    rcases lt_abs.1 habs with h | h
    · exact Or.inl ⟨k, hk.le, hkeq'.symm ▸ h⟩
    · exact Or.inr ⟨k, hk.le, hkeq'.symm ▸ h⟩
  have habs0 : ∫ ω, |(fun s ω ↦ -X s ω) ⊥ ω| ∂μ = ∫ ω, |X ⊥ ω| ∂μ := by
    congr 1 with ω
    rw [abs_neg]
  have habsn : ∫ ω, |(fun s ω ↦ -X s ω) t ω| ∂μ = ∫ ω, |X t ω| ∂μ := by
    congr 1 with ω
    rw [abs_neg]
  rw [hidx0, hidxn] at hpos hneg
  rw [habs0, habsn] at hneg
  have hunion : μ.real {ω | ∃ s ∈ F, lam < |X s ω|}
      ≤ μ.real {ω | ∃ k ≤ n, lam < X (idx k) ω} + μ.real {ω | ∃ k ≤ n, lam < -X (idx k) ω} :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have hI : (0 : ℝ) ≤ ∫ ω, |X t ω - X ⊥ ω| ∂μ := integral_nonneg fun ω ↦ abs_nonneg _
  rw [le_div_iff₀ hlam]
  have hmul : lam * μ.real {ω | ∃ s ∈ F, lam < |X s ω|}
      ≤ lam * (μ.real {ω | ∃ k ≤ n, lam < X (idx k) ω}
        + μ.real {ω | ∃ k ≤ n, lam < -X (idx k) ω}) :=
    mul_le_mul_of_nonneg_left hunion hlam.le
  rw [mul_add] at hmul
  nlinarith [hpos, hneg, hmul]

end Maximal

/-! ### Almost-sure regularity along countable time sets -/

section CountableEvents

set_option linter.unusedSectionVars false

variable {T : Set ι} {t : ι} {a b lam : ℝ} {m : ℕ}

lemma countable_setOf_finset_coe_subset (hT : T.Countable) :
    {F : Finset ι | ↑F ⊆ T}.Countable := by
  have h1 : {F : Finset ι | ↑F ⊆ T}
      ⊆ (fun F : Finset ι ↦ (F : Set ι)) ⁻¹' {u : Set ι | u.Finite ∧ u ⊆ T} :=
    fun F hF ↦ ⟨F.finite_toSet, hF⟩
  exact ((Set.countable_setOf_finite_subset hT).preimage Finset.coe_injective).mono h1

/-- The union of the alternation events over all finite subsets of a countable set of times
below `t` has measure at most `K / ((b - a) * m)`. -/
lemma measure_biUnion_altSet_le [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hab : a < b) (hm : 0 < m) (hT : T.Countable) :
    μ (⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b m)
      ≤ ENNReal.ofReal ((C + ∫ ω, max (a - X t ω) 0 ∂μ) / (b - a) / m) := by
  have hcnt : {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}.Countable :=
    countable_setOf_finset_coe_subset (hT.mono Set.inter_subset_left)
  have hdir : DirectedOn (Function.onFun (· ⊆ ·) fun F : Finset ι ↦ altSet X F a b m)
      {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t} := by
    intro F₁ h₁ F₂ h₂
    refine ⟨F₁ ∪ F₂, ?_, altSet_mono Finset.subset_union_left,
      altSet_mono Finset.subset_union_right⟩
    rw [Set.mem_setOf_eq, Finset.coe_union]
    exact Set.union_subset h₁ h₂
  rw [measure_biUnion_eq_iSup hcnt hdir]
  refine iSup₂_le fun F hF ↦ ?_
  have hF' : ∀ s ∈ F, s ≤ t := fun s hs ↦ (hF hs).2
  calc μ (altSet X F a b m) = ENNReal.ofReal (μ.real (altSet X F a b m)) :=
        (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
        (measureReal_altSet_le (μ := μ) hX hXint hC hab hm hF')

/-- Almost surely, there is no infinite family of alternations of `X` from below `a` to above `b`
at times in a countable set `T` below `t`. -/
lemma measure_iInter_biUnion_altSet [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hab : a < b) (hT : T.Countable) :
    μ (⋂ m : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b (m + 1)) = 0 := by
  refine le_antisymm ?_ zero_le'
  have hbound : ∀ m : ℕ,
      μ (⋂ m : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b (m + 1))
        ≤ ENNReal.ofReal ((C + ∫ ω, max (a - X t ω) 0 ∂μ) / (b - a) / (m + 1)) := by
    intro m
    refine (measure_mono (Set.iInter_subset _ m)).trans ?_
    have := measure_biUnion_altSet_le (μ := μ) hX hXint hC hab (Nat.succ_pos m) hT
    convert this using 3
    push_cast
    ring
  have hlim : Tendsto (fun m : ℕ ↦
      ENNReal.ofReal ((C + ∫ ω, max (a - X t ω) 0 ∂μ) / (b - a) / (m + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    have h1 : Tendsto (fun n : ℕ ↦ ((C + ∫ ω, max (a - X t ω) 0 ∂μ) / (b - a)) / n)
        atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    have h2 := h1.comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun m ↦ ?_
    simp [Function.comp, div_div]
  exact ge_of_tendsto' hlim hbound

/-- The union of the maximal events over all finite subsets of a countable set of times below
`t` has measure at most `K / lam`. -/
lemma measure_biUnion_exists_abs_le [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hlam : 0 < lam) (hT : T.Countable) :
    μ (⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, {ω | ∃ s ∈ F, lam < |X s ω|})
      ≤ ENNReal.ofReal (2 * (C + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ
          + ∫ ω, |X t ω| ∂μ) / lam) := by
  have hcnt : {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}.Countable :=
    countable_setOf_finset_coe_subset (hT.mono Set.inter_subset_left)
  have hdir : DirectedOn (Function.onFun (· ⊆ ·)
      fun F : Finset ι ↦ {ω | ∃ s ∈ F, lam < |X s ω|})
      {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t} := by
    intro F₁ h₁ F₂ h₂
    refine ⟨F₁ ∪ F₂, ?_, fun ω ⟨s, hs, hval⟩ ↦ ⟨s, Finset.mem_union_left _ hs, hval⟩,
      fun ω ⟨s, hs, hval⟩ ↦ ⟨s, Finset.mem_union_right _ hs, hval⟩⟩
    rw [Set.mem_setOf_eq, Finset.coe_union]
    exact Set.union_subset h₁ h₂
  rw [measure_biUnion_eq_iSup hcnt hdir]
  refine iSup₂_le fun F hF ↦ ?_
  have hF' : ∀ s ∈ F, s ≤ t := fun s hs ↦ (hF hs).2
  calc μ {ω | ∃ s ∈ F, lam < |X s ω|}
      = ENNReal.ofReal (μ.real {ω | ∃ s ∈ F, lam < |X s ω|}) :=
        (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
        (measureReal_exists_abs_lt_le (μ := μ) hX hXint hC hlam hF')

/-- Almost surely, `X` is bounded on any countable set of times below `t`. -/
lemma measure_iInter_biUnion_exists_abs [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hT : T.Countable) :
    μ (⋂ M : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t},
      {ω | ∃ s ∈ F, (M + 1 : ℝ) < |X s ω|}) = 0 := by
  refine le_antisymm ?_ zero_le'
  have hbound : ∀ M : ℕ,
      μ (⋂ M : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t},
          {ω | ∃ s ∈ F, (M + 1 : ℝ) < |X s ω|})
        ≤ ENNReal.ofReal (2 * (C + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ
            + ∫ ω, |X t ω| ∂μ) / (M + 1)) := by
    intro M
    refine (measure_mono (Set.iInter_subset _ M)).trans ?_
    exact measure_biUnion_exists_abs_le (μ := μ) hX hXint hC (by positivity) hT
  have hlim : Tendsto (fun M : ℕ ↦
      ENNReal.ofReal (2 * (C + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ
        + ∫ ω, |X t ω| ∂μ) / (M + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    have h1 : Tendsto (fun n : ℕ ↦ (2 * (C + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ
        + ∫ ω, |X t ω| ∂μ)) / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    have h2 := h1.comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun M ↦ ?_
    simp [Function.comp]
  exact ge_of_tendsto' hlim hbound

end CountableEvents

/-! ### Selection of alternating tuples from frequent oscillation -/

section Selection

set_option linter.unusedSectionVars false

variable {T : Set ι} {x d : ι} {a b : ℝ} {ω : Ω}

/-- If `X` is frequently below `a` and frequently above `b` in the right-neighborhood filter of
`x` within `T`, then arbitrarily many alternations occur in `T ∩ Ioo x d`. -/
lemma exists_finset_altSet_of_frequently_right (hxd : x < d)
    (hfa : ∃ᶠ s in 𝓝[>] x ⊓ 𝓟 T, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[>] x ⊓ 𝓟 T, b < X s ω) (m : ℕ) :
    ∃ F : Finset ι, ↑F ⊆ T ∩ Set.Ioo x d ∧ ω ∈ altSet X F a b m := by
  classical
  -- descending selection: even picks above `b`, odd picks below `a`
  have hsel : ∀ k : ℕ, ∃ c : ℕ → ι, (∀ i, i + 1 < k → c (i + 1) < c i)
      ∧ (∀ i < k, c i ∈ T ∩ Set.Ioo x d)
      ∧ (∀ i < k, if Even i then b < X (c i) ω else X (c i) ω < a) := by
    intro k
    induction k with
    | zero => exact ⟨fun _ ↦ d, by omega, by omega, by omega⟩
    | succ k ih =>
      obtain ⟨c, hdesc, hmem, hval⟩ := ih
      -- previous lower endpoint
      set u : ι := if hk : 0 < k then c (k - 1) else d with hu
      have hxu : x < u := by
        rw [hu]
        split_ifs with hk
        · exact (hmem (k - 1) (by omega)).2.1
        · exact hxd
      have hud : u ≤ d := by
        rw [hu]
        split_ifs with hk
        · exact (hmem (k - 1) (by omega)).2.2.le
        · exact le_rfl
      have hU : Set.Ioo x u ∩ T ∈ 𝓝[>] x ⊓ 𝓟 T :=
        Filter.inter_mem (Filter.mem_inf_of_left (Ioo_mem_nhdsGT hxu))
          (Filter.mem_inf_of_right (Filter.mem_principal_self T))
      have hpick : ∃ s, s ∈ Set.Ioo x u ∩ T
          ∧ if Even k then b < X s ω else X s ω < a := by
        by_cases hk : Even k
        · simp only [if_pos hk]
          obtain ⟨s, hs1, hs2⟩ := (hfb.and_eventually (Filter.eventually_of_mem hU
            (fun s hs ↦ hs))).exists
          exact ⟨s, hs2, hs1⟩
        · simp only [if_neg hk]
          obtain ⟨s, hs1, hs2⟩ := (hfa.and_eventually (Filter.eventually_of_mem hU
            (fun s hs ↦ hs))).exists
          exact ⟨s, hs2, hs1⟩
      obtain ⟨s, ⟨hsIoo, hsT⟩, hsval⟩ := hpick
      refine ⟨Function.update c k s, ?_, ?_, ?_⟩
      · intro i hi
        rcases Nat.lt_or_ge (i + 1) k with h | h
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hdesc i h
        · have hik : i + 1 = k := by omega
          have hipos : 0 < k := by omega
          rw [hik, Function.update_self, Function.update_of_ne (by omega)]
          have hci : c i = u := by
            rw [hu, dif_pos hipos]
            congr 1
            omega
          rw [hci]
          exact hsIoo.2
      · intro i hi
        rcases Nat.lt_or_ge i k with h | h
        · rw [Function.update_of_ne (by omega)]
          exact hmem i h
        · have hik : i = k := by omega
          rw [hik, Function.update_self]
          exact ⟨hsT, hsIoo.1, hsIoo.2.trans_le hud⟩
      · intro i hi
        rcases Nat.lt_or_ge i k with h | h
        · rw [Function.update_of_ne (by omega)]
          exact hval i h
        · have hik : i = k := by omega
          subst hik
          rw [Function.update_self]
          exact hsval
  obtain ⟨c, hdesc, hmem, hval⟩ := hsel (2 * m)
  -- reverse the order
  set ca : ℕ → ι := fun j ↦ c (2 * m - 1 - j) with hca
  refine ⟨(Finset.range (2 * m)).image ca, ?_, ca, ?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [Finset.coe_image, Set.mem_image, Finset.coe_range, Set.mem_Iio] at hs
    obtain ⟨j, hj, rfl⟩ := hs
    exact hmem _ (by omega)
  · intro j hj
    have h1 : 2 * m - 1 - (j + 1) + 1 = 2 * m - 1 - j := by omega
    have h2 := hdesc (2 * m - 1 - (j + 1)) (by omega)
    rw [h1] at h2
    exact h2
  · intro j hj
    exact Finset.mem_image_of_mem _ (Finset.mem_range.2 hj)
  · intro i hi
    have hodd : ¬ Even (2 * m - 1 - 2 * i) := by
      have h1 : 2 * m - 1 - 2 * i = 2 * (m - i - 1) + 1 := by omega
      rw [h1]
      simp
    have h2 := hval (2 * m - 1 - 2 * i) (by omega)
    rw [if_neg hodd] at h2
    exact h2
  · intro i hi
    have heven : Even (2 * m - 1 - (2 * i + 1)) := by
      have h1 : 2 * m - 1 - (2 * i + 1) = 2 * (m - i - 1) := by omega
      exact h1 ▸ even_two_mul _
    have h2 := hval (2 * m - 1 - (2 * i + 1)) (by omega)
    rw [if_pos heven] at h2
    exact h2

/-- Left-neighborhood version of `exists_finset_altSet_of_frequently_right`: the alternations
occur in `T ∩ Iio x`. -/
lemma exists_finset_altSet_of_frequently_left
    (hfa : ∃ᶠ s in 𝓝[<] x ⊓ 𝓟 T, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[<] x ⊓ 𝓟 T, b < X s ω) (m : ℕ) :
    ∃ F : Finset ι, ↑F ⊆ T ∩ Set.Iio x ∧ ω ∈ altSet X F a b m := by
  classical
  -- ascending selection: even picks below `a`, odd picks above `b`
  have hsel : ∀ k : ℕ, ∃ c : ℕ → ι, (∀ i, i + 1 < k → c i < c (i + 1))
      ∧ (∀ i < k, c i ∈ T ∩ Set.Iio x)
      ∧ (∀ i < k, if Even i then X (c i) ω < a else b < X (c i) ω) := by
    intro k
    induction k with
    | zero => exact ⟨fun _ ↦ x, by omega, by omega, by omega⟩
    | succ k ih =>
      obtain ⟨c, hasc, hmem, hval⟩ := ih
      have hU : (if 0 < k then Set.Ioo (c (k - 1)) x else Set.Iio x) ∩ T
          ∈ 𝓝[<] x ⊓ 𝓟 T := by
        refine Filter.inter_mem (Filter.mem_inf_of_left ?_)
          (Filter.mem_inf_of_right (Filter.mem_principal_self T))
        split_ifs with hk
        · exact Ioo_mem_nhdsLT (hmem (k - 1) (by omega)).2
        · exact self_mem_nhdsWithin
      have hpick : ∃ s, s ∈ (if 0 < k then Set.Ioo (c (k - 1)) x else Set.Iio x) ∩ T
          ∧ if Even k then X s ω < a else b < X s ω := by
        by_cases hk : Even k
        · simp only [if_pos hk]
          obtain ⟨s, hs1, hs2⟩ := (hfa.and_eventually (Filter.eventually_of_mem hU
            (fun s hs ↦ hs))).exists
          exact ⟨s, hs2, hs1⟩
        · simp only [if_neg hk]
          obtain ⟨s, hs1, hs2⟩ := (hfb.and_eventually (Filter.eventually_of_mem hU
            (fun s hs ↦ hs))).exists
          exact ⟨s, hs2, hs1⟩
      obtain ⟨s, ⟨hsIoo, hsT⟩, hsval⟩ := hpick
      have hsx : s < x := by
        by_cases hk : 0 < k
        · rw [if_pos hk] at hsIoo
          exact hsIoo.2
        · rw [if_neg hk] at hsIoo
          exact hsIoo
      refine ⟨Function.update c k s, ?_, ?_, ?_⟩
      · intro i hi
        rcases Nat.lt_or_ge (i + 1) k with h | h
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hasc i h
        · have hik : i + 1 = k := by omega
          have hipos : 0 < k := by omega
          rw [hik, Function.update_self, Function.update_of_ne (by omega)]
          rw [if_pos hipos] at hsIoo
          have hci : c i = c (k - 1) := by congr 1; omega
          rw [hci]
          exact hsIoo.1
      · intro i hi
        rcases Nat.lt_or_ge i k with h | h
        · rw [Function.update_of_ne (by omega)]
          exact hmem i h
        · have hik : i = k := by omega
          rw [hik, Function.update_self]
          exact ⟨hsT, hsx⟩
      · intro i hi
        rcases Nat.lt_or_ge i k with h | h
        · rw [Function.update_of_ne (by omega)]
          exact hval i h
        · have hik : i = k := by omega
          subst hik
          rw [Function.update_self]
          exact hsval
  obtain ⟨c, hasc, hmem, hval⟩ := hsel (2 * m)
  refine ⟨(Finset.range (2 * m)).image c, ?_, c, hasc, ?_, ?_, ?_⟩
  · intro s hs
    simp only [Finset.coe_image, Set.mem_image, Finset.coe_range, Set.mem_Iio] at hs
    obtain ⟨j, hj, rfl⟩ := hs
    exact hmem _ (by omega)
  · intro j hj
    exact Finset.mem_image_of_mem _ (Finset.mem_range.2 hj)
  · intro i hi
    have h2 := hval (2 * i) (by omega)
    rwa [if_pos (even_two_mul i)] at h2
  · intro i hi
    have hodd : ¬ Even (2 * i + 1) := by simp
    have h2 := hval (2 * i + 1) (by omega)
    rwa [if_neg hodd] at h2

end Selection

/-! ### Almost-sure existence of one-sided limits along a countable time set -/

section AETendsto

set_option linter.unusedSectionVars false

/-- **Almost surely, `X` admits one-sided limits along a countable cofinal time set `T` at every
point of `ι`.** This is the probabilistic core of the regularization theorem. -/
lemma ae_tendsto_along_countable [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ)
    (hXbdd : ∀ t : ι, ∃ C, ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    {T : Set ι} (hT : T.Countable) (hTcof : ∀ x : ι, ∃ d ∈ T, x < d) :
    ∀ᵐ ω ∂μ, ∀ x : ι, (∃ l, Tendsto (fun s ↦ X s ω) (𝓝[>] x ⊓ 𝓟 T) (𝓝 l))
      ∧ (∃ l, Tendsto (fun s ↦ X s ω) (𝓝[<] x ⊓ 𝓟 T) (𝓝 l)) := by
  classical
  choose C hC using hXbdd
  set badAlt : ℚ → ℚ → ι → Set Ω := fun q r d ↦
    ⋂ m : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic d}, altSet X F q r (m + 1) with hbadAlt_def
  set badMax : ι → Set Ω := fun d ↦
    ⋂ M : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic d},
      {ω | ∃ s ∈ F, (M + 1 : ℝ) < |X s ω|} with hbadMax_def
  -- the bad sets are null
  have h1 : ∀ᵐ ω ∂μ, ∀ d ∈ T, ∀ q r : ℚ, (q : ℝ) < (r : ℝ) → ω ∉ badAlt q r d := by
    rw [ae_ball_iff hT]
    intro d _
    rw [ae_all_iff]
    intro q
    rw [ae_all_iff]
    intro r
    rw [eventually_imp_distrib_left]
    intro hqr
    exact compl_mem_ae_iff.2 (measure_iInter_biUnion_altSet hX hXint (hC d) hqr hT)
  have h2 : ∀ᵐ ω ∂μ, ∀ d ∈ T, ω ∉ badMax d := by
    rw [ae_ball_iff hT]
    intro d _
    exact compl_mem_ae_iff.2 (measure_iInter_biUnion_exists_abs hX hXint (hC d) hT)
  filter_upwards [h1, h2] with ω hω1 hω2
  intro x
  obtain ⟨d, hdT, hxd⟩ := hTcof x
  -- pathwise boundedness on `T ∩ Iic d`
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
    have hnot := hω2 d hdT
    rw [hbadMax_def] at hnot
    simp only [Set.mem_iInter, not_forall] at hnot
    obtain ⟨M, hM⟩ := hnot
    refine ⟨M, fun s' hs' ↦ ?_⟩
    by_contra hcon
    push Not at hcon
    refine hM (Set.mem_biUnion (x := ({s'} : Finset ι)) ?_ ?_)
    · rw [Set.mem_setOf_eq, Finset.coe_singleton, Set.singleton_subset_iff]
      exact hs'
    · exact ⟨s', Finset.mem_singleton_self s', hcon⟩
  have hdense : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
  constructor
  · -- right limits
    have hU : Set.Ioc x d ∩ T ∈ 𝓝[>] x ⊓ 𝓟 T :=
      Filter.inter_mem (Filter.mem_inf_of_left (Ioc_mem_nhdsGT hxd))
        (Filter.mem_inf_of_right (Filter.mem_principal_self T))
    have hbddAbove : Filter.IsBoundedUnder (· ≤ ·) (𝓝[>] x ⊓ 𝓟 T) (fun s' ↦ X s' ω) := by
      refine ⟨(M : ℝ) + 1, ?_⟩
      rw [Filter.eventually_map]
      filter_upwards [hU] with s' hs'
      exact le_of_abs_le (hM s' ⟨hs'.2, hs'.1.2⟩)
    have hbddBelow : Filter.IsBoundedUnder (· ≥ ·) (𝓝[>] x ⊓ 𝓟 T) (fun s' ↦ X s' ω) := by
      refine ⟨-((M : ℝ) + 1), ?_⟩
      rw [Filter.eventually_map]
      filter_upwards [hU] with s' hs'
      exact neg_le_of_abs_le (hM s' ⟨hs'.2, hs'.1.2⟩)
    refine tendsto_of_no_upcrossings hdense ?_ hbddAbove hbddBelow
    rintro p ⟨q, rfl⟩ p' ⟨r, rfl⟩ hqr ⟨hfa, hfb⟩
    refine hω1 d hdT q r hqr ?_
    rw [hbadAlt_def]
    rw [Set.mem_iInter]
    intro m
    obtain ⟨F, hFsub, hFalt⟩ := exists_finset_altSet_of_frequently_right hxd hfa hfb (m + 1)
    refine Set.mem_biUnion ?_ hFalt
    rw [Set.mem_setOf_eq]
    exact hFsub.trans (Set.inter_subset_inter_right T
      (Set.Ioo_subset_Ioc_self.trans Set.Ioc_subset_Iic_self))
  · -- left limits
    have hU : Set.Iio x ∩ T ∈ 𝓝[<] x ⊓ 𝓟 T :=
      Filter.inter_mem (Filter.mem_inf_of_left self_mem_nhdsWithin)
        (Filter.mem_inf_of_right (Filter.mem_principal_self T))
    have hbddAbove : Filter.IsBoundedUnder (· ≤ ·) (𝓝[<] x ⊓ 𝓟 T) (fun s' ↦ X s' ω) := by
      refine ⟨(M : ℝ) + 1, ?_⟩
      rw [Filter.eventually_map]
      filter_upwards [hU] with s' hs'
      exact le_of_abs_le (hM s' ⟨hs'.2, (hs'.1.trans hxd).le⟩)
    have hbddBelow : Filter.IsBoundedUnder (· ≥ ·) (𝓝[<] x ⊓ 𝓟 T) (fun s' ↦ X s' ω) := by
      refine ⟨-((M : ℝ) + 1), ?_⟩
      rw [Filter.eventually_map]
      filter_upwards [hU] with s' hs'
      exact neg_le_of_abs_le (hM s' ⟨hs'.2, (hs'.1.trans hxd).le⟩)
    refine tendsto_of_no_upcrossings hdense ?_ hbddAbove hbddBelow
    rintro p ⟨q, rfl⟩ p' ⟨r, rfl⟩ hqr ⟨hfa, hfb⟩
    refine hω1 d hdT q r hqr ?_
    rw [hbadAlt_def]
    rw [Set.mem_iInter]
    intro m
    obtain ⟨F, hFsub, hFalt⟩ := exists_finset_altSet_of_frequently_left hfa hfb (m + 1)
    refine Set.mem_biUnion ?_ hFalt
    rw [Set.mem_setOf_eq]
    refine hFsub.trans (Set.inter_subset_inter_right T ?_)
    exact fun s' hs' ↦ le_of_lt (lt_trans hs' hxd)

end AETendsto

/-! ### Pathwise regularization

For a fixed path `h : ι → ℝ` admitting one-sided limits along a dense set `T`, the right-limit
regularization `r` is right-continuous and inherits the left limits of `h`. -/

section PathRegularization

set_option linter.unusedSectionVars false

variable {T : Set ι} {h r : ι → ℝ} {x : ι}

lemma nhdsGT_inf_principal_neBot (hTd : Dense T) (x : ι) : (𝓝[>] x ⊓ 𝓟 T).NeBot := by
  rw [Filter.inf_principal_neBot_iff]
  intro U hU
  obtain ⟨u, hxu, hsub⟩ := (nhdsGT_basis x).mem_iff.1 hU
  obtain ⟨s', hs'T, hs'⟩ := hTd.exists_mem_open isOpen_Ioo
    (Set.nonempty_Ioo.2 hxu)
  exact ⟨s', hsub hs', hs'T⟩

/-- The right-limit regularization is right-continuous at every point. -/
lemma continuousWithinAt_rightLim (hTd : Dense T)
    (hr : ∀ y, Tendsto h (𝓝[>] y ⊓ 𝓟 T) (𝓝 (r y))) (x : ι) :
    ContinuousWithinAt r (Set.Ioi x) x := by
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hev : ∀ᶠ s in 𝓝[>] x ⊓ 𝓟 T, |h s - r x| < ε / 2 := by
    have hball := (hr x).eventually (Metric.ball_mem_nhds (r x) (by positivity : (0:ℝ) < ε / 2))
    filter_upwards [hball] with s hs
    rwa [Real.dist_eq] at hs
  obtain ⟨u, hxu, hu⟩ := (nhdsGT_basis x).eventually_iff.1 (Filter.eventually_inf_principal.1 hev)
  filter_upwards [Ioo_mem_nhdsGT hxu] with y hy
  have hyev : ∀ᶠ s in 𝓝[>] y ⊓ 𝓟 T, |h s - r x| ≤ ε / 2 := by
    refine Filter.eventually_inf_principal.2 ?_
    filter_upwards [Ioo_mem_nhdsGT hy.2] with s hs hsT
    exact (hu ⟨hy.1.trans hs.1, hs.2⟩ hsT).le
  have hne := nhdsGT_inf_principal_neBot hTd y
  have hle : |r y - r x| ≤ ε / 2 :=
    le_of_tendsto (((hr y).sub_const (r x)).abs) hyev
  calc dist (r y) (r x) = |r y - r x| := Real.dist_eq _ _
    _ ≤ ε / 2 := hle
    _ < ε := by linarith

/-- The right-limit regularization inherits left limits of `h` along `T`. -/
lemma tendsto_rightLim_nhdsLT (hTd : Dense T)
    (hr : ∀ y, Tendsto h (𝓝[>] y ⊓ 𝓟 T) (𝓝 (r y))) {L : ℝ}
    (hL : Tendsto h (𝓝[<] x ⊓ 𝓟 T) (𝓝 L)) :
    Tendsto r (𝓝[<] x) (𝓝 L) := by
  by_cases hex : ∃ u, u < x
  swap
  · have hempty : Set.Iio x = ∅ := Set.eq_empty_iff_forall_notMem.2
      (fun u hu ↦ hex ⟨u, hu⟩)
    rw [nhdsWithin, hempty, Filter.principal_empty, inf_bot_eq]
    exact tendsto_bot
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev : ∀ᶠ s in 𝓝[<] x ⊓ 𝓟 T, |h s - L| < ε / 2 := by
    have hball := hL.eventually (Metric.ball_mem_nhds L (by positivity : (0:ℝ) < ε / 2))
    filter_upwards [hball] with s hs
    rwa [Real.dist_eq] at hs
  obtain ⟨v, hvx, hv⟩ := (nhdsLT_basis_of_exists_lt hex).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  filter_upwards [Ioo_mem_nhdsLT hvx] with y hy
  have hyev : ∀ᶠ s in 𝓝[>] y ⊓ 𝓟 T, |h s - L| ≤ ε / 2 := by
    refine Filter.eventually_inf_principal.2 ?_
    filter_upwards [Ioo_mem_nhdsGT hy.2] with s hs hsT
    exact (hv ⟨hy.1.trans hs.1, hs.2⟩ hsT).le
  have hne := nhdsGT_inf_principal_neBot hTd y
  have hle : |r y - L| ≤ ε / 2 :=
    le_of_tendsto (((hr y).sub_const L).abs) hyev
  calc dist (r y) L = |r y - L| := Real.dist_eq _ _
    _ ≤ ε / 2 := hle
    _ < ε := by linarith

/-- Along a strictly increasing sequence `u → x` from the left, the regularized values
`r (u k)` tend to the left limit of `h` at `x` along `T' ⊇ T`. -/
lemma tendsto_rightLim_comp_of_lt (hTd : Dense T) {T' : Set ι} (hTT' : T ⊆ T')
    (hr : ∀ y, Tendsto h (𝓝[>] y ⊓ 𝓟 T) (𝓝 (r y))) {u : ℕ → ι} {L : ℝ}
    (hux : ∀ k, u k < x) (hutend : Tendsto u atTop (𝓝 x))
    (hL : Tendsto h (𝓝[<] x ⊓ 𝓟 T') (𝓝 L)) :
    Tendsto (fun k ↦ r (u k)) atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev : ∀ᶠ s in 𝓝[<] x ⊓ 𝓟 T', |h s - L| < ε / 2 := by
    have hball := hL.eventually (Metric.ball_mem_nhds L (by positivity : (0:ℝ) < ε / 2))
    filter_upwards [hball] with s hs
    rwa [Real.dist_eq] at hs
  obtain ⟨v, hvx, hv⟩ := (nhdsLT_basis_of_exists_lt ⟨u 0, hux 0⟩).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  have hevk : ∀ᶠ k in atTop, u k ∈ Set.Ioi v :=
    hutend (IsOpen.mem_nhds isOpen_Ioi hvx)
  filter_upwards [hevk] with k hk
  have hyev : ∀ᶠ s in 𝓝[>] (u k) ⊓ 𝓟 T, |h s - L| ≤ ε / 2 := by
    refine Filter.eventually_inf_principal.2 ?_
    filter_upwards [Ioo_mem_nhdsGT (hux k)] with s hs hsT
    exact (hv ⟨hk.trans hs.1, hs.2⟩ (hTT' hsT)).le
  have hne := nhdsGT_inf_principal_neBot hTd (u k)
  have hle : |r (u k) - L| ≤ ε / 2 :=
    le_of_tendsto (((hr (u k)).sub_const L).abs) hyev
  calc dist (r (u k)) L = |r (u k) - L| := Real.dist_eq _ _
    _ ≤ ε / 2 := hle
    _ < ε := by linarith

/-- Along a strictly decreasing sequence `u → x` from the right, the regularized values
`r (u k)` tend to the right limit of `h` at `x` along `T' ⊇ T`. -/
lemma tendsto_rightLim_comp_of_gt (hTd : Dense T) {T' : Set ι} (hTT' : T ⊆ T')
    (hr : ∀ y, Tendsto h (𝓝[>] y ⊓ 𝓟 T) (𝓝 (r y))) {u : ℕ → ι} {L : ℝ}
    (hux : ∀ k, x < u k) (hutend : Tendsto u atTop (𝓝 x))
    (hL : Tendsto h (𝓝[>] x ⊓ 𝓟 T') (𝓝 L)) :
    Tendsto (fun k ↦ r (u k)) atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev : ∀ᶠ s in 𝓝[>] x ⊓ 𝓟 T', |h s - L| < ε / 2 := by
    have hball := hL.eventually (Metric.ball_mem_nhds L (by positivity : (0:ℝ) < ε / 2))
    filter_upwards [hball] with s hs
    rwa [Real.dist_eq] at hs
  obtain ⟨v, hvx, hv⟩ := (nhdsGT_basis x).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  have hevk : ∀ᶠ k in atTop, u k ∈ Set.Iio v :=
    hutend (IsOpen.mem_nhds isOpen_Iio hvx)
  filter_upwards [hevk] with k hk
  have hyev : ∀ᶠ s in 𝓝[>] (u k) ⊓ 𝓟 T, |h s - L| ≤ ε / 2 := by
    refine Filter.eventually_inf_principal.2 ?_
    filter_upwards [Ioo_mem_nhdsGT hk] with s hs hsT
    exact (hv ⟨(hux k).trans hs.1, hs.2⟩ (hTT' hsT)).le
  have hne := nhdsGT_inf_principal_neBot hTd (u k)
  have hle : |r (u k) - L| ≤ ε / 2 :=
    le_of_tendsto (((hr (u k)).sub_const L).abs) hyev
  calc dist (r (u k)) L = |r (u k) - L| := Real.dist_eq _ _
    _ ≤ ε / 2 := hle
    _ < ε := by linarith

end PathRegularization

/-! ### Uncountable sets accumulate from the right -/

section Accumulation

set_option linter.unusedSectionVars false

/-- In a separable, densely-ordered linear order with order topology, the set of points of `A`
that are isolated from the right in `A` is countable. -/
lemma countable_setOf_right_isolated [TopologicalSpace.SeparableSpace ι] (A : Set ι) :
    {p ∈ A | ∃ b, p < b ∧ Set.Ioo p b ∩ A = ∅}.Countable := by
  classical
  obtain ⟨D₀, hD₀c, hD₀d⟩ := TopologicalSpace.exists_countable_dense ι
  set I := {p ∈ A | ∃ b, p < b ∧ Set.Ioo p b ∩ A = ∅} with hI
  have hbw : ∀ p ∈ I, ∃ bq : ι × ι, p < bq.1 ∧ Set.Ioo p bq.1 ∩ A = ∅
      ∧ bq.2 ∈ D₀ ∧ bq.2 ∈ Set.Ioo p bq.1 := by
    rintro p ⟨hpA, b, hpb, hbA⟩
    obtain ⟨q, hqD, hq⟩ := hD₀d.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.2 hpb)
    exact ⟨(b, q), hpb, hbA, hqD, hq⟩
  choose! bq hb1 hb2 hb3 hb4 using hbw
  have hkey : ∀ p ∈ I, ∀ p' ∈ I, p < p' → (bq p).2 < (bq p').2 := by
    intro p hp p' hp' hlt
    have hble : (bq p).1 ≤ p' := by
      by_contra hcon
      rw [not_le] at hcon
      have hmem : p' ∈ Set.Ioo p (bq p).1 ∩ A := ⟨⟨hlt, hcon⟩, hp'.1⟩
      rw [hb2 p hp] at hmem
      exact hmem
    exact ((hb4 p hp).2.trans_le hble).trans (hb4 p' hp').1
  have hinj : Set.InjOn (fun p ↦ (bq p).2) I := by
    intro p hp p' hp' hqq
    rcases lt_trichotomy p p' with h | h | h
    · exact absurd hqq (hkey p hp p' hp' h).ne
    · exact h
    · exact absurd hqq.symm (hkey p' hp' p hp h).ne
  exact Set.MapsTo.countable_of_injOn (fun p hp ↦ hb3 p hp) hinj hD₀c

/-- Any uncountable set in a separable, densely-ordered, first-countable linear order admits a
strictly decreasing sequence of its elements converging to a point from the right. -/
lemma exists_seq_strictAnti_tendsto_of_not_countable [TopologicalSpace.SeparableSpace ι]
    {A : Set ι} (hA : ¬ A.Countable) :
    ∃ p : ι, ∃ u : ℕ → ι, StrictAnti u ∧ (∀ k, u k ∈ A) ∧ (∀ k, p < u k)
      ∧ Tendsto u atTop (𝓝 p) := by
  classical
  have hsub : ¬ (A ⊆ {p ∈ A | ∃ b, p < b ∧ Set.Ioo p b ∩ A = ∅}) := by
    intro hcon
    exact hA ((countable_setOf_right_isolated A).mono hcon)
  rw [Set.not_subset] at hsub
  obtain ⟨p, hpA, hpiso⟩ := hsub
  have hacc : ∀ b, p < b → (Set.Ioo p b ∩ A).Nonempty := by
    intro b hb
    rw [Set.nonempty_iff_ne_empty]
    intro hcon
    exact hpiso ⟨hpA, b, hb, hcon⟩
  obtain ⟨V, hV⟩ := (𝓝 p).exists_antitone_basis
  have hstep : ∀ prev : ι, p < prev → ∀ j : ℕ, ∃ y, y ∈ A ∧ p < y ∧ y < prev ∧ y ∈ V j := by
    intro prev hprev j
    obtain ⟨w, hw, hsubV⟩ := exists_Ico_subset_of_mem_nhds (hV.mem j) ⟨prev, hprev⟩
    obtain ⟨y, hy⟩ := hacc (min w prev) (lt_min hw hprev)
    exact ⟨y, hy.2, hy.1.1, hy.1.2.trans_le (min_le_right _ _),
      hsubV ⟨hy.1.1.le, hy.1.2.trans_le (min_le_left _ _)⟩⟩
  obtain ⟨w0, hw0⟩ := exists_gt p
  obtain ⟨y0, hy0⟩ := hacc w0 hw0
  -- build the sequence by recursion through a subtype
  let Q : Type _ := {y : ι // y ∈ A ∧ p < y}
  let step : ℕ → Q → Q := fun k prev ↦
    ⟨(hstep prev.1 prev.2.2 (k + 1)).choose, (hstep prev.1 prev.2.2 (k + 1)).choose_spec.1,
      (hstep prev.1 prev.2.2 (k + 1)).choose_spec.2.1⟩
  let u' : ℕ → Q := fun k ↦ Nat.rec ⟨y0, hy0.2, hy0.1.1⟩ step k
  have hu'succ : ∀ k, u' (k + 1) = step k (u' k) := fun k ↦ rfl
  have hlt : ∀ k, (u' (k + 1)).1 < (u' k).1 := by
    intro k
    rw [hu'succ k]
    exact (hstep (u' k).1 (u' k).2.2 (k + 1)).choose_spec.2.2.1
  have hmemV : ∀ k, (u' (k + 1)).1 ∈ V (k + 1) := by
    intro k
    rw [hu'succ k]
    exact (hstep (u' k).1 (u' k).2.2 (k + 1)).choose_spec.2.2.2
  refine ⟨p, fun k ↦ (u' k).1, strictAnti_nat_of_succ_lt hlt, fun k ↦ (u' k).2.1,
    fun k ↦ (u' k).2.2, ?_⟩
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  exact hV.tendsto fun k ↦ hV.antitone (Nat.le_succ k) (hmemV k)

end Accumulation

/-- If `X` is an adapted integrable stochastic process such that the sets
`{𝔼[(𝟙_A ● X) t] | A elementary predicatable}` is bounded for any t, then it has a modification `Y`
which has left and right limits everywhere and is right continuous on a co-countable set
`s : Set ι`. -/
lemma exists_modification_left_right_limit [TopologicalSpace.SeparableSpace ι] [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ t, Integrable (X t) μ)
    (hXbdd : ∀ t : ι, ∃ C, ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C) :
    ∃ Y : ι → Ω → ℝ, (∀ t, Y t =ᵐ[μ] X t) ∧
      (∀ x ω, ∃ l, Tendsto (Y · ω) (𝓝[<] x) (𝓝 l)) ∧ -- left limit
      (∀ x ω, ∃ l, Tendsto (Y · ω) (𝓝[>] x) (𝓝 l)) ∧ -- right limit
      ∃ s : Set ι, s.Countable ∧ ∀ x ∉ s, ∀ ω, ContinuousWithinAt (Y · ω) (Set.Ioi x) x := by
  classical
  obtain ⟨D₀, hD₀c, hD₀d⟩ := TopologicalSpace.exists_countable_dense ι
  -- every dense set is cofinal
  have hcof : ∀ T : Set ι, Dense T → ∀ x : ι, ∃ d ∈ T, x < d := by
    intro T hTd x
    obtain ⟨y, hy⟩ := exists_gt x
    obtain ⟨z, hz⟩ := exists_between hy
    obtain ⟨d, hdT, hd⟩ := hTd.exists_mem_open isOpen_Ioo ⟨z, hz.1, hz.2⟩
    exact ⟨d, hdT, hd.1⟩
  -- the right-limit value along `T`, by choice
  set R : Set ι → ι → Ω → ℝ := fun T x ω ↦
    if h : ∃ l, Tendsto (fun s' ↦ X s' ω) (𝓝[>] x ⊓ 𝓟 T) (𝓝 l) then h.choose else 0 with hRdef
  have hRspec : ∀ T x ω, (∃ l, Tendsto (fun s' ↦ X s' ω) (𝓝[>] x ⊓ 𝓟 T) (𝓝 l)) →
      Tendsto (fun s' ↦ X s' ω) (𝓝[>] x ⊓ 𝓟 T) (𝓝 (R T x ω)) := by
    intro T x ω h
    rw [hRdef]
    simp only [dif_pos h]
    exact h.choose_spec
  have hXmeas : ∀ s', Measurable (X s') := fun s' ↦ (hX s').measurable.mono (𝓕.le _) le_rfl
  -- Stage 1: a.e. one-sided limits along D₀
  have hae₀ := ae_tendsto_along_countable hX hXint hXbdd hD₀c (hcof D₀ hD₀d)
  -- Stage 2: measurable versions of `R D₀ x`
  have hRm : ∀ x : ι, ∃ g : Ω → ℝ, Measurable g ∧ g =ᵐ[μ] R D₀ x := by
    intro x
    have hne : (𝓝[>] x ⊓ 𝓟 D₀).NeBot := nhdsGT_inf_principal_neBot hD₀d x
    obtain ⟨v, hv⟩ := exists_seq_tendsto (𝓝[>] x ⊓ 𝓟 D₀)
    have haet : ∀ᵐ ω ∂μ, Tendsto (fun j ↦ X (v j) ω) atTop (𝓝 (R D₀ x ω)) := by
      filter_upwards [hae₀] with ω hω
      exact (hRspec D₀ x ω (hω x).1).comp hv
    obtain ⟨g, hgmeas, hgae⟩ := measurable_limit_of_tendsto_metrizable_ae
      (f := fun j ↦ X (v j)) (L := atTop) (fun j ↦ (hXmeas (v j)).aemeasurable)
      (by filter_upwards [haet] with ω hω using ⟨_, hω⟩)
    refine ⟨g, hgmeas, ?_⟩
    filter_upwards [haet, hgae] with ω h1 h2
    exact tendsto_nhds_unique h2 h1
  choose Rm hRmMeas hRmae using hRm
  -- Stage 3: the exceptional set is countable
  set Sset : Set ι := {x | ¬ R D₀ x =ᵐ[μ] X x} with hSdef
  have hScount : Sset.Countable := by
    by_contra hSunc
    set Sn : ℕ → Set ι := fun n ↦
      {x | ENNReal.ofReal (1 / (n + 1)) < μ {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|}} with hSn
    have hSsub : Sset ⊆ ⋃ n, Sn n := by
      intro x hx
      have hxm : ¬ Rm x =ᵐ[μ] X x := fun hcon ↦ hx ((hRmae x).symm.trans hcon)
      have hpos : μ {ω | Rm x ω ≠ X x ω} ≠ 0 := by
        intro hcon
        exact hxm hcon
      have hBmono : Monotone (fun n : ℕ ↦ {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|}) := by
        intro n n' hnn' ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hω
        have : (n : ℝ) ≤ (n' : ℝ) := by exact_mod_cast hnn'
        linarith
      have hBunion : {ω | Rm x ω ≠ X x ω}
          = ⋃ n : ℕ, {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · intro hne
          have habs : 0 < |Rm x ω - X x ω| := abs_pos.2 (sub_ne_zero.2 hne)
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt habs
          exact ⟨n, by exact_mod_cast hn⟩
        · rintro ⟨n, hn⟩
          intro hcon
          rw [hcon, sub_self, abs_zero] at hn
          exact absurd hn (not_lt.2 (by positivity))
      have hexn : ∃ n₀ : ℕ, 0 < μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} := by
        by_contra hcon
        push Not at hcon
        simp only [nonpos_iff_eq_zero] at hcon
        refine hpos ?_
        rw [hBunion]
        refine le_antisymm ((measure_iUnion_le _).trans ?_) zero_le'
        calc ∑' n : ℕ, μ {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|}
            = ∑' _ : ℕ, (0 : ℝ≥0∞) := by
              congr 1 with n
              exact hcon n
          _ ≤ 0 := by simp
      obtain ⟨n₀, hn₀⟩ := hexn
      have hfin : μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} ≠ ⊤ := measure_ne_top μ _
      set ε : ℝ := (μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|}).toReal with hε
      have hεpos : 0 < ε := ENNReal.toReal_pos hn₀.ne' hfin
      obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hεpos
      set n := max n₀ n₁ with hn
      refine Set.mem_iUnion.2 ⟨n, ?_⟩
      rw [hSn]
      have hsub2 : {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|}
          ⊆ {ω | 1 / ((n : ℝ) + 1) < |Rm x ω - X x ω|} :=
        hBmono (le_max_left n₀ n₁)
      calc ENNReal.ofReal (1 / (n + 1))
          ≤ ENNReal.ofReal (1 / (n₁ + 1)) := by
            refine ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by positivity) ?_)
            have hcast : (n₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_right n₀ n₁
            linarith
        _ < ENNReal.ofReal ε := by
            refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.2 ?_
            exact_mod_cast hn₁
        _ = μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} := by
            rw [hε, ENNReal.ofReal_toReal hfin]
        _ ≤ μ {ω | 1 / ((n : ℝ) + 1) < |Rm x ω - X x ω|} := measure_mono hsub2
    have hexSn : ∃ n, ¬ (Sn n).Countable := by
      by_contra hcon
      push Not at hcon
      exact hSunc ((Set.countable_iUnion hcon).mono hSsub)
    obtain ⟨n, hSnunc⟩ := hexSn
    obtain ⟨p, u, hanti, huSn, hup, hutend⟩ :=
      exists_seq_strictAnti_tendsto_of_not_countable hSnunc
    set T' : Set ι := D₀ ∪ (Set.range u ∪ {p}) with hT'
    have hT'c : T'.Countable :=
      hD₀c.union ((Set.countable_range u).union (Set.countable_singleton p))
    have hT'd : Dense T' := hD₀d.mono Set.subset_union_left
    have hae' := ae_tendsto_along_countable hX hXint hXbdd hT'c (hcof T' hT'd)
    have haediff : ∀ᵐ ω ∂μ, Tendsto (fun k ↦ Rm (u k) ω - X (u k) ω) atTop (𝓝 0) := by
      have hcnt : ∀ᵐ ω ∂μ, ∀ k, Rm (u k) ω = R D₀ (u k) ω := ae_all_iff.2 fun k ↦ hRmae (u k)
      filter_upwards [hae₀, hae', hcnt] with ω hω₀ hω' hkeq
      have hL' := hRspec T' p ω (hω' p).1
      have hXu : Tendsto (fun k ↦ X (u k) ω) atTop (𝓝 (R T' p ω)) := by
        refine hL'.comp ?_
        rw [Filter.tendsto_inf]
        constructor
        · rw [tendsto_nhdsWithin_iff]
          exact ⟨hutend, Filter.Eventually.of_forall fun k ↦ hup k⟩
        · rw [Filter.tendsto_principal]
          exact Filter.Eventually.of_forall fun k ↦ Or.inr (Or.inl ⟨k, rfl⟩)
      have hRu : Tendsto (fun k ↦ R D₀ (u k) ω) atTop (𝓝 (R T' p ω)) :=
        tendsto_rightLim_comp_of_gt hD₀d Set.subset_union_left
          (fun y ↦ hRspec D₀ y ω (hω₀ y).1) hup hutend hL'
      have hsub := hRu.sub hXu
      rw [sub_self] at hsub
      refine Tendsto.congr (fun k ↦ ?_) hsub
      rw [hkeq k]
    have htim : TendstoInMeasure μ (fun k ω ↦ Rm (u k) ω - X (u k) ω) atTop
        (fun _ ↦ (0 : ℝ)) := by
      refine tendstoInMeasure_of_tendsto_ae
        (fun k ↦ ((hRmMeas (u k)).sub (hXmeas (u k))).aestronglyMeasurable) ?_
      filter_upwards [haediff] with ω hω using hω
    have hcontra := htim (ENNReal.ofReal (1 / (n + 1 : ℝ)))
      (by rw [ENNReal.ofReal_pos]; positivity)
    have hev : ∀ᶠ k in atTop,
        μ {ω | ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ edist (Rm (u k) ω - X (u k) ω) 0}
          < ENNReal.ofReal (1 / (n + 1)) := by
      refine hcontra.eventually_lt_const ?_
      rw [ENNReal.ofReal_pos]
      positivity
    obtain ⟨k, hk⟩ := hev.exists
    have hmem := huSn k
    rw [hSn, Set.mem_setOf_eq] at hmem
    have hsub3 : {ω | 1 / (n + 1 : ℝ) < |Rm (u k) ω - X (u k) ω|}
        ⊆ {ω | ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ edist (Rm (u k) ω - X (u k) ω) 0} := by
      intro ω hω
      rw [Set.mem_setOf_eq] at hω ⊢
      rw [edist_dist, dist_zero_right, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal hω.le
    exact absurd ((hmem.trans_le (measure_mono hsub3)).trans hk) (lt_irrefl _)
  -- Stage 4: the final process along T'' = D₀ ∪ Sset
  set T'' : Set ι := D₀ ∪ Sset with hT''
  have hT''c : T''.Countable := hD₀c.union hScount
  have hT''d : Dense T'' := hD₀d.mono Set.subset_union_left
  have hae'' := ae_tendsto_along_countable hX hXint hXbdd hT''c (hcof T'' hT''d)
  set Gset : Set Ω := {ω | ∀ x : ι,
    (∃ l, Tendsto (fun s' ↦ X s' ω) (𝓝[>] x ⊓ 𝓟 T'') (𝓝 l))
      ∧ (∃ l, Tendsto (fun s' ↦ X s' ω) (𝓝[<] x ⊓ 𝓟 T'') (𝓝 l))} with hGdef
  have hGae : ∀ᵐ ω ∂μ, ω ∈ Gset := hae''
  -- left-limit values along T''
  set Lc : ι → Ω → ℝ := fun x ω ↦
    if h : ∃ l, Tendsto (fun s' ↦ X s' ω) (𝓝[<] x ⊓ 𝓟 T'') (𝓝 l) then h.choose else 0 with hLdef
  have hLspec : ∀ x ω, (∃ l, Tendsto (fun s' ↦ X s' ω) (𝓝[<] x ⊓ 𝓟 T'') (𝓝 l)) →
      Tendsto (fun s' ↦ X s' ω) (𝓝[<] x ⊓ 𝓟 T'') (𝓝 (Lc x ω)) := by
    intro x ω h
    rw [hLdef]
    simp only [dif_pos h]
    exact h.choose_spec
  set Y : ι → Ω → ℝ := fun x ω ↦
    if ω ∈ Gset then (if x ∈ Sset then X x ω else R T'' x ω) else 0 with hYdef
  -- key: for good ω, `Y · ω` tends to `R T'' x ω` from the right at every `x`
  have hYright : ∀ ω ∈ Gset, ∀ x : ι,
      Tendsto (fun x' ↦ Y x' ω) (𝓝[>] x) (𝓝 (R T'' x ω)) := by
    intro ω hω x
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hA : ∀ᶠ s' in 𝓝[>] x, s' ∈ T'' → dist (X s' ω) (R T'' x ω) < ε :=
      Filter.eventually_inf_principal.1
        ((hRspec T'' x ω (hω x).1).eventually (Metric.ball_mem_nhds _ hε))
    have hB : ∀ᶠ s' in 𝓝[>] x, dist (R T'' s' ω) (R T'' x ω) < ε :=
      Metric.tendsto_nhds.1 (continuousWithinAt_rightLim hT''d
        (fun y ↦ hRspec T'' y ω (hω y).1) x) ε hε
    filter_upwards [hA, hB] with s' hs'A hs'B
    rw [hYdef]
    simp only [if_pos hω]
    by_cases hs'S : s' ∈ Sset
    · rw [if_pos hs'S]
      exact hs'A (Or.inr hs'S)
    · rw [if_neg hs'S]
      exact hs'B
  -- and to `Lc x ω` from the left
  have hYleft : ∀ ω ∈ Gset, ∀ x : ι,
      Tendsto (fun x' ↦ Y x' ω) (𝓝[<] x) (𝓝 (Lc x ω)) := by
    intro ω hω x
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hA : ∀ᶠ s' in 𝓝[<] x, s' ∈ T'' → dist (X s' ω) (Lc x ω) < ε :=
      Filter.eventually_inf_principal.1
        ((hLspec x ω (hω x).2).eventually (Metric.ball_mem_nhds _ hε))
    have hB : ∀ᶠ s' in 𝓝[<] x, dist (R T'' s' ω) (Lc x ω) < ε :=
      Metric.tendsto_nhds.1 (tendsto_rightLim_nhdsLT hT''d
        (fun y ↦ hRspec T'' y ω (hω y).1) (hLspec x ω (hω x).2)) ε hε
    filter_upwards [hA, hB] with s' hs'A hs'B
    rw [hYdef]
    simp only [if_pos hω]
    by_cases hs'S : s' ∈ Sset
    · rw [if_pos hs'S]
      exact hs'A (Or.inr hs'S)
    · rw [if_neg hs'S]
      exact hs'B
  refine ⟨Y, ?_, ?_, ?_, Sset, hScount, ?_⟩
  · -- modification
    intro t
    by_cases htS : t ∈ Sset
    · filter_upwards [hGae] with ω hω
      rw [hYdef]
      simp only [if_pos hω, if_pos htS]
    · have htR : R D₀ t =ᵐ[μ] X t := not_not.1 htS
      filter_upwards [hGae, hae₀, htR] with ω hω hω₀ hωR
      rw [hYdef]
      simp only [if_pos hω, if_neg htS]
      have hne : (𝓝[>] t ⊓ 𝓟 D₀).NeBot := nhdsGT_inf_principal_neBot hD₀d t
      have h1 : Tendsto (fun s' ↦ X s' ω) (𝓝[>] t ⊓ 𝓟 D₀) (𝓝 (R T'' t ω)) :=
        (hRspec T'' t ω (hω t).1).mono_left
          (inf_le_inf_left _ (Filter.principal_mono.2 Set.subset_union_left))
      have h2 := hRspec D₀ t ω (hω₀ t).1
      rw [tendsto_nhds_unique h1 h2]
      exact hωR
  · -- left limits everywhere, for every ω
    intro x ω
    by_cases hω : ω ∈ Gset
    · exact ⟨Lc x ω, hYleft ω hω x⟩
    · refine ⟨0, ?_⟩
      have hconst : (fun x' ↦ Y x' ω) = fun _ ↦ (0 : ℝ) := by
        funext x'
        rw [hYdef]
        simp only [if_neg hω]
      rw [hconst]
      exact tendsto_const_nhds
  · -- right limits everywhere, for every ω
    intro x ω
    by_cases hω : ω ∈ Gset
    · exact ⟨R T'' x ω, hYright ω hω x⟩
    · refine ⟨0, ?_⟩
      have hconst : (fun x' ↦ Y x' ω) = fun _ ↦ (0 : ℝ) := by
        funext x'
        rw [hYdef]
        simp only [if_neg hω]
      rw [hconst]
      exact tendsto_const_nhds
  · -- right continuity off `Sset`, for every ω
    intro x hxS ω
    by_cases hω : ω ∈ Gset
    · have hYx : Y x ω = R T'' x ω := by
        rw [hYdef]
        simp only [if_pos hω, if_neg hxS]
      rw [ContinuousWithinAt, hYx]
      exact hYright ω hω x
    · have hconst : (fun x' ↦ Y x' ω) = fun _ ↦ (0 : ℝ) := by
        funext x'
        rw [hYdef]
        simp only [if_neg hω]
      have hYx0 : Y x ω = 0 := by
        rw [hYdef]
        simp only [if_neg hω]
      rw [ContinuousWithinAt, hYx0, hconst]
      exact tendsto_const_nhds

/-- If `X` is an adapted integrable stochastic process which is right continuous in probability,
and is such that the set `{𝔼[(𝟙_A ● X) t] | A elementary predicatable}` is bounded for any t,
then it admits a cadlag modification. -/
lemma exists_modification_isCadlag [TopologicalSpace.SeparableSpace ι] [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ t, Integrable (X t) μ)
    (hXRC : ∀ t, TendstoInMeasure μ X (𝓝[>] t) (X t))
    (hXbdd : ∀ t : ι, ∃ C, ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C) :
    ∃ Y : ι → Ω → ℝ, (∀ t, Y t =ᵐ[μ] X t) ∧ (∀ t, Integrable (Y t) μ) ∧ ∀ ω, IsCadlag (Y · ω) := by
  classical
  obtain ⟨Y, hY, hYLL, hYRL, s, hs, hYCont⟩ := exists_modification_left_right_limit hX hXint hXbdd
  set S := ⋃ t ∈ s, {ω | ¬ ContinuousWithinAt (Y · ω) (Set.Ioi t) t} with hSdef
  have hS : ∀ᵐ ω ∂μ, ω ∉ S := by
    simp only [ae_iff, not_not, Set.setOf_mem_eq, hSdef, measure_biUnion_null_iff hs]
    refine fun t ht ↦ ae_iff.1 ?_
    choose l hl using hYRL t
    suffices l =ᵐ[μ] X t by
      have : ∀ᵐ ω ∂μ, Tendsto (fun x ↦ Y x ω) (𝓝[>] t) (𝓝 (X t ω)) := by
        filter_upwards [this] with ω hω using by simp [← hω, hl _]
      filter_upwards [this, hY t] with ω hω₁ hω₂ using by rwa [ContinuousWithinAt, hω₂]
    obtain ⟨_, hseq⟩ := exists_seq_tendsto (𝓝[>] t)
    exact tendstoInMeasure_ae_unique ((tendstoInMeasure_of_tendsto_ae
      (fun _ ↦ (hXint _).1.congr (hY _).symm)
      (ae_of_all _ <| fun ω ↦ (hl ω).comp hseq)).congr (fun _ ↦ hY _) (by rfl))
      ((hXRC t).comp hseq)
  set Z := fun t ω ↦ if ω ∈ S then 0 else Y t ω
  have hZ : ∀ t, Z t =ᵐ[μ] X t :=
    fun t ↦ EventuallyEq.trans
      (by filter_upwards [hS] with ω hω using by simp [Z, if_neg hω]) (hY t)
  refine ⟨Z, hZ, fun t ↦ (hXint t).congr <| (hZ _).symm,
    fun ω ↦ ⟨?_, fun x ↦ by_cases (p := ω ∈ S)
      (fun hω ↦ ⟨0, by simp [Z, if_pos hω, tendsto_const_nhds]⟩)
      (fun hω ↦ by simp [Z, if_neg hω, hYLL x ω])⟩⟩
  by_cases hω : ω ∈ S
  · simpa [Z, if_pos hω] using Function.isRightContinuous_const _
  · simp_rw [Z, if_neg hω]
    intro t
    simp only [hSdef, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, not_exists,
      not_and, not_not] at hω
    exact by_cases (p := t ∈ s) (fun ht ↦ hω _ ht) <| fun ht ↦ hYCont t ht ω

end ProbabilityTheory
