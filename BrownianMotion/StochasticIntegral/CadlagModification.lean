/-
Copyright (c) 2026 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import BrownianMotion.Auxiliary.LeftLimWithin
public import BrownianMotion.Auxiliary.Upcrossing
public import BrownianMotion.Continuity.LimitModification
public import BrownianMotion.StochasticIntegral.Cadlag
public import BrownianMotion.StochasticIntegral.SimpleProcess
public import BrownianMotion.StochasticIntegral.OptionalSampling
public import Mathlib.Probability.Notation

/-! # Cadlag modification stochastic processes -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

lemma TendstoInMeasure.add {ι E : Type*} [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {f g : ι → Ω → E} {l₁ l₂ : Ω → E} {u : Filter ι}
    (hf : TendstoInMeasure μ f u l₁) (hg : TendstoInMeasure μ g u l₂) :
    TendstoInMeasure μ (fun n ω ↦ f n ω + g n ω) u (fun ω ↦ l₁ ω + l₂ ω) := by
  unfold TendstoInMeasure at hf hg ⊢
  intro ε hε
  have hε' : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  specialize hf (ε / 2) hε'
  specialize hg (ε / 2) hε'
  simp only
  have h_subset1 i : {x | ε ≤ edist (f i x + g i x) (l₁ x + l₂ x)}
      ⊆ {x | ε ≤ edist (f i x) (l₁ x) + edist (g i x) (l₂ x)} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact hx.trans (edist_add_add_le _ _ _ _)
  have h_subset2 i : {x | ε ≤ edist (f i x + g i x) (l₁ x + l₂ x)}
      ⊆ {x | ε / 2 ≤ edist (f i x) (l₁ x)} ∪ {x | ε / 2 ≤ edist (g i x) (l₂ x)} := by
    refine (h_subset1 i).trans fun x ↦ ?_
    simp only [Set.mem_setOf_eq, Set.mem_union]
    contrapose!
    intro ⟨h1, h2⟩
    conv_rhs => rw [← ENNReal.add_halves ε]
    gcongr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun i ↦ μ {x | ε / 2 ≤ edist (f i x) (l₁ x)} + μ {x | ε / 2 ≤ edist (g i x) (l₂ x)})
    ?_ (by positivity) ?_
  · rw [← add_zero (0 : ℝ≥0∞)]
    exact hf.add hg
  · intro i
    simp only
    grw [measure_mono (h_subset2 i)]
    exact measure_union_le _ _

/-! ### Finite skeletons and the elementary integral bridge

Discrete data along a monotone sequence of times is converted into elementary predictable sets,
whose elementary stochastic integrals compute weighted sums of increments of `X`. -/

section Bridge

/-- The filtration on `ℕ` obtained by pulling back `𝓕` along a monotone sequence of times. -/
def pullbackFiltration (𝓕 : Filtration ι mΩ) {idx : ℕ → ι} (hidx : Monotone idx) :
    Filtration ℕ mΩ where
  seq k := 𝓕 (idx k)
  mono' _ _ h := 𝓕.mono (hidx h)
  le' _ := 𝓕.le _

@[simp] lemma pullbackFiltration_apply {idx : ℕ → ι} (hidx : Monotone idx) (k : ℕ) :
    pullbackFiltration 𝓕 hidx k = 𝓕 (idx k) := rfl

/-- The monotone enumeration of a finite set of times, extended by the constant `t` at indices
beyond `#F`. -/
@[grind]
noncomputable def finIdx (F : Finset ι) (t : ι) : ℕ → ι := fun k ↦
  if h : k < #F then (F.orderIsoOfFin rfl ⟨k, h⟩ : ι) else t

variable {F : Finset ι} {t : ι} {k l : ℕ}

lemma finIdx_mem (h : k < #F) : finIdx F t k ∈ F := by grind

lemma finIdx_eq_of_card_le (h : #F ≤ k) : finIdx F t k = t := by grind

lemma finIdx_le (hF : ∀ s ∈ F, s ≤ t) (k : ℕ) : finIdx F t k ≤ t := by grind

lemma finIdx_lt_of_lt (hkl : k < l) (hl : l < #F) : finIdx F t k < finIdx F t l := by
  rw [finIdx, finIdx, dif_pos (hkl.trans hl), dif_pos hl]
  exact mod_cast (F.orderIsoOfFin rfl).strictMono (mod_cast hkl)

lemma finIdx_lt_finIdx_iff (hk : k < #F) (hl : l < #F) :
    finIdx F t k < finIdx F t l ↔ k < l := by
  rw [finIdx, finIdx, dif_pos hk, dif_pos hl, Subtype.coe_lt_coe, OrderIso.lt_iff_lt, Fin.mk_lt_mk]

@[gcongr]
lemma finIdx_monotone (hF : ∀ s ∈ F, s ≤ t) : Monotone (finIdx F t) := by
  intro k l hkl
  rcases eq_or_lt_of_le hkl with rfl | hkl
  · exact le_rfl
  rcases lt_or_ge l #F with h | h
  · exact (finIdx_lt_of_lt hkl h).le
  · grind

lemma exists_finIdx_eq {s : ι} (hs : s ∈ F) : ∃ k, k < #F ∧ finIdx F t k = s := by
  obtain ⟨k, hk⟩ := (F.orderIsoOfFin rfl).surjective ⟨s, hs⟩
  exact ⟨k, k.2, by rw [finIdx, dif_pos k.2, Fin.eta, hk]⟩

lemma finIdx_zero_eq_bot [OrderBot ι] (hbot : ⊥ ∈ F) : finIdx F t 0 = ⊥ := by
  have hcard : 0 < #F := card_pos.2 ⟨⊥, hbot⟩
  obtain ⟨k, hk, hkeq⟩ := exists_finIdx_eq (t := t) hbot
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact hkeq
  · exact le_bot_iff.1 (hkeq ▸ (finIdx_lt_of_lt hkpos hk).le)

@[simps]
noncomputable
def elemPredSetOfSeq [OrderBot ι] {idx : ℕ → ι} (hidx : Monotone idx) {W : ℕ → Ω → ℝ} (n : ℕ)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) :
    ElementaryPredictableSet 𝓕 :=
  letI K : Finset ℕ := {k ∈ range n | idx k < idx (k + 1)}
  { setBot := ∅
    I := K.image fun k ↦ (idx k, idx (k + 1))
    set := fun p ↦ if h : ∃ k ∈ K, (idx k, idx (k + 1)) = p then W h.choose ⁻¹' {1} else ∅
    le_of_mem_I := by grind
    measurableSet_setBot := @MeasurableSet.empty _ (𝓕 ⊥)
    measurableSet_set p hp := by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hp
      have hex : ∃ k' ∈ K, (idx k', idx (k' + 1)) = (idx k, idx (k + 1)) := ⟨k, hk, rfl⟩
      simp only [dif_pos hex]
      obtain ⟨hcK, hceq⟩ := hex.choose_spec
      have h1 : idx hex.choose = idx k := (Prod.ext_iff.1 hceq).1
      have hKmem {k} (hk : k ∈ K) : k < n ∧ idx k < idx (k + 1) := by simpa [K] using hk
      have h2 : MeasurableSet[𝓕 (idx hex.choose)] (W hex.choose ⁻¹' {1}) :=
        hWmeas _ (hKmem hcK).1 (measurableSet_singleton 1)
      rwa [h1] at h2
    pairwiseDisjoint p hp q hq hpq := by
      simp only [coe_image, Set.mem_image, mem_coe] at hp hq
      obtain ⟨k, hk, rfl⟩ := hp
      obtain ⟨l, hl, rfl⟩ := hq
      have hkl : k ≠ l := fun h ↦ hpq (by rw [h])
      have hIoc : Disjoint (Set.Ioc (idx k) (idx (k + 1))) (Set.Ioc (idx l) (idx (l + 1))) := by
        rcases lt_or_gt_of_ne hkl with h | h
        · exact Set.Ioc_disjoint_Ioc_of_le (hidx (Nat.succ_le_of_lt h))
        · exact (Set.Ioc_disjoint_Ioc_of_le (hidx (Nat.succ_le_of_lt h))).symm
      exact Set.disjoint_left.2 fun x hx hx' ↦
        Set.disjoint_left.1 hIoc hx.1 hx'.1 }

lemma integral_elemPredSetOfSeq [OrderBot ι] {t : ι} (n : ℕ) {idx : ℕ → ι}
    (hidx : Monotone idx) (hidxt : ∀ k, idx k ≤ t) {W : ℕ → Ω → ℝ}
    (hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) (ω : Ω) :
    ((elemPredSetOfSeq hidx n hWmeas).indicator (1 : ℝ) ● X) t ω =
      ∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω) := by
  set K : Finset ℕ := {k ∈ range n | idx k < idx (k + 1)} with hK
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
  rw [ElementaryPredictableSet.integral_indicator_apply]
  simp only [elemPredSetOfSeq_I, elemPredSetOfSeq_set]
  simp only [mem_filter, mem_range, ContinuousLinearMap.mul_apply', one_mul]
  rw [sum_image fun k hk l hl h ↦ hinj hk hl h]
  simp only [mem_filter, mem_range, Prod.mk.injEq]
  refine (sum_congr rfl fun k hk ↦ ?_).trans (sum_subset (filter_subset _ _) fun k hk hkK ↦ ?_)
  · -- per-term equality on K
    have h : ∃ k_1 ∈ {k ∈ range n | idx k < idx (k + 1)},
      (idx k_1, idx (k_1 + 1)) = (idx k, idx (k + 1)) := ⟨k, hk, rfl⟩
    rw [dif_pos h]
    suffices (W h.choose ⁻¹' {1}).indicator
        (fun ω ↦ stoppedProcess X (fun x ↦ ↑t) (idx (k + 1)) ω -
          stoppedProcess X (fun x ↦ ↑t) (idx k) ω) ω =
        W k ω * (X (idx (k + 1)) ω - X (idx k) ω) by
      convert this
      · rfl
      · simp
      · simp
    have hchoose : h.choose = k := hinj h.choose_spec.1 hk h.choose_spec.2
    have hst : ∀ j, stoppedProcess X (fun _ ↦ (t : WithTop ι)) (idx j) ω = X (idx j) ω :=
      fun j ↦ stoppedProcess_eq_of_le (mod_cast hidxt j)
    simp only [hchoose]
    rcases hW01 k (hKmem hk).1 ω with h0 | h1
    · simp [h0]
    · simp [h1, hst]
  · -- terms outside K vanish
    have hno : ¬ idx k < idx (k + 1) := fun h ↦ hkK (by simp [hK, mem_range.1 hk, h])
    have heq : idx (k + 1) = idx k :=
      le_antisymm (not_lt.1 hno) (hidx k.le_succ)
    rw [heq, sub_self, mul_zero]

end Bridge

/-! ### Upcrossing and alternation bounds along finite time sets -/

section UpcrossingBound

variable {a b : ℝ} {t : ι} {F : Finset ι} {m : ℕ}

lemma integrable_integral_elementaryPredictableSet [OrderBot ι] [IsFiniteMeasure μ]
    (hXint : ∀ s, Integrable (X s) μ) (S : ElementaryPredictableSet 𝓕) (c : ℝ) :
    Integrable (((S.indicator c) ● X) t) μ := by
  refine integrable_finsetSum _ fun p hp ↦ Integrable.bdd_mul
    (((hXint _).sub (hXint _))) ?_ (c := ‖c‖) (ae_of_all _ fun ω ↦ ?_)
  · simp only [ElementaryPredictableSet.value_indicator]
    split_ifs with hp
    swap; · fun_prop
    refine StronglyMeasurable.aestronglyMeasurable ?_
    refine StronglyMeasurable.indicator (by fun_prop) ?_
    have hmeas : MeasurableSet[𝓕 p.1] (S.set p) := S.measurableSet_set p hp
    exact 𝓕.le _ _ hmeas
  · simp only [ElementaryPredictableSet.value_indicator, Real.norm_eq_abs]
    split_ifs with hp
    · by_cases hω : ω ∈ S.set p <;> simp [hω]
    · simp

noncomputable
def upcrossingWithinPredSet [OrderBot ι] (a b : ℝ) (F : Finset ι) (hF : ∀ s ∈ F, s ≤ t)
    (hX : StronglyAdapted 𝓕 X) :
    ElementaryPredictableSet 𝓕 :=
  letI f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω
  haveI hadapt : StronglyAdapted (pullbackFiltration 𝓕 (finIdx_monotone hF)) f :=
    fun j ↦ hX (finIdx F t j)
  elemPredSetOfSeq (W := upcrossingStrat a b f #F) (finIdx_monotone hF) #F
    fun k _ ↦ (hadapt.upcrossingStrat k).measurable

/-- Expectation bound on the number of upcrossings along a finite set of times `F ⊆ Iic t`,
from the boundedness of elementary stochastic integrals at time `t`. -/
lemma mul_integral_upcrossingsBefore_finIdx_le [OrderBot ι] [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator 1 ● X) t] ≤ C)
    (hab : a < b) (hF : ∀ s ∈ F, s ≤ t) :
    (b - a) * ∫ ω, (upcrossingsBefore a b (fun k ↦ X (finIdx F t k)) #F ω : ℝ) ∂μ
      ≤ C + ∫ ω, (a - X t ω)⁺ ∂μ := by
  set f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω with hf
  have hadapt : StronglyAdapted (pullbackFiltration 𝓕 (finIdx_monotone hF)) f :=
    fun j ↦ hX (finIdx F t j)
  let S := elemPredSetOfSeq (W := upcrossingStrat a b f #F) (finIdx_monotone hF) #F fun k hk ↦
    (hadapt.upcrossingStrat k).measurable
  have hS := integral_elemPredSetOfSeq (𝓕 := 𝓕) (X := X) #F (finIdx_monotone hF) (finIdx_le hF)
    (W := upcrossingStrat a b f #F) (fun k _ ω ↦ upcrossingStrat_eq_zero_or_one a b f #F k ω)
    (fun k _ ↦ (hadapt.upcrossingStrat k).measurable)
  have hpath ω : (b - a) * (upcrossingsBefore a b f #F ω : ℝ)
      ≤ (S.indicator (1 : ℝ) ● X) t ω + (a - X t ω)⁺ := by
    have h1 := mul_upcrossingsBefore_le_sum_add_posPart (f := f) (N := #F) (ω := ω) hab
    have hfn : f #F ω = X t ω := by
      change X (finIdx F t #F) ω = X t ω
      rw [finIdx_eq_of_card_le le_rfl]
    rw [hfn] at h1
    have h2 : (S.indicator (1 : ℝ) ● X) t ω
        = ∑ k ∈ range #F, upcrossingStrat a b f #F k ω * (f (k + 1) - f k) ω := hS ω
    rwa [← h2] at h1
  -- integrability of the elementary integral at `t`
  have hWmeas : ∀ k, Measurable (upcrossingStrat a b f #F k) := fun k ↦
    ((hadapt.upcrossingStrat k).measurable).mono (𝓕.le _) le_rfl
  have hintS : Integrable ((S.indicator (1 : ℝ) ● X) t) μ :=
    integrable_integral_elementaryPredictableSet hXint S 1
  have hintmax : Integrable (fun ω ↦ (a - X t ω)⁺) μ :=
    (((integrable_const a).sub (hXint t))).pos_part
  have hintcount : Integrable (fun ω ↦ (upcrossingsBefore a b f #F ω : ℝ)) μ :=
    hadapt.integrable_upcrossingsBefore hab
  calc (b - a) * ∫ ω, (upcrossingsBefore a b f #F ω : ℝ) ∂μ
      = ∫ ω, (b - a) * (upcrossingsBefore a b f #F ω : ℝ) ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ ω, ((S.indicator (1 : ℝ) ● X) t ω + (a - X t ω)⁺) ∂μ :=
        integral_mono (hintcount.const_mul _) (hintS.add hintmax) hpath
    _ = μ[(S.indicator (1 : ℝ) ● X) t] + ∫ ω, (a - X t ω)⁺ ∂μ :=
        integral_add hintS hintmax
    _ ≤ C + ∫ ω, (a - X t ω)⁺ ∂μ := by gcongr; exact hC S

variable (X) in
/-- The event that `X` makes `m` alternations from at most `a` to at least `b` at
increasing times inside the finite time set `F`. The levels are non-strict (`X ≤ a`, `b ≤ X`) to
match the `Set.Iic a` / `Set.Ici b` hitting conditions of `MeasureTheory.upcrossingsBefore`; with
this convention `altSet` coincides with the event of at least `m` upcrossings (see
`altSet_eq_upcrossingsBefore`). -/
def altSet (F : Finset ι) (a b : ℝ) (m : ℕ) : Set Ω :=
  {ω | ∃ c : ℕ → ι, (∀ i, i + 1 < 2 * m → c i < c (i + 1)) ∧ (∀ i < 2 * m, c i ∈ F)
    ∧ (∀ i < m, X (c (2 * i)) ω ≤ a) ∧ (∀ i < m, b ≤ X (c (2 * i + 1)) ω)}

lemma altSet_mono {F G : Finset ι} (h : F ⊆ G) : altSet X F a b m ⊆ altSet X G a b m :=
  fun _ ⟨c, hc1, hc2, hca, hcb⟩ ↦ ⟨c, hc1, fun i hi ↦ h (hc2 i hi), hca, hcb⟩

lemma altSet_mono' {a' b' : ℝ} (hab : a ≤ a') (hba : b' ≤ b) :
    altSet X F a b m ⊆ altSet X F a' b' m :=
  fun _ ⟨c, hc1, hc2, hca, hcb⟩ ↦ ⟨c, hc1, hc2, by grind⟩

/-- On the event `altSet X F a b m`, the process `X` has at least `m` upcrossings along the
enumeration of `F`. The upper alternation level of `altSet` is non-strict (`b ≤ X`), which matches
the `Set.Ici b` upper-crossing condition used by `upcrossingsBefore`. -/
lemma altSet_subset_upcrossingsBefore (hab : a < b) :
    altSet X F a b m
      ⊆ {ω | m ≤ upcrossingsBefore a b (fun k ↦ X (finIdx F t k)) #F ω} := by
  rintro ω ⟨c, hc1, hc2, hca, hcb⟩
  have hex : ∀ i, i < 2 * m → ∃ k, k < #F ∧ finIdx F t k = c i :=
    fun i hi ↦ exists_finIdx_eq (hc2 i hi)
  let c' : ℕ → ℕ := fun i ↦ if hi : i < 2 * m then (hex i hi).choose else 0
  have hc'spec : ∀ i (hi : i < 2 * m), c' i < #F ∧ finIdx F t (c' i) = c i := by grind
  refine le_upcrossingsBefore_of_alternating hab (c := c') ?_ (by grind) ?_ ?_
  · intro i hi
    obtain ⟨hlt1, heq1⟩ := hc'spec i (by lia)
    obtain ⟨hlt2, heq2⟩ := hc'spec (i + 1) hi
    rw [← finIdx_lt_finIdx_iff (t := t) hlt1 hlt2, heq1, heq2]
    exact hc1 i hi
  · intro i hi
    obtain ⟨_, heq⟩ := hc'spec (2 * i) (by lia)
    simp only [heq]
    exact hca i hi
  · intro i hi
    obtain ⟨_, heq⟩ := hc'spec (2 * i + 1) (by lia)
    simp only [heq]
    exact hcb i hi

/-- Converse of `altSet_subset_upcrossingsBefore`: at least `m` upcrossings of the monotone
enumeration of `F` yield `m` alternations of `X` at times in `F`. The alternating times are the
lower/upper crossing times, transported back to `F` through `finIdx`. -/
lemma upcrossingsBefore_subset_altSet (hab : a < b) :
    {ω | m ≤ upcrossingsBefore a b (fun k ↦ X (finIdx F t k)) #F ω} ⊆ altSet X F a b m := by
  intro ω hω
  obtain ⟨c, hmono, hcN, ha, hb⟩ := exists_alternating_of_le_upcrossingsBefore hab hω
  exact ⟨fun i ↦ finIdx F t (c i), fun i hi ↦ finIdx_lt_of_lt (hmono i hi) (hcN (i + 1) hi),
    fun i hi ↦ finIdx_mem (hcN i hi), fun i hi ↦ ha i hi, fun i hi ↦ hb i hi⟩

/-- **`altSet X F a b m` is exactly the event of at least `m` upcrossings** of `[a, b]` by the
monotone enumeration `finIdx F t` of `F`. This is the reason for the non-strict inequalities in the
definition of `altSet`. -/
lemma altSet_eq_upcrossingsBefore (hab : a < b) :
    altSet X F a b m = {ω | m ≤ upcrossingsBefore a b (fun k ↦ X (finIdx F t k)) #F ω} :=
  Set.Subset.antisymm (altSet_subset_upcrossingsBefore hab) (upcrossingsBefore_subset_altSet hab)

/-- Quantitative alternation bound: the probability of `m` alternations along any finite
`F ⊆ Iic t` is at most `K / m` with `K` independent of `F` and `m`. -/
lemma measureReal_altSet_le [OrderBot ι] [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hab : a < b) (hm : 0 < m) (hF : ∀ s ∈ F, s ≤ t) :
    μ.real (altSet X F a b m) ≤ (C + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a) / m := by
  let f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω
  have hadapt : StronglyAdapted (pullbackFiltration 𝓕 (finIdx_monotone hF)) f :=
    fun j ↦ hX (finIdx F t j)
  rw [altSet_eq_upcrossingsBefore (t := t) hab, div_div, le_div_iff₀ (by positivity)]
  calc μ.real {ω | m ≤ upcrossingsBefore a b f #F ω} * ((b - a) * m)
  _ = μ.real {ω | (m : ℝ) ≤ (upcrossingsBefore a b f #F ω : ℝ)} * ((b - a) * m) := by norm_cast
  _ = (b - a) * ((m : ℝ) * μ.real {ω | (m : ℝ) ≤ (upcrossingsBefore a b f #F ω : ℝ)}) := by ring
  _ ≤ (b - a) * ∫ ω, (upcrossingsBefore a b f #F ω : ℝ) ∂μ := by
    gcongr
    exact mul_meas_ge_le_integral_of_nonneg
      (ae_of_all _ fun ω ↦ by positivity) (hadapt.integrable_upcrossingsBefore hab) m
  _ ≤ C + ∫ ω, (a - X t ω)⁺ ∂μ :=
    mul_integral_upcrossingsBefore_finIdx_le (μ := μ) hX hXint hC hab hF

/-- The set of outcomes where there are infinitely many alternations of `X` from below `a`
to above `b` at times in a set `T` below `t`. -/
def infiniteAlt (T : Set ι) (t : ι) (X : ι → Ω → ℝ) (a b : ℝ) : Set Ω :=
  ⋂ m : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b m

lemma infiniteAlt_mono' {T : Set ι} {a' b' : ℝ} (h : a ≤ a') (h' : b' ≤ b) :
    infiniteAlt T t X a b ⊆ infiniteAlt T t X a' b' := by
  unfold infiniteAlt
  gcongr
  exact altSet_mono' h h'

lemma infiniteAlt_mono'' {T : Set ι} {s t : ι} (h : s ≤ t) :
    infiniteAlt T s X a b ⊆ infiniteAlt T t X a b := by
  unfold infiniteAlt
  gcongr with F
  refine Set.iUnion_mono' ?_
  intro hF
  simp only [Set.subset_inter_iff, Set.mem_setOf_eq] at hF
  simp only [subset_refl, Set.subset_inter_iff, Set.mem_setOf_eq, exists_prop, and_true]
  refine ⟨hF.1, hF.2.trans ?_⟩
  grind

end UpcrossingBound

/-! ### Maximal inequality along finite time sets -/

section Maximal

variable {t : ι} {F : Finset ι} {lam : ℝ}

-- todo name
lemma sum_indicator_mul_sub_eq_stopped'' (f : ℕ → Ω → ℝ) (s : Set ℝ) (n : ℕ) (ω : Ω) :
    ∑ k ∈ range n, {ω' | ∀ j ≤ k, f j ω' ∉ s}.indicator 1 ω * (f (k + 1) ω - f k ω)
      = f (hittingBtwn f s 0 n ω) ω - f 0 ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    by_cases hhit : ∃ j ∈ Set.Icc 0 n, f j ω ∈ s
    · -- already hit by time `n`: the hitting time stabilizes and the last weight vanishes
      have hstab : hittingBtwn f s 0 n ω = hittingBtwn f s 0 (n + 1) ω :=
        hittingBtwn_eq_hittingBtwn_of_exists (Nat.le_succ n) hhit
      obtain ⟨j, hj, hjs⟩ := hhit
      rw [Set.indicator_of_notMem]
      · grind
      · simp only [Set.mem_setOf_eq, not_forall, not_not]
        exact ⟨j, hj.2, hjs⟩
    · rw [hittingBtwn, if_neg hhit]
      have h2 : hittingBtwn f s 0 (n + 1) ω = n + 1 := by
        refine le_antisymm (hittingBtwn_le ω) (not_lt.1 fun hlt ↦ ?_)
        obtain ⟨j, hj, hjs⟩ := (hittingBtwn_lt_iff (n + 1) le_rfl).1 hlt
        grind
      rw [h2, Set.indicator_of_mem (by simpa using hhit)]
      simp

/-- Discrete stopped telescoping identity: weighting the increments of `f` by the indicator of
"not yet above `lam`" telescopes to the value at the first time `f` exceeds `lam`. -/
lemma sum_indicator_mul_sub_eq_stopped (f : ℕ → Ω → ℝ) (lam : ℝ) (n : ℕ) (ω : Ω) :
    ∑ k ∈ range n, {ω' | ∀ j ≤ k, f j ω' ≤ lam}.indicator 1 ω * (f (k + 1) ω - f k ω)
      = f (hittingBtwn f (Set.Ioi lam) 0 n ω) ω - f 0 ω := by
  convert sum_indicator_mul_sub_eq_stopped'' f (Set.Ioi lam) n ω
  simp

omit [LinearOrder ι] in
/-- Integrability of bounded-weight increment sums. -/
lemma integrable_sum_weight_increments {g : ι → Ω → ℝ} (hgint : ∀ s, Integrable (g s) μ)
    {n : ℕ} {idx : ℕ → ι} {W : ℕ → Ω → ℝ}
    (hWmeas : ∀ k, k < n → AEStronglyMeasurable (W k) μ)
    (hWb : ∀ k, k < n → ∀ ω, ‖W k ω‖ ≤ 1) :
    Integrable (fun ω ↦ ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) μ :=
  integrable_finsetSum _ fun k hk ↦ Integrable.bdd_mul ((hgint _).sub (hgint _))
    (hWmeas k (mem_range.1 hk)) (ae_of_all _ (hWb k (mem_range.1 hk)))

/-- Two-sided expectation bound for adapted `{0,1}`-weighted increment sums of `X`, from the
boundedness of elementary stochastic integrals at time `t`. The lower bound uses the
complementary weights `1 - W`. -/
lemma integral_sum_weight_increments_mem_Icc [OrderBot ι] [IsFiniteMeasure μ]
    (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    {n : ℕ} {idx : ℕ → ι} (hidx : Monotone idx) (hidxt : ∀ k, idx k ≤ t)
    {W : ℕ → Ω → ℝ} (hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) :
    ∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
        ∈ Set.Icc (-(C + ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)) C := by
  have hb01 : ∀ (V : ℕ → Ω → ℝ), (∀ k, k < n → ∀ ω, V k ω = 0 ∨ V k ω = 1) →
      ∀ k, k < n → ∀ ω, ‖V k ω‖ ≤ 1 := by
    intro V hV k hk ω
    rcases hV k hk ω with h | h <;> simp [h]
  have hupper : ∀ (V : ℕ → Ω → ℝ), (∀ k, k < n → ∀ ω, V k ω = 0 ∨ V k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (V k)) →
      ∫ ω, (∑ k ∈ range n, V k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ ≤ C := by
    intro V hV01 hVmeas
    let S := elemPredSetOfSeq hidx n hVmeas
    have hS := integral_elemPredSetOfSeq (𝓕 := 𝓕) (X := X) n hidx hidxt (W := V) hV01 hVmeas
    rw [← funext_iff] at hS
    rw [← hS]
    exact hC S
  constructor
  · -- lower bound via the complementary weights
    have hW1 : ∀ k, k < n → ∀ ω, (1 - W k ω) = 0 ∨ (1 - W k ω) = 1 := by grind
    have hW1meas : ∀ k, k < n → Measurable[𝓕 (idx k)] (fun ω ↦ 1 - W k ω) :=
      fun k hk ↦ (measurable_const.sub (hWmeas k hk))
    have hco := hupper (fun k ω ↦ 1 - W k ω) hW1 hW1meas
    have hsplit : ∀ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω))
        = (X (idx n) ω - X (idx 0) ω)
          - ∑ k ∈ range n, (1 - W k ω) * (X (idx (k + 1)) ω - X (idx k) ω) := by
      intro ω
      have htel : ∑ k ∈ range n, (X (idx (k + 1)) ω - X (idx k) ω)
          = X (idx n) ω - X (idx 0) ω := sum_range_sub (fun k ↦ X (idx k) ω) n
      rw [← htel, ← sum_sub_distrib]
      grind
    have hint1 : Integrable
        (fun ω ↦ ∑ k ∈ range n, (1 - W k ω) * (X (idx (k + 1)) ω - X (idx k) ω)) μ :=
      integrable_sum_weight_increments hXint
        (fun k hk ↦ ((hW1meas k hk).mono (𝓕.le _) le_rfl).aestronglyMeasurable)
        (hb01 _ hW1)
    have hintsub : Integrable (fun ω ↦ X (idx n) ω - X (idx 0) ω) μ :=
      (hXint _).sub (hXint _)
    have hI : ∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
        = (∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ)
          - ∫ ω, (∑ k ∈ range n, (1 - W k ω) * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ := by
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
      ∫ ω, (∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) ∂μ ≤ K) :
    lam * μ.real {ω | ∃ k ≤ n, lam < g (idx k) ω}
      ≤ K + ∫ ω, |g (idx 0) ω| ∂μ + ∫ ω, |g (idx n) ω| ∂μ := by
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
      have : {ω' | ∀ j ≤ k, f j ω' ≤ lam} = ⋂ j ∈ Iic k, f j ⁻¹' Set.Iic lam := by
        ext ω'
        simp [Set.mem_iInter]
      rw [this]
      refine MeasurableSet.biInter (Iic k).countable_toSet fun j hj ↦ ?_
      have hj' : j ≤ k := mem_Iic.1 hj
      exact (𝓕.mono (hidx hj')) _ ((hg (idx j)).measurable measurableSet_Iic)
    exact (measurable_const.indicator hset)
  have hWb : ∀ k, k < n → ∀ ω, ‖W k ω‖ ≤ 1 := by
    intro k hk ω
    rcases hW01 k hk ω with h | h <;> simp [h]
  -- the stopped value
  set tau : Ω → ℕ := fun ω ↦ hittingBtwn f (Set.Ioi lam) 0 n ω with htau
  set ftau : Ω → ℝ := fun ω ↦ f (tau ω) ω with hftau
  have htel : ∀ ω, ftau ω = f 0 ω
      + ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω) := by
    intro ω
    have := sum_indicator_mul_sub_eq_stopped f lam n ω
    rw [hftau, htau]
    have hterm k : W k ω * (g (idx (k + 1)) ω - g (idx k) ω)
        = ({ω' | ∀ j ≤ k, f j ω' ≤ lam}.indicator 1 ω : ℝ) * (f (k + 1) ω - f k ω) := rfl
    simp_rw [hterm]
    rw [this]
    ring
  have hint_sum : Integrable
      (fun ω ↦ ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) μ :=
    integrable_sum_weight_increments hgint
      (fun k hk ↦ ((hWmeas k hk).mono (𝓕.le _) le_rfl).aestronglyMeasurable) hWb
  have hint_ftau : Integrable ftau μ := by
    have : ftau = fun ω ↦ f 0 ω
        + ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω) := funext htel
    rw [this]
    exact (hgint _).add hint_sum
  -- the event
  set H : Set Ω := {ω | ∃ k ≤ n, lam < g (idx k) ω} with hH
  have hHmeas : MeasurableSet H := by
    have : H = ⋃ k ∈ Iic n, (g (idx k)) ⁻¹' Set.Ioi lam := by ext; simp [hH]
    rw [this]
    exact MeasurableSet.biUnion (Iic n).countable_toSet fun k _ ↦
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
        + ∫ ω, (∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) ∂μ := by
      rw [← integral_add (hgint _) hint_sum]
      exact integral_congr_ae (ae_of_all _ htel)
    rw [this]
    have h0 : ∫ ω, f 0 ω ∂μ ≤ ∫ ω, |g (idx 0) ω| ∂μ :=
      integral_mono (hgint _) (hgint _).abs fun ω ↦ le_abs_self _
    have hsum := hK W hW01 hWmeas
    linarith
  linarith [hsplit, hlower, hcompl, htotal]

/-- **Maximal inequality**: the probability that `|X|` exceeds `lam` somewhere on a finite set
`F ⊆ Iic t` is at most `K / lam`, with `K` independent of `F`. -/
lemma measureReal_exists_abs_lt_le [OrderBot ι] [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hlam : 0 < lam) (hF : ∀ s ∈ F, s ≤ t) :
    μ.real {ω | ∃ s ∈ F, lam < |X s ω|}
      ≤ 2 * (C + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ + ∫ ω, |X t ω| ∂μ) / lam := by
  set G : Finset ι := insert ⊥ F with hG
  have hGF : F ⊆ G := subset_insert _ _
  have hGle : ∀ s ∈ G, s ≤ t := by simp [G]; grind
  set n : ℕ := G.card with hn
  set idx : ℕ → ι := finIdx G t with hidx
  have hmono : Monotone idx := finIdx_monotone hGle
  have hidx0 : idx 0 = ⊥ := finIdx_zero_eq_bot (mem_insert_self _ _)
  have hidxn : idx n = t := finIdx_eq_of_card_le hn.ge
  -- two-sided expectation bound for adapted 0/1 weights along `idx`
  have hbdd : ∀ W : ℕ → Ω → ℝ, (∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) →
      ∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
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
      have h2 : ∫ ω, (∑ k ∈ range n, W k ω * (-X (idx (k + 1)) ω - -X (idx k) ω)) ∂μ
          = -∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ := by
        rw [← integral_neg]
        congr 1 with ω
        rw [← sum_neg_distrib]
        grind
      rw [h2]
      linarith)
  -- combine the two events
  have hsub : {ω | ∃ s ∈ F, lam < |X s ω|}
      ⊆ {ω | ∃ k ≤ n, lam < X (idx k) ω} ∪ {ω | ∃ k ≤ n, lam < -X (idx k) ω} := by
    rintro ω ⟨s, hs, habs⟩
    obtain ⟨k, hk, hkeq⟩ := exists_finIdx_eq (t := t) (hGF hs)
    grind
  have habs u : ∫ ω, |(fun s ω ↦ -X s ω) u ω| ∂μ = ∫ ω, |X u ω| ∂μ := by simp
  rw [hidx0, hidxn] at hpos hneg
  rw [habs ⊥, habs t] at hneg
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

variable {T : Set ι} {t : ι} {a b lam : ℝ} {m : ℕ}

omit [LinearOrder ι] in
lemma countable_setOf_finset_coe_subset (hT : T.Countable) :
    {F : Finset ι | ↑F ⊆ T}.Countable := by
  have h1 : {F : Finset ι | ↑F ⊆ T}
      ⊆ (fun F : Finset ι ↦ (F : Set ι)) ⁻¹' {u : Set ι | u.Finite ∧ u ⊆ T} :=
    fun F hF ↦ ⟨F.finite_toSet, hF⟩
  exact ((Set.countable_setOf_finite_subset hT).preimage coe_injective).mono h1

variable [OrderBot ι]

/-- The union of the alternation events over all finite subsets of a countable set of times
below `t` has measure at most `K / ((b - a) * m)`. -/
lemma measure_biUnion_altSet_le [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hab : a < b) (hm : 0 < m) (hT : T.Countable) :
    μ (⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b m)
      ≤ ENNReal.ofReal ((C + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a) / m) := by
  have hcnt : {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}.Countable :=
    countable_setOf_finset_coe_subset (hT.mono Set.inter_subset_left)
  have hdir : DirectedOn (Function.onFun (· ⊆ ·) fun F : Finset ι ↦ altSet X F a b m)
      {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t} :=
    fun F₁ h₁ F₂ h₂ ↦ ⟨F₁ ∪ F₂, by grind, altSet_mono subset_union_left,
      altSet_mono subset_union_right⟩
  rw [measure_biUnion_eq_iSup hcnt hdir]
  refine iSup₂_le fun F hF ↦ ?_
  have hF' : ∀ s ∈ F, s ≤ t := fun s hs ↦ (hF hs).2
  calc μ (altSet X F a b m) = ENNReal.ofReal (μ.real (altSet X F a b m)) :=
        (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
        (measureReal_altSet_le (μ := μ) hX hXint hC hab hm hF')

/-- Almost surely, there is no infinite family of alternations of `X` from below `a` to above `b`
at times in a countable set `T` below `t`. -/
lemma measure_infiniteAlt [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hab : a < b) (hT : T.Countable) :
    μ (infiniteAlt T t X a b) = 0 := by
  suffices μ (⋂ m : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b (m + 1)) = 0 by
    refine measure_mono_null ?_ this
    intro ω
    simp only [infiniteAlt, Set.subset_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion,
      exists_prop]
    exact fun h i ↦ h (i + 1)
  refine le_antisymm ?_ zero_le
  have hbound : ∀ m : ℕ,
      μ (⋂ m : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b (m + 1))
        ≤ ENNReal.ofReal ((C + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a) / (m + 1)) := by
    intro m
    refine (measure_mono (Set.iInter_subset _ m)).trans ?_
    have := measure_biUnion_altSet_le (μ := μ) hX hXint hC hab (Nat.succ_pos m) hT
    simpa using this
  have hlim : Tendsto (fun m : ℕ ↦
      ENNReal.ofReal ((C + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a) / (m + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    have h1 : Tendsto (fun n : ℕ ↦ ((C + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a)) / n)
        atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    have h2 := h1.comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun m ↦ ?_
    simp [Function.comp, div_div]
  exact ge_of_tendsto' hlim hbound

lemma measure_all_infiniteAlt'' [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) (t : ι) {C : ℝ}
    (hXbdd : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (T : Set ι) (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ q r, q < r → ω ∉ infiniteAlt T t X q r := by
  suffices ∀ᵐ ω ∂μ, ∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T t X q r by
    filter_upwards [this] with ω hω q r hqr
    obtain ⟨q', r', hqq', hq'r', hr'r⟩ : ∃ q' r' : ℚ, q < q' ∧ q' < r' ∧ r' < r := by
      obtain ⟨r', hqr', hr'r⟩ := exists_rat_btwn hqr
      obtain ⟨q', hqq', hq'r'⟩ := exists_rat_btwn hqr'
      exact ⟨q', r', hqq', mod_cast hq'r', hr'r⟩
    exact fun h_mem ↦ hω q' r' hq'r' (infiniteAlt_mono' hqq'.le hr'r.le h_mem)
  simp_rw [ae_all_iff]
  intro q r hqr
  exact compl_mem_ae_iff.2 (measure_infiniteAlt hX hXint hXbdd (mod_cast hqr) hT)

-- todo: to be superceded by a more general `IsQuasimartingale`
structure IsRealQuasimartingale (𝓕 : Filtration ι mΩ) (X : ι → Ω → ℝ) (μ : Measure Ω) : Prop where
  stronglyAdapted : StronglyAdapted 𝓕 X
  integrable : ∀ t, Integrable (X t) μ
  boundedVariation :
    ∀ t, ∃ C, ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C

lemma IsRealQuasimartingale.measurable (hX : IsRealQuasimartingale 𝓕 X μ) (t : ι) :
    Measurable[𝓕 t] (X t) := (hX.stronglyAdapted t).measurable

lemma IsRealQuasimartingale.measurable' (hX : IsRealQuasimartingale 𝓕 X μ) (t : ι) :
    Measurable (X t) := (hX.measurable t).mono (𝓕.le t) le_rfl

lemma measure_all_infiniteAlt [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T T' : Set ι} (hT : T.Countable) (hT' : T'.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T', ∀ q r, q < r → ω ∉ infiniteAlt T d X q r := by
  rw [ae_ball_iff hT']
  exact fun t _ ↦ measure_all_infiniteAlt'' hX.stronglyAdapted hX.integrable t
    (hX.boundedVariation t).choose_spec T hT

lemma measure_all_infiniteAlt' [IsFiniteMeasure μ] [(atTop : Filter ι).IsCountablyGenerated]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    (T : Set ι) (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ d, ∀ q r, q < r → ω ∉ infiniteAlt T d X q r := by
  obtain ⟨u, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  suffices ∀ᵐ ω ∂μ, ∀ n, ∀ q r, q < r → ω ∉ infiniteAlt T (u n) X q r by
    filter_upwards [this] with ω hω d q r hqr
    obtain ⟨n, hn⟩ : ∃ n, d ≤ u n := (hu.2.eventually_ge_atTop d).exists
    specialize hω n q r hqr
    exact fun h_mem ↦ hω (infiniteAlt_mono'' hn h_mem)
  rw [ae_all_iff]
  exact fun n ↦ measure_all_infiniteAlt'' hX.stronglyAdapted hX.integrable (u n)
    (hX.boundedVariation (u n)).choose_spec T hT

/-- The union of the maximal events over all finite subsets of a countable set of times below
`t` has measure at most `K / lam`. -/
lemma measure_biUnion_exists_abs_le [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator 1 ● X) t] ≤ C)
    (hlam : 0 < lam) (hT : T.Countable) :
    μ (⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, {ω | ∃ s ∈ F, lam < |X s ω|})
      ≤ ENNReal.ofReal (2 * (C + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ
          + ∫ ω, |X t ω| ∂μ) / lam) := by
  have hcnt : {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}.Countable :=
    countable_setOf_finset_coe_subset (hT.mono Set.inter_subset_left)
  have hdir : DirectedOn (Function.onFun (· ⊆ ·) fun F : Finset ι ↦ {ω | ∃ s ∈ F, lam < |X s ω|})
      {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t} :=
    fun F₁ h₁ F₂ h₂ ↦ ⟨F₁ ∪ F₂, by grind, by grind, by grind⟩
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
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator 1 ● X) t] ≤ C)
    (hT : T.Countable) :
    μ (⋂ M : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t},
      {ω | ∃ s ∈ F, (M + 1 : ℝ) < |X s ω|}) = 0 := by
  refine le_antisymm ?_ zero_le
  have hbound (M : ℕ) :
      μ (⋂ M : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t},
          {ω | ∃ s ∈ F, (M + 1 : ℝ) < |X s ω|})
        ≤ ENNReal.ofReal (2 * (C + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ
            + ∫ ω, |X t ω| ∂μ) / (M + 1)) := by
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
    simp
  exact ge_of_tendsto' hlim hbound

lemma ae_exists_bound'' [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    (hT : T.Countable) (d : ι) :
    ∀ᵐ ω ∂μ, ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
  choose C hC using hX.boundedVariation
  have h2 : ∀ᵐ ω ∂μ, ω ∉ ⋂ M : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic d},
      {ω | ∃ s ∈ F, (M + 1 : ℝ) < |X s ω|} :=
    compl_mem_ae_iff.2
      (measure_iInter_biUnion_exists_abs hX.stronglyAdapted hX.integrable (hC d) hT)
  filter_upwards [h2] with ω hω2
  simp only [Set.subset_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop,
    not_forall, not_exists, not_and, not_lt, and_imp] at hω2
  obtain ⟨M, hM⟩ := hω2
  refine ⟨M, fun s' hs' ↦ ?_⟩
  specialize hM {s'} (by grind) (by grind)
  grind

lemma ae_exists_bound [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    (hT : T.Countable) {T' : Set ι} (hT' : T'.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T', ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
  rw [ae_ball_iff hT']
  intro d hdT
  choose C hC using hX.boundedVariation
  have h2 : ∀ᵐ ω ∂μ, ω ∉ ⋂ M : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic d},
      {ω | ∃ s ∈ F, (M + 1 : ℝ) < |X s ω|} :=
    compl_mem_ae_iff.2
      (measure_iInter_biUnion_exists_abs hX.stronglyAdapted hX.integrable (hC d) hT)
  filter_upwards [h2] with ω hω2
  simp only [Set.subset_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop,
    not_forall, not_exists, not_and, not_lt, and_imp] at hω2
  obtain ⟨M, hM⟩ := hω2
  refine ⟨M, fun s' hs' ↦ ?_⟩
  specialize hM {s'} (by grind) (by grind)
  grind

lemma ae_exists_bound' [IsFiniteMeasure μ] [(atTop : Filter ι).IsCountablyGenerated]
    (hX : IsRealQuasimartingale 𝓕 X μ) (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ d, ∃ M : ℕ, ∀ s ∈ T ∩ Set.Iic d, |X s ω| ≤ M + 1 := by
  obtain ⟨u, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  suffices ∀ᵐ ω ∂μ, ∀ n, ∃ M : ℕ, ∀ s ∈ T ∩ Set.Iic (u n), |X s ω| ≤ M + 1 by
    filter_upwards [this] with ω hω d
    obtain ⟨n, hn⟩ : ∃ n, d ≤ u n := (hu.2.eventually_ge_atTop d).exists
    obtain ⟨M, hM⟩ := hω n
    exact ⟨M, fun s hsT ↦ hM s (by grind)⟩
  rw [ae_all_iff]
  exact fun n ↦ ae_exists_bound'' hX hT (u n)

end CountableEvents

/-! ### Selection of alternating tuples from frequent oscillation -/

section Selection

variable [TopologicalSpace ι] [OrderTopology ι]

variable {T : Set ι} {x d : ι} {a b : ℝ} {ω : Ω}

lemma aux1 (hxd : x < d) : Set.Ioo x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x := by
  simp only [inter_mem_iff]
  constructor
  · rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [eventually_lt_nhds hxd] with s hs
    grind
  · exact mem_nhdsWithin_self_inter

lemma aux2 (hxd : d < x) : Set.Ioo d x ∩ T ∈ 𝓝[T ∩ Set.Iio x] x := by
  simp only [inter_mem_iff]
  constructor
  · rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [eventually_gt_nhds hxd] with s hs
    grind
  · exact mem_nhdsWithin_self_inter

lemma exists_finset_altSet_of_frequently_right (hxd : x < d)
    (hfa : ∃ᶠ s in 𝓝[T ∩ Set.Ioi x] x, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[T ∩ Set.Ioi x] x, b < X s ω) (m : ℕ) :
    ∃ F : Finset ι, ↑F ⊆ T ∩ Set.Ioo x d ∧ ω ∈ altSet X F a b m := by
  -- descending selection: even picks above `b`, odd picks below `a`
  have hsel k : ∃ c : ℕ → ι, (∀ i, i + 1 < k → c (i + 1) < c i)
      ∧ (∀ i < k, c i ∈ T ∩ Set.Ioo x d)
      ∧ (∀ i < k, if Even i then b < X (c i) ω else X (c i) ω < a) := by
    induction k with
    | zero => exact ⟨fun _ ↦ d, by lia, by lia, by lia⟩
    | succ k ih =>
      obtain ⟨c, hdesc, hmem, hval⟩ := ih
      -- previous lower endpoint
      set u : ι := if hk : 0 < k then c (k - 1) else d with hu
      have hxu : x < u := by grind
      have hud : u ≤ d := by grind
      have hU : Set.Ioo x u ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x := aux1 hxu
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
      exact ⟨Function.update c k s, by grind⟩
  obtain ⟨c, hdesc, hmem, hval⟩ := hsel (2 * m)
  -- reverse the order
  set ca : ℕ → ι := fun j ↦ c (2 * m - 1 - j) with hca
  exact ⟨(range (2 * m)).image ca, by grind, ca, by grind⟩

lemma mem_infiniteAlt_of_frequently_right (hxd : x < d)
    (hfa : ∃ᶠ s in 𝓝[T ∩ Set.Ioi x] x, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[T ∩ Set.Ioi x] x, b < X s ω) :
    ω ∈ infiniteAlt T d X a b := by
  simp only [infiniteAlt, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
  intro m
  obtain ⟨F, hFmem, hFalt⟩ := exists_finset_altSet_of_frequently_right hxd hfa hfb m
  refine ⟨F, ?_, hFalt⟩
  simp only [Set.subset_inter_iff] at hFmem ⊢
  refine ⟨hFmem.1, hFmem.2.trans ?_⟩
  grind

lemma exists_finset_altSet_of_frequently_left
    (hfa : ∃ᶠ s in 𝓝[T ∩ Set.Iio x] x, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[T ∩ Set.Iio x] x, b < X s ω) (m : ℕ) :
    ∃ F : Finset ι, ↑F ⊆ T ∩ Set.Iio x ∧ ω ∈ altSet X F a b m := by
  -- ascending selection: even picks below `a`, odd picks above `b`
  have hsel k : ∃ c : ℕ → ι, (∀ i, i + 1 < k → c i < c (i + 1))
      ∧ (∀ i < k, c i ∈ T ∩ Set.Iio x)
      ∧ (∀ i < k, if Even i then X (c i) ω < a else b < X (c i) ω) := by
    induction k with
    | zero => exact ⟨fun _ ↦ x, by lia, by lia, by lia⟩
    | succ k ih =>
      obtain ⟨c, hasc, hmem, hval⟩ := ih
      have hU : (if 0 < k then Set.Ioo (c (k - 1)) x else Set.Iio x) ∩ T
          ∈ 𝓝[T ∩ Set.Iio x] x := by
        split_ifs with hk
        · exact aux2 (hmem (k - 1) (by lia)).2
        · rw [Set.inter_comm]
          exact self_mem_nhdsWithin
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
      have hsx : s < x := by grind
      refine ⟨Function.update c k s, ?_, by grind⟩
      intro i hi
      rcases Nat.lt_or_ge (i + 1) k with h | h
      · grind
      · have hik : i + 1 = k := by lia
        rw [hik, Function.update_self, Function.update_of_ne (by lia)]
        have hci : c i = c (k - 1) := by congr 1; lia
        grind
  obtain ⟨c, hasc, hmem, hval⟩ := hsel (2 * m)
  exact ⟨(range (2 * m)).image c, by grind, c, hasc, by grind⟩

lemma mem_infiniteAlt_of_frequently_left (hxd : x ≤ d)
    (hfa : ∃ᶠ s in 𝓝[T ∩ Set.Iio x] x, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[T ∩ Set.Iio x] x, b < X s ω) :
    ω ∈ infiniteAlt T d X a b := by
  simp only [infiniteAlt, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
  intro m
  obtain ⟨F, hFmem, hFalt⟩ := exists_finset_altSet_of_frequently_left hfa hfb m
  refine ⟨F, ?_, hFalt⟩
  simp only [Set.subset_inter_iff] at hFmem ⊢
  refine ⟨hFmem.1, hFmem.2.trans ?_⟩
  grind

end Selection

section RegularitySet

def regularitySet (T : Set ι) (X : ι → Ω → ℝ) (d : ι) : Set Ω :=
  {ω | (∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r) ∧
    (∃ M : ℕ, ∀ s ∈ T ∩ Set.Iic d, |X s ω| ≤ M + 1)}

def regularitySetRight (T : Set ι) (X : ι → Ω → ℝ) (d : ι) : Set Ω :=
  ⋃ s ∈ T ∩ Set.Ioi d, regularitySet T X s

lemma regularitySet_anti {T : Set ι} {X : ι → Ω → ℝ} {d₁ d₂ : ι} (hd : d₁ ≤ d₂) :
    regularitySet T X d₂ ⊆ regularitySet T X d₁ := by
  intro ω hω
  simp only [regularitySet, Set.mem_setOf_eq] at hω ⊢
  constructor
  · intro q r hqr
    have hω' :=  hω.1 q r hqr
    refine fun h_mem ↦ hω' ?_
    exact infiniteAlt_mono'' hd h_mem
  · obtain ⟨M, hM⟩ := hω.2
    refine ⟨M, fun s hs ↦ ?_⟩
    specialize hM s (by grind)
    grind

lemma regularitySetRight_eq_biUnion_lt
    {T : Set ι} {X : ι → Ω → ℝ} {d t : ι} (hT : ∃ u ∈ T, d < u ∧ u ≤ t) :
    regularitySetRight T X d = ⋃ d' ∈ T ∩ Set.Ioc d t, regularitySet T X d' := by
  ext ω
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, exists_prop,
    Set.mem_Ioc]
  refine ⟨fun ⟨i, ⟨hiT, hdi⟩, hωi⟩ ↦ ?_, fun ⟨i, ⟨hiT, hdi, hit⟩, hωi⟩ ↦ ?_⟩
  · obtain ⟨u, huT, hud, hut⟩ := hT
    refine ⟨min i u, ?_, ?_⟩
    · grind
    · exact regularitySet_anti (by grind) hωi
  · exact ⟨i, ⟨hiT, hdi⟩, hωi⟩

lemma regularitySetRight_anti {T : Set ι} {X : ι → Ω → ℝ} {d₁ d₂ : ι} (hd : d₁ ≤ d₂) :
    regularitySetRight T X d₂ ⊆ regularitySetRight T X d₁ := by
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.iUnion_subset_iff, and_imp]
  intro i hiT hd₂i ω hω
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨i, ⟨hiT, by grind⟩, hω⟩

variable [OrderBot ι]

lemma ae_mem_regularitySet [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) (hdT : d ∈ T) :
    ∀ᵐ ω ∂μ, ω ∈ regularitySet T X d := by
  filter_upwards [measure_all_infiniteAlt hX hT hT, ae_exists_bound hX hT hT] with ω hω1 hω2
  exact ⟨fun q r hqr ↦ hω1 d hdT q r (mod_cast hqr), hω2 d hdT⟩

lemma ae_mem_all_regularitySet [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T, ω ∈ regularitySet T X d := by
  filter_upwards [measure_all_infiniteAlt hX hT hT, ae_exists_bound hX hT hT] with ω hω1 hω2 d hdT
  exact ⟨fun q r hqr ↦ hω1 d hdT q r (mod_cast hqr), hω2 d hdT⟩

lemma ae_mem_regularitySetRight [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (hTcof : ∀ x, ∃ s ∈ T, x < s) :
    ∀ᵐ ω ∂μ, ∀ d, ω ∈ regularitySetRight T X d := by
  have h1 : ∀ᵐ ω ∂μ, ∀ s ∈ T, ω ∈ regularitySet T X s := ae_mem_all_regularitySet hX hT
  filter_upwards [h1] with ω hω d
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, exists_prop]
  obtain ⟨s, hs, hsd⟩ := hTcof d
  exact ⟨s, ⟨hs, hsd⟩, hω s hs⟩

lemma measurableSet_altSet [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    (d : ι) (F : Finset ι) (hF : ∀ i ∈ F, i ≤ d) {q r : ℚ} (_hqr : q < r) (m : ℕ) :
    MeasurableSet[𝓕 d] (altSet X F q r m) := by
  have hXmeas : ∀ s ∈ F, Measurable[𝓕 d] (X s) := fun s hs ↦
    (hX.measurable s).mono (𝓕.mono (hF s hs)) le_rfl
  have hset : altSet X F (q : ℝ) (r : ℝ) m
      = ⋃ g ∈ Fintype.piFinset (fun _ : Fin (2 * m) ↦ F),
          {ω | (∀ (i : Fin (2 * m)) (h : (i : ℕ) + 1 < 2 * m), g i < g ⟨(i : ℕ) + 1, h⟩)
            ∧ (∀ i : Fin m, X (g ⟨2 * (i : ℕ), by omega⟩) ω ≤ (q : ℝ))
            ∧ (∀ i : Fin m, (r : ℝ) ≤ X (g ⟨2 * (i : ℕ) + 1, by omega⟩) ω)} := by
    ext ω
    simp only [altSet, Set.mem_setOf_eq, Set.mem_iUnion, Fintype.mem_piFinset, exists_prop]
    constructor
    · rintro ⟨c, hc1, hc2, hc3, hc4⟩
      exact ⟨fun i ↦ c (i : ℕ), fun i ↦ hc2 (i : ℕ) i.2,
        fun i h ↦ hc1 (i : ℕ) h, fun i ↦ hc3 (i : ℕ) i.2, fun i ↦ hc4 (i : ℕ) i.2⟩
    · rintro ⟨g, hgF, hg1, hg3, hg4⟩
      refine ⟨fun k ↦ if h : k < 2 * m then g ⟨k, h⟩ else ⊥, by grind, by grind, ?_, ?_⟩
      · intro i hi
        have h2i : 2 * i < 2 * m := by lia
        simp only [dif_pos h2i]
        exact hg3 ⟨i, hi⟩
      · intro i hi
        have h2i : 2 * i + 1 < 2 * m := by lia
        simp only [dif_pos h2i]
        exact hg4 ⟨i, hi⟩
  rw [hset]
  refine Finset.measurableSet_biUnion _ fun g hg ↦ ?_
  have hgF : ∀ i, g i ∈ F := Fintype.mem_piFinset.mp hg
  -- Split off the (measure-space independent) monotonicity condition, then recognise the event
  -- as a finite intersection of measurable half-lines `{X s ≤ q}` and `{r ≤ X s}`, `s ∈ F`.
  rw [Set.setOf_and]
  refine (MeasurableSet.const _).inter ?_
  rw [Set.setOf_and, Set.setOf_forall, Set.setOf_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i ↦ ?_) (MeasurableSet.iInter fun i ↦ ?_)
  · exact hXmeas _ (hgF ⟨2 * (i : ℕ), by lia⟩) measurableSet_Iic
  · exact hXmeas _ (hgF ⟨2 * (i : ℕ) + 1, by lia⟩) measurableSet_Ici

lemma measurableSet_infiniteAlt [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) {q r : ℚ} (hqr : q < r) :
    MeasurableSet[𝓕 d] (infiniteAlt T d X q r) := by
  unfold infiniteAlt
  refine MeasurableSet.iInter fun m ↦ MeasurableSet.biUnion ?_ fun F ↦ ?_
  · refine countable_setOf_finset_coe_subset ?_
    exact hT.mono (by grind)
  · intro hF
    refine measurableSet_altSet hX d F ?_ hqr m
    simp only [Set.subset_inter_iff, Set.mem_setOf_eq] at hF
    intro i hi
    exact hF.2 hi

lemma measurableSet_regularitySet [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) :
    MeasurableSet[𝓕 d] (regularitySet T X d) := by
  suffices MeasurableSet[𝓕 d]
        ((⋂ (q : ℚ) (r : ℚ) (hqr : q < r), {ω | ω ∉ infiniteAlt T d X q r}) ∩
        (⋃ M : ℕ, ⋂ s ∈ T ∩ Set.Iic d, {ω | |X s ω| ≤ M + 1})) by
      convert this
      ext ω
      simp [regularitySet]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun p ↦ MeasurableSet.iInter fun q ↦ ?_
    by_cases hpq : p < q
    · simp only [hpq, Set.iInter_true]
      refine MeasurableSet.compl ?_
      exact measurableSet_infiniteAlt hX hT d hpq
    · simp [hpq]
  · refine MeasurableSet.iUnion fun M ↦ MeasurableSet.biInter (hT.mono (by grind)) fun s hs ↦ ?_
    refine measurableSet_le ?_ (by fun_prop)
    simp only [Set.mem_inter_iff, Set.mem_Iic] at hs
    refine Measurable.mono ?_ (𝓕.mono hs.2) le_rfl
    simp_rw [← Real.norm_eq_abs]
    exact (hX.stronglyAdapted s).norm.measurable

omit [OrderBot ι] in
/-- For a right-continuous filtration, a set that is `𝓕 s`-measurable for every `s > t` is already
`𝓕 t`-measurable, since `𝓕 t = ⨅ s > t, 𝓕 s`. -/
lemma measurableSet_of_forall_gt [DenselyOrdered ι] [NoMaxOrder ι] [𝓕.IsRightContinuous]
    {t : ι} {A : Set Ω}
    (h : ∀ s, t < s → MeasurableSet[𝓕 s] A) :
    MeasurableSet[𝓕 t] A := by
  have hrc : (𝓕 t : MeasurableSpace Ω) = ⨅ j > t, 𝓕 j := by
    have h1 := 𝓕.rightCont_eq t
    rwa [Filtration.IsRightContinuous.eq] at h1
  rw [hrc, MeasurableSpace.measurableSet_iInf]
  intro j
  rw [MeasurableSpace.measurableSet_iInf]
  exact h j

lemma measurableSet_regularitySetRight [TopologicalSpace ι] [OrderClosedTopology ι]
    [DenselyOrdered ι] [NoMaxOrder ι] [IsFiniteMeasure μ] [𝓕.IsRightContinuous]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (hTd : Dense T) (d : ι) :
    MeasurableSet[𝓕 d] (regularitySetRight T X d) := by
  refine measurableSet_of_forall_gt fun s hs ↦ ?_
  rw [regularitySetRight_eq_biUnion_lt (t := s)]
  swap
  · obtain ⟨z, hz1, hz2, hz3⟩ := hTd.exists_between hs
    exact ⟨z, hz1, hz2, hz3.le⟩
  refine MeasurableSet.biUnion ?_ fun t ht ↦ ?_
  · exact hT.mono (by grind)
  · simp only [Set.mem_inter_iff, Set.mem_Ioc] at ht
    exact 𝓕.mono ht.2.2 _ (measurableSet_regularitySet hX hT t)

lemma measurableSet_regularitySetRight' [TopologicalSpace ι] [OrderClosedTopology ι]
    [DenselyOrdered ι] [NoMaxOrder ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) :
    MeasurableSet (regularitySetRight T X d) := by
  rw [regularitySetRight]
  refine MeasurableSet.biUnion ?_ fun t ht ↦ ?_
  · exact hT.mono (by grind)
  · exact 𝓕.le _ _ (measurableSet_regularitySet hX hT t)

variable [TopologicalSpace ι] [OrderTopology ι]

omit [OrderBot ι] in
lemma right_limit_of_mem_regularitySet {T : Set ι}
    (x d : ι) {ω : Ω} (hxd : x < d) (hω : ω ∈ regularitySet T X d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 l) := by
  simp only [regularitySet, Set.mem_inter_iff, Set.mem_Iic, and_imp, Set.mem_setOf_eq] at hω
  have h1 : ∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r := hω.1
  have h2 : ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
    convert hω.2
    simp
  obtain ⟨M, hM⟩ := h2
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩ hqr ⟨hfa, hfb⟩
    refine h1 p p' (mod_cast hqr) ?_
    exact mem_infiniteAlt_of_frequently_right hxd hfa hfb
  · refine ⟨((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Ioc x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x := Filter.mem_of_superset (aux1 hxd) (by grind)
    filter_upwards [hU] with s' hs' using by grind
  · refine ⟨-((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Ioc x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x := Filter.mem_of_superset (aux1 hxd) (by grind)
    filter_upwards [hU] with s' hs' using by grind

omit [OrderBot ι] in
lemma left_limit_of_mem_regularitySet {T : Set ι}
    (x d : ι) {ω : Ω} (hxle : x ≤ d) (hω : ω ∈ regularitySet T X d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 l) := by
  simp only [regularitySet, Set.mem_inter_iff, Set.mem_Iic, and_imp, Set.mem_setOf_eq] at hω
  have h1 : ∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r := hω.1
  have h2 : ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
    convert hω.2
    simp
  obtain ⟨M, hM⟩ := h2
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩ hqr ⟨hfa, hfb⟩
    refine h1 p p' (mod_cast hqr) ?_
    exact mem_infiniteAlt_of_frequently_left hxle hfa hfb
  · refine ⟨(M : ℝ) + 1, ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Iio x ∩ T ∈ 𝓝[T ∩ Set.Iio x] x := by
      rw [Set.inter_comm]
      exact self_mem_nhdsWithin
    filter_upwards [hU] with s' hs' using by grind
  · refine ⟨-((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Iio x ∩ T ∈ 𝓝[T ∩ Set.Iio x] x := by
      rw [Set.inter_comm]
      exact self_mem_nhdsWithin
    filter_upwards [hU] with s' hs' using by grind

omit [OrderBot ι] in
lemma eventually_mem_regularitySetRight_of_mem {T : Set ι}
    {x : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) :
    ∀ᶠ y in 𝓝[>] x, ω ∈ regularitySetRight T X y := by
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, exists_prop] at hω
  obtain ⟨d, ⟨hdT, hxd⟩, hω'⟩ := hω
  rw [eventually_nhdsWithin_iff]
  filter_upwards [eventually_lt_nhds hxd] with y hy hxy
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, exists_prop]
  refine ⟨d, ⟨hdT, hy⟩, ?_⟩
  exact regularitySet_anti (by grind) hω'

omit [OrderBot ι] in
lemma right_limit_of_mem_regularitySetRight {T : Set ι}
    {x y : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) (hyx : y ≤ x) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi y] y) (𝓝 l) := by
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, exists_prop] at hω
  obtain ⟨d, ⟨hdT, hxd⟩, hω'⟩ := hω
  exact right_limit_of_mem_regularitySet y d (by grind) hω'

omit [OrderBot ι] in
lemma eventually_right_limit_of_mem_regularitySetRight' {T : Set ι}
    {x : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) :
    ∀ᶠ y in 𝓝[>] x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi y] y) (𝓝 l) := by
  filter_upwards [eventually_mem_regularitySetRight_of_mem hω] with y hy
  exact right_limit_of_mem_regularitySetRight hy le_rfl

omit [OrderBot ι] in
lemma left_limit_of_mem_regularitySetRight {T : Set ι}
    {x y : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) (hyx : y ≤ x) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio y] y) (𝓝 l) := by
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, exists_prop] at hω
  obtain ⟨d, ⟨hdT, hxd⟩, hω'⟩ := hω
  exact left_limit_of_mem_regularitySet y d (by grind) hω'

omit [OrderBot ι] in
lemma eventually_left_limit_of_mem_regularitySetRight' {T : Set ι}
    {x : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) :
    ∀ᶠ y in 𝓝[>] x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio y] y) (𝓝 l) := by
  filter_upwards [eventually_mem_regularitySetRight_of_mem hω] with y hy
  exact left_limit_of_mem_regularitySetRight hy le_rfl

lemma ae_right_limit [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (hTcof : ∀ x, ∃ d ∈ T, x < d) :
    ∀ᵐ ω ∂μ, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 l) := by
  filter_upwards [ae_mem_all_regularitySet hX hT] with ω hω
  intro x
  obtain ⟨d, hdT, hxd⟩ := hTcof x
  exact right_limit_of_mem_regularitySet x d hxd (hω d hdT)

lemma ae_left_limit [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (hTcof : ∀ x, ∃ d ∈ T, x ≤ d) :
    ∀ᵐ ω ∂μ, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 l) := by
  filter_upwards [ae_mem_all_regularitySet hX hT] with ω hω
  intro x
  obtain ⟨d, hdT, hxle⟩ := hTcof x
  exact left_limit_of_mem_regularitySet x d hxle (hω d hdT)

end RegularitySet

variable [TopologicalSpace ι] [OrderBot ι] [OrderTopology ι]
  --[FirstCountableTopology ι] -- required for ∀ t : ι, (𝓝[>] t).IsCountablyGenerated
  [DenselyOrdered ι] [NoMaxOrder ι] -- required for ∀ t : ι, (𝓝[>] t).NeBot)

/-! ### Pathwise regularization

For a fixed path `h : ι → ℝ` admitting one-sided limits along a dense set `T`, the right-limit
regularization `r` is right-continuous and inherits the left limits of `h`. -/

section PathRegularization

variable {T : Set ι} {h r : ι → ℝ} {x : ι}

-- todo: delete this
omit [OrderBot ι] in
lemma nhdsGT_inf_principal_neBot (hTd : Dense T) (x : ι) : (𝓝[T ∩ Set.Ioi x] x).NeBot := by
  rw [Set.inter_comm]
  exact nhdsWithin_Ioi_inter_neBot hTd x

omit [OrderBot ι] in
/-- The right-limit regularization inherits left limits of `h` along `T`. -/
lemma tendsto_rightLim_nhdsLT (hTd : Dense T)
    (hr : ∀ᶠ y in 𝓝[<] x, Tendsto h (𝓝[T ∩ Set.Ioi y] y) (𝓝 (r y))) {L : ℝ}
    (hL : Tendsto h (𝓝[T ∩ Set.Iio x] x) (𝓝 L)) :
    Tendsto r (𝓝[<] x) (𝓝 L) := by
  by_cases hex : ∃ u, u < x
  swap
  · have hempty : Set.Iio x = ∅ := Set.eq_empty_iff_forall_notMem.2
      (fun u hu ↦ hex ⟨u, hu⟩)
    rw [nhdsWithin, hempty, Filter.principal_empty, inf_bot_eq]
    exact tendsto_bot
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro C ⟨hCmem, hCclosed⟩
  have hev : ∀ᶠ s in 𝓝[<] x ⊓ 𝓟 T, h s ∈ C := by
    rw [nhdsWithin_inf_principal, Set.inter_comm]; exact hL.eventually hCmem
  obtain ⟨v, hvx, hv⟩ := (nhdsLT_basis_of_exists_lt hex).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  filter_upwards [Ioo_mem_nhdsLT hvx, hr] with y hy hr
  have hne := nhdsGT_inf_principal_neBot hTd y
  refine hCclosed.mem_of_tendsto hr ?_
  rw [Set.inter_comm, ← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT hy.2] with s hs hsT
  exact hv ⟨hy.1.trans hs.1, hs.2⟩ hsT

omit [OrderBot ι] in
/-- Along a strictly increasing sequence `u → x` from the left, the regularized values
`r (u k)` tend to the left limit of `h` at `x` along `T' ⊇ T`. -/
lemma tendsto_rightLim_comp_of_lt (hTd : Dense T) {T' : Set ι} (hTT' : T ⊆ T')
    (hr : ∀ y, Tendsto h (𝓝[T ∩ Set.Ioi y] y) (𝓝 (r y))) {u : ℕ → ι} {L : ℝ}
    (hux : ∀ k, u k < x) (hutend : Tendsto u atTop (𝓝 x))
    (hL : Tendsto h (𝓝[T' ∩ Set.Iio x] x) (𝓝 L)) :
    Tendsto (fun k ↦ r (u k)) atTop (𝓝 L) := by
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro C ⟨hCmem, hCclosed⟩
  have hev : ∀ᶠ s in 𝓝[<] x ⊓ 𝓟 T', h s ∈ C := by
    rw [nhdsWithin_inf_principal, Set.inter_comm]; exact hL.eventually hCmem
  obtain ⟨v, hvx, hv⟩ := (nhdsLT_basis_of_exists_lt ⟨u 0, hux 0⟩).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  have hevk : ∀ᶠ k in atTop, u k ∈ Set.Ioi v :=
    hutend (IsOpen.mem_nhds isOpen_Ioi hvx)
  filter_upwards [hevk] with k hk
  have hne := nhdsGT_inf_principal_neBot hTd (u k)
  refine hCclosed.mem_of_tendsto (hr (u k)) ?_
  rw [Set.inter_comm, ← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT (hux k)] with s hs hsT
  exact hv ⟨hk.trans hs.1, hs.2⟩ (hTT' hsT)

omit [OrderBot ι] in
/-- Along a strictly decreasing sequence `u → x` from the right, the regularized values
`r (u k)` tend to the right limit of `h` at `x` along `T' ⊇ T`. -/
lemma tendsto_rightLim_comp_of_gt (hTd : Dense T) {T' : Set ι} (hTT' : T ⊆ T')
    (hr : ∀ y, Tendsto h (𝓝[T ∩ Set.Ioi y] y) (𝓝 (r y))) {u : ℕ → ι} {L : ℝ}
    (hux : ∀ k, x < u k) (hutend : Tendsto u atTop (𝓝 x))
    (hL : Tendsto h (𝓝[T' ∩ Set.Ioi x] x) (𝓝 L)) :
    Tendsto (fun k ↦ r (u k)) atTop (𝓝 L) := by
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro C ⟨hCmem, hCclosed⟩
  have hev : ∀ᶠ s in 𝓝[>] x ⊓ 𝓟 T', h s ∈ C := by
    rw [nhdsWithin_inf_principal, Set.inter_comm]; exact hL.eventually hCmem
  obtain ⟨v, hvx, hv⟩ := (nhdsGT_basis x).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  have hevk : ∀ᶠ k in atTop, u k ∈ Set.Iio v :=
    hutend (IsOpen.mem_nhds isOpen_Iio hvx)
  filter_upwards [hevk] with k hk
  have hne := nhdsGT_inf_principal_neBot hTd (u k)
  refine hCclosed.mem_of_tendsto (hr (u k)) ?_
  rw [Set.inter_comm, ← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT hk] with s hs hsT
  exact hv ⟨(hux k).trans hs.1, hs.2⟩ (hTT' hsT)

end PathRegularization

/-! ### Uncountable sets accumulate from the right -/

section Accumulation

omit [OrderBot ι] [NoMaxOrder ι] in
/-- Any uncountable set in a separable, densely-ordered, first-countable linear order admits a
strictly decreasing sequence of its elements converging to a point from the right. -/
lemma exists_seq_strictAnti_tendsto_of_not_countable [TopologicalSpace.SeparableSpace ι]
    {A : Set ι} (hA : ¬ A.Countable) :
    ∃ (p : ι) (u : ℕ → ι), (∀ k, u k ∈ A) ∧ (∀ k, p < u k) ∧
      Tendsto u atTop (𝓝 p) := by
  have : SecondCountableTopology ι := .of_separableSpace_orderTopology _
  have h := countable_setOf_isolated_right_within (s := A)
  have hsub : ¬ A ⊆ {x | x ∈ A ∧ 𝓝[A ∩ Set.Ioi x] x = ⊥} := by
    intro hcon
    exact hA (h.mono hcon)
  rw [Set.not_subset] at hsub
  obtain ⟨p, hpA, hpiso⟩ := hsub
  simp only [Set.mem_setOf_eq, not_and] at hpiso
  have : (𝓝[A ∩ Set.Ioi p] p).NeBot := ⟨hpiso hpA⟩
  obtain ⟨u, hu⟩ := exists_seq_tendsto (𝓝[A ∩ Set.Ioi p] p)
  simp only [tendsto_nhdsWithin_iff, Set.mem_inter_iff, Set.mem_Ioi, eventually_atTop] at hu
  obtain ⟨hu_tendsto, a, hu⟩ := hu
  refine ⟨p, fun k ↦ u (a + k), fun k ↦ (hu (a + k) (by grind)).1,
    fun k ↦ (hu (a + k) (by grind)).2, ?_⟩
  simp_rw [add_comm a]
  exact (tendsto_add_atTop_iff_nat a).mpr hu_tendsto

end Accumulation

noncomputable
def rightLimWithin (T : Set ι) (X : ι → Ω → ℝ) : ι → Ω → ℝ :=
  fun t ω ↦ Function.rightLimWithin (X · ω) T t

omit [OrderBot ι] [DenselyOrdered ι] [NoMaxOrder ι] in
lemma tendsto_rightLimWithin {ω : Ω} {T : Set ι} {x : ι}
    (h : ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 l)) :
    Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 (rightLimWithin T X x ω)) := by
  unfold rightLimWithin
  simp_rw [Set.inter_comm T] at h ⊢
  exact tendsto_rightLimWithin_of_tendsto h

omit [OrderBot ι] [DenselyOrdered ι] [NoMaxOrder ι] in
lemma tendsto_nhdsGT_rightLimWithin_of_mem_regularitySetRight
    {T : Set ι} {x : ι} {ω : Ω} (hmem : ω ∈ regularitySetRight T X x) :
    Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 (rightLimWithin T X x ω)) := by
  have h := right_limit_of_mem_regularitySetRight hmem le_rfl
  rw [Set.inter_comm] at h ⊢
  exact tendsto_rightLimWithin_of_tendsto h

omit [OrderBot ι] [DenselyOrdered ι] [NoMaxOrder ι] in
lemma tendsto_nhdsLT_leftLimWithin_of_mem_regularitySetRight
    {T : Set ι} {x : ι} {ω : Ω} (hmem : ω ∈ regularitySetRight T X x) :
    Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 (Function.leftLimWithin (X · ω) T x)) := by
  have h := left_limit_of_mem_regularitySetRight hmem le_rfl
  rw [Set.inter_comm] at h ⊢
  exact tendsto_leftLimWithin_of_tendsto h

omit [OrderBot ι] in
lemma rightContinuous_rightLimWithin_of_mem_regularitySetRight
    {T : Set ι} (hTd : Dense T) {x : ι}
    {ω : Ω} (hmem : ω ∈ regularitySetRight T X x) :
    ContinuousWithinAt (rightLimWithin T X · ω) (Set.Ici x) x := by
  refine continuousWithinAt_rightLimWithin_Ici_of_dense hTd ?_ ?_
  · have h := right_limit_of_mem_regularitySetRight hmem le_rfl
    rw [Set.inter_comm] at h
    exact tendsto_rightLimWithin_of_tendsto h
  · have h_ev_mem : ∀ᶠ y in 𝓝[>] x, ω ∈ regularitySetRight T X y :=
      eventually_mem_regularitySetRight_of_mem hmem
    filter_upwards [h_ev_mem] with y hy
    rw [Set.inter_comm]
    exact tendsto_nhdsGT_rightLimWithin_of_mem_regularitySetRight hy

omit [OrderBot ι] in
lemma measurableSet_tendsto_nhdsGT [FirstCountableTopology ι] [𝓕.IsRightContinuous]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) (t : ι) :
    MeasurableSet[𝓕 t] {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)} := by
  -- It suffices to prove `𝓕 s`-measurability for every `s > t`.
  refine measurableSet_of_forall_gt fun s hts ↦ ?_
  -- Along the countable set `S = (T ∩ Ioi t) ∩ Iio s` (all of whose points are `< s`), the limit
  -- along `𝓝[T ∩ Ioi t] t` is a limit along the countable index `↥S`.
  let S : Set ι := (T ∩ Set.Ioi t) ∩ Set.Iio s
  have hScount : S.Countable := hT.mono (Set.inter_subset_left.trans Set.inter_subset_left)
  have hSlt x (hx : x ∈ S) : x < s := by unfold S at hx; exact hx.2
  have hSmem : S ∈ 𝓝[T ∩ Set.Ioi t] t :=
    Filter.inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hts)))
  have : Countable S := hScount.to_subtype
  set l₀ : Filter S := Filter.comap ((↑) : S → ι) (𝓝[T ∩ Set.Ioi t] t) with hl₀
  have : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
  have hmap : Filter.map ((↑) : S → ι) l₀ = 𝓝[T ∩ Set.Ioi t] t :=
    Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact hSmem)
  have hset : {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)}
      = {ω | ∃ c, Tendsto (fun s' : S ↦ X s' ω) l₀ (𝓝 c)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    refine exists_congr fun c ↦ ?_
    rw [← hmap]
    exact tendsto_map'_iff
  rw [hset]
  have hf (s' : S) : Measurable[𝓕 s] (X s') := (hX s').mono (𝓕.mono (hSlt s' s'.2).le) le_rfl
  exact @MeasureTheory.measurableSet_exists_tendsto S ℝ Ω (𝓕 s) _ _ _ _ _ _ l₀ _ _ hf

omit [OrderBot ι] [OrderTopology ι] [DenselyOrdered ι] [NoMaxOrder ι] in
lemma measurableSet_tendsto_nhdsGT' [FirstCountableTopology ι]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) (t : ι) :
    MeasurableSet {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)} := by
  let S : Set ι := (T ∩ Set.Ioi t)
  have hScount : S.Countable := hT.mono (Set.inter_subset_left)
  have : Countable S := hScount.to_subtype
  set l₀ : Filter S := Filter.comap ((↑) : S → ι) (𝓝[T ∩ Set.Ioi t] t) with hl₀
  have : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
  have hmap : Filter.map ((↑) : S → ι) l₀ = 𝓝[T ∩ Set.Ioi t] t :=
    Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact self_mem_nhdsWithin)
  have hset : {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)}
      = {ω | ∃ c, Tendsto (fun s' : S ↦ X s' ω) l₀ (𝓝 c)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    refine exists_congr fun c ↦ ?_
    rw [← hmap]
    exact tendsto_map'_iff
  rw [hset]
  have hf (s' : S) : Measurable (X s') := (hX s').mono (𝓕.le _) le_rfl
  exact MeasureTheory.measurableSet_exists_tendsto hf

omit [OrderBot ι] [OrderTopology ι] [DenselyOrdered ι] [NoMaxOrder ι] in
lemma measurableSet_tendsto_nhdsLT [FirstCountableTopology ι]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) (t : ι) :
    MeasurableSet[𝓕 t] {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio t] t) (𝓝 l)} := by
  -- Every point of `S = T ∩ Iio t` is `< t`, so `X` there is already `𝓕 t`-measurable; the limit
  -- along `𝓝[T ∩ Iio t] t` is a limit along the countable index `↥S`.
  let S : Set ι := T ∩ Set.Iio t
  have hScount : S.Countable := hT.mono Set.inter_subset_left
  have hSlt x (hx : x ∈ S) : x < t := by unfold S at hx; exact hx.2
  have hSmem : S ∈ 𝓝[T ∩ Set.Iio t] t := self_mem_nhdsWithin
  haveI : Countable S := hScount.to_subtype
  set l₀ : Filter S := Filter.comap ((↑) : S → ι) (𝓝[T ∩ Set.Iio t] t) with hl₀
  haveI : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
  have hmap : Filter.map ((↑) : S → ι) l₀ = 𝓝[T ∩ Set.Iio t] t :=
    Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact hSmem)
  have hset : {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio t] t) (𝓝 l)}
      = {ω | ∃ c, Tendsto (fun s' : S ↦ X s' ω) l₀ (𝓝 c)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    refine exists_congr fun c ↦ ?_
    rw [← hmap]
    exact tendsto_map'_iff
  rw [hset]
  have hf (s' : S) : Measurable[𝓕 t] (X s') := (hX s').mono (𝓕.mono (hSlt s' s'.2).le) le_rfl
  exact @MeasureTheory.measurableSet_exists_tendsto S ℝ Ω (𝓕 t) _ _ _ _ _ _ l₀ _ _ hf

omit [OrderBot ι] [DenselyOrdered ι] [NoMaxOrder ι] in
lemma measurable_rightLimWithin [FirstCountableTopology ι]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) (t : ι) :
    Measurable (rightLimWithin T X t) := by
  rcases (𝓝[T ∩ Set.Ioi t] t).eq_or_neBot with hlbot | hlne
  · -- If the right neighbourhood filter is trivial, the right limit is just `X t`.
    have heq : rightLimWithin T X t = X t := by
      funext ω
      change Function.rightLimWithin (X · ω) T t = X t ω
      exact rightLimWithin_eq_of_eq_bot _ (by rw [Set.inter_comm]; exact hlbot)
    rw [heq]
    exact (hX t).mono (𝓕.le _) le_rfl
  · -- The set where the right limit exists is `𝓕 t`-measurable.
    have hAmeas : MeasurableSet {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)} :=
      measurableSet_tendsto_nhdsGT' hT hX t
    -- Off that set, the right limit equals `X t`.
    have hoffA : ∀ ω, ¬ (∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)) →
        rightLimWithin T X t ω = X t ω := by
      intro ω hω
      change Function.rightLimWithin (X · ω) T t = X t ω
      refine rightLimWithin_eq_of_not_tendsto _ ?_
      rw [Set.inter_comm]
      exact hω
    -- A measurable version of the right limit along the countable index `↥S`, `S ⊆ (t, s)`.
    set S : Set ι := (T ∩ Set.Ioi t) with hSdef
    have hScount : S.Countable := hT.mono (Set.inter_subset_left)
    have : Countable ↥S := hScount.to_subtype
    set l₀ : Filter ↥S := Filter.comap ((↑) : ↥S → ι) (𝓝[T ∩ Set.Ioi t] t) with hl₀
    have : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
    have hmap : Filter.map ((↑) : ↥S → ι) l₀ = 𝓝[T ∩ Set.Ioi t] t :=
      Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact self_mem_nhdsWithin)
    have : l₀.NeBot := by
      constructor
      intro h
      rw [h, Filter.map_bot] at hmap
      exact hlne.ne' hmap.symm
    -- The measurable candidate.
    have hf : ∀ s' : ↥S, Measurable (fun ω => X ↑s' ω) :=
      fun s' => (hX ↑s').mono (𝓕.le _) le_rfl
    have hgmeas : Measurable (fun ω => limUnder l₀ (fun s' : ↥S => X ↑s' ω)) :=
      @measurable_limUnder ↥S Ω ℝ mΩ _ _ _ _ _ l₀ _ _ _ hf
    -- On the set where the limit exists, the candidate is the right limit.
    have hgA : ∀ ω, (∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)) →
        limUnder l₀ (fun s' : ↥S => X ↑s' ω) = rightLimWithin T X t ω := by
      intro ω hω
      have htend := tendsto_rightLimWithin hω
      rw [← hmap, tendsto_map'_iff] at htend
      exact htend.limUnder_eq
    -- Assemble via `piecewise`.
    classical
    have hpw : rightLimWithin T X t
        = {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)}.piecewise
            (fun ω ↦ limUnder l₀ (fun s' : ↥S => X ↑s' ω)) (X t) := by
      funext ω
      simp only [Set.piecewise]
      split_ifs with hω
      · exact (hgA ω hω).symm
      · exact hoffA ω hω
    rw [hpw]
    refine Measurable.piecewise ?_ hgmeas ?_
    · exact hAmeas
    · exact (hX t).mono (𝓕.le _) le_rfl

omit [OrderBot ι] in
lemma adapted_rightLimWithin [FirstCountableTopology ι] [𝓕.IsRightContinuous]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) :
    Adapted 𝓕 (rightLimWithin T X) := by
  classical
  intro t
  rcases (𝓝[T ∩ Set.Ioi t] t).eq_or_neBot with hlbot | hlne
  · -- If the right neighbourhood filter is trivial, the right limit is just `X t`.
    have heq : rightLimWithin T X t = X t := by
      funext ω
      change Function.rightLimWithin (X · ω) T t = X t ω
      exact rightLimWithin_eq_of_eq_bot _ (by rw [Set.inter_comm]; exact hlbot)
    rw [heq]
    exact (hX t)
  · -- The set where the right limit exists is `𝓕 t`-measurable.
    have hAmeas : MeasurableSet[𝓕 t] {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)} :=
      measurableSet_tendsto_nhdsGT hT hX t
    -- Off that set, the right limit equals `X t`.
    have hoffA : ∀ ω, ¬ (∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)) →
        rightLimWithin T X t ω = X t ω := by
      intro ω hω
      change Function.rightLimWithin (X · ω) T t = X t ω
      refine rightLimWithin_eq_of_not_tendsto _ ?_
      rw [Set.inter_comm]
      exact hω
    -- It suffices to show `𝓕 s`-measurability for every `s > t`.
    suffices key : ∀ s, t < s → Measurable[𝓕 s] (rightLimWithin T X t) by
      intro B hB
      exact measurableSet_of_forall_gt fun s hts => key s hts hB
    intro s hts
    -- A measurable version of the right limit along the countable index `↥S`, `S ⊆ (t, s)`.
    set S : Set ι := (T ∩ Set.Ioi t) ∩ Set.Iio s with hSdef
    have hScount : S.Countable := hT.mono (Set.inter_subset_left.trans Set.inter_subset_left)
    have hSlt : ∀ x ∈ S, x < s := by
      intro x hx; rw [hSdef] at hx; exact hx.2
    have hSmem : S ∈ 𝓝[T ∩ Set.Ioi t] t :=
      Filter.inter_mem self_mem_nhdsWithin
        (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hts)))
    have : Countable ↥S := hScount.to_subtype
    set l₀ : Filter ↥S := Filter.comap ((↑) : ↥S → ι) (𝓝[T ∩ Set.Ioi t] t) with hl₀
    have : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
    have hmap : Filter.map ((↑) : ↥S → ι) l₀ = 𝓝[T ∩ Set.Ioi t] t :=
      Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact hSmem)
    have : l₀.NeBot := by
      constructor
      intro h
      rw [h, Filter.map_bot] at hmap
      exact hlne.ne' hmap.symm
    -- The measurable candidate.
    have hf : ∀ s' : ↥S, Measurable[𝓕 s] (fun ω => X ↑s' ω) :=
      fun s' => (hX ↑s').mono (𝓕.mono (hSlt ↑s' s'.2).le) le_rfl
    have hgmeas : Measurable[𝓕 s] (fun ω => limUnder l₀ (fun s' : ↥S => X ↑s' ω)) :=
      @measurable_limUnder ↥S Ω ℝ (𝓕 s) _ _ _ _ _ l₀ _ _ _ hf
    -- On the set where the limit exists, the candidate is the right limit.
    have hgA : ∀ ω, (∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)) →
        limUnder l₀ (fun s' : ↥S => X ↑s' ω) = rightLimWithin T X t ω := by
      intro ω hω
      have htend := tendsto_rightLimWithin hω
      rw [← hmap, tendsto_map'_iff] at htend
      exact htend.limUnder_eq
    -- Assemble via `piecewise`.
    have hpw : rightLimWithin T X t
        = {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)}.piecewise
            (fun ω ↦ limUnder l₀ (fun s' : ↥S => X ↑s' ω)) (X t) := by
      funext ω
      simp only [Set.piecewise]
      split_ifs with hω
      · exact (hgA ω hω).symm
      · exact hoffA ω hω
    rw [hpw]
    refine Measurable.piecewise ?_ hgmeas ?_
    · exact 𝓕.mono hts.le _ hAmeas
    · exact (hX t).mono (𝓕.mono hts.le) le_rfl

def notContSet (T : Set ι) (X : ι → Ω → ℝ) (μ : Measure Ω) : Set ι :=
  {t | ¬ rightLimWithin T X t =ᵐ[μ] X t}

omit [OrderBot ι] in
protected lemma Dense.exists_gt {T : Set ι} (hTd : Dense T) (x : ι) :
    ∃ d ∈ T, x < d := by
  obtain ⟨y, hy⟩ := exists_gt x
  obtain ⟨d, hdT, hd⟩ := hTd.exists_mem_open isOpen_Ioo (exists_between hy)
  exact ⟨d, hdT, hd.1⟩

lemma countable_notContSet [SecondCountableTopology ι] [IsFiniteMeasure μ]
    {T : Set ι} (hTc : T.Countable) (hTd : Dense T)
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    (notContSet T X μ).Countable := by
  -- every dense set is cofinal
  have hcof : ∀ T : Set ι, Dense T → ∀ x : ι, ∃ d ∈ T, x < d := fun T hTd x ↦ hTd.exists_gt x
  -- the right-limit value along `T`, by choice
  let R T' x ω : ℝ := Function.rightLimWithin (X · ω) T' x
  have hRspec T' x ω (h : ∃ l, Tendsto (X · ω) (𝓝[T' ∩ Set.Ioi x] x) (𝓝 l)) :
      Tendsto (X · ω) (𝓝[T' ∩ Set.Ioi x] x) (𝓝 (R T' x ω)) := tendsto_rightLimWithin h
  -- Stage 1: a.e. one-sided limits along D₀
  have hae₀ := ae_right_limit hX hTc (hcof T hTd)
  -- Stage 2: measurable versions of `R D₀ x`
  have hRm : ∀ x : ι, ∃ g : Ω → ℝ, Measurable g ∧ g =ᵐ[μ] R T x := by
    intro x
    have hne : (𝓝[T ∩ Set.Ioi x] x).NeBot := nhdsGT_inf_principal_neBot hTd x
    obtain ⟨v, hv⟩ := exists_seq_tendsto (𝓝[T ∩ Set.Ioi x] x)
    have haet : ∀ᵐ ω ∂μ, Tendsto (fun j ↦ X (v j) ω) atTop (𝓝 (R T x ω)) := by
      filter_upwards [hae₀] with ω hω
      exact (hRspec T x ω (hω x)).comp hv
    obtain ⟨g, hgmeas, hgae⟩ := measurable_limit_of_tendsto_metrizable_ae
      (f := fun j ↦ X (v j)) (L := atTop) (fun j ↦ (hX.measurable' (v j)).aemeasurable)
      (by filter_upwards [haet] with ω hω using ⟨_, hω⟩)
    refine ⟨g, hgmeas, ?_⟩
    filter_upwards [haet, hgae] with ω h1 h2
    exact tendsto_nhds_unique h2 h1
  choose Rm hRmMeas hRmae using hRm
  -- Stage 3: the set of points where `R D₀ x` and `X x` disagree is countable
  let Sset : Set ι := {x | ¬ R T x =ᵐ[μ] X x}
  change Sset.Countable
  by_contra hSunc
  set Sn : ℕ → Set ι := fun n ↦
    {x | ENNReal.ofReal (1 / (n + 1)) < μ {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|}} with hSn
  have hSsub : Sset ⊆ ⋃ n, Sn n := by
    intro x hx
    have hxm : ¬ Rm x =ᵐ[μ] X x := fun hcon ↦ hx ((hRmae x).symm.trans hcon)
    have hpos : μ {ω | Rm x ω ≠ X x ω} ≠ 0 := hxm
    have hBmono : Monotone (fun n : ℕ ↦ {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|}) := by
      intro n n' hnn' ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hω
      have : (n : ℝ) ≤ (n' : ℝ) := mod_cast hnn'
      gcongr
    have hBunion : {ω | Rm x ω ≠ X x ω} = ⋃ n : ℕ, {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro hne
        have habs : 0 < |Rm x ω - X x ω| := abs_pos.2 (sub_ne_zero.2 hne)
        exact exists_nat_one_div_lt habs
      · rintro ⟨n, hn⟩ hcon
        rw [hcon, sub_self, abs_zero] at hn
        exact absurd hn (not_lt.2 (by positivity))
    have hexn : ∃ n₀ : ℕ, 0 < μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} := by
      by_contra! hcon
      simp only [nonpos_iff_eq_zero] at hcon
      refine hpos ?_
      rw [hBunion]
      refine le_antisymm ((measure_iUnion_le _).trans ?_) zero_le
      simp only [hcon, tsum_zero, Std.le_refl]
    obtain ⟨n₀, hn₀⟩ := hexn
    have hfin : μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} ≠ ⊤ := measure_ne_top μ _
    let ε : ℝ := (μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|}).toReal
    have hεpos : 0 < ε := ENNReal.toReal_pos hn₀.ne' hfin
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hεpos
    let n := max n₀ n₁
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    rw [hSn]
    have hsub2 : {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|}
        ⊆ {ω | 1 / ((n : ℝ) + 1) < |Rm x ω - X x ω|} :=
      hBmono (le_max_left n₀ n₁)
    calc ENNReal.ofReal (1 / (n + 1))
        ≤ ENNReal.ofReal (1 / (n₁ + 1)) := by
          refine ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by positivity) ?_)
          gcongr
          exact mod_cast le_max_right n₀ n₁
      _ < ENNReal.ofReal ε := ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.2 hn₁
      _ = μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} := by rw [ENNReal.ofReal_toReal hfin]
      _ ≤ μ {ω | 1 / ((n : ℝ) + 1) < |Rm x ω - X x ω|} := measure_mono hsub2
  have hexSn : ∃ n, ¬ (Sn n).Countable := by
    by_contra! hcon
    exact hSunc ((Set.countable_iUnion hcon).mono hSsub)
  obtain ⟨n, hSnunc⟩ := hexSn
  obtain ⟨p, u, huSn, hup, hutend⟩ :=
    exists_seq_strictAnti_tendsto_of_not_countable hSnunc
  set T' : Set ι := T ∪ (Set.range u ∪ {p}) with hT'
  have hT'c : T'.Countable :=
    hTc.union ((Set.countable_range u).union (Set.countable_singleton p))
  have hT'd : Dense T' := hTd.mono Set.subset_union_left
  have haediff : ∀ᵐ ω ∂μ, Tendsto (fun k ↦ Rm (u k) ω - X (u k) ω) atTop (𝓝 0) := by
    have hcnt : ∀ᵐ ω ∂μ, ∀ k, Rm (u k) ω = R T (u k) ω := ae_all_iff.2 fun k ↦ hRmae (u k)
    filter_upwards [hae₀, ae_right_limit hX hT'c (hcof T' hT'd), hcnt] with ω hω₀ hω' hkeq
    have hL' := hRspec T' p ω (hω' p)
    have hXu : Tendsto (fun k ↦ X (u k) ω) atTop (𝓝 (R T' p ω)) := by
      refine hL'.comp ?_
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hutend, Filter.Eventually.of_forall fun k ↦ by grind⟩
    have hRu : Tendsto (fun k ↦ R T (u k) ω) atTop (𝓝 (R T' p ω)) :=
      tendsto_rightLim_comp_of_gt hTd Set.subset_union_left
        (fun y ↦ hRspec T y ω (hω₀ y)) hup hutend hL'
    have hsub := hRu.sub hXu
    rw [sub_self] at hsub
    refine Tendsto.congr (fun k ↦ ?_) hsub
    rw [hkeq k]
  have htim : TendstoInMeasure μ (fun k ω ↦ Rm (u k) ω - X (u k) ω) atTop
      (fun _ ↦ (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae
      (fun k ↦ ((hRmMeas (u k)).sub (hX.measurable' (u k))).aestronglyMeasurable) ?_
    filter_upwards [haediff] with ω hω using hω
  have hcontra := htim (ENNReal.ofReal (1 / (n + 1 : ℝ)))
    (by rw [ENNReal.ofReal_pos]; positivity)
  have hev : ∀ᶠ k in atTop,
      μ {ω | ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ edist (Rm (u k) ω - X (u k) ω) 0}
        < ENNReal.ofReal (1 / (n + 1)) := by
    refine hcontra.eventually_lt_const ?_
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
  exact lt_irrefl _ ((hmem.trans_le (measure_mono hsub3)).trans hk)

noncomputable
def rightContModif (T : Set ι) (X : ι → Ω → ℝ) (t : ι) (ω : Ω) : ℝ :=
  open Classical in
  if ω ∈ regularitySetRight T X t then rightLimWithin T X t ω else 0

lemma stronglyAdapted_rightContModif [SecondCountableTopology ι] [𝓕.IsRightContinuous]
    [IsFiniteMeasure μ] {T : Set ι} (hTc : T.Countable) (hTd : Dense T)
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    StronglyAdapted 𝓕 (rightContModif T X) := by
  refine fun i ↦ StronglyMeasurable.ite (measurableSet_regularitySetRight hX hTc hTd i) ?_
    (by fun_prop)
  refine Measurable.stronglyMeasurable ?_
  exact adapted_rightLimWithin hTc hX.stronglyAdapted.adapted i

lemma measurable_rightContModif [SecondCountableTopology ι]
    [IsFiniteMeasure μ] {T : Set ι} (hTc : T.Countable)
    (hX : IsRealQuasimartingale 𝓕 X μ) (t : ι) :
    Measurable (rightContModif T X t) := by
  refine Measurable.ite (measurableSet_regularitySetRight' hX hTc t) ?_ (by fun_prop)
  exact measurable_rightLimWithin hTc hX.stronglyAdapted.adapted t

omit [OrderBot ι] in
lemma tendsto_rightContModif_rightLimWithin [SecondCountableTopology ι]
    {T : Set ι} (hTd : Dense T) {x : ι} {ω : Ω}
    (hω : ω ∈ regularitySetRight T X x) :
    Tendsto (rightContModif T X · ω) (𝓝[>] x) (𝓝 (rightLimWithin T X x ω)) := by
  have h_mem : ∀ᶠ y in 𝓝[>] x, ω ∈ regularitySetRight T X y :=
    eventually_mem_regularitySetRight_of_mem hω
  classical
  rw [tendsto_congr' (f₂ := (rightLimWithin T X · ω))]
  swap; · filter_upwards [h_mem] with s' hs using by grind [notContSet, rightContModif]
  suffices ContinuousWithinAt (rightLimWithin T X · ω) (Set.Ici x) x by
    rwa [← continuousWithinAt_Ioi_iff_Ici] at this
  exact rightContinuous_rightLimWithin_of_mem_regularitySetRight hTd hω

omit [OrderBot ι] in
lemma tendsto_rightContModif_leftLimWithin [SecondCountableTopology ι]
    {T : Set ι} (hTd : Dense T) {x : ι} {ω : Ω}
    (hω : ω ∈ regularitySetRight T X x) :
    Tendsto (rightContModif T X · ω) (𝓝[<] x) (𝓝 (Function.leftLimWithin (X · ω) T x)) := by
  let R := rightLimWithin T X
  have hRspec x ω (hω : ω ∈ regularitySetRight T X x) :
      Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 (R x ω)) :=
    tendsto_nhdsGT_rightLimWithin_of_mem_regularitySetRight hω
  let Lc x ω := Function.leftLimWithin (X · ω) T x
  have hLspec x ω (h : ∃ l, Tendsto (fun s' ↦ X s' ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 l)) :
      Tendsto (fun s' ↦ X s' ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 (Lc x ω)) := by
    unfold Lc
    simp_rw [Set.inter_comm T] at h ⊢
    exact tendsto_leftLimWithin_of_tendsto h
  have h_mem y (hyx : y ≤ x) : ω ∈ regularitySetRight T X y := regularitySetRight_anti hyx hω
  classical
  rw [tendsto_congr' (f₂ := (R · ω))]
  swap; · exact eventually_nhdsWithin_of_forall fun y hy ↦ by grind [notContSet, rightContModif]
  unfold R
  refine tendsto_rightLim_nhdsLT hTd ?_ (hLspec x ω ?_)
  · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
    exact hRspec y ω (h_mem y (by grind))
  · exact left_limit_of_mem_regularitySetRight (h_mem x le_rfl) le_rfl

omit [OrderBot ι] [OrderTopology ι] [DenselyOrdered ι] [NoMaxOrder ι] in
lemma rightContModif_eq_zero [SecondCountableTopology ι]
    {T : Set ι} {x : ι} {ω : Ω} (hω : ω ∉ regularitySetRight T X x) :
    (rightContModif T X · ω) =ᶠ[𝓝[>] x] 0 := by
  have h_all y (hy : x ≤ y) : ω ∉ regularitySetRight T X y :=
    fun hω' ↦ hω (regularitySetRight_anti hy hω')
  refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
  simp at hy ⊢
  grind [rightContModif]

omit [OrderBot ι] in
lemma continuousWithinAt_rightContModif [SecondCountableTopology ι]
    {T : Set ι} (hTd : Dense T) (x : ι) (ω : Ω) :
    ContinuousWithinAt (rightContModif T X · ω) (Set.Ioi x) x := by
  by_cases hω : ω ∈ regularitySetRight T X x
  · have hYx : rightContModif T X x ω =
        rightLimWithin T X x ω := by
      simp only [rightContModif, if_pos hω]
    rw [ContinuousWithinAt, hYx]
    exact tendsto_rightContModif_rightLimWithin hTd hω
  · refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (rightContModif_eq_zero hω) ?_
    · fun_prop
    · simp [rightContModif, hω]

omit [DenselyOrdered ι] in
lemma rightContModif_ae_eq [SecondCountableTopology ι] [IsFiniteMeasure μ]
    {T : Set ι} (hTc : T.Countable) (hTd : Dense T)
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    ∀ t ∉ notContSet T X μ, rightContModif T X t =ᵐ[μ] X t := by
  have hGae : ∀ᵐ ω ∂μ, ∀ x, ω ∈ regularitySetRight T X x :=
    ae_mem_regularitySetRight hX hTc hTd.exists_gt
  intro t htS
  have htR : rightLimWithin T X t =ᵐ[μ] X t := not_not.1 htS
  filter_upwards [hGae, htR] with ω hω hωR
  simp only [rightContModif, if_pos (hω _)]
  exact hωR

lemma rightContModif_ae_eq_of_tendstoInMeasure [SecondCountableTopology ι] [IsFiniteMeasure μ]
    {T : Set ι} (hTc : T.Countable) (hTd : Dense T)
    (hX : IsRealQuasimartingale 𝓕 X μ)
    (t : ι) (hXRC : TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    rightContModif T X t =ᵐ[μ] X t := by
  classical
  -- every dense set is cofinal
  have hcof : ∀ T : Set ι, Dense T → ∀ x : ι, ∃ d ∈ T, x < d := fun T hTd x ↦ hTd.exists_gt x
  let Y := rightContModif T X
  have hY_meas t : Measurable (Y t) := measurable_rightContModif hTc hX t
  have hYCont x ω: ContinuousWithinAt (Y · ω) (Set.Ioi x) x :=
    continuousWithinAt_rightContModif hTd x ω
  have hX_cont x : ∀ᵐ ω ∂μ, Tendsto (X · ω) (𝓝[>] x ⊓ 𝓟 T) (𝓝 (Y x ω)) := by
    have hX_cont' x ω (hω : ω ∈ regularitySetRight T X x) :
        Tendsto (X · ω) (𝓝[>] x ⊓ 𝓟 T) (𝓝 (rightLimWithin T X x ω)) := by
      rw [nhdsWithin_inf_principal, Set.inter_comm]
      exact tendsto_nhdsGT_rightLimWithin_of_mem_regularitySetRight hω
    have h1 := ae_mem_regularitySetRight hX hTc (hcof T hTd)
    filter_upwards [h1] with ω hω using by grind [notContSet, rightContModif]
  have : (𝓝[Set.Ioi t ∩ T] t).NeBot := by
    rw [Set.inter_comm]; exact nhdsGT_inf_principal_neBot hTd t
  obtain ⟨w, hseq'⟩ := exists_seq_tendsto (𝓝[Set.Ioi t ∩ T] t)
  obtain hseq : Tendsto w atTop (𝓝[>] t) := by
    rw [tendsto_nhdsWithin_iff] at hseq' ⊢
    refine ⟨hseq'.1, ?_⟩
    filter_upwards [hseq'.2] with n hn using by grind
  refine tendstoInMeasure_ae_unique ?_ ?_ (f := Y ∘ w) (u := atTop)
  · refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
    · exact (hY_meas (w n)).aestronglyMeasurable
    · exact ae_of_all _ fun ω ↦ (hYCont t ω).tendsto.comp hseq
  suffices TendstoInMeasure μ (fun k ω ↦ Y (w k) ω - X (w k) ω) atTop 0 by
    have hX_tendsto := hXRC.comp hseq
    have h_eq : Y ∘ w = (fun k ω ↦ Y (w k) ω - X (w k) ω) + (X ∘ w) := by ext; simp
    rw [h_eq, ← zero_add (X t)]
    exact TendstoInMeasure.add this hX_tendsto
  refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
  · refine StronglyMeasurable.aestronglyMeasurable ?_
    exact (hY_meas (w n)).stronglyMeasurable.sub ((hX.stronglyAdapted (w n)).mono (𝓕.le _))
  filter_upwards [hX_cont t] with ω hX_cont
  simp only [Pi.zero_apply]
  have : 0 = Y t ω - Y t ω := by simp
  rw [this]
  refine Tendsto.sub ?_ ?_
  · exact (hYCont t ω).tendsto.comp hseq
  · refine hX_cont.comp ?_
    rwa [nhdsWithin_inf_principal]

/-- If `X` is an adapted integrable stochastic process which is right continuous in probability,
and is such that the set `{𝔼[(𝟙_A ● X) t] | A elementary predicatable}` is bounded for any t,
then it admits a cadlag modification. -/
lemma exists_modification_isCadlag [SecondCountableTopology ι] [IsFiniteMeasure μ]
    [𝓕.IsRightContinuous]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    (hXRC : ∀ t, TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    ∃ Y : ι → Ω → ℝ, (∀ t, Y t =ᵐ[μ] X t) ∧ (∀ t, Integrable (Y t) μ) ∧ ∀ ω, IsCadlag (Y · ω) := by
  sorry

end ProbabilityTheory
