/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.DoobMeyer

/-! # Doob-Meyer decomposition for submartingales of class DL

`ProbabilityTheory.ClassD.doob_meyer` gives the Doob-Meyer decomposition of a càdlàg submartingale
of class D over an index set with a top element. If the index set has no top element (for example
`ℝ≥0`), the right hypothesis is class DL. We deduce that case from the class D theorem.

For `b : ι`, the restriction of a class DL submartingale `S` to `Set.Icc ⊥ b` is of class D, hence
has a Doob-Meyer decomposition `S = M' + A'` on `Set.Icc ⊥ b`. Composing with the maps
`t ↦ min t c` for `c ≤ b` (seen as maps from `ι` to `Set.Icc ⊥ b`), we get a decomposition of the
increment `S (min t b) - S (min t a)` on the whole of `ι`, for all `a ≤ b`. We then sum these
decompositions along a monotone sequence of times tending to infinity: the sum is locally finite.

## Main statements

* `ProbabilityTheory.ClassDL.doob_meyer`: Doob-Meyer decomposition of a càdlàg submartingale of
  class DL.
-/

@[expose] public section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

namespace MeasureTheory

section MinIcc

variable {ι : Type*} [LinearOrder ι] [OrderBot ι] {b c : ι}

/-- The map `t ↦ min t c` for `c ≤ b`, seen as a map to `Set.Icc ⊥ b`. -/
def minIcc (hcb : c ≤ b) (t : ι) : Icc (⊥ : ι) b :=
  ⟨min t c, bot_le, (min_le_right t c).trans hcb⟩

@[simp]
lemma coe_minIcc (hcb : c ≤ b) (t : ι) : (minIcc hcb t : ι) = min t c := rfl

lemma monotone_minIcc (hcb : c ≤ b) : Monotone (minIcc hcb) :=
  fun _ _ hst ↦ Subtype.mk_le_mk.2 (min_le_min_right c hst)

lemma continuous_minIcc [TopologicalSpace ι] [OrderTopology ι] (hcb : c ≤ b) :
    Continuous (minIcc hcb) :=
  Continuous.subtype_mk (by fun_prop) _

lemma minIcc_of_le (hcb : c ≤ b) {t : ι} (htc : t ≤ c) :
    minIcc hcb t = ⟨t, bot_le, htc.trans hcb⟩ :=
  Subtype.ext (min_eq_left htc)

lemma minIcc_of_ge (hcb : c ≤ b) {t : ι} (hct : c ≤ t) :
    minIcc hcb t = ⟨c, bot_le, hcb⟩ :=
  Subtype.ext (min_eq_right hct)

end MinIcc

section RestrictIcc

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The restriction of a filtration to the interval `Set.Icc ⊥ b`. -/
abbrev Filtration.restrictIcc [Preorder ι] [OrderBot ι] (𝓕 : Filtration ι mΩ) (b : ι) :
    Filtration (Icc (⊥ : ι) b) mΩ :=
  𝓕.indexComap (Subtype.mono_coe (· ∈ Icc (⊥ : ι) b))

instance [PartialOrder ι] [OrderBot ι] {𝓕 : Filtration ι mΩ} [𝓕.IsComplete P] (b : ι) :
    (𝓕.restrictIcc b).IsComplete P :=
  ⟨fun _ hs t ↦ Filtration.IsComplete.measurableSet_of_null (𝓕 := 𝓕) hs (t : ι)⟩

instance [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous] (b : ι) :
    (𝓕.restrictIcc b).IsRightContinuous := by
  refine ⟨fun t ↦ ?_⟩
  by_cases hne : (𝓝[>] t).NeBot
  · -- `t` is not the top element of `Icc ⊥ b`, and is not isolated on the right in `ι`
    obtain ⟨u, hu⟩ : (Ioi t).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      exact hne.ne (by rw [h, nhdsWithin_empty])
    have htb : (t : ι) < b := (Subtype.coe_lt_coe.2 hu).trans_le u.2.2
    have hne' : (𝓝[>] (t : ι)).NeBot := by
      have h_tendsto : Tendsto (Subtype.val : Icc (⊥ : ι) b → ι) (𝓝[>] t) (𝓝[>] (t : ι)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (continuous_subtype_val.continuousAt.mono_left nhdsWithin_le_nhds)
          (by filter_upwards [self_mem_nhdsWithin] with s hs using Subtype.coe_lt_coe.2 hs)
      exact h_tendsto.neBot
    rw [Filtration.rightCont_eq_of_neBot_nhdsGT]
    have h_eq : 𝓕 (t : ι) = ⨅ j > (t : ι), 𝓕 j := by
      conv_lhs => rw [← Filtration.IsRightContinuous.eq (𝓕 := 𝓕)]
      rw [Filtration.rightCont_eq_of_neBot_nhdsGT]
    change ⨅ j > t, 𝓕 (j : ι) ≤ 𝓕 (t : ι)
    rw [h_eq]
    refine le_iInf₂ fun j hj ↦ ?_
    refine iInf₂_le_of_le ⟨min j b, bot_le, min_le_right _ _⟩ ?_ (𝓕.mono (min_le_left _ _))
    exact Subtype.coe_lt_coe.1 (lt_min hj htb)
  · rw [Filtration.rightCont_eq_of_nhdsGT_eq_bot _ (not_neBot.1 hne)]

/-- If `M` is a martingale on `Set.Icc ⊥ b` with respect to the restricted filtration, then
`t ↦ M (min t c)` is a martingale on `ι`. -/
lemma Martingale.comp_minIcc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [LinearOrder ι] [OrderBot ι] {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration P 𝓕] {b c : ι} {M : Icc (⊥ : ι) b → Ω → E}
    (hM : Martingale M (𝓕.restrictIcc b) P) (hcb : c ≤ b) :
    Martingale (fun t ↦ M (minIcc hcb t)) 𝓕 P := by
  have h_adapted (t : ι) : StronglyMeasurable[𝓕 t] (M (minIcc hcb t)) :=
    (hM.stronglyAdapted (minIcc hcb t)).mono (𝓕.mono (min_le_left t c))
  refine ⟨h_adapted, fun s t hst ↦ ?_⟩
  obtain hsc | hcs := le_or_gt s c
  · have h : P[M (minIcc hcb t) | 𝓕 (min s c)] =ᵐ[P] M (minIcc hcb s) :=
      hM.condExp_ae_eq (monotone_minIcc hcb hst)
    rwa [min_eq_left hsc] at h
  · simp only [minIcc_of_ge hcb (hcs.le.trans hst)]
    rw [← minIcc_of_ge hcb hcs.le, condExp_of_stronglyMeasurable (𝓕.le s) (h_adapted s)
      (hM.integrable _)]

/-- If `A` is a predictable process on `Set.Icc ⊥ b` with respect to the restricted filtration,
then `t ↦ A (min t c)` is a predictable process on `ι`. -/
lemma IsStronglyPredictable.comp_minIcc {E : Type*} [TopologicalSpace E]
    [ConditionallyCompleteLinearOrderBot ι] {𝓕 : Filtration ι mΩ} {b c : ι}
    {A : Icc (⊥ : ι) b → Ω → E}
    (hA : haveI : Fact ((⊥ : ι) ≤ b) := ⟨bot_le⟩; IsStronglyPredictable (𝓕.restrictIcc b) A)
    (hcb : c ≤ b) :
    IsStronglyPredictable 𝓕 (fun t ↦ A (minIcc hcb t)) := by
  haveI : Fact ((⊥ : ι) ≤ b) := ⟨bot_le⟩
  have h_meas : @Measurable (ι × Ω) (Icc (⊥ : ι) b × Ω) 𝓕.predictable
      (𝓕.restrictIcc b).predictable (fun p ↦ (minIcc hcb p.1, p.2)) := by
    rw [measurable_iff_comap_le]
    refine MeasurableSpace.comap_le_iff_le_map.2 <|
      measurableSpace_le_predictable_of_measurableSet (fun B hB ↦ ?_) (fun s B hB ↦ ?_)
    · have hB' : MeasurableSet[𝓕 ⊥] B := by
        have h : MeasurableSet[𝓕 ((⊥ : Icc (⊥ : ι) b) : ι)] B := hB
        rwa [Set.Icc.coe_bot] at h
      simp only [MeasurableSpace.map_def]
      by_cases hc : c = ⊥
      · have h_eq : (fun p : ι × Ω ↦ (minIcc hcb p.1, p.2)) ⁻¹' ({⊥} ×ˢ B) = univ ×ˢ B := by
          ext p
          simp [Subtype.ext_iff, hc]
        rw [h_eq]
        exact measurableSet_predictable_univ_prod hB'
      · have h_eq : (fun p : ι × Ω ↦ (minIcc hcb p.1, p.2)) ⁻¹' ({⊥} ×ˢ B) = {⊥} ×ˢ B := by
          ext p
          simp [Subtype.ext_iff, hc]
        rw [h_eq]
        exact measurableSet_predictable_singleton_bot_prod hB'
    · have hB' : MeasurableSet[𝓕 (s : ι)] B := hB
      simp only [MeasurableSpace.map_def]
      by_cases hsc : (s : ι) < c
      · have h_eq : (fun p : ι × Ω ↦ (minIcc hcb p.1, p.2)) ⁻¹' (Ioi s ×ˢ B)
            = Ioi (s : ι) ×ˢ B := by
          ext p
          simp [← Subtype.coe_lt_coe, hsc]
        rw [h_eq]
        exact measurableSet_predictable_Ioi_prod hB'
      · have h_eq : (fun p : ι × Ω ↦ (minIcc hcb p.1, p.2)) ⁻¹' (Ioi s ×ˢ B) = ∅ := by
          ext p
          simp [← Subtype.coe_lt_coe, hsc]
        simp [h_eq]
  exact hA.comp_measurable h_meas

/-- The restriction of a predictable process to `Set.Icc ⊥ b` is predictable with respect to the
restricted filtration. -/
lemma IsStronglyPredictable.restrictIcc {E : Type*} [TopologicalSpace E]
    [ConditionallyCompleteLinearOrderBot ι] {𝓕 : Filtration ι mΩ} {A : ι → Ω → E}
    (hA : IsStronglyPredictable 𝓕 A) (b : ι) :
    haveI : Fact ((⊥ : ι) ≤ b) := ⟨bot_le⟩
    IsStronglyPredictable (𝓕.restrictIcc b) (fun t : Icc (⊥ : ι) b ↦ A t) := by
  haveI : Fact ((⊥ : ι) ≤ b) := ⟨bot_le⟩
  have h_meas : @Measurable (Icc (⊥ : ι) b × Ω) (ι × Ω) (𝓕.restrictIcc b).predictable
      𝓕.predictable (fun p ↦ ((p.1 : ι), p.2)) := by
    rw [measurable_iff_comap_le]
    refine MeasurableSpace.comap_le_iff_le_map.2 <|
      measurableSpace_le_predictable_of_measurableSet (fun B hB ↦ ?_) (fun s B hB ↦ ?_)
    · have hB' : MeasurableSet[𝓕.restrictIcc b ⊥] B := by
        change MeasurableSet[𝓕 ((⊥ : Icc (⊥ : ι) b) : ι)] B
        rwa [Set.Icc.coe_bot]
      simp only [MeasurableSpace.map_def]
      have h_eq : (fun p : Icc (⊥ : ι) b × Ω ↦ ((p.1 : ι), p.2)) ⁻¹' ({⊥} ×ˢ B) = {⊥} ×ˢ B := by
        ext p
        simp only [mem_preimage, mem_prod, mem_singleton_iff, Subtype.ext_iff, Set.Icc.coe_bot]
      rw [h_eq]
      exact measurableSet_predictable_singleton_bot_prod hB'
    · simp only [MeasurableSpace.map_def]
      by_cases hsb : s ≤ b
      · have hB' : MeasurableSet[𝓕.restrictIcc b ⟨s, bot_le, hsb⟩] B := hB
        have h_eq : (fun p : Icc (⊥ : ι) b × Ω ↦ ((p.1 : ι), p.2)) ⁻¹' (Ioi s ×ˢ B)
            = Ioi ⟨s, bot_le, hsb⟩ ×ˢ B := by
          ext p
          simp [← Subtype.coe_lt_coe]
        rw [h_eq]
        exact measurableSet_predictable_Ioi_prod hB'
      · have h_eq : (fun p : Icc (⊥ : ι) b × Ω ↦ ((p.1 : ι), p.2)) ⁻¹' (Ioi s ×ˢ B) = ∅ := by
          ext p
          simp only [mem_preimage, mem_prod, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
          exact fun h ↦ absurd (h.le.trans p.1.2.2) hsb
        simp [h_eq]
  exact hA.comp_measurable h_meas

end RestrictIcc

end MeasureTheory

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [NormedAddCommGroup E]

/-- The restriction of a process of class DL to `Set.Icc ⊥ b` is of class D. -/
lemma ClassDL.classD_restrictIcc [LinearOrder ι] [OrderBot ι] [MeasurableSpace ι]
    {𝓕 : Filtration ι mΩ} {S : ι → Ω → E} (hd : ClassDL S 𝓕 P) (b : ι) :
    haveI : Fact ((⊥ : ι) ≤ b) := ⟨bot_le⟩
    ClassD (fun t : Icc (⊥ : ι) b ↦ S t) (𝓕.restrictIcc b) P := by
  haveI : Fact ((⊥ : ι) ≤ b) := ⟨bot_le⟩
  refine ⟨fun t ↦ ?_, ?_⟩
  · have h_meas : @Measurable (Iic t × Ω) (Iic (t : ι) × Ω)
        (Subtype.instMeasurableSpace.prod (𝓕 t)) (Subtype.instMeasurableSpace.prod (𝓕 t))
        (fun p ↦ (⟨p.1.1.1, p.1.2⟩, p.2)) := by
      refine Measurable.prodMk ?_ measurable_snd
      exact (measurable_subtype_coe.comp (measurable_subtype_coe.comp measurable_fst)).subtype_mk
    exact (hd.1 t).comp_measurable h_meas
  · let f : {T : Ω → WithTop (Icc (⊥ : ι) b) |
          IsStoppingTime (𝓕.restrictIcc b) T ∧ ∀ ω, T ω ≠ ⊤} →
        {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ b} :=
      fun τ ↦ ⟨fun ω ↦ (τ.1 ω).map Subtype.val, fun i ↦ ?_, fun ω ↦ ?_⟩
    · convert (hd.2 b).comp f with τ
      ext ω
      obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 (τ.2.2 ω)
      simp [stoppedValue, f, ← hx]
    · have h_eq : {ω | (τ.1 ω).map Subtype.val ≤ (i : WithTop ι)}
          = {ω | τ.1 ω ≤ ((⟨min i b, bot_le, min_le_right _ _⟩ : Icc (⊥ : ι) b) :
            WithTop (Icc (⊥ : ι) b))} := by
        ext ω
        obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 (τ.2.2 ω)
        simp only [← hx, WithTop.map_coe, mem_ofPred_eq, WithTop.coe_le_coe, ← Subtype.coe_le_coe,
          le_min_iff, x.2.2, and_true]
      rw [h_eq]
      exact 𝓕.mono (min_le_left i b) _ (τ.2.1 _)
    · obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 (τ.2.2 ω)
      simp only [← hx, WithTop.map_coe, WithTop.coe_le_coe]
      exact x.2.2

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [SecondCountableTopology ι] [MeasurableSpace ι] [BorelSpace ι] [IsFiniteMeasure P]
  {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous] [𝓕.IsComplete P]

/-- Doob-Meyer decomposition of the increment `t ↦ S (min t b) - S (min t a)` of a càdlàg
submartingale of class DL. -/
lemma ClassDL.exists_doob_meyer_increment (hd : ClassDL S 𝓕 P) (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) {a b : ι} (hab : a ≤ b) :
    ∃ (N B : ι → Ω → ℝ), (∀ t, S (min t b) - S (min t a) = N t + B t) ∧ Martingale N 𝓕 P ∧
      (∀ ω, IsCadlag (N · ω)) ∧ IsStronglyPredictable 𝓕 B ∧ (∀ ω, IsCadlag (B · ω)) ∧
      (∀ ω, Monotone (B · ω)) ∧ ∀ t ≤ a, B t = 0 := by
  haveI : Fact ((⊥ : ι) ≤ b) := ⟨bot_le⟩
  have h_mono : Monotone (Subtype.val : Icc (⊥ : ι) b → ι) := Subtype.mono_coe _
  obtain ⟨M', A', hSMA, hM', hM'c, hA', hA'c, hA'm, -⟩ :=
    ClassD.doob_meyer (hd.classD_restrictIcc b) (hs.indexComap h_mono)
      (fun ω ↦ (hc ω).comp_of_monotone_of_continuous h_mono continuous_subtype_val)
  have hbb : b ≤ b := le_rfl
  refine ⟨fun t ↦ M' (minIcc hbb t) - M' (minIcc hab t),
    fun t ↦ A' (minIcc hbb t) - A' (minIcc hab t), fun t ↦ ?_, ?_, fun ω ↦ ?_, ?_, fun ω ↦ ?_,
    fun ω s t hst ↦ ?_, fun t hta ↦ ?_⟩
  · have h1 : S (min t b) = M' (minIcc hbb t) + A' (minIcc hbb t) :=
      congrFun hSMA (minIcc hbb t)
    have h2 : S (min t a) = M' (minIcc hab t) + A' (minIcc hab t) :=
      congrFun hSMA (minIcc hab t)
    rw [h1, h2]
    exact add_sub_add_comm _ _ _ _
  · exact (hM'.comp_minIcc hbb).sub (hM'.comp_minIcc hab)
  · exact ((hM'c ω).comp_of_monotone_of_continuous (monotone_minIcc hbb)
      (continuous_minIcc hbb)).sub ((hM'c ω).comp_of_monotone_of_continuous (monotone_minIcc hab)
      (continuous_minIcc hab))
  · exact (hA'.comp_minIcc hbb).sub (hA'.comp_minIcc hab)
  · exact ((hA'c ω).comp_of_monotone_of_continuous (monotone_minIcc hbb)
      (continuous_minIcc hbb)).sub ((hA'c ω).comp_of_monotone_of_continuous (monotone_minIcc hab)
      (continuous_minIcc hab))
  · simp only [Pi.sub_apply]
    obtain hsa | has := le_or_gt s a
    · have h_le : minIcc hab t ≤ minIcc hbb t := Subtype.mk_le_mk.2 (min_le_min_left t hab)
      rw [minIcc_of_le hab hsa, minIcc_of_le hbb (hsa.trans hab), sub_self]
      exact sub_nonneg.2 (hA'm ω h_le)
    · rw [minIcc_of_ge hab has.le, minIcc_of_ge hab (has.le.trans hst)]
      exact sub_le_sub_right (hA'm ω (monotone_minIcc hbb hst)) _
  · change A' (minIcc hbb t) - A' (minIcc hab t) = 0
    rw [minIcc_of_le hab hta, minIcc_of_le hbb (hta.trans hab), sub_self]

/-- **Doob–Meyer decomposition** of a càdlàg submartingale of class DL. -/
theorem ClassDL.doob_meyer (hd : ClassDL S 𝓕 P) (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) :
    ∃ (M A : ι → Ω → ℝ), S = M + A ∧ Martingale M 𝓕 P ∧ (∀ ω, IsCadlag (M · ω)) ∧
      IsStronglyPredictable 𝓕 A ∧ (∀ ω, IsCadlag (A · ω)) ∧ (∀ ω, Monotone (A · ω)) ∧
      A ⊥ = 0 := by
  -- a monotone sequence of times `U`, starting at `⊥` and tending to infinity
  obtain ⟨T, hT_mono, hT_tendsto⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  let U : ℕ → ι := fun n ↦ n.casesOn ⊥ T
  have hU_mono : Monotone U := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    cases n with
    | zero => exact bot_le
    | succ n => exact hT_mono n.le_succ
  have hU (t : ι) : ∃ k, t ≤ U k := by
    obtain ⟨n, hn⟩ := (hT_tendsto.eventually_ge_atTop t).exists
    exact ⟨n + 1, hn⟩
  -- the decompositions of the increments of `S` between `U n` and `U (n + 1)`
  choose N B hSNB hN hNc hB hBc hBm hB0 using
    fun n ↦ hd.exists_doob_meyer_increment hs hc (hU_mono (Nat.le_succ n))
  -- the partial sums of the predictable parts
  let Asum : ℕ → ι → Ω → ℝ := fun k ↦ ∑ n ∈ Finset.range k, B n
  have hAsum_succ (k : ℕ) : Asum (k + 1) = Asum k + B k := Finset.sum_range_succ _ _
  have hAsum_pred (k : ℕ) : IsStronglyPredictable 𝓕 (Asum k) := by
    induction k with
    | zero => exact IsStronglyPredictable.const (c := (0 : ℝ))
    | succ k ih => exact hAsum_succ k ▸ ih.add (hB k)
  have hAsum_cadlag (k : ℕ) (ω : Ω) : IsCadlag (Asum k · ω) := by
    induction k with
    | zero => exact isCadlag_const (0 : ℝ)
    | succ k ih => exact hAsum_succ k ▸ ih.add (hBc k ω)
  have hAsum_mono (k : ℕ) (ω : Ω) : Monotone (Asum k · ω) := by
    induction k with
    | zero => exact monotone_const (c := (0 : ℝ))
    | succ k ih => exact hAsum_succ k ▸ ih.add (hBm k ω)
  have hAsum_eq {k k' : ℕ} (hkk' : k ≤ k') {t : ι} (ht : t ≤ U k) : Asum k' t = Asum k t := by
    simp only [Asum, Finset.sum_apply]
    refine (Finset.sum_subset (Finset.range_mono hkk') fun n _ hn ↦ ?_).symm
    exact hB0 n t (ht.trans (hU_mono (by simpa using hn)))
  -- the predictable part: the sum of the `B n`, which is locally finite
  choose κ hκ using hU
  let A : ι → Ω → ℝ := fun t ↦ Asum (κ t) t
  have hA_eq {k : ℕ} {t : ι} (ht : t ≤ U k) : A t = Asum k t := by
    obtain h | h := le_total (κ t) k
    · exact (hAsum_eq h (hκ t)).symm
    · exact hAsum_eq h ht
  have hA_ev (x : ι) : ∃ k, ∀ᶠ t in 𝓝 x, A t = Asum k t := by
    by_cases hx : ∃ y, x < y
    · obtain ⟨y, hxy⟩ := hx
      obtain ⟨k, hk⟩ : ∃ k, y ≤ U k := ⟨κ y, hκ y⟩
      exact ⟨k, by filter_upwards [Iio_mem_nhds hxy] with t ht using hA_eq (ht.le.trans hk)⟩
    · push Not at hx
      obtain ⟨k, hk⟩ : ∃ k, x ≤ U k := ⟨κ x, hκ x⟩
      exact ⟨k, .of_forall fun t ↦ hA_eq ((hx t).trans hk)⟩
  have hA_pred : IsStronglyPredictable 𝓕 A := by
    refine stronglyMeasurable_of_tendsto atTop (f := fun k ↦ Function.uncurry (Asum k))
      hAsum_pred (tendsto_pi_nhds.2 fun p ↦ ?_)
    refine tendsto_atTop_of_eventually_const (i₀ := κ p.1) fun k hk ↦ ?_
    exact congrFun (hAsum_eq hk (hκ p.1)) p.2
  have hA_cadlag (ω : Ω) : IsCadlag (A · ω) := by
    refine ⟨fun x ↦ ?_, fun x ↦ ?_⟩
    · obtain ⟨k, hk⟩ := hA_ev x
      refine ((hAsum_cadlag k ω).right_continuous x).congr_of_eventuallyEq ?_
        (congrFun (hk.self_of_nhds) ω)
      filter_upwards [hk.filter_mono nhdsWithin_le_nhds] with t ht using congrFun ht ω
    · obtain ⟨k, hk⟩ := hA_ev x
      obtain ⟨l, hl⟩ := (hAsum_cadlag k ω).left_limit x
      refine ⟨l, hl.congr' ?_⟩
      filter_upwards [hk.filter_mono nhdsWithin_le_nhds] with t ht using (congrFun ht ω).symm
  have hA_mono (ω : Ω) : Monotone (A · ω) := by
    intro s t hst
    obtain ⟨k, hk⟩ : ∃ k, t ≤ U k := ⟨κ t, hκ t⟩
    simp only [hA_eq hk, hA_eq (hst.trans hk)]
    exact hAsum_mono k ω hst
  -- the martingale part coincides locally with a finite sum of martingales
  let L : ℕ → ι → Ω → ℝ := fun k ↦ (fun _ ↦ S ⊥) + ∑ n ∈ Finset.range k, N n
  have hL (k : ℕ) : Martingale (L k) 𝓕 P := by
    refine (martingale_const_fun 𝓕 P (hs.stronglyAdapted ⊥) (hs.integrable ⊥)).add ?_
    induction k with
    | zero => simpa using martingale_zero ℝ 𝓕 P
    | succ k ih => exact Finset.sum_range_succ (N ·) k ▸ ih.add (hN k)
  have hSA_eq {k : ℕ} {t : ι} (ht : t ≤ U k) : (S - A) t = L k t := by
    have h_sum : ∑ n ∈ Finset.range k, (N n t + B n t) = S t - S ⊥ := by
      simp_rw [← hSNB]
      rw [Finset.sum_range_sub (fun n ↦ S (min t (U n)))]
      simp [U, min_eq_left ht]
    simp only [Pi.sub_apply, hA_eq ht, L, Asum, Pi.add_apply, Finset.sum_apply]
    rw [Finset.sum_add_distrib] at h_sum
    have h_S : S t = S ⊥ + (∑ n ∈ Finset.range k, N n t + ∑ n ∈ Finset.range k, B n t) := by
      rw [h_sum]
      exact (add_sub_cancel _ _).symm
    conv_lhs => rw [h_S]
    rw [← add_assoc, add_sub_cancel_right]
  refine ⟨S - A, A, (sub_add_cancel S A).symm, ⟨?_, fun s t hst ↦ ?_⟩,
    fun ω ↦ (hc ω).sub (hA_cadlag ω), hA_pred, hA_cadlag, hA_mono, ?_⟩
  · exact fun t ↦ (hs.stronglyAdapted t).sub (hA_pred.stronglyAdapted t)
  · obtain ⟨k, hk⟩ : ∃ k, t ≤ U k := ⟨κ t, hκ t⟩
    rw [hSA_eq hk, hSA_eq (hst.trans hk)]
    exact (hL k).condExp_ae_eq hst
  · have h : A ⊥ = Asum 0 ⊥ := hA_eq (k := 0) (t := ⊥) le_rfl
    simp [h, Asum]

end ProbabilityTheory
