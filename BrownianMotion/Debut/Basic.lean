/-
Copyright (c) 2025 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli
-/

import BrownianMotion.Choquet.Capacity
import BrownianMotion.StochasticIntegral.Predictable
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Process.HittingTime

/-!
This file contains the basic definitions and properties of the debut of a set.


## Implementation notes

We follow the implementation of hitting times in `Mathlib.Probability.Process.HittingTime`.
The debut has values in `WithTop ι`, ensuring that it is always well-defined.
-/

open Filter
open scoped Topology

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

open scoped Classical in
/-- The debut of a set `E ⊆ T × Ω` after `n` is the random variable that gives the smallest
`t ≥ n` such that `(t, ω) ∈ E` for a given `ω`. -/
noncomputable def debut [Preorder ι] [InfSet ι] (E : Set (ι × Ω)) (n : ι) : Ω → WithTop ι :=
  hittingAfter (fun t ω ↦ (t, ω)) E n

open scoped Classical in
lemma debut_eq_ite [Preorder ι] [InfSet ι] (E : Set (ι × Ω)) (n : ι) :
    debut E n = fun ω ↦ if ∃ t ≥ n, (t, ω) ∈ E then
      ((sInf {t ≥ n | (t, ω) ∈ E} : ι) : WithTop ι) else ⊤ := rfl

lemma debut_eq_hittingAfter_indicator [Preorder ι] [InfSet ι] (E : Set (ι × Ω))
    [∀ t ω, Decidable ((t, ω) ∈ E)] (n : ι) :
    debut E n = hittingAfter (fun t ω ↦ if (t, ω) ∈ E then 1 else 0) {1} n := by
  ext ω
  simp only [debut, hittingAfter]
  split_ifs <;> simp <;> grind

lemma hittingAfter_eq_debut [Preorder ι] [InfSet ι] {β : Type*} (u : ι → Ω → β)
    (s : Set β) (n : ι) :
    hittingAfter u s n = debut {p : ι × Ω | u p.1 p.2 ∈ s} n := rfl

section Debut

/-- The debut of the empty set is the constant function that returns `m`. -/
@[simp]
lemma debut_empty [Preorder ι] [InfSet ι] (n : ι) : debut (∅ : Set (ι × Ω)) n = fun _ ↦ ⊤ :=
  hittingAfter_empty n

@[simp]
lemma debut_univ [ConditionallyCompleteLattice ι] (n : ι) :
    debut (.univ : Set (ι × Ω)) n = fun _ ↦ (n : WithTop ι) := hittingAfter_univ n

open scoped Classical in
@[simp]
lemma debut_prod [Preorder ι] [InfSet ι] (n : ι) (I : Set ι) (A : Set Ω) :
    debut (I ×ˢ A) n = fun ω ↦ if .Ici n ∩ I ≠ ∅ then
        if ω ∈ A then ((sInf (.Ici n ∩ I) : ι) : WithTop ι) else ⊤
      else ⊤ := by
  ext ω
  split_ifs with hI hω
  · simp only [debut_eq_ite, Set.mem_prod, hω, and_true]
    convert if_pos (Set.nonempty_iff_ne_empty.mpr hI) using 1
  · simp [debut_eq_ite, hω]
  · simp only [ne_eq, Decidable.not_not] at hI
    refine if_neg ?_
    simp only [Set.mem_prod, not_exists, not_and]
    exact fun i hni hiI _ ↦ Set.notMem_empty i (hI ▸ ⟨hni, hiI⟩)

lemma debut_prod_univ [Preorder ι] [InfSet ι] (n : ι) (I : Set ι) [Decidable (Set.Ici n ∩ I ≠ ∅)] :
    debut (I ×ˢ (.univ : Set Ω)) n = fun _ ↦ if .Ici n ∩ I ≠ ∅ then
      ((sInf (.Ici n ∩ I) : ι) : WithTop ι) else ⊤ := by simp

lemma debut_univ_prod [ConditionallyCompleteLattice ι] (n : ι) (A : Set Ω) [DecidablePred (· ∈ A)] :
    debut ((.univ : Set ι) ×ˢ A) n = fun ω ↦ if ω ∈ A then (n : WithTop ι) else ⊤ := by
  rw [debut_eq_ite]
  ext ω
  split_ifs with hi hω hω
  · simp only [Set.mem_prod, Set.mem_univ, hω, and_true, WithTop.coe_eq_coe]
    exact csInf_Ici
  · simp_all
  · simp only [Set.mem_prod, Set.mem_univ, hω, and_true, not_exists] at hi
    simpa only [le_refl, not_true_eq_false] using hi n
  · simp_all

lemma debut_anti [ConditionallyCompleteLinearOrder ι] (n : ι) : Antitone (debut (Ω := Ω) · n) :=
  hittingAfter_anti _ n

section Inequalities

variable [ConditionallyCompleteLinearOrder ι] {E : Set (ι × Ω)} {n t : ι} {ω : Ω}

lemma notMem_of_lt_debut (ht : t < debut E n ω) (hnt : n ≤ t) : (t, ω) ∉ E :=
  notMem_of_lt_hittingAfter ht hnt

lemma debut_eq_top_iff : debut E n ω = ⊤ ↔ ∀ t ≥ n, (t, ω) ∉ E := hittingAfter_eq_top_iff

lemma le_debut (ω : Ω) : n ≤ debut E n ω := le_hittingAfter ω

lemma debut_mem_set [WellFoundedLT ι] (h : ∃ t ≥ n, (t, ω) ∈ E) :
    ((debut E n ω).untopA, ω) ∈ E := hittingAfter_mem_set h

lemma debut_mem_set_of_ne_top [WellFoundedLT ι] (h : debut E n ω ≠ ⊤) :
    ((debut E n ω).untopA, ω) ∈ E := hittingAfter_mem_set_of_ne_top h

lemma debut_le_of_mem (ht : n ≤ t) (h_mem : (t, ω) ∈ E) :
    debut E n ω ≤ t := hittingAfter_le_of_mem ht h_mem

-- todo: replace `hittingAfter_lt_iff` with this
lemma hittingAfter_lt_iff' {Ω β ι : Type*} [ConditionallyCompleteLinearOrder ι]
    {u : ι → Ω → β} {s : Set β} {n : ι} {ω : Ω} {i : ι} :
    hittingAfter u s n ω < i ↔ ∃ j ∈ Set.Ico n i, u j ω ∈ s := by
  constructor <;> intro h'
  · have h_top : hittingAfter u s n ω ≠ ⊤ := fun h ↦ by simp [h] at h'
    have h_top' : ∃ j, n ≤ j ∧ u j ω ∈ s := by
      rw [ne_eq, hittingAfter_eq_top_iff] at h_top
      push_neg at h_top
      exact h_top
    have h_le := le_hittingAfter (u := u) (s := s) (n := n) ω
    rw [hittingAfter, if_pos h_top'] at h'
    norm_cast at h'
    rw [csInf_lt_iff] at h'
    rotate_left
    · exact ⟨n, by simp [mem_lowerBounds]; grind⟩
    · exact h_top'
    simp only [Set.mem_setOf_eq] at h'
    obtain ⟨j, hj₁, hj₂⟩ := h'
    refine ⟨j, ⟨hj₁.1, hj₂⟩, hj₁.2⟩
  · obtain ⟨j, hj₁, hj₂⟩ := h'
    refine lt_of_le_of_lt ?_ (mod_cast hj₁.2 : (j : WithTop ι) < i)
    exact hittingAfter_le_of_mem hj₁.1 hj₂

lemma debut_le_iff [WellFoundedLT ι] : debut E n ω ≤ t ↔ ∃ j ∈ Set.Icc n t, (j, ω) ∈ E :=
  hittingAfter_le_iff

lemma debut_lt_iff : debut E n ω < t ↔ ∃ j ∈ Set.Ico n t, (j, ω) ∈ E :=
  hittingAfter_lt_iff'

lemma debut_mono (E : Set (ι × Ω)) (ω : Ω) : Monotone (debut E · ω) := hittingAfter_apply_mono _ _ _

end Inequalities

-- TODO: this may be put in a separate file, maybe in the file where ProgMeasurable is?
/- TODO: can we find some condition equivalent to this definition that is easier to state, maybe
something that does not involde the indicator function and only uses E as a set? Maybe there is a
σ algebra over `ι × Ω` such that ProgMeasurableSet is equivalent to being measurable with respect
to that σ-algebra?
maybe something like (mι : MeasurableSpace ι) [BorelSpace ι]
`∀ t, MeasurableSet[mι.prod (f t)] (E ∩ Set.Iic t ×ˢ Ω)`? I'm not completely sure this is actually
equivalent, but if I stated the lemma `MeasureTheory.Approximation.of_mem_prod_borel` correctly
this should be enough to prove the theorem below.
before changing this definition it may be worth it to begin the proof of `debut.isStoppingTime`
to identify exactly what is needed, maybe in the end we do not even need to define the concpet of
progressively measurable set, but we can just add the necessary hypothesis manually. -/

/-- A set `E : Set ι × Ω` is *Progressively measurable* with respect to a filtration `f` if the
indicator function of `E` is a progressively measurable process with respect to `f`. -/
def ProgMeasurableSet [Preorder ι] [MeasurableSpace ι] (E : Set (ι × Ω)) (𝓕 : Filtration ι mΩ) :=
  ProgMeasurable 𝓕 (E.indicator fun _ ↦ 1).curry

lemma ProgMeasurableSet.measurableSet_prod [Preorder ι] [MeasurableSpace ι]
    {E : Set (ι × Ω)} {𝓕 : Filtration ι mΩ} (hE : ProgMeasurableSet E 𝓕) (t : ι) :
    MeasurableSet[Subtype.instMeasurableSpace.prod (𝓕 t)]
      {p : Set.Iic t × Ω | ((p.1 : ι), p.2) ∈ E} := by
  rw [← measurable_indicator_const_iff (b := 1)]
  exact (hE t).measurable

lemma ProgMeasurableSet.measurableSet_inter_Iic [Preorder ι] {mι : MeasurableSpace ι}
    {E : Set (ι × Ω)} {𝓕 : Filtration ι mΩ} (hE : ProgMeasurableSet E 𝓕) (t : ι) :
    MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Iic t ×ˢ .univ)) := by
  have h_prod := hE.measurableSet_prod t
  sorry

lemma ProgMeasurableSet.measurableSet_inter_Iio [LinearOrder ι] {mι : MeasurableSpace ι}
    {E : Set (ι × Ω)} {𝓕 : Filtration ι mΩ} (hE : ProgMeasurableSet E 𝓕) (t : ι) :
    MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Iio t ×ˢ .univ)) := by
  -- write Iio as a countable union of Iic and use the previous lemma
  sorry

@[gcongr]
lemma MeasurableSpace.prod_mono {mι : MeasurableSpace ι} {mι' : MeasurableSpace ι}
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω}
    (h₁ : mι ≤ mι') (h₂ : mΩ ≤ mΩ') :
    mι.prod mΩ ≤ mι'.prod mΩ' := by
  simp only [MeasurableSpace.prod, sup_le_iff]
  refine ⟨le_sup_of_le_left ?_, le_sup_of_le_right ?_⟩
  · rw [MeasurableSpace.comap_le_iff_le_map]
    exact h₁.trans MeasurableSpace.le_map_comap
  · rw [MeasurableSpace.comap_le_iff_le_map]
    exact h₂.trans MeasurableSpace.le_map_comap

lemma ProgMeasurableSet.measurableSet_inter_Ico [LinearOrder ι] {mι : MeasurableSpace ι}
    {E : Set (ι × Ω)} {𝓕 : Filtration ι mΩ} (hE : ProgMeasurableSet E 𝓕) (s t : ι) :
    MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Ico s t ×ˢ .univ)) := by
  rcases le_total t s with h_ts | h_st
  · simp [h_ts]
  -- write `Ico s t` as `Iio t \ Iio s` and use the previous lemmas
  have h_meas_s : MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Iio s ×ˢ .univ)) := by
    have hs := hE.measurableSet_inter_Iio s
    have h_le : mι.prod (𝓕 s) ≤ mι.prod (𝓕 t) := MeasurableSpace.prod_mono le_rfl (𝓕.mono h_st)
    exact h_le _ hs
  have h_meas_t := hE.measurableSet_inter_Iio t
  convert h_meas_t.diff h_meas_s using 1
  ext
  simp
  grind

lemma ProgMeasurableSet.measurableSet_debut_lt
    [MeasurableSpace ι] [ConditionallyCompleteLinearOrder ι] [OrderBot ι] [StandardBorelSpace ι]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration ι mΩ} (h𝓕 : 𝓕.HasUsualConditions P)
    {E : Set (ι × Ω)} (hE : ProgMeasurableSet E 𝓕) (n s : ι) :
    MeasurableSet[𝓕 s] {ω | debut E n ω < s} := by
  have h_eq_fst : {ω | debut E n ω < s} = Prod.snd '' (E ∩ (Set.Ico n s ×ˢ .univ)) := by
    simp_rw [debut_lt_iff]
    ext
    simp
    grind
  rw [h_eq_fst]
  refine NullMeasurableSet.measurable_of_complete (m0 := 𝓕 s) (μ := P.trim (𝓕.le s)) ?_
  refine MeasurableSet.nullMeasurableSet_snd ?_ (P.trim (𝓕.le s))
  exact hE.measurableSet_inter_Ico n s

/-- **Debut Theorem**: The debut of a progressively measurable set `E` is a stopping time. -/
theorem isStoppingTime_debut [MeasurableSpace ι] [ConditionallyCompleteLinearOrder ι] [OrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι] [BorelSpace ι]
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ι mΩ} (h𝓕 : 𝓕.HasUsualConditions P)
    {E : Set (ι × Ω)} (hE : ProgMeasurableSet E 𝓕) (n : ι) :
    IsStoppingTime 𝓕 (debut E n) := by
  intro t
  -- case on whether `t` is isolated on the right or not
  by_cases ht_gt : (𝓝[>] t).NeBot
  swap
  -- if it's isolated then `{debut ≤} = {debut <} ∪ {(t, ω) ∈ E}`
  · sorry
  -- now `t` is a limit point on the right
  obtain ⟨s, hs_gt, hs_tendsto⟩ : ∃ s : ℕ → ι, (∀ n, t < s n) ∧ Tendsto s atTop (𝓝 t) := by
    have h_freq : ∃ᶠ x in 𝓝[>] t, t < x :=
      Eventually.frequently <| eventually_nhdsWithin_of_forall fun _ hx ↦ hx
    have := exists_seq_forall_of_frequently h_freq
    simp_rw [tendsto_nhdsWithin_iff] at this
    obtain ⟨s, ⟨hs_tendsto, _⟩, hs_gt⟩ := this
    exact ⟨s, hs_gt, hs_tendsto⟩
  suffices ∀ m : ℕ, MeasurableSet[𝓕 (s m)] {ω | debut E n ω < s m} by
    have h_eq_iInter : {ω | debut E n ω ≤ t} = ⋂ m, {ω | debut E n ω < s m} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      refine ⟨fun h_le m ↦ h_le.trans_lt (mod_cast (hs_gt m)), fun h_lt ↦ ?_⟩
      refine le_of_forall_gt fun u hu ↦ ?_
      obtain ⟨i, hi⟩ : ∃ i, s i < u := by
        refine Eventually.exists (f := atTop) ?_
        have hs_tendsto' : Tendsto (fun n ↦ (s n : WithTop ι)) atTop (𝓝 (t : WithTop ι)) :=
          WithTop.continuous_coe.continuousAt.tendsto.comp hs_tendsto
        exact hs_tendsto'.eventually_lt_const hu
      exact (h_lt i).trans hi
    rw [h_eq_iInter]
    have h𝓕_eq_iInf : 𝓕 t = ⨅ m, 𝓕 (s m) := by
      have ht_cont : 𝓕 t = 𝓕.rightCont t := by
        congr
        exact (h𝓕.toIsRightContinuous (μ := P)).eq.symm
      rw [ht_cont, Filtration.rightCont_eq_of_neBot_nhdsGT]
      sorry
    rw [h𝓕_eq_iInf]
    simp only [MeasurableSpace.measurableSet_sInf, Set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff]
    intro k
    have h_eq_k : ⋂ m, {ω | debut E n ω < s m} =
        ⋂ (m) (hm : s m ≤ s k), {ω | debut E n ω < s m} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h m _ ↦ h m, fun h m ↦ ?_⟩
      rcases le_total (s m) (s k) with hmk | hkm
      · exact h m hmk
      · exact (h k le_rfl).trans_le (mod_cast hkm)
    rw [h_eq_k]
    refine MeasurableSet.iInter fun m ↦ MeasurableSet.iInter fun hm ↦ ?_
    exact 𝓕.mono hm _ (this m)
  exact fun _ ↦ hE.measurableSet_debut_lt h𝓕 n _

end Debut

section HittingTime

lemma _root_.MeasurableSet.progMeasurableSet_preimage
    [MeasurableSpace ι] [ConditionallyCompleteLinearOrder ι]
    [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι] [BorelSpace ι]
    {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {𝓕 : Filtration ι mΩ}
    {X : ι → Ω → β} (hX : ProgMeasurable 𝓕 X) {s : Set β} (hs : MeasurableSet s) :
    ProgMeasurableSet (X.uncurry ⁻¹' s) 𝓕 :=
  sorry

/-- The hitting time of a measurable set by a progressively measurable process for a filtration
satisfying the usual conditions is a stopping time. -/
theorem isStoppingTime_hittingAfter' [MeasurableSpace ι] [ConditionallyCompleteLinearOrder ι]
    [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι] [BorelSpace ι]
    {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration ι mΩ} (h𝓕 : 𝓕.HasUsualConditions P)
    {X : ι → Ω → β} (hX : ProgMeasurable 𝓕 X) {s : Set β} (hs : MeasurableSet s) (n : ι) :
    IsStoppingTime 𝓕 (hittingAfter X s n) := by
  rw [hittingAfter_eq_debut]
  refine isStoppingTime_debut h𝓕 ?_ n
  exact hs.progMeasurableSet_preimage hX

end HittingTime

end MeasureTheory
