/-
Copyright (c) 2025 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli, Rémy Degenne
-/
module

public import BrownianMotion.Choquet.Capacity
public import BrownianMotion.StochasticIntegral.Predictable
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Martingale.BorelCantelli

/-!
# The debut of a set

The debut after `n` of a set `E ⊆ ι × Ω` is the random time `ω ↦ inf {t ≥ n | (t, ω) ∈ E}`.

## Main definitions

* `MeasureTheory.debut E n`: the debut of `E` after `n`.
* `MeasureTheory.ProgMeasurableSet E 𝓕`: the set `E` is progressively measurable for the
  filtration `𝓕`.
* `MeasureTheory.leastGT f r`: the first time that the process `f` is greater than `r`.

## Main statements

* `MeasureTheory.IsPavingAnalytic.nullMeasurable_debut`: the debut of an analytic set is
  null-measurable with respect to any s-finite measure.
* `MeasureTheory.isStoppingTime_debut`: **debut theorem**. The debut of a progressively measurable
  set is a stopping time, for a filtration that is right-continuous and complete with respect to an
  s-finite measure.
* `MeasureTheory.IsStronglyProgressive.isStoppingTime_hittingAfter`: the hitting time of a
  measurable set by a progressively measurable process is a stopping time, under the same
  assumptions on the filtration.

## Implementation notes

We follow the implementation of hitting times in `Mathlib.Probability.Process.HittingTime`.
The debut has values in `WithTop ι`, ensuring that it is always well-defined.

## References

* [S. He, J. Wang and J. Yan, *Semimartingale theory and stochastic calculus*][he2019semimartingale]
-/

@[expose] public section

open Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory

instance : MeasurableInf₂ (WithTop ℝ≥0) := inferInstanceAs (MeasurableInf₂ ℝ≥0∞)

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Completeness of a filtration only depends on the null sets of the measure, and `P.toFinite` has
the same null sets as `P`. -/
instance Filtration.IsComplete.toFinite [PartialOrder ι] {𝓕 : Filtration ι mΩ} [SFinite P]
    [𝓕.IsComplete P] :
    𝓕.IsComplete P.toFinite :=
  ⟨fun _ hs t ↦ Filtration.IsComplete.measurableSet_of_null (absolutelyContinuous_toFinite P hs) t⟩

/-- The debut of a set `E ⊆ ι × Ω` after `n` is the random variable that gives the smallest
`t ≥ n` such that `(t, ω) ∈ E` for a given `ω`, or `⊤` if there is no such `t`. -/
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

/-- The debut of the empty set is the constant function that returns `⊤`. -/
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
    exact ite_eq_left (Set.nonempty_iff_ne_empty.mpr hI)
  · simp [debut_eq_ite, hω]
  · simp only [ne_eq, Decidable.not_not] at hI
    refine ite_eq_right ?_
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

lemma debut_ne_top_iff : debut E n ω ≠ ⊤ ↔ ∃ t ≥ n, (t, ω) ∈ E := by simp [debut_eq_top_iff]

lemma le_debut (ω : Ω) : n ≤ debut E n ω := le_hittingAfter ω

lemma debut_mem_set [WellFoundedLT ι] (h : ∃ t ≥ n, (t, ω) ∈ E) :
    ((debut E n ω).untopA, ω) ∈ E := hittingAfter_mem_set h

lemma debut_mem_set_of_ne_top [WellFoundedLT ι] (h : debut E n ω ≠ ⊤) :
    ((debut E n ω).untopA, ω) ∈ E := hittingAfter_mem_set_of_ne_top h

lemma debut_le_of_mem (ht : n ≤ t) (h_mem : (t, ω) ∈ E) :
    debut E n ω ≤ t := hittingAfter_le_of_mem ht h_mem

lemma debut_le_iff [WellFoundedLT ι] : debut E n ω ≤ t ↔ ∃ j ∈ Set.Icc n t, (j, ω) ∈ E :=
  hittingAfter_le_iff

lemma debut_lt_iff : debut E n ω < t ↔ ∃ j ∈ Set.Ico n t, (j, ω) ∈ E :=
  hittingAfter_lt_iff

lemma debut_mono (E : Set (ι × Ω)) (ω : Ω) : Monotone (debut E · ω) := hittingAfter_apply_mono _ _ _

lemma debut_ne_top_iff_of_isBot (hn : IsBot n) : debut E n ω ≠ ⊤ ↔ ω ∈ Prod.snd '' E := by
  simp [debut_ne_top_iff, hn _]

lemma setOf_debut_ne_top_eq_of_isBot (hn : IsBot n) : {ω | debut E n ω ≠ ⊤} = Prod.snd '' E :=
  Set.ext fun _ ↦ debut_ne_top_iff_of_isBot hn

variable (E n t) in
lemma setOf_debut_lt_eq : {ω | debut E n ω < t} = Prod.snd '' (E ∩ (Set.Ico n t ×ˢ .univ)) := by
  ext
  simp [debut_lt_iff]
  grind

variable (E n) in
lemma setOf_debut_ne_top_eq :
    {ω | debut E n ω ≠ ⊤} = Prod.snd '' (E ∩ (Set.Ici n ×ˢ .univ)) := by
  ext
  simp [debut_ne_top_iff]
  grind

-- TODO: unused
lemma measure_debut_ne_top_mono {A B : Set (ι × Ω)} (hAB : A ⊆ B) (u : ι) :
    P {ω | debut A u ω ≠ ⊤} ≤ P {ω | debut B u ω ≠ ⊤} := by
  refine measure_mono fun ω ↦ ?_
  simp only [ne_eq, Set.mem_ofPred_eq]
  refine fun hωA hωs ↦ hωA ?_
  rw [eq_top_iff, ← hωs]
  exact debut_anti _ hAB ω

end Inequalities

lemma debut_mem_of_isClosed {𝓧 ι : Type*} [TopologicalSpace ι] [ConditionallyCompleteLinearOrder ι]
    [OrderTopology ι] [FirstCountableTopology ι]
    {s : Set (ι × 𝓧)} {ω : 𝓧} {n : ι}
    (hs : IsClosed {t | n ≤ t ∧ (t, ω) ∈ s}) (hω : debut s n ω ≠ ⊤) :
    ((debut s n ω).untopA, ω) ∈ s := by
  obtain ⟨t₀, ht₀⟩ : ∃ t ≥ n, (t, ω) ∈ s := debut_ne_top_iff.mp hω
  obtain ⟨u, _, hu_tendso, hu_mem⟩ : ∃ u : ℕ → ι, Antitone u ∧
      Tendsto u atTop (𝓝 ((debut s n ω).untopA)) ∧ (∀ i, n ≤ u i ∧ (u i, ω) ∈ s) := by
    simp only [debut_eq_ite, ge_iff_le]
    rw [ite_eq_left (debut_ne_top_iff.mp hω)]
    have : ((sInf {t : ι |  n ≤ t ∧ (t, ω) ∈ s} : ι) : WithTop ι).untopA =
        sInf {t | n ≤ t ∧ (t, ω) ∈ s} := by
      rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [this]
    exact exists_seq_tendsto_sInf (S := {t | n ≤ t ∧ (t, ω) ∈ s}) (debut_ne_top_iff.mp hω)
      ⟨n, mem_lowerBounds.mpr (by grind)⟩
  suffices (debut s n ω).untopA ∈ {t | n ≤ t ∧ (t, ω) ∈ s} from this.2
  exact IsClosed.mem_of_tendsto (f := u) hs hu_tendso (.of_forall hu_mem)

-- TODO: change the name to reflect the `IsStronglyProgressive` new name
/-- A set `E : Set ι × Ω` is progressively measurable with respect to a filtration `𝓕` if the
indicator function of `E` is a progressively measurable process with respect to `𝓕`. -/
def ProgMeasurableSet [Preorder ι] [MeasurableSpace ι] (E : Set (ι × Ω)) (𝓕 : Filtration ι mΩ) :=
  IsStronglyProgressive 𝓕 (E.indicator fun _ ↦ 1).curry

lemma ProgMeasurableSet.measurableSet_prod [Preorder ι] [MeasurableSpace ι]
    {E : Set (ι × Ω)} {𝓕 : Filtration ι mΩ} (hE : ProgMeasurableSet E 𝓕) (t : ι) :
    MeasurableSet[Subtype.instMeasurableSpace.prod (𝓕 t)]
      {p : Set.Iic t × Ω | ((p.1 : ι), p.2) ∈ E} := by
  rw [← measurable_indicator_const_iff (b := 1)]
  exact (hE t).measurable

lemma ProgMeasurableSet.measurableSet_inter_Iic [Preorder ι]
    [TopologicalSpace ι] [ClosedIicTopology ι] {mι : MeasurableSpace ι} [OpensMeasurableSpace ι]
    {E : Set (ι × Ω)} {𝓕 : Filtration ι mΩ} (hE : ProgMeasurableSet E 𝓕) (t : ι) :
    MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Iic t ×ˢ .univ)) := by
  have h_prod := hE.measurableSet_prod t
  have : (E ∩ Set.Iic t ×ˢ Set.univ) =
      (Prod.map ((↑) : Set.Iic t → ι) id) '' {p : Set.Iic t × Ω | ((p.1 : ι), p.2) ∈ E} := by
    ext; simp; grind
  rw [this]
  refine (@MeasurableEmbedding.measurableSet_image _ _ _ (Subtype.instMeasurableSpace.prod (𝓕 t))
    (mι.prod (𝓕 t)) _ ?_).mpr h_prod
  refine MeasurableEmbedding.prodMap ?_ .id
  exact MeasurableEmbedding.subtype_coe measurableSet_Iic

lemma ProgMeasurableSet.measurableSet_inter_Iio [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [FirstCountableTopology ι] [OrderTopology ι]
    {mι : MeasurableSpace ι} [OpensMeasurableSpace ι]
    {E : Set (ι × Ω)} {𝓕 : Filtration ι mΩ} (hE : ProgMeasurableSet E 𝓕) (t : ι) :
    MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Iio t ×ˢ .univ)) := by
  by_cases ht : 𝓝[<] t = ⊥
  · rw [nhdsLT_eq_bot_iff] at ht
    cases ht with
    | inl ht =>
      have h_empty : Set.Iio t = ∅ := by ext x; simp [ht x]
      simp [h_empty]
    | inr ht =>
      obtain ⟨s, hst, hs⟩ := ht
      simp only [not_lt] at hs
      have h_eq_Iic : Set.Iio t = Set.Iic s := by
        ext x
        simp only [Set.mem_Iio, Set.mem_Iic]
        rcases le_or_gt x s <;> grind
      rw [h_eq_Iic]
      have hs := hE.measurableSet_inter_Iic s
      have h_le : mι.prod (𝓕 s) ≤ mι.prod (𝓕 t) := MeasurableSpace.prod_mono le_rfl (𝓕.mono hst.le)
      exact h_le _ hs
  have : (𝓝[<] t).NeBot := ⟨ht⟩
  -- write Iio as a countable union of Iic and use the previous lemma
  obtain ⟨s, hs_gt, hs_tendsto⟩ : ∃ s : ℕ → ι, (∀ n, s n < t) ∧ Tendsto s atTop (𝓝 t) := by
    have h_freq : ∃ᶠ x in 𝓝[<] t, x < t :=
      Eventually.frequently <| eventually_nhdsWithin_of_forall fun _ hx ↦ hx
    have := exists_seq_forall_of_frequently h_freq
    simp_rw [tendsto_nhdsWithin_iff] at this
    obtain ⟨s, ⟨hs_tendsto, _⟩, hs_gt⟩ := this
    exact ⟨s, hs_gt, hs_tendsto⟩
  have h_iUnion : ⋃ i, Set.Iic (s i) = Set.Iio t :=
    iUnion_Iic_eq_Iio_of_lt_of_tendsto hs_gt hs_tendsto
  rw [← h_iUnion, Set.iUnion_prod_const, Set.inter_iUnion]
  refine MeasurableSet.iUnion fun i ↦ ?_
  have hs := hE.measurableSet_inter_Iic (s i)
  have h_le : mι.prod (𝓕 (s i)) ≤ mι.prod (𝓕 t) := MeasurableSpace.prod_mono le_rfl
    (𝓕.mono (hs_gt _).le)
  exact h_le _ hs

lemma ProgMeasurableSet.measurableSet_inter_Ico [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [FirstCountableTopology ι] [OrderTopology ι]
    {mι : MeasurableSpace ι} [OpensMeasurableSpace ι]
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

lemma ProgMeasurableSet.measurableSet_inter_Icc [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [FirstCountableTopology ι] [OrderTopology ι]
    {mι : MeasurableSpace ι} [OpensMeasurableSpace ι]
    {E : Set (ι × Ω)} {𝓕 : Filtration ι mΩ} (hE : ProgMeasurableSet E 𝓕) (s t : ι) :
    MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Icc s t ×ˢ .univ)) := by
  rcases le_or_gt s t with h_st | h_ts
  swap; · simp [h_ts]
  -- write `Icc s t` as `Iic t \ Iio s` and use the previous lemmas
  have h_meas_s : MeasurableSet[mι.prod (𝓕 t)] (E ∩ (Set.Iio s ×ˢ .univ)) := by
    have hs := hE.measurableSet_inter_Iio s
    have h_le : mι.prod (𝓕 s) ≤ mι.prod (𝓕 t) := MeasurableSpace.prod_mono le_rfl (𝓕.mono h_st)
    exact h_le _ hs
  convert (hE.measurableSet_inter_Iic t).diff h_meas_s using 1
  ext
  simp
  grind

lemma ProgMeasurableSet.measurableSet_preimage_prodMk [Preorder ι] [MeasurableSpace ι]
    {𝓕 : Filtration ι mΩ} {E : Set (ι × Ω)} (hE : ProgMeasurableSet E 𝓕) (t : ι) :
    MeasurableSet[𝓕 t] {ω | (t, ω) ∈ E} :=
  (hE.measurableSet_prod t).preimage
    (@measurable_prodMk_left _ _ _ (𝓕 t) (⟨t, le_rfl⟩ : Set.Iic t))

lemma IsPavingAnalytic.nullMeasurableSet_debut_lt {ι : Type}
    [ConditionallyCompleteLinearOrder ι] [DenselyOrdered ι]
    [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [PolishSpace ι] [BorelSpace ι]
    {P : Measure Ω} [SFinite P] {E : Set (ι × Ω)}
    (hE : IsPavingAnalytic {t | MeasurableSet t} E) (n s : ι) :
    NullMeasurableSet {ω | debut E n ω < s} P := by
  rw [setOf_debut_lt_eq]
  refine IsPavingAnalytic.nullMeasurableSet_snd ?_ P
  exact hE.inter <| isPavingAnalytic_of_mem (measurableSet_Ico.prod .univ)

lemma _root_.MeasurableSet.nullMeasurableSet_debut_lt
    [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [ClosedIciTopology ι] [MeasurableSpace ι] [PolishSpace ι] [BorelSpace ι]
    {P : Measure Ω} [SFinite P]
    {E : Set (ι × Ω)} (hE : MeasurableSet E) (n s : ι) :
    NullMeasurableSet {ω | debut E n ω < s} P := by
  rw [setOf_debut_lt_eq]
  refine MeasurableSet.nullMeasurableSet_snd ?_ P
  exact hE.inter (MeasurableSet.prod measurableSet_Ico .univ)

lemma _root_.MeasurableSet.measurableSet_debut_lt
    [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [ClosedIciTopology ι] [MeasurableSpace ι] [PolishSpace ι] [BorelSpace ι]
    (P : Measure Ω) [SFinite P] [P.IsComplete]
    {E : Set (ι × Ω)} (hE : MeasurableSet E) (n s : ι) :
    MeasurableSet {ω | debut E n ω < s} :=
  NullMeasurableSet.measurable_of_complete (μ := P) (hE.nullMeasurableSet_debut_lt n s)

/-- The debut of an analytic set is universally measurable: it is null-measurable
with respect to any s-finite measure. -/
lemma IsPavingAnalytic.nullMeasurable_debut {ι : Type}
    [ConditionallyCompleteLinearOrder ι] [DenselyOrdered ι]
    [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [PolishSpace ι] [BorelSpace ι]
    {P : Measure Ω} [SFinite P] {s : Set (ι × Ω)}
    (hs : IsPavingAnalytic {t | MeasurableSet t} s) (u : ι) :
    NullMeasurable (debut s u) P := by
  refine nullMeasurable_of_Iio fun x ↦ ?_
  cases x with
  | top =>
    -- `{debut < ⊤}` is the projection of `s ∩ (Ici u ×ˢ univ)`
    simp_rw [Set.preimage, Set.mem_Iio, lt_top_iff_ne_top, setOf_debut_ne_top_eq]
    exact IsPavingAnalytic.nullMeasurableSet_snd
      (hs.inter (isPavingAnalytic_of_mem (measurableSet_Ici.prod .univ))) P
  | coe r => exact hs.nullMeasurableSet_debut_lt u r

lemma ProgMeasurableSet.measurableSet_debut_lt
    [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [PolishSpace ι] [BorelSpace ι]
    (P : Measure Ω) [SFinite P] {𝓕 : Filtration ι mΩ} [𝓕.IsComplete P]
    {E : Set (ι × Ω)} (hE : ProgMeasurableSet E 𝓕) (n s : ι) :
    MeasurableSet[𝓕 s] {ω | debut E n ω < s} := by
  rw [setOf_debut_lt_eq]
  -- the set is null-measurable for the finite measure `P.toFinite.trim _`, for which `𝓕 s` is
  -- complete
  refine NullMeasurableSet.measurable_of_complete (m0 := 𝓕 s) (μ := P.toFinite.trim (𝓕.le s)) ?_
  refine MeasurableSet.nullMeasurableSet_snd ?_ (P.toFinite.trim (𝓕.le s))
  exact hE.measurableSet_inter_Ico n s

lemma debut_eq_iff_of_nhdsGT_eq_bot
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (E : Set (ι × Ω)) {n t : ι} (hnt : n ≤ t) (ht : 𝓝[>] t = ⊥) (ω : Ω)
    (h_ge : t ≤ debut E n ω) :
    debut E n ω = t ↔ (t, ω) ∈ E := by
  -- todo: extract a lemma about hittingAfter?
  simp only [debut, hittingAfter] at h_ge ⊢
  split_ifs with h_exists
  swap
  · simp only [not_exists, not_and] at h_exists
    simp only [WithTop.top_ne_coe, false_iff]
    exact h_exists t hnt
  simp only [h_exists, ↓reduceIte, WithTop.coe_le_coe, WithTop.coe_inj] at h_ge ⊢
  refine ⟨fun h_eq ↦ ?_, fun h_mem ↦ ?_⟩
  · rw [nhdsGT_eq_bot_iff] at ht
    cases ht with
    | inl ht =>
      obtain ⟨j, hj⟩ := h_exists
      suffices htj : t ≤ j by
        have htj_eq := le_antisymm htj (ht j)
        simpa [htj_eq] using hj.2
      refine h_ge.trans ?_
      refine csInf_le ?_ hj
      exact ⟨n, by simp [mem_lowerBounds]; grind⟩
    | inr ht =>
      obtain ⟨u, htu, hu⟩ := ht
      simp only [not_lt] at hu
      by_contra! h_notMem
      suffices u ≤ sInf {j | n ≤ j ∧ (j, ω) ∈ E} by
        refine not_le.mpr htu ?_
        rwa [h_eq] at this
      refine le_csInf h_exists fun j hj ↦ ?_
      refine hu (lt_of_le_of_ne ?_ ?_)
      · rw [le_csInf_iff] at h_ge
        · exact h_ge j hj
        · exact ⟨n, by simp [mem_lowerBounds]; grind⟩
        · exact h_exists
      · intro htj_eq
        simp only [Set.mem_ofPred_eq, ← htj_eq] at hj
        exact h_notMem hj.2
  · refine le_antisymm ?_ h_ge
    refine csInf_le ?_ ⟨hnt, h_mem⟩
    exact ⟨n, by simp [mem_lowerBounds]; grind⟩

/-- **Debut theorem**: the debut of a progressively measurable set `E` is a stopping time, for a
filtration that is right-continuous and complete with respect to an s-finite measure. -/
theorem isStoppingTime_debut [MeasurableSpace ι] [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι] [BorelSpace ι]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ι mΩ} [𝓕.IsComplete P] [𝓕.IsRightContinuous]
    {E : Set (ι × Ω)} (hE : ProgMeasurableSet E 𝓕) (n : ι) :
    IsStoppingTime 𝓕 (debut E n) := by
  intro t
  rcases lt_or_ge t n with htn | hnt
  · convert MeasurableSet.empty
    rename_i ω
    simp only [Set.mem_eq_mem, Set.mem_empty_iff_false, iff_false, not_le]
    refine (mod_cast htn : (t : WithTop ι) < n).trans_le ?_
    exact le_debut ω
  -- case on whether `t` is isolated on the right or not
  by_cases ht_gt : (𝓝[>] t).NeBot
  swap
  -- if it's isolated then `{debut ≤} = {debut <} ∪ {(t, ω) ∈ E}`
  · have h_eq : {ω | debut E n ω ≤ t} = {ω | debut E n ω < t} ∪ {ω | (t, ω) ∈ E} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      rw [le_iff_lt_or_eq]
      rcases lt_or_ge (debut E n ω) t with h_lt | h_ge
      · simp [h_lt]
      -- `⊢ debut E n ω = ↑t ↔ (t, ω) ∈ E`; use `𝓝[>] t = ⊥`
      congr!
      rw [debut_eq_iff_of_nhdsGT_eq_bot E hnt ?_ _ h_ge]
      simpa using ht_gt
    rw [h_eq]
    exact (hE.measurableSet_debut_lt P n t).union (hE.measurableSet_preimage_prodMk t)
  -- now `t` is a limit point on the right
  obtain ⟨s, hs_gt, hs_tendsto⟩ : ∃ s : ℕ → ι, (∀ n, t < s n) ∧ Tendsto s atTop (𝓝 t) := by
    have h_freq : ∃ᶠ x in 𝓝[>] t, t < x :=
      Eventually.frequently <| eventually_nhdsWithin_of_forall fun _ hx ↦ hx
    have := exists_seq_forall_of_frequently h_freq
    simp_rw [tendsto_nhdsWithin_iff] at this
    obtain ⟨s, ⟨hs_tendsto, _⟩, hs_gt⟩ := this
    exact ⟨s, hs_gt, hs_tendsto⟩
  have h_exists_lt (u : ι) (hu : t < u) : ∃ i, s i < u :=
    Eventually.exists (f := atTop) (hs_tendsto.eventually_lt_const hu)
  have h_exists_lt' (u : WithTop ι) (hu : t < u) : ∃ i, s i < u := by
    refine Eventually.exists (f := atTop) ?_
    have hs_tendsto' : Tendsto (fun n ↦ (s n : WithTop ι)) atTop (𝓝 (t : WithTop ι)) :=
      WithTop.continuous_coe.continuousAt.tendsto.comp hs_tendsto
    exact hs_tendsto'.eventually_lt_const hu
  -- we write `{debut ≤ t}` as a countable intersection of `{debut < s n}`
  have h_eq_iInter : {ω | debut E n ω ≤ t} = ⋂ m, {ω | debut E n ω < s m} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun h_le m ↦ h_le.trans_lt (mod_cast (hs_gt m)), fun h_lt ↦ ?_⟩
    refine le_of_forall_gt fun u hu ↦ ?_
    obtain ⟨i, hi⟩ : ∃ i, s i < u := h_exists_lt' u hu
    exact (h_lt i).trans hi
  rw [h_eq_iInter]
  have h_meas_lt m : MeasurableSet[𝓕 (s m)] {ω | debut E n ω < s m} :=
    hE.measurableSet_debut_lt P n (s m)
  have h𝓕_eq_iInf : 𝓕 t = ⨅ m, 𝓕 (s m) := by
    have ht_cont : 𝓕 t = 𝓕.rightCont t := by
      congr
      exact Filtration.IsRightContinuous.eq.symm
    rw [ht_cont, Filtration.rightCont_eq_of_neBot_nhdsGT]
    refine le_antisymm ?_ ?_
    · simp only [gt_iff_lt, le_iInf_iff]
      exact fun i ↦ iInf₂_le (s i) (hs_gt i)
    · simp only [gt_iff_lt, le_iInf_iff]
      intro i hti
      obtain ⟨m, hm⟩ := h_exists_lt i hti
      exact (iInf_le _ m).trans (𝓕.mono hm.le)
  rw [h𝓕_eq_iInf]
  simp only [MeasurableSpace.measurableSet_iInf]
  intro k
  have h_eq_k : ⋂ m, {ω | debut E n ω < s m} =
      ⋂ (m) (hm : s m ≤ s k), {ω | debut E n ω < s m} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨fun h m _ ↦ h m, fun h m ↦ ?_⟩
    rcases le_total (s m) (s k) with hmk | hkm
    · exact h m hmk
    · exact (h k le_rfl).trans_le (mod_cast hkm)
  rw [h_eq_k]
  refine MeasurableSet.iInter fun m ↦ MeasurableSet.iInter fun hm ↦ ?_
  exact 𝓕.mono hm _ (h_meas_lt m)

end Debut

section HittingTime

lemma _root_.MeasurableSet.progMeasurableSet_preimage [MeasurableSpace ι] [Preorder ι]
    {β : Type*} [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β]
    {𝓕 : Filtration ι mΩ}
    {X : ι → Ω → β} (hX : IsStronglyProgressive 𝓕 X) {s : Set β} (hs : MeasurableSet s) :
    ProgMeasurableSet (X.uncurry ⁻¹' s) 𝓕 :=
  fun t ↦ StronglyMeasurable.indicator (by fun_prop) (hs.preimage (hX t).measurable)

/-- The hitting time of a measurable set by a progressively measurable process for a filtration
satisfying the usual conditions is a stopping time. -/
theorem IsStronglyProgressive.isStoppingTime_hittingAfter [MeasurableSpace ι]
    [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι] [BorelSpace ι]
    {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
    [BorelSpace β]
    (P : Measure Ω) [SFinite P] {𝓕 : Filtration ι mΩ} [𝓕.IsComplete P] [𝓕.IsRightContinuous]
    {X : ι → Ω → β} (hX : IsStronglyProgressive 𝓕 X) {s : Set β} (hs : MeasurableSet s) (n : ι) :
    IsStoppingTime 𝓕 (hittingAfter X s n) := by
  rw [hittingAfter_eq_debut]
  refine isStoppingTime_debut P ?_ n
  exact hs.progMeasurableSet_preimage hX

lemma isStoppingTime_leastGE [MeasurableSpace ι] [ConditionallyCompleteLinearOrder ι]
    [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι] [BorelSpace ι]
    {β : Type*} [Preorder β] [TopologicalSpace β] [ClosedIciTopology β]
    [MeasurableSpace β] [TopologicalSpace.PseudoMetrizableSpace β] [BorelSpace β]
    (P : Measure Ω) [SFinite P] {𝓕 : Filtration ι mΩ} [𝓕.IsComplete P] [𝓕.IsRightContinuous]
    {X : ι → Ω → β} (hX : IsStronglyProgressive 𝓕 X) (r : β) :
    IsStoppingTime 𝓕 (leastGE X r) :=
  hX.isStoppingTime_hittingAfter P measurableSet_Ici _

/-- `leastGT f r` is the stopping time corresponding to the first time `f > r`. -/
noncomputable def leastGT {ι Ω β : Type*} [Preorder ι] [OrderBot ι] [InfSet ι] [Preorder β]
    (f : ι → Ω → β) (r : β) : Ω → WithTop ι :=
  hittingAfter f (Set.Ioi r) ⊥

lemma leastGT_lt_iff {ι β : Type*} [ConditionallyCompleteLinearOrder ι] [OrderBot ι] [Preorder β]
    (X : ι → Ω → β) (a : β) (t : ι) (ω : Ω) :
    leastGT X a ω < t ↔ ∃ s < t, a < X s ω := by simp [leastGT, hittingAfter_lt_iff]

lemma isStoppingTime_leastGT [MeasurableSpace ι] [ConditionallyCompleteLinearOrder ι]
    [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι] [BorelSpace ι]
    {β : Type*} [LinearOrder β] [TopologicalSpace β] [ClosedIicTopology β]
    [MeasurableSpace β] [TopologicalSpace.PseudoMetrizableSpace β] [BorelSpace β]
    (P : Measure Ω) [SFinite P] {𝓕 : Filtration ι mΩ} [𝓕.IsComplete P] [𝓕.IsRightContinuous]
    {X : ι → Ω → β} (hX : IsStronglyProgressive 𝓕 X) (r : β) :
    IsStoppingTime 𝓕 (leastGT X r) :=
  hX.isStoppingTime_hittingAfter P measurableSet_Ioi _

end HittingTime

end MeasureTheory
