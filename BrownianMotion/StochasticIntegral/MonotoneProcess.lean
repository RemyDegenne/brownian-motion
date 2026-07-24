/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BrownianMotion.Auxiliary.Filtration
public import BrownianMotion.StochasticIntegral.Cadlag
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs
public import Mathlib.Probability.Kernel.Defs

/-! # The Keneral Associated with a Process

-/

@[expose] public section

open MeasureTheory Filter Function Set Topology ProbabilityTheory
open scoped ENNReal

variable {ι Ω E : Type*} [TopologicalSpace ι] [LinearOrder ι] {a b : ι}
variable {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
variable {X : ι → Ω → ℝ} {Y : ι → Ω → E}

section StieltjesKernel

/-- Restrict domain of a Stieltjes function `f` to a set `s`. -/
def StieltjesFunction.restrict (f : StieltjesFunction ι) (s : Set ι) : StieltjesFunction s where
  toFun x := f x
  mono' x y hxy := f.mono hxy
  right_continuous' x :=
    (f.right_continuous x).comp continuousAt_subtype_val.continuousWithinAt fun i => by simp

lemma StieltjesFunction.bddAbove_restrict_Ioc (f : StieltjesFunction ι) :
    BddAbove (range (f.restrict (Ioc a b))) :=
  ⟨f b, fun y ⟨c, hc⟩ => hc ▸ by simp [restrict, f.mono c.2.2]⟩

lemma StieltjesFunction.bddBelow_restrict_Ioc (f : StieltjesFunction ι) :
    BddBelow (range (f.restrict (Ioc a b))) :=
  ⟨f a, fun y ⟨c, hc⟩ => hc ▸ by simp [restrict, f.mono c.2.1.le]⟩

lemma StieltjesFunction.iSup_restrict_Ioc (f : StieltjesFunction ι) (hab : a < b) :
    ⨆ i, (f.restrict (Ioc a b)) i = f b := by
  have := nonempty_Ioc_subtype hab
  refine le_antisymm (ciSup_le fun i => by simp [restrict, f.mono i.2.2]) ?_
  have : f b = (f.restrict (Ioc a b)) (⟨b, ⟨hab, refl b⟩⟩ : Ioc a b) := by simp [restrict]
  grw [this, le_ciSup f.bddAbove_restrict_Ioc]

variable [OrderTopology ι] [DenselyOrdered ι]

lemma StieltjesFunction.iInf_restrict_Ioc (f : StieltjesFunction ι) (hab : a < b) :
    ⨅ i, (f.restrict (Ioc a b)) i = f a := by
  have := nonempty_Ioc_subtype hab
  have : Tendsto (f.restrict (Ioc a b)) atBot (𝓝 (f a)) := by
    have : Tendsto (Subtype.val : (Ioc a b) → ι) atBot (𝓝[≥] a) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, .of_forall (by grind)⟩
      apply tendsto_atBot_isGLB (Subtype.mono_coe _)
      simp [Subtype.range_coe_subtype, -mem_Ioc, isGLB_Ioc hab]
    exact (f.right_continuous a).tendsto.comp this
  exact (tendsto_nhds_unique this (tendsto_atBot_ciInf (f.restrict (Ioc a b)).mono
    f.bddBelow_restrict_Ioc)).symm

variable [MeasurableSpace ι] [BorelSpace ι] [CompactIccSpace ι] [SecondCountableTopology ι]

private lemma StieltjesFunction.measurable_measure_of_isFiniteMeasure {f : Ω → StieltjesFunction ι}
    [∀ ω, IsFiniteMeasure (f ω).measure] (hmbot : Measurable (fun ω => ⨅ i, f ω i))
    (hmtop : Measurable (fun ω => ⨆ i, f ω i)) (hf : ∀ i, Measurable (f · i)) :
    Measurable fun ω => (f ω).measure := by
  by_cases! Nonempty ι
  · apply Measurable.measure_of_isPiSystem ?_ (isPiSystem_Ioc id id)
    · rintro t ⟨i, j, hl, rfl⟩
      simp only [id_eq, StieltjesFunction.measure_Ioc]
      fun_prop
    · have hbot (ω : Ω) : Tendsto (f ω) atBot (𝓝 (⨅ i, (f ω) i)) := by
        apply tendsto_atBot_ciInf (f ω).mono
        by_contra!
        have := measure_univ_of_tendsto_atBot_atBot (f ω) <|
          tendsto_atBot_atBot_of_monotone' (f ω).mono this
        aesop
      have htop (ω : Ω) : Tendsto (f ω) atTop (𝓝 (⨆ i, (f ω) i)) := by
        apply tendsto_atTop_ciSup (f ω).mono
        by_contra!
        have := measure_univ_of_tendsto_atTop_atTop (f ω) <|
          tendsto_atTop_atTop_of_monotone' (f ω).mono this
        aesop
      simp_all [fun ω => measure_univ (f ω) (hbot ω) (htop ω)]
      measurability
    · borelize ι
      exact borel_eq_generateFrom_Ioc ι
  · simp [Measure.eq_zero_of_isEmpty]

instance {X : Type*} [TopologicalSpace X] [Preorder X] [CompactIccSpace X] {a b : X} :
    CompactIccSpace (Ioc a b) where
  isCompact_Icc := by
    intro c d
    exact IsEmbedding.subtypeVal.isCompact_iff.2 (by simp [isCompact_Icc])

lemma StieltjesFunction.measure_restrict_Ioc (f : StieltjesFunction ι) (hab : a < b) :
    (f.restrict (Ioc a b)).measure univ = ENNReal.ofReal (f b - f a) := by
  have := nonempty_Ioc_subtype hab
  have hbot : Tendsto (f.restrict (Ioc a b)) atBot (𝓝 (f a)) := by
    have : Tendsto (Subtype.val : (Ioc a b) → ι) atBot (𝓝[≥] a) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, .of_forall (by grind)⟩
      apply tendsto_atBot_isGLB (Subtype.mono_coe _)
      simp [Subtype.range_coe_subtype, -mem_Ioc, isGLB_Ioc hab]
    exact (f.right_continuous a).tendsto.comp this
  have htop : Tendsto (f.restrict (Ioc a b)) atTop (𝓝 (f b)) := by
    rw [← f.iSup_restrict_Ioc hab]
    convert tendsto_atTop_ciSup (f.restrict (Ioc a b)).mono f.bddAbove_restrict_Ioc
  simp [-mem_Ioc, ← measure_univ (f.restrict (Ioc a b)) hbot htop]

instance StieltjesFunction.isFiniteMeasure_restrict_Ioc {f : StieltjesFunction ι} :
    IsFiniteMeasure (f.restrict (Ioc a b)).measure where
  measure_univ_lt_top := by
    by_cases! hab : a < b
    · simp [f.measure_restrict_Ioc hab]
    · have : (univ : Set (Ioc a b)) = ∅ := by grind
      simp [this, measure_empty]

lemma StieltjesFunction.measure_restrict_eq_comap (f : StieltjesFunction ι) (a b : ι) :
    (f.restrict (Ioc a b)).measure = f.measure.comap Subtype.val := by
  apply ext_of_generate_finite _ _ (isPiSystem_Ioc id id)
  · rintro t ⟨i, j, hl, rfl⟩
    simp [measure_Ioc, (MeasurableEmbedding.subtype_coe measurableSet_Ioc).comap_apply, restrict]
  · by_cases! hab : a < b
    · simp [-mem_Ioc, f.measure_restrict_Ioc hab,
        (MeasurableEmbedding.subtype_coe measurableSet_Ioc).comap_apply]
    · have : (univ : Set (Ioc a b)) = ∅ := by grind
      simp [this, measure_empty]
  · exact (Subtype.borelSpace (Ioc a b)).measurable_eq ▸ borel_eq_generateFrom_Ioc ↑(Ioc a b)

theorem StieltjesFunction.measurable_measure' {f : Ω → StieltjesFunction ι}
    (hf : ∀ i, Measurable (f · i)) :
    Measurable fun ω => (f ω).measure := by
  by_cases! Nonempty ι
  · refine Measure.measurable_measure.2 fun s hs => ?_
    obtain ⟨u, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
    obtain ⟨v, hv⟩ := exists_seq_antitone_tendsto_atTop_atBot ι
    have hc : univ = botSet ∪ ⋃ n, Ioc (v n) (u n) := by
      ext x
      by_cases! hx : IsBot x
      <;> simp_all only [IsBot, mem_univ, botSet, mem_union, mem_ofPred_eq,
        implies_true, mem_iUnion, mem_Ioc, and_true, true_or, tendsto_atTop_atTop,
        tendsto_atTop_atBot, not_forall, not_le, true_iff]
      apply Or.inr
      obtain ⟨i, hi⟩ := hu.2 x
      obtain ⟨z, hz⟩ := hx
      obtain ⟨j, hj⟩ := hv.2 z
      refine ⟨max i j, ?_, ?_⟩
      · exact (hj (max i j) (le_max_right i j)).trans_lt hz
      · exact hi (max i j) (le_max_left i j)
    have hm : Monotone fun n => s ∩ Ioc (v n) (u n) := by
      intro i j hij x hx
      simp_all only [Monotone, Antitone, mem_inter_iff, true_and]
      exact ⟨(hv.1 hij).trans_lt hx.2.1, hx.2.2.trans (hu.1 hij)⟩
    have heq (n : ℕ) (ω : Ω) : (f ω).measure (s ∩ Ioc (v n) (u n)) =
      ((f ω).restrict (Ioc (v n) (u n))).measure (Subtype.val ⁻¹' s) := by
      simp [measure_restrict_eq_comap, inter_comm,
        (MeasurableEmbedding.subtype_coe measurableSet_Ioc).comap_apply]
    rw [← inter_univ s, hc, inter_union_distrib_left, inter_iUnion]
    have hd : Disjoint (s ∩ botSet) (⋃ n, s ∩ Ioc (v n) (u n)) := by
      refine disjoint_left.2 fun a ⟨_, ha⟩ ⟨_, ⟨⟨i, rfl⟩, ⟨_, hm⟩⟩⟩ => ?_
      grind [hm.1, ha (v i)]
    have hz (ω : Ω) : (f ω).measure (s ∩ botSet) = 0 :=
      measure_mono_null inter_subset_right (measure_botSet (f ω))
    simp only [measure_union' hd (hs.inter measurableSet_botSet), hz, hm.measure_iUnion, heq,
      zero_add]
    refine Measurable.iSup fun n => (Measure.measurable_measure.1 ?_) _ (by measurability)
    refine measurable_measure_of_isFiniteMeasure ?_ ?_ fun i => (by measurability)
    <;> by_cases! hvu : v n < u n
    · simp [fun ω => (f ω).iInf_restrict_Ioc hvu, hf (v n)]
    · simp_all
    · simp [fun ω => (f ω).iSup_restrict_Ioc hvu, hf (u n)]
    · simp_all
  · simp [Measure.eq_zero_of_isEmpty]

/-- If `X : ι → Ω → ℝ` is a right continuous and monotone process, then for each `ω : Ω`, `X · ω` is
a `StieltjesFunction` defined on `ι`. -/
def StieltjesFunction.rightContMono (hcont : ∀ ω, IsRightContinuous (X · ω))
    (hmono : ∀ ω, Monotone (X · ω)) : Ω → StieltjesFunction ι :=
  fun ω => StieltjesFunction.mk (X · ω) (hmono ω)
    (fun i => continuousWithinAt_Ioi_iff_Ici.1 (hcont ω i))

/-- If `f : Ω → StieltjesFunction ι` satisfies for each `i`, `f · i` is measurable, then `f` defines
a kernel. -/
noncomputable def StieltjesFunction.kernel {f : Ω → StieltjesFunction ι}
    (hf : ∀ i, Measurable (f · i)) : ProbabilityTheory.Kernel Ω ι where
  toFun ω := (f ω).measure
  measurable' := measurable_measure' hf

/-- If `X : ι → Ω → ℝ` is a right continuous, adapted, and monotone process, then `X` defines a
kernel that maps each `ω` to `(X · ω).measure`. -/
noncomputable def StieltjesFunction.kernelOfRightContAdaptedMono
    (ha : Adapted ℱ X) (hcont : ∀ ω, IsRightContinuous (X · ω)) (hmono : ∀ ω, Monotone (X · ω)) :
    Kernel Ω ι where
  toFun ω := (rightContMono hcont hmono ω).measure
  measurable' := by
    apply measurable_measure'
    simp_all [rightContMono, fun i => ha.measurable (i := i)]

end StieltjesKernel

namespace MeasureTheory.VectorMeasure

variable {ι : Type*} [MeasurableSpace ι]
variable [AddCommMonoid E] [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Measurability structure on `VectorMeasure`. -/
instance : MeasurableSpace (VectorMeasure ι E) :=
  ⨆ (s : Set ι) (_ : MeasurableSet s), (borel E).comap fun μ => μ s

theorem measurable_coe {s : Set ι} (hs : MeasurableSet s) :
    Measurable fun μ : VectorMeasure ι E => μ s := by
  borelize E
  apply Measurable.of_comap_le <| _
  apply le_biSup _ hs

theorem measurable_of_measurable_coe {f : Ω → VectorMeasure ι E}
    (h : ∀ (s : Set ι), MeasurableSet s → Measurable fun ω => f ω s) :
    Measurable f := by
  refine Measurable.of_le_map <| iSup₂_le fun s hs => MeasurableSpace.comap_le_iff_le_map.2 ?_
  rw [MeasurableSpace.map_comp]
  borelize E
  exact h s hs

end MeasureTheory.VectorMeasure

section StronglyMeasurableLim

variable [OrderTopology ι] [SecondCountableTopology ι]
variable [NormedAddCommGroup E] [CompleteSpace E]

lemma stronglyMeasurable_limUnder_atTop [Nonempty ι]
    (hY : ∀ i, StronglyMeasurable (Y i)) (hvar : ∀ ω, BoundedVariationOn (Y · ω) univ) :
    StronglyMeasurable fun ω => limUnder atTop (Y · ω) := by
  obtain ⟨u, hu⟩ := atTop.exists_seq_tendsto (α := ι)
  convert (StronglyMeasurable.limUnder (l := atTop) fun n => hY (u n)) using 1
  ext ω
  exact ((hvar ω).tendsto_atTop_limUnder.comp hu).limUnder_eq.symm

lemma stronglyMeasurable_limUnder_atBot [Nonempty ι]
    (hY : ∀ i, StronglyMeasurable (Y i)) (hvar : ∀ ω, BoundedVariationOn (Y · ω) univ) :
    StronglyMeasurable fun ω => limUnder atBot (Y · ω) := by
  obtain ⟨u, hu⟩ := atBot.exists_seq_tendsto (α := ι)
  convert (StronglyMeasurable.limUnder (l := atTop) fun n => hY (u n)) using 1
  ext ω
  exact ((hvar ω).tendsto_atBot_limUnder.comp hu).limUnder_eq.symm

variable [DenselyOrdered ι]

lemma stronglyMeasurable_rightLim
    (hY : ∀ i, StronglyMeasurable (Y i)) (hvar : ∀ ω, BoundedVariationOn (Y · ω) univ)
    (x : ι) : StronglyMeasurable fun ω => (Y · ω).rightLim x := by
  by_cases hx : IsTop x
  · simpa [rightLim_eq_of_isTop hx] using hY x
  have := nhdsGT_neBot_of_exists_gt (by simp_all [IsTop] : ∃ y, x < y)
  obtain ⟨u, hu⟩ := (𝓝[>] x).exists_seq_tendsto
  convert (StronglyMeasurable.limUnder (l := atTop) fun n => hY (u n)) using 1
  ext ω
  exact (((hvar ω).tendsto_rightLim x).comp hu).limUnder_eq.symm

variable [MeasurableSpace ι] [BorelSpace ι] [CompactIccSpace ι]

lemma stronglyMeasurable_vectorMeasure_Ioc
    (hY : ∀ i, StronglyMeasurable (Y i)) (hvar : ∀ ω, BoundedVariationOn (Y · ω) univ)
    {a b : ι} (hab : a ≤ b) :
    StronglyMeasurable fun ω => (hvar ω).vectorMeasure (Ioc a b) := by
  simpa [fun ω => (hvar ω).vectorMeasure_Ioc hab] using
    (continuous_sub.comp_stronglyMeasurable
      ((stronglyMeasurable_rightLim hY hvar b).prodMk (stronglyMeasurable_rightLim hY hvar a)))

lemma stronglyMeasurable_vectorMeasure_univ
    (hY : ∀ i, StronglyMeasurable (Y i)) (hvar : ∀ ω, BoundedVariationOn (Y · ω) univ) :
    StronglyMeasurable fun ω => (hvar ω).vectorMeasure univ := by
  by_cases! hι : IsEmpty ι
  · simpa [eq_empty_of_isEmpty] using stronglyMeasurable_const
  · simpa [(hvar _).vectorMeasure_univ] using
      (continuous_sub.comp_stronglyMeasurable ((stronglyMeasurable_limUnder_atTop hY hvar).prodMk
        (stronglyMeasurable_limUnder_atBot hY hvar)))

end StronglyMeasurableLim

namespace BoundedVariationOn

variable [OrderTopology ι] [DenselyOrdered ι] [MeasurableSpace ι] [BorelSpace ι]
   [CompactIccSpace ι] [SecondCountableTopology ι]
variable [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_vectorMeasure_of_stronglyMeasurable
    (hY : ∀ i, StronglyMeasurable (Y i)) (hvar : ∀ ω, BoundedVariationOn (Y · ω) univ) :
    Measurable fun ω => (hvar ω).vectorMeasure := by
  refine VectorMeasure.measurable_of_measurable_coe fun s hs ↦ StronglyMeasurable.measurable ?_
  induction s, hs using MeasurableSpace.induction_on_inter
      (‹BorelSpace ι›.measurable_eq.trans (borel_eq_generateFrom_Ioc ι))
      (isPiSystem_Ioc id id) with
  | empty => simpa using stronglyMeasurable_const
  | basic s hs =>
      obtain ⟨a, b, hlt, rfl⟩ := hs
      simpa using stronglyMeasurable_vectorMeasure_Ioc hY hvar hlt.le
  | compl s hs ihs =>
      simpa [fun ω => (hvar ω).vectorMeasure.of_compl hs] using
        continuous_sub.comp_stronglyMeasurable
          ((stronglyMeasurable_vectorMeasure_univ hY hvar).prodMk ihs)
  | iUnion f hfd hfm ihf =>
      refine stronglyMeasurable_of_tendsto atTop
        (fun n => (Finset.range n).stronglyMeasurable_sum fun i hi => ihf i) ?_
      simp only [tendsto_pi_nhds, Finset.sum_apply]
      exact fun ω ↦ ((hvar ω).vectorMeasure.m_iUnion' hfm hfd).tendsto_sum_nat

lemma measurable_vectorMeasure_of_measurable [SecondCountableTopology E]
    (hY : ∀ i, Measurable (Y i)) (hvar : ∀ ω, BoundedVariationOn (Y · ω) univ) :
    Measurable fun ω => (hvar ω).vectorMeasure :=
  measurable_vectorMeasure_of_stronglyMeasurable (fun i ↦ (hY i).stronglyMeasurable) hvar

lemma measurable_vectorMeasure_of_adapted [SecondCountableTopology E]
    (ha : Adapted ℱ Y) (hvar : ∀ ω, BoundedVariationOn (Y · ω) univ) :
    Measurable fun ω => (hvar ω).vectorMeasure :=
  measurable_vectorMeasure_of_measurable (fun _ ↦ ha.measurable) hvar

lemma measurable_vectorMeasure_of_stronglyAdapted
    (ha : StronglyAdapted ℱ Y) (hvar : ∀ ω, BoundedVariationOn (Y · ω) univ) :
    Measurable fun ω => (hvar ω).vectorMeasure :=
  measurable_vectorMeasure_of_stronglyMeasurable (fun _ ↦ ha.stronglyMeasurable) hvar

end BoundedVariationOn
