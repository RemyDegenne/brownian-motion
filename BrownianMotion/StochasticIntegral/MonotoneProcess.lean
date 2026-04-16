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
public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs
public import Mathlib.Probability.Kernel.Defs

/-! # The Keneral Associated with a Process

-/

@[expose] public section

open MeasureTheory Filter Function Set Topology ProbabilityTheory
open scoped ENNReal

variable {ι Ω : Type*} [TopologicalSpace ι] [LinearOrder ι]

def StieltjesFunction.restrict (f : StieltjesFunction ι) (s : Set ι) : StieltjesFunction s where
  toFun x := f x
  mono' x y hxy := f.mono hxy
  right_continuous' x :=
    (f.right_continuous x).comp continuousAt_subtype_val.continuousWithinAt fun i => by simp

lemma StieltjesFunction.restrict_Ioc_BddAbove (f : StieltjesFunction ι) {a b : ι} :
    BddAbove (range (f.restrict (Ioc a b))) :=
  ⟨f b, fun y ⟨c, hc⟩ => hc ▸ by simp [restrict, f.mono c.2.2]⟩

lemma StieltjesFunction.restrict_Ioc_BddBelow (f : StieltjesFunction ι) {a b : ι} :
    BddBelow (range (f.restrict (Ioc a b))) :=
  ⟨f a, fun y ⟨c, hc⟩ => hc ▸ by simp [restrict, f.mono c.2.1.le]⟩

lemma StieltjesFunction.restrict_Ioc_iSup (f : StieltjesFunction ι) {a b : ι} (hab : a < b) :
    f b = ⨆ i, (f.restrict (Ioc a b)) i := by
  have := nonempty_Ioc_subtype hab
  refine le_antisymm ?_ (ciSup_le fun i => by simp [restrict, f.mono i.2.2])
  have : f b = (f.restrict (Ioc a b)) (⟨b, ⟨hab, refl b⟩⟩ : Ioc a b) := by simp [restrict]
  grw [this, le_ciSup f.restrict_Ioc_BddAbove]

variable [OrderTopology ι] [DenselyOrdered ι]

lemma StieltjesFunction.restrict_Ioc_iInf (f : StieltjesFunction ι) {a b : ι} (hab : a < b) :
    f a = ⨅ i, (f.restrict (Ioc a b)) i := by
  have := nonempty_Ioc_subtype hab
  have : Tendsto (f.restrict (Ioc a b)) atBot (𝓝 (f a)) := by
    have : Tendsto (Subtype.val : (Ioc a b) → ι) atBot (𝓝[≥] a) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, .of_forall (by grind)⟩
      apply tendsto_atBot_isGLB (Subtype.mono_coe _)
      simp [Subtype.range_coe_subtype, -mem_Ioc, isGLB_Ioc hab]
    simpa [restrict] using (f.right_continuous a).tendsto.comp this
  exact tendsto_nhds_unique this (tendsto_atBot_ciInf (f.restrict (Ioc a b)).mono
    f.restrict_Ioc_BddBelow)

variable [MeasurableSpace ι] [BorelSpace ι] [CompactIccSpace ι]
  [SecondCountableTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

private lemma StieltjesFunction.measurable_finite_measure {f : Ω → StieltjesFunction ι}
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

lemma StieltjesFunction.restrict_measure_Ioc (f : StieltjesFunction ι) {a b : ι} (hab : a < b) :
    (f.restrict (Ioc a b)).measure univ = ENNReal.ofReal (f b - f a) := by
  have := nonempty_Ioc_subtype hab
  have hbot : Tendsto (f.restrict (Ioc a b)) atBot (𝓝 (f a)) := by
    have : Tendsto (Subtype.val : (Ioc a b) → ι) atBot (𝓝[≥] a) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, .of_forall (by grind)⟩
      apply tendsto_atBot_isGLB (Subtype.mono_coe _)
      simp [Subtype.range_coe_subtype, -mem_Ioc, isGLB_Ioc hab]
    simpa [restrict] using (f.right_continuous a).tendsto.comp this
  have htop : Tendsto (f.restrict (Ioc a b)) atTop (𝓝 (f b)) := by
    rw [f.restrict_Ioc_iSup hab]
    convert tendsto_atTop_ciSup (f.restrict (Ioc a b)).mono f.restrict_Ioc_BddAbove
  simp [-mem_Ioc, ← measure_univ (f.restrict (Ioc a b)) hbot htop]

instance StieltjesFunction.isFiniteMeasure_restrict_Ioc {f : StieltjesFunction ι} {a b : ι} :
    IsFiniteMeasure (f.restrict (Ioc a b)).measure where
  measure_univ_lt_top := by
    by_cases! hab : a < b
    · simp [f.restrict_measure_Ioc hab]
    · have : (univ : Set (Ioc a b)) = ∅ := by grind
      simp [this, measure_empty]

lemma StieltjesFunction.restrict_eq_measure (f : StieltjesFunction ι) (a b : ι) :
    (f.restrict (Ioc a b)).measure = f.measure.comap Subtype.val := by
  apply ext_of_generate_finite _ _ (isPiSystem_Ioc id id)
  · rintro t ⟨i, j, hl, rfl⟩
    simp [id_eq, measure_Ioc, (MeasurableEmbedding.subtype_coe measurableSet_Ioc).comap_apply,
      restrict]
  · by_cases! hab : a < b
    · simp [-mem_Ioc, f.restrict_measure_Ioc hab,
        (MeasurableEmbedding.subtype_coe measurableSet_Ioc).comap_apply]
    · have : (univ : Set (Ioc a b)) = ∅ := by grind
      simp [this, measure_empty]
  · exact (Subtype.borelSpace (Ioc a b)).measurable_eq ▸ borel_eq_generateFrom_Ioc ↑(Ioc a b)

theorem StieltjesFunction.measurable_measure {f : Ω → StieltjesFunction ι}
    (hf : ∀ i, Measurable (f · i)) :
    Measurable fun ω => (f ω).measure := by
  by_cases! Nonempty ι
  · refine Measure.measurable_measure.2 fun s hs => ?_
    obtain ⟨u, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
    obtain ⟨v, hv⟩ := exists_seq_antitone_tendsto_atTop_atBot ι
    have hc : univ = botSet ∪ ⋃ n, Ioc (v n) (u n) := by
      ext x
      by_cases! hx : IsBot x
      <;> simp_all only [IsBot, mem_univ, botSet, mem_union, mem_setOf_eq,
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
      simp [restrict_eq_measure, inter_comm,
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
    refine measurable_finite_measure ?_ ?_ fun i => (by measurability)
    <;> by_cases! hvu : v n < u n
    · simp [fun ω => ((f ω).restrict_Ioc_iInf hvu).symm, hf (v n)]
    · simp_all
    · simp [fun ω => ((f ω).restrict_Ioc_iSup hvu).symm, hf (u n)]
    · simp_all
  · simp [Measure.eq_zero_of_isEmpty]

variable {X : ι → Ω → ℝ}

/-- If `X : ι → Ω → ℝ` is a right continuous and monotone process, then for each `ω : Ω`, `X · ω` is
a `StieltjesFunction` defined on `ι`. -/
def StieltjesFunction.rightCont_mono (hcont : ∀ ω, RightContinuous (X · ω))
    (hmono : ∀ ω, Monotone (X · ω)) : Ω → StieltjesFunction ι :=
  fun ω => StieltjesFunction.mk (X · ω) (hmono ω)
    (fun i => continuousWithinAt_Ioi_iff_Ici.1 (hcont ω i))

/-- If `f : Ω → StieltjesFunction ι` satisfies for each `i`, `f · i` is measurable, then `f` defines
a kernel. -/
noncomputable def StieltjesFunction.kernel {f : Ω → StieltjesFunction ι}
    (hf : ∀ i, Measurable (f · i)) : ProbabilityTheory.Kernel Ω ι where
  toFun ω := (f ω).measure
  measurable' := measurable_measure hf

/-- If `X : ι → Ω → ℝ` is a right continuous, adapted, and monotone process, then `X` defines a
kernel that maps each `ω` to `(X · ω).measure`. -/
noncomputable def StieltjesFunction.kernel_of_rightCont_adapted_mono {ℱ : Filtration ι mΩ}
    (ha : Adapted ℱ X) (hcont : ∀ ω, RightContinuous (X · ω)) (hmono : ∀ ω, Monotone (X · ω)) :
    Kernel Ω ι where
  toFun ω := (rightCont_mono hcont hmono ω).measure
  measurable' := by
    apply measurable_measure
    simp_all [rightCont_mono, fun i => ha.measurable (i := i)]

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {Y : ι → Ω → E}

/-- If `Y : ι → Ω → E` has paths of bounded variation, then `Y` defines a kernel that maps each
`ω` to the variation of `Y · ω`. -/
noncomputable def StieltjesFunction.kernel_of_boundedVariation
    (hvar : ∀ ω, BoundedVariationOn (Y · ω) univ) : Kernel Ω ι where
  toFun ω := (hvar ω).vectorMeasure.variation
  measurable' := by sorry

theorem StieltjesFunction.kernel_of_boundedVariation_eq_kernel_of_rightCont_adapted_mono
    {ℱ : Filtration ι mΩ} (ha : Adapted ℱ X) (hcont : ∀ ω, RightContinuous (X · ω))
    (hmono : ∀ ω, Monotone (X · ω)) (hvar : ∀ ω, BoundedVariationOn (Y · ω) univ) :
    StieltjesFunction.kernel_of_boundedVariation hvar =
      StieltjesFunction.kernel_of_rightCont_adapted_mono ha hcont hmono := by
  sorry
