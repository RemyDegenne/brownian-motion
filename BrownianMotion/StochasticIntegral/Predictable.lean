/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Process.Filtration
public import Mathlib

/-!
# Progressively Measurable σ-algebra

This file defines the progressively measurable σ-algebra associated to a filtration, as well as the
notion of predictable processes. We prove that predictable processes are progressively measurable
and adapted. We also give an equivalent characterization of predictability for discrete processes.

## Main definitions

* `Filtration.rightCont`: The right continuation of a filtration.
* `Filtration.Predictable`: The predictable σ-algebra associated to a filtration.
* `Filtration.IsPredictable`: A process is predictable if it is measurable with respect to the
  predictable σ-algebra.

## Main results

* `Filtration.IsPredictable.progMeasurable`: A predictable process is progressively measurable.
* `Filtration.IsPredictable.measurable_succ`: `u` is a discrete predictable process iff
  `u (n + 1)` is `𝓕 n`-measurable and `u 0` is `𝓕 0`-measurable.

## Implementation note

To avoid requiring a `TopologicalSpace` instance on `ι` in the definition of `rightCont`,
we endow `ι` with the order topology `Preorder.topology` inside the definition.
Say you write a statement about `𝓕₊` which does not require a `TopologicalSpace` structure on `ι`,
but you wish to use a statement which requires a topology (such as `rightCont_def`).
Then you can endow `ι` with the order topology by writing
```lean
  letI := Preorder.topology ι
  haveI : OrderTopology ι := ⟨rfl⟩
```

## Notation

* Given a filtration `𝓕`, its right continuation is denoted `𝓕₊` (type `₊` with `;_+`).
-/

@[expose] public section

open Finset Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

namespace Filtration

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {E : Type*} [TopologicalSpace E] [PartialOrder ι]

/-- A filtration `𝓕` is said to satisfy the usual conditions if it is right continuous and `𝓕 0`
  and consequently `𝓕 t` is complete (i.e. contains all null sets) for all `t`. -/
class HasUsualConditions (𝓕 : Filtration ι m) (μ : Measure Ω := by volume_tac)
    extends IsRightContinuous 𝓕 where
    /-- `𝓕 ⊥` contains all the null sets. -/
    IsComplete ⦃s : Set Ω⦄ (hs : μ s = 0) (t : ι) : MeasurableSet[𝓕 t] s

variable [OrderBot ι]

instance {𝓕 : Filtration ι m} {μ : Measure Ω} [u : HasUsualConditions 𝓕 μ] {i : ι} :
    @Measure.IsComplete Ω (𝓕 i) (μ.trim <| 𝓕.le _) :=
  ⟨fun _ hs ↦ u.2 (measure_eq_zero_of_trim_eq_zero (Filtration.le 𝓕 _) hs) i⟩

lemma HasUsualConditions.measurableSet_of_null
    (𝓕 : Filtration ι m) {μ : Measure Ω} [u : HasUsualConditions 𝓕 μ] (s : Set Ω) (hs : μ s = 0) :
    MeasurableSet[𝓕 ⊥] s :=
  u.2 hs ⊥

end Filtration

section LeftApprox

variable {ι : Type*} [LinearOrder ι] [OrderBot ι]

private noncomputable abbrev leftApprox (f : ℕ → ι) (n : ℕ) (t : ι) : ι :=
  (((range (n + 1)).image f).filter (· < t)).sup id

private lemma leftApprox_le (f : ℕ → ι) (n : ℕ) (t : ι) : leftApprox f n t ≤ t :=
  Finset.sup_le fun _ hx ↦ le_of_lt (mem_filter.mp hx).2

private lemma leftApprox_mem_insert_bot (f : ℕ → ι) (n : ℕ) (t : ι) :
    leftApprox f n t ∈ (insert ⊥ ((range (n + 1)).image f) : Finset ι) := by
  obtain h | h := (((range (n + 1)).image f).filter (· < t)).eq_empty_or_nonempty
  · simp [leftApprox, h]
  · refine mem_insert_of_mem ?_
    change (((range (n + 1)).image f).filter (· < t)).sup id ∈ (range (n + 1)).image f
    obtain ⟨x, hx_mem, hx_eq⟩ :=
      (Set.mem_image _ _ _).mp (sup_mem_of_nonempty h (f := id))
    rw [← hx_eq]
    exact mem_of_mem_filter x hx_mem

private lemma leftApprox_le_of_filter_eq_empty (f : ℕ → ι) (n : ℕ) {s : ι}
    (hF : ((range (n + 1)).image f).filter (s < ·) = ∅) (t : ι) :
    leftApprox f n t ≤ s := by
  refine Finset.sup_le fun x hx ↦ ?_
  simp only [mem_filter] at hx
  by_contra! h
  have : x ∈ ((range (n + 1)).image f).filter (s < ·) := mem_filter.mpr ⟨hx.1, h⟩
  simp [hF] at this

private lemma lt_of_leftApprox_eq (f : ℕ → ι) (n : ℕ) {s : ι} (hne : s ≠ ⊥) {t : ι}
    (heq : leftApprox f n t = s) : s < t := by
  have hne_filt : (((range (n + 1)).image f).filter (· < t)).Nonempty := by
    by_contra h
    simp only [leftApprox, not_nonempty_iff_eq_empty.mp h] at heq
    exact hne heq.symm
  obtain ⟨x, hx_mem, hx_eq⟩ := (Set.mem_image _ _ _).mp
    (sup_mem_of_nonempty hne_filt (f := id))
  simp only [id] at hx_eq
  rw [hx_eq.trans heq] at hx_mem
  exact (mem_filter.mp (mem_coe.mp hx_mem)).2

private lemma leftApprox_eq_le (f : ℕ → ι) (n : ℕ) {s : ι}
    {y : ι} (hy : y ∈ (range (n + 1)).image f) (hsy : s < y)
    {t : ι} (heq : leftApprox f n t = s) : t ≤ y := by
  by_contra! h
  exact absurd heq (hsy.trans_le (le_sup (f := id) (mem_filter.mpr ⟨hy, h⟩))).ne'

private lemma leftApprox_le_of_le_min' (f : ℕ → ι) (n : ℕ) {s : ι}
    {F : Finset ι} (hFdef : F = ((range (n + 1)).image f).filter (s < ·))
    (hF : F.Nonempty) {t : ι} (hle : t ≤ F.min' hF) :
    leftApprox f n t ≤ s := by
  refine Finset.sup_le fun x hx ↦ ?_
  simp only [mem_filter] at hx
  by_contra! hc
  exact absurd (hx.2.trans_le hle)
    (not_lt.mpr (min'_le F x (hFdef ▸ mem_filter.mpr ⟨hx.1, hc⟩)))

variable [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]

private lemma tendsto_leftApprox_nhdsWithin_Iio
    {D : Set ι} {d : ℕ → D} (hDdense : Dense D) (hd_surj : Function.Surjective d)
    {t : ι} (ht : t ≠ ⊥) :
    Tendsto (leftApprox (fun k ↦ (d k : ι)) · t) atTop (nhdsWithin t (Set.Iio t)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · rw [tendsto_order]
    constructor
    · intro s hst
      obtain ⟨q, hqD, hsq, hqt⟩ := hDdense.exists_between hst
      obtain ⟨k, hk⟩ := hd_surj ⟨q, hqD⟩
      have hdk : (↑(d k) : ι) = q := congrArg Subtype.val hk
      rw [eventually_atTop]
      exact ⟨k, fun n hn ↦ hsq.trans_le
        (le_sup (f := id) (mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨k, mem_range.mpr (Nat.lt_succ_of_le hn),
            hdk⟩, hdk ▸ hqt⟩))⟩
    · exact fun s hts ↦ .of_forall fun n ↦
        (leftApprox_le _ n t).trans_lt hts
  · exact .of_forall fun n ↦ Finset.sup_lt_iff
      (bot_le.lt_of_ne (Ne.symm ht)) |>.mpr
      fun b hb ↦ (mem_filter.mp hb).2

end LeftApprox

section PredictableMeasurability

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι]
    {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ}

lemma measurable_predictable_snd :
    Measurable[𝓕.predictable, 𝓕 ⊥] (Prod.snd : ι × Ω → Ω) := fun s hs ↦ by
  rw [← Set.univ_prod, ← Set.Iic_union_Ioi (a := (⊥ : ι)),
    Set.Iic_bot, Set.union_prod]
  exact (measurableSet_predictable_singleton_bot_prod hs).union
    (measurableSet_predictable_Ioi_prod hs)

variable {E : Type*} [TopologicalSpace E]

private lemma measurableSet_predictable_leftApprox_fiber_prod
    {u : ι → Ω → E} (h_adapted : StronglyAdapted 𝓕 u)
    (f : ℕ → ι) (n m : ℕ) (c : E)
    {s : ι} (hs : s ∈ (insert ⊥ ((range (n + 1)).image f) : Finset ι)) :
    MeasurableSet[𝓕.predictable]
      ({t | leftApprox f n t = s} ×ˢ ((h_adapted s).approx m ⁻¹' {c})) := by
  set pts := (range (n + 1)).image f
  have hA_meas : MeasurableSet[𝓕 s] ((h_adapted s).approx m ⁻¹' {c}) :=
    @SimpleFunc.measurableSet_fiber _ _ (𝓕 s) _ c
  let F := pts.filter (s < ·)
  obtain hF | hF := F.eq_empty_or_nonempty
  · obtain rfl | hne := eq_or_ne s ⊥
    · rw [show {t | leftApprox f n t = ⊥} = Set.univ from Set.eq_univ_of_forall fun t ↦
        le_antisymm (leftApprox_le_of_filter_eq_empty f n hF t) bot_le, Set.univ_prod]
      exact measurable_predictable_snd hA_meas
    · rw [show {t | leftApprox f n t = s} = Set.Ioi s from Set.ext fun t ↦
        ⟨fun heq ↦ lt_of_leftApprox_eq f n hne heq, fun hlt ↦ le_antisymm
          (leftApprox_le_of_filter_eq_empty f n hF t)
          (le_sup (f := id) (mem_filter.mpr ⟨(mem_insert.mp hs).resolve_left hne, hlt⟩))⟩]
      exact measurableSet_predictable_Ioi_prod hA_meas
  · let s' := F.min' hF
    have hmin := min'_mem F hF
    obtain rfl | hne := eq_or_ne s ⊥
    · rw [show {t | leftApprox f n t = ⊥} = Set.Iic s' from Set.ext fun t ↦
        ⟨fun heq ↦ leftApprox_eq_le f n (mem_of_mem_filter _ hmin) (mem_filter.mp hmin).2 heq,
         fun hle ↦ le_antisymm (leftApprox_le_of_le_min' f n rfl hF hle) bot_le⟩,
        show Set.Iic s' = {⊥} ∪ Set.Ioc ⊥ s' from by
          rw [← Set.Iic_bot, Set.Iic_union_Ioc_eq_Iic bot_le], Set.union_prod]
      exact (measurableSet_predictable_singleton_bot_prod hA_meas).union
        (measurableSet_predictable_Ioc_prod ⊥ s' hA_meas)
    · rw [show {t | leftApprox f n t = s} = Set.Ioc s s' from Set.ext fun t ↦
        ⟨fun heq ↦ ⟨lt_of_leftApprox_eq f n hne heq,
          leftApprox_eq_le f n (mem_of_mem_filter _ hmin) (mem_filter.mp hmin).2 heq⟩,
         fun ⟨hlt, hle⟩ ↦ le_antisymm (leftApprox_le_of_le_min' f n rfl hF hle)
          (le_sup (f := id) (mem_filter.mpr ⟨(mem_insert.mp hs).resolve_left hne, hlt⟩))⟩]
      exact measurableSet_predictable_Ioc_prod s s' hA_meas

variable [PseudoMetrizableSpace E]

private lemma StronglyAdapted.stronglyMeasurable_leftApprox
    {u : ι → Ω → E} (h_adapted : StronglyAdapted 𝓕 u) (f : ℕ → ι) (n : ℕ) :
    StronglyMeasurable[𝓕.predictable]
      (fun p : ι × Ω ↦ u (leftApprox f n p.1) p.2) := by
  set pts := (range (n + 1)).image f
  refine @stronglyMeasurable_of_tendsto (ι × Ω) E ℕ 𝓕.predictable _ _ atTop _ _
    (fun m p ↦ (h_adapted (leftApprox f n p.1)).approx m p.2) _ (fun m ↦ ?_)
    (tendsto_pi_nhds.mpr fun ⟨t, ω⟩ ↦ (h_adapted (leftApprox f n t)).tendsto_approx ω)
  let W := @SimpleFunc.mk (ι × Ω) 𝓕.predictable E
      (fun p ↦ (h_adapted (leftApprox f n p.1)).approx m p.2)
      (fun c ↦ by
        have heq : (fun p ↦ (h_adapted (leftApprox f n p.1)).approx m p.2) ⁻¹' {c}
            = ⋃ s ∈ insert ⊥ pts,
              {t | leftApprox f n t = s} ×ˢ ((h_adapted s).approx m ⁻¹' {c}) := by
          ext ⟨t, ω⟩
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
            Set.mem_prod, Set.mem_setOf_eq]
          exact ⟨fun h ↦ ⟨leftApprox f n t, leftApprox_mem_insert_bot _ n t, rfl, h⟩,
            fun ⟨_, _, rfl, h⟩ ↦ h⟩
        rw [heq]
        exact MeasurableSet.biUnion (insert ⊥ pts).finite_toSet.countable
          (fun s hs ↦ measurableSet_predictable_leftApprox_fiber_prod
            h_adapted f n m c (mem_coe.mp hs)))
      (by
        refine ((insert ⊥ pts).finite_toSet.biUnion (fun s _ ↦
          @SimpleFunc.finite_range Ω E (𝓕 s) ((h_adapted s).approx m))).subset ?_
        rintro c ⟨⟨t, ω⟩, rfl⟩
        exact Set.mem_biUnion (mem_coe.mpr (leftApprox_mem_insert_bot _ n t)) ⟨ω, rfl⟩)
  exact W.stronglyMeasurable

end PredictableMeasurability

section LeftApproxConvergence

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] [TopologicalSpace E]

private lemma tendsto_leftApprox_uncurry
    {u : ι → Ω → E}
    (h_left_cont : ∀ ω i, Tendsto (u · ω) (𝓝[<] i) (𝓝 (u i ω)))
    {D : Set ι} (hDdense : Dense D) {d : ℕ → D} (hd_surj : Function.Surjective d) :
    Tendsto (fun n (p : ι × Ω) ↦ u (leftApprox (fun k ↦ (d k : ι)) n p.1) p.2)
      atTop (nhds (Function.uncurry u)) := by
  rw [tendsto_pi_nhds]
  intro ⟨t, ω⟩
  by_cases ht : t = ⊥
  · subst ht
    simp_rw [show ∀ n, leftApprox (fun k ↦ (d k : ι)) n ⊥ = ⊥ from
      fun n ↦ le_antisymm (leftApprox_le _ n ⊥) bot_le]
    exact tendsto_const_nhds
  · exact (h_left_cont ω t).comp (tendsto_leftApprox_nhdsWithin_Iio hDdense hd_surj ht)

end LeftApproxConvergence

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [DenselyOrdered ι] [SecondCountableTopology ι] [TopologicalSpace E] [PseudoMetrizableSpace E]
    {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ}

theorem StronglyAdapted.isPredictable_of_leftContinuous
    {u : ι → Ω → E} (h_adapted : StronglyAdapted 𝓕 u)
    (h_left_cont : ∀ ω i, Tendsto (u · ω) (𝓝[<] i) (𝓝 (u i ω))) : IsPredictable 𝓕 u := by
  obtain ⟨D, hDcount, hDdense⟩ := exists_countable_dense ι
  obtain ⟨d, hd_surj⟩ := hDcount.exists_surjective hDdense.nonempty
  exact @stronglyMeasurable_of_tendsto (ι × Ω) E ℕ 𝓕.predictable _ _ atTop _ _
    (fun n p ↦ u (leftApprox (fun k ↦ (d k : ι)) n p.1) p.2)
    (Function.uncurry u)
    (fun n ↦ h_adapted.stronglyMeasurable_leftApprox _ n)
    (tendsto_leftApprox_uncurry h_left_cont hDdense hd_surj)

end MeasureTheory
