/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Probability.Process.Predictable

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
* `MeasureTheory.StronglyAdapted.isPredictable_of_leftContinuous`: A left-continuous adapted
  process is predictable if the index set is `DenselyOrdered`.

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

open Filter Function MeasureTheory Order Set TopologicalSpace

open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {ι : Type*} [LinearOrder ι] [OrderBot ι]

/-- helper function which (strictly) rounds down `i` onto the set `{⊥} ∪ s` -/
private def roundDown (s : Finset ι) (i : ι) :=
  (insert ⊥ {j ∈ s | j < i}).max' (by simp)

private lemma roundDown_bot {s : Finset ι} : roundDown s ⊥ = ⊥ :=
  eq_bot_iff.mpr <| Finset.max'_le _ _ _ (by simp)

private lemma roundDown_lt_of_ne_bot {s : Finset ι} {i : ι} (h : i ≠ ⊥) :
    roundDown s i < i := by
  apply lt_of_le_of_ne
  · apply Finset.max'_le _ _ _ (fun _ _ ↦ by grind)
  · contrapose! h
    simp [roundDown, Finset.max'_eq_iff] at h
    aesop

private lemma roundDown_le_of_subset {s t : Finset ι} {i : ι} (h : s ⊆ t) :
    roundDown s i ≤ roundDown t i :=
  Finset.max'_le _ _ _ <| fun _ _ ↦ by apply Finset.le_max'; aesop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ}

lemma measurableSet_predictable_univ_prod {s : Set Ω} (hs : MeasurableSet[𝓕 ⊥] s) :
    MeasurableSet[𝓕.predictable] (univ ×ˢ s) := by
  rw [(by simp : univ = {⊥} ∪ Ioi ⊥), union_prod]
  refine MeasurableSet.union ?_ ?_
  · exact measurableSet_predictable_singleton_bot_prod hs
  · exact measurableSet_predictable_Ioi_prod hs

lemma measurableSet_predictable_Iic_prod {s : Set Ω} (hs : MeasurableSet[𝓕 ⊥] s) {i} :
    MeasurableSet[𝓕.predictable] (Iic i ×ˢ s) := by
  rw [(by simp : Iic i = {⊥} ∪ Ioc ⊥ i), union_prod]
  refine MeasurableSet.union ?_ ?_
  · exact measurableSet_predictable_singleton_bot_prod hs
  · exact measurableSet_predictable_Ioc_prod ⊥ i hs

variable {β : Type*} {mβ : MeasurableSpace β} [TopologicalSpace β] [PseudoMetrizableSpace β]
variable {X : ι → Ω → β}

/- a 'rounded down' function is predictable -/
private lemma StronglyAdapted.isPredictable_roundDown {times : Finset ι}
    (h_adap : StronglyAdapted 𝓕 X) :
    IsPredictable 𝓕 (fun i ω ↦ X (roundDown times i) ω) := by
  letI : MeasurableSpace (ι × Ω) := 𝓕.predictable
  -- `X_ap i` approximates X at times `i`
  let X_ap n i := (h_adap i).approx n
  -- For `Y` and `Y_ap`, we keep `s` as a variable for use in the induction step
  -- `Y` is the uncurried version of the rounded down `X`
  let Y s (x : ι × Ω) := X (roundDown s x.1) x.2
  -- `Y_ap` approximates `Y`
  let Y_ap n s (x : ι × Ω) := X_ap n (roundDown s x.1) x.2
  apply stronglyMeasurable_of_tendsto (u := atTop) (f := fun n x ↦ Y_ap n times x)
  · intro n
    refine SimpleFunc.mk (Y_ap n times) ?_ ?_ |>.stronglyMeasurable
    · intro b
      -- induction on the largest element of `times`
      refine times.induction_on_max ?_ ?_
      · apply MeasurableSet.congr (s := univ ×ˢ (X_ap n ⊥ ⁻¹' {b})) _ (by aesop)
        exact measurableSet_predictable_univ_prod (by measurability)
      intro t times ht_max hm
      apply MeasurableSet.congr
        (s := ((Y_ap n times ⁻¹' {b}) ∩ (Iic t ×ˢ univ)) ∪ (Ioi t) ×ˢ (X_ap n t ⁻¹' {b}))
      · apply MeasurableSet.union
        · apply MeasurableSet.inter (by assumption)
          exact measurableSet_predictable_Iic_prod (by measurability)
        · exact measurableSet_predictable_Ioi_prod (by measurability)
      · ext ⟨i, ω⟩
        simp_rw [Y_ap, mem_preimage]
        by_cases! hi : i ≤ t
        · have : roundDown (insert t times) i = roundDown times i := by
            rw [roundDown]; congr 2; grind
          rw [this]; aesop
        · have : roundDown (insert t times) i = t := by
            rw [roundDown, Finset.max'_eq_iff]; grind
          rw [this]; aesop
    · apply Finite.subset (s := (⋃ i ∈ (range (roundDown times)), range (X_ap n i))) _
        <| fun _ _ ↦ by aesop
      apply Finite.biUnion _ <| fun i _ ↦ by apply @(X_ap n i).finite_range
      apply Finite.subset (s := insert ⊥ times) (by aesop)
      intro i hi
      obtain ⟨j, rfl⟩ := mem_range.mp hi
      rw [← Finset.coe_insert, Finset.mem_coe]
      apply Finset.mem_of_subset (s₁ := insert ⊥ ({s ∈ times | s < j})) (by simp)
      apply Finset.max'_mem
  · simpa [Y_ap, tendsto_pi_nhds] using fun _ ↦ by apply StronglyMeasurable.tendsto_approx

variable [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [DenselyOrdered ι]

lemma StronglyAdapted.isPredictable_of_leftContinuous (h_adap : StronglyAdapted 𝓕 X)
    (h_cont : ∀ ω a, ContinuousWithinAt (X · ω) (Iio a) a) :
    IsPredictable 𝓕 X := by
  obtain ⟨d, hd_count, hd_dense⟩ := exists_countable_dense ι
  let times n := Finset.image (enumerateCountable hd_count ⊥) (Finset.range n)
  rw [IsPredictable]
  apply stronglyMeasurable_of_tendsto atTop (f := fun n x ↦ X (roundDown (times n) x.1) x.2)
  · exact fun _ ↦ isPredictable_roundDown (by aesop)
  rw [tendsto_pi_nhds]
  intro ⟨i, ω⟩
  apply (h_cont ω i).insert.tendsto.comp
  simp_rw [Iio_insert, tendsto_nhdsWithin_iff]
  by_cases! hi_bot : i = ⊥
  · simp [hi_bot, roundDown_bot]
  refine ⟨?_, .of_forall <| fun _ ↦ le_of_lt <| roundDown_lt_of_ne_bot hi_bot⟩
  apply tendsto_atTop_isLUB
    (fun _ _ _ ↦ roundDown_le_of_subset <| Finset.image_subset_image (by aesop))
  apply (isLUB_congr _).mp (isLUB_Iio (a := i))
  ext j; simp_rw [mem_upperBounds, mem_Iio]
  constructor
  · intro hj k hk
    apply hj
    obtain ⟨y, rfl⟩ := mem_range.mp hk
    apply roundDown_lt_of_ne_bot hi_bot
  · intro hj k hk
    obtain ⟨r, hr_mem, hr_lt⟩ := hd_dense.exists_between hk
    obtain ⟨n, h_rn⟩ := mem_range.mp <| subset_range_enumerate hd_count ⊥ hr_mem
    trans roundDown (times (n + 1)) i
    · trans r
      · exact le_of_lt (by aesop)
      · apply Finset.le_max' _ _ (by aesop)
    · apply hj _ (by aesop)

end MeasureTheory

namespace MeasureTheory.Filtration

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {E : Type*} [TopologicalSpace E] [PartialOrder ι]

/-- A filtration `𝓕` is complete with respect to a measure `μ` if for all `i`, `𝓕 i` contains all
the `μ`-null sets. -/
class IsComplete (𝓕 : Filtration ι m) (μ : Measure Ω := by volume_tac) where
    /-- `𝓕 ⊥` contains all the null sets. -/
    measurableSet_of_null ⦃s : Set Ω⦄ (hs : μ s = 0) (t : ι) : MeasurableSet[𝓕 t] s

instance {𝓕 : Filtration ι m} {μ : Measure Ω} [u : IsComplete 𝓕 μ] {i : ι} :
    (μ.trim <| 𝓕.le i).IsComplete :=
  ⟨fun _ hs ↦ IsComplete.measurableSet_of_null (measure_eq_zero_of_trim_eq_zero (𝓕.le i) hs) i⟩

end MeasureTheory.Filtration
