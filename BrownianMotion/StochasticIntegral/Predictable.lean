/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Adapted

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

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory.Filtration

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {E : Type*} [TopologicalSpace E]

open scoped Classical in
/-- Given a filtration `𝓕`, its **right continuation** is the filtration `𝓕₊` defined as follows:
- If `i` is isolated on the right, then `𝓕₊ i := 𝓕 i`;
- Otherwise, `𝓕₊ i := ⨅ j > i, 𝓕 j`.
It is sometimes simply defined as `𝓕₊ i := ⨅ j > i, 𝓕 j` when the index type is `ℝ`. In the
general case this is not ideal however. If `i` is maximal for instance, then `𝓕₊ i = ⊤`, which
is inconvenient because `𝓕₊` is not  a `Filtration ι m` anymore. If the index type
is discrete (such as `ℕ`), then we would have `𝓕 = 𝓕₊` (i.e. `𝓕` is right-continuous) only if
`𝓕` is constant.

To avoid requiring a `TopologicalSpace` instance on `ι` in the definition, we endow `ι` with
the order topology `Preorder.topology` inside the definition. Say you write a statement about
`𝓕₊` which does not require a `TopologicalSpace` structure on `ι`,
but you wish to use a statement which requires a topology (such as `rightCont_def`).
Then you can endow `ι` with
the order topology by writing
```lean
  letI := Preorder.topology ι
  haveI : OrderTopology ι := ⟨rfl⟩
``` -/
noncomputable def rightCont [PartialOrder ι] (𝓕 : Filtration ι m) : Filtration ι m :=
  letI : TopologicalSpace ι := Preorder.topology ι
  { seq i := if (𝓝[>] i).NeBot then ⨅ j > i, 𝓕 j else 𝓕 i
    mono' i j hij := by
      simp only [gt_iff_lt]
      split_ifs with hi hj hj
      · exact le_iInf₂ fun k hkj ↦ iInf₂_le k (hij.trans_lt hkj)
      · obtain rfl | hj := eq_or_ne j i
        · contradiction
        · exact iInf₂_le j (lt_of_le_of_ne hij hj.symm)
      · exact le_iInf₂ fun k hk ↦ 𝓕.mono (hij.trans hk.le)
      · exact 𝓕.mono hij
    le' i := by
      split_ifs with hi
      · obtain ⟨j, hj⟩ := (frequently_gt_nhds i).exists
        exact iInf₂_le_of_le j hj (𝓕.le j)
      · exact 𝓕.le i }

@[inherit_doc] scoped postfix:max "₊" => rightCont

open scoped Classical in
lemma rightCont_def [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) (i : ι) :
    𝓕₊ i = if (𝓝[>] i).NeBot then ⨅ j > i, 𝓕 j else 𝓕 i := sorry

lemma rightCont_eq_of_nhdsGT_eq_bot [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) {i : ι} (hi : 𝓝[>] i = ⊥) :
    𝓕₊ i = 𝓕 i := sorry

/-- If the index type is a `SuccOrder`, then `𝓕₊ = 𝓕`. -/
lemma rightCont_eq_self [LinearOrder ι] [SuccOrder ι] (𝓕 : Filtration ι m) :
    𝓕₊ = 𝓕 := sorry

lemma rightCont_eq_of_isMax [PartialOrder ι] (𝓕 : Filtration ι m) {i : ι} (hi : IsMax i) :
    𝓕₊ i = 𝓕 i := sorry

lemma rightCont_eq_of_exists_gt [PartialOrder ι] (𝓕 : Filtration ι m) {i : ι}
    (hi : ∃ j > i, Set.Ioo i j = ∅) :
    𝓕₊ i = 𝓕 i := sorry

/-- If `i` is not isolated on the right, then `𝓕₊ i = ⨅ j > i, 𝓕 j`. This is for instance the case
when `ι` is a densely ordered linear order with no maximal elements and equipped with the order
topology, see `rightCont_eq`. -/
lemma rightCont_eq_of_neBot_nhdsGT [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) (i : ι) [(𝓝[>] i).NeBot] :
    𝓕₊ i = ⨅ j > i, 𝓕 j := sorry

lemma rightCont_eq_of_not_isMax [LinearOrder ι] [DenselyOrdered ι]
    (𝓕 : Filtration ι m) {i : ι} (hi : ¬IsMax i) :
    𝓕₊ i = ⨅ j > i, 𝓕 j := sorry

/-- If `ι` is a densely ordered linear order with no maximal elements, then no point is isolated
on the right, so that `𝓕₊ i = ⨅ j > i, 𝓕 j` holds for all `i`. This is in particular the
case when `ι := ℝ≥0`. -/
lemma rightCont_eq [LinearOrder ι] [DenselyOrdered ι] [NoMaxOrder ι]
    (𝓕 : Filtration ι m) (i : ι) :
    𝓕₊ i = ⨅ j > i, 𝓕 j := sorry

variable [PartialOrder ι]

lemma le_rightCont (𝓕 : Filtration ι m) : 𝓕 ≤ 𝓕₊ := sorry

lemma rightCont_self (𝓕 : Filtration ι m) : 𝓕₊₊ = 𝓕₊ := sorry

/-- A filtration `𝓕` is right continuous if it is equal to its right continuation `𝓕₊`. -/
class IsRightContinuous (𝓕 : Filtration ι m) where
    /-- The right continuity property. -/
    RC : 𝓕₊ ≤ 𝓕

lemma IsRightContinuous.eq {𝓕 : Filtration ι m} [h : IsRightContinuous 𝓕] :
    𝓕 = 𝓕₊ := sorry

lemma isRightContinuous_rightCont (𝓕 : Filtration ι m) : 𝓕₊.IsRightContinuous := sorry

lemma IsRightContinuous.measurableSet {𝓕 : Filtration ι m} [IsRightContinuous 𝓕] {i : ι}
    {s : Set Ω} (hs : MeasurableSet[𝓕₊ i] s) :
    MeasurableSet[𝓕 i] s := sorry

/-- A filtration `𝓕` is said to satisfy the usual conditions if it is right continuous and `𝓕 0`
  and consequently `𝓕 t` is complete (i.e. contains all null sets) for all `t`. -/
class HasUsualConditions [OrderBot ι] (𝓕 : Filtration ι m) (μ : Measure Ω := by volume_tac)
    extends IsRightContinuous 𝓕 where
    /-- `𝓕 ⊥` contains all the null sets. -/
    IsComplete ⦃s : Set Ω⦄ (hs : μ s = 0) : MeasurableSet[𝓕 ⊥] s

variable [OrderBot ι]

instance {𝓕 : Filtration ι m} {μ : Measure Ω} [u : HasUsualConditions 𝓕 μ] {i : ι} :
    @Measure.IsComplete Ω (𝓕 i) (μ.trim <| 𝓕.le _) :=
  ⟨fun _ hs ↦ 𝓕.mono bot_le _ <| u.2 (measure_eq_zero_of_trim_eq_zero (Filtration.le 𝓕 _) hs)⟩

lemma HasUsualConditions.measurableSet_of_null
    (𝓕 : Filtration ι m) {μ : Measure Ω} [u : HasUsualConditions 𝓕 μ] (s : Set Ω) (hs : μ s = 0) :
    MeasurableSet[𝓕 ⊥] s :=
  u.2 hs

end MeasureTheory.Filtration
