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
* `Filtration.Predictable` : The predictable σ-algebra associated to a filtration.
* `Filtration.IsPredictable` : A process is predictable if it is measurable with respect to the
  predictable σ-algebra.

## Main results
* `Filtration.IsPredictable.progMeasurable` : A predictable process is progressively measurable.
* `Filtration.IsPredictable.measurable_succ` : `u` is a discrete predictable process iff
  `u (n + 1)` is `𝓕 n`-measurable and `u 0` is `𝓕 0`-measurable.

-/

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory.Filtration

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {E : Type*} [TopologicalSpace E]

section

variable [Preorder ι]

/-- Given a filtration `𝓕`, its **right continuation** is defined by
`𝓕 i := m ⊓ ⨅ j > i, 𝓕 j`. We define it with `m ⊓ ·` to ensure that it is smaller than `m`.

In general the index set does not contain any maximal element and we recover the usual expression,
see `rightCont_eq`. -/
def rightCont (𝓕 : Filtration ι m) : Filtration ι m where
  seq i := m ⊓ ⨅ j > i, 𝓕 j
  mono' i j hij := by
    refine le_inf (inf_le_left.trans le_rfl) ?_
    exact inf_le_right.trans <| le_iInf₂ fun k hkj ↦ iInf₂_le k (hij.trans_lt hkj)
  le' _ := inf_le_left

lemma rightCont_def (𝓕 : Filtration ι m) (i : ι) :
    𝓕.rightCont i = m ⊓ ⨅ j > i, 𝓕 j := sorry

lemma rightCont_eq_of_not_isMax (𝓕 : Filtration ι m) {i : ι} (hi : ¬IsMax i) :
    𝓕.rightCont i = ⨅ j > i, 𝓕 j := sorry

lemma rightCont_eq_of_isMax (𝓕 : Filtration ι m) {i : ι} (hi : IsMax i) :
    𝓕.rightCont i = m := sorry

lemma rightCont_eq [NoMaxOrder ι] (𝓕 : Filtration ι m) (i : ι) :
    𝓕.rightCont i = ⨅ j > i, 𝓕 j := sorry

lemma le_rightCont (𝓕 : Filtration ι m) : 𝓕 ≤ 𝓕.rightCont := sorry

/-- A filtration `𝓕` is right continuous if it is equal to its right continuation `𝓕.rightCont`,
i.e. for all `i`, `𝓕 i = m ⊓ ⨅ j > i, ℱ j`. -/
class IsRightContinuous (𝓕 : Filtration ι m) where
    /-- The right continuity property. -/
    RC : 𝓕.rightCont ≤ 𝓕

lemma IsRightContinuous.eq {𝓕 : Filtration ι m} [h : IsRightContinuous 𝓕] :
    𝓕 = 𝓕.rightCont := sorry

lemma IsRightContinuous.measurableSet {𝓕 : Filtration ι m} [IsRightContinuous 𝓕] {i : ι}
    {s : Set Ω} (hs : MeasurableSet[𝓕.rightCont i] s) :
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

end

end MeasureTheory.Filtration
