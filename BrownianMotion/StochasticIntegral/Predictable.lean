/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Process.Filtration

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

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory.Filtration

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

end MeasureTheory.Filtration
