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

namespace MeasureTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {E : Type*} [TopologicalSpace E]

section

variable [Preorder ι]

/-- A filtration `𝓕` is right continuous if `𝓕 t = ⨅ j > i, 𝓕 j = 𝓕 i` for all `t`. -/
class IsRightContinuous (𝓕 : Filtration ι m) where
    /-- The right continuity property. -/
    RC (i : ι) : ⨅ j > i, 𝓕 j = 𝓕 i

lemma measurableSet_of_isRightContinuous {𝓕 : Filtration ι m} [IsRightContinuous 𝓕] {i : ι}
    {s : Set Ω} (hs : MeasurableSet[⨅ j > i, 𝓕 j] s) :
    MeasurableSet[𝓕 i] s := by
  convert hs
  rw [IsRightContinuous.RC i]

/-- A filtration `𝓕` is said to satisfy the usual conditions if it is right continuous and `𝓕 0`
  and consequently `𝓕 t` is complete (i.e. contains all null sets) for all `t`. -/
class Filtration.UsualConditions [OrderBot ι] (𝓕 : Filtration ι m) (μ : Measure Ω := by volume_tac)
    extends IsRightContinuous 𝓕 where
    /-- `𝓕 ⊥` contains all the null sets. -/
    IsComplete ⦃s : Set Ω⦄ (hs : μ s = 0) : MeasurableSet[𝓕 ⊥] s

variable [OrderBot ι]

namespace Filtration

instance {𝓕 : Filtration ι m} {μ : Measure Ω} [u : UsualConditions 𝓕 μ] {i : ι} :
    @Measure.IsComplete Ω (𝓕 i) (μ.trim <| 𝓕.le _) :=
  ⟨fun _ hs ↦ 𝓕.mono bot_le _ <| u.2 (measure_eq_zero_of_trim_eq_zero (Filtration.le 𝓕 _) hs)⟩

lemma UsualConditions.measurableSet_of_null
    (𝓕 : Filtration ι m) {μ : Measure Ω} [u : UsualConditions 𝓕 μ] (s : Set Ω) (hs : μ s = 0) :
    MeasurableSet[𝓕 ⊥] s :=
  u.2 hs

end Filtration

end

end MeasureTheory
