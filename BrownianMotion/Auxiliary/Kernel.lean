/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Probability.Kernel.Basic

/-! # Sufficient conditions for a kernel to be s-finite
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- A kernel all of whose measures are finite is s-finite. -/
lemma isSFiniteKernel_of_isFiniteMeasure (κ : Kernel α β) [∀ a, IsFiniteMeasure (κ a)] :
    IsSFiniteKernel κ := by
  classical
  let s : ℕ → Set α := fun n ↦ (fun a ↦ ⌊(κ a Set.univ).toNNReal⌋₊) ⁻¹' {n}
  have hs n : MeasurableSet (s n) :=
    Measurable.nat_floor (κ.measurable_coe MeasurableSet.univ).ennreal_toNNReal
      (measurableSet_singleton n)
  refine ⟨⟨fun n ↦ Kernel.piecewise (hs n) κ 0, fun n ↦ ⟨n + 1, by simp, fun a ↦ ?_⟩, ?_⟩⟩
  · rw [Kernel.piecewise_apply']
    split_ifs with ha
    · rw [← ENNReal.coe_toNNReal (measure_ne_top (κ a) Set.univ)]
      have h := Nat.lt_floor_add_one (κ a Set.univ).toNNReal
      have ha' : ⌊(κ a Set.univ).toNNReal⌋₊ = n := ha
      rw [ha'] at h
      exact_mod_cast h.le
    · simp
  · ext a t ht
    rw [Kernel.sum_apply, Measure.sum_apply _ ht, tsum_eq_single ⌊(κ a Set.univ).toNNReal⌋₊]
    · simp [Kernel.piecewise_apply', s]
    · intro n hn
      simp [Kernel.piecewise_apply', s, hn.symm]

/-- A kernel whose measures are finite on each set of a countable measurable cover is s-finite. -/
lemma isSFiniteKernel_of_measure_lt_top (κ : Kernel α β) {s : ℕ → Set β}
    (hs : ∀ n, MeasurableSet (s n)) (hs_univ : ⋃ n, s n = Set.univ)
    (h_fin : ∀ a n, κ a (s n) < ∞) : IsSFiniteKernel κ := by
  have hd n : MeasurableSet (disjointed s n) := MeasurableSet.disjointed hs n
  have h_eq : κ = Kernel.sum fun n ↦ κ.restrict (hd n) := by
    ext a t ht
    rw [Kernel.sum_apply, Measure.sum_apply _ ht]
    simp_rw [Kernel.restrict_apply' _ _ _ ht]
    rw [← measure_iUnion, ← Set.inter_iUnion, iUnion_disjointed, hs_univ, Set.inter_univ]
    · exact fun i j hij ↦ (disjoint_disjointed s hij).mono Set.inter_subset_right
        Set.inter_subset_right
    · exact fun n ↦ ht.inter (hd n)
  rw [h_eq]
  have h_sfin n : IsSFiniteKernel (κ.restrict (hd n)) := by
    have : ∀ a, IsFiniteMeasure (κ.restrict (hd n) a) := fun a ↦ ⟨by
      rw [Kernel.restrict_apply, Measure.restrict_apply_univ]
      exact (measure_mono (disjointed_subset s n)).trans_lt (h_fin a n)⟩
    exact Kernel.isSFiniteKernel_of_isFiniteMeasure _
  infer_instance

end ProbabilityTheory.Kernel
