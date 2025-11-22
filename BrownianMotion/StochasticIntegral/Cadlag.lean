/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # cadlag functions

-/

open Filter TopologicalSpace Bornology
open scoped Topology

variable {ι E : Type*} [PartialOrder ι] [TopologicalSpace ι] [TopologicalSpace E]

/-- The predicate that a function is right continuous. -/
abbrev Function.RightContinuous (f : ι → E) :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a

/-- A function is cadlag if it is right-continuous and has left limits. -/
structure IsCadlag (f : ι → E) : Prop where
  right_continuous : Function.RightContinuous f
  left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)

/-- A càdlàg function maps compact sets to bounded sets. -/
lemma isBounded_image_of_isCadlag_of_isCompact {E : Type*}
    [FirstCountableTopology ι] [PseudoMetricSpace E] {f : ι → E}
    (hf : IsCadlag f) {s : Set ι} (hs : IsCompact s) :
    IsBounded (f '' s) := by
  sorry
