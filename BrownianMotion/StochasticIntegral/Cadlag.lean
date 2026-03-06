/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Basic

/-! # cadlag functions

-/

open Filter TopologicalSpace Bornology
open scoped Topology

variable {ι E : Type*} [TopologicalSpace ι] [TopologicalSpace E]

/-- The predicate that a function is right continuous. -/
abbrev Function.RightContinuous [PartialOrder ι] (f : ι → E) :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a

lemma Function.RightContinuous.continuous_comp {F : Type*} [TopologicalSpace F] [PartialOrder ι]
    {g : E → F}
    {f : ι → E} (hg : Continuous g) (hf : RightContinuous f) : RightContinuous (g ∘ f) :=
  fun x ↦ (hg.tendsto (f x)).comp (hf x)

/-- A function is cadlag if it is right-continuous and has left limits. -/
structure IsCadlag [PartialOrder ι] (f : ι → E) : Prop where
  right_continuous : Function.RightContinuous f
  left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)

/-- A càdlàg function is locally bounded. -/
lemma isLocallyBounded_of_isCadlag {E : Type*} [LinearOrder ι] [PseudoMetricSpace E]
    {f : ι → E} (hf : IsCadlag f) (x : ι) : ∃ t ∈ 𝓝 x, IsBounded (f '' t) := by
  obtain ⟨l, hl⟩ := hf.2 x
  obtain ⟨U, ⟨⟨A, ⟨hp, ⟨W, hW⟩⟩⟩, hU⟩⟩ := Metric.exists_isBounded_image_of_tendsto hl
  obtain ⟨V, ⟨⟨B, ⟨hq, ⟨R, hR⟩⟩⟩, hV⟩⟩ := Metric.exists_isBounded_image_of_tendsto (hf.1 x).tendsto
  refine ⟨A ∩ B, inter_mem hp hq, ?_⟩
  apply IsBounded.subset ((hU.union hV).union (isBounded_singleton : Bornology.IsBounded ({f x})))
  rintro _ ⟨y, ⟨hyL, hyR⟩ , rfl⟩
  rcases lt_trichotomy y x with (hlt | heq | hgt)
  · have : y ∈ U := hW.2 ▸ ⟨hyL, hW.1 hlt⟩
    grind
  · grind
  · have : y ∈ V := hR.2 ▸ ⟨hyR, hR.1 hgt⟩
    grind

/-- A càdlàg function maps compact sets to bounded sets. -/
lemma isBounded_image_of_isCadlag_of_isCompact {E : Type*} [LinearOrder ι] [PseudoMetricSpace E]
    {f : ι → E} (hf : IsCadlag f) {s : Set ι} (hs : IsCompact s) :
    IsBounded (f '' s) :=
  isBounded_image_of_isLocallyBounded_of_isCompact hs (isLocallyBounded_of_isCadlag hf)
