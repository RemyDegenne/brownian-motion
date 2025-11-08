/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Topology.Defs.Filter

/-! # cadlag functions

-/

open Filter
open scoped Topology

variable {ι E : Type*} [LinearOrder ι] [TopologicalSpace ι] [TopologicalSpace E]

/-- A function is cadlag if it is right-continuous and has left limits. -/
def cadlag (f : ι → E) : Prop :=
  ∀ x, ContinuousWithinAt f (Set.Ici x) x ∧ ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)
