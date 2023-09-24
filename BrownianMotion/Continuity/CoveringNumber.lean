import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ENat.Lattice

variable {α : Type*}

/-- A set `C` is an `r`-cover of another set `A` if every point in `A` belongs to a ball with radius
`r` around a point of `C`. -/
def IsCover [Dist α] (C : Set α) (r : ℝ) (A : Set α) : Prop :=
  ∀ a ∈ A, ∃ c ∈ C, dist a c ≤ r

def IsSeparated [Dist α] (C : Set α) (r : ℝ) : Prop :=
  ∀ (a : α) (b : α) (_ : a ∈ C) (_ : b ∈ C), r ≤ dist a b

noncomputable
def externalCoveringNumber [Dist α] (r : ℝ) (A : Set α) : ENat :=
  ⨅ (C : Finset α) (_ : IsCover C r A), C.card

noncomputable
def internalCoveringNumber [Dist α] (r : ℝ) (A : Set α) : ENat :=
  ⨅ (C : Finset α) (_ : ↑C ⊆ A) (_ : IsCover C r A), C.card

noncomputable
def packingNumber [Dist α] (r : ℝ) (A : Set α) : ENat :=
  ⨆ (C : Finset α) (_ : ↑C ⊆ A) (_ : IsSeparated (C : Set α) r), C.card