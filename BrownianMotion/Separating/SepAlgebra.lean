import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

import Mathlib.Analysis.RCLike.Basic

/-!
# Separating algebras of bounded continuous functions

Bounded continuous functions

These functions are a star-subalgebra of `E →ᵇ ℂ` (see `expPoly`).

-/

open scoped BigOperators

open BoundedContinuousFunction Complex Set MeasureTheory

variable {α 𝕜 : Type*}

noncomputable
def IsSeparatesPoints (M : Set (α → 𝕜)) : Prop :=
∀ x y : α, x≠y → ∃ f ∈ M, f x ≠ f y

example (M : Set (α → 𝕜)) : IsSeparatesPoints M ↔ SeparatesPoints M := by
  rfl

variable [TopologicalSpace α] [MeasurableSpace α] [MetricSpace α] [BorelSpace α] [NormedAddCommGroup 𝕜]

def IsSeparating [NormedSpace ℝ 𝕜] (M : Set (α →ᵇ 𝕜)) : Prop :=
∀ P Q : Measure α, IsFiniteMeasure P →  IsFiniteMeasure Q → (∀ f ∈ M, ∫ x, f x ∂P = ∫ x, f x ∂Q) → P = Q

theorem IsSeparating_Cb [NormedSpace ℝ 𝕜] : IsSeparating (univ : Set (α →ᵇ 𝕜))  := by 
  sorry

example (f : α →ᵇ 𝕜) : (f : α → 𝕜) = @DFunLike.coe (α →ᵇ 𝕜) α (fun x ↦ 𝕜) instFunLike (f : α →ᵇ 𝕜) := by
  simp

example (f : α →ᵇ 𝕜) : (f : α → 𝕜) = DFunLike.coe f := by
  simp only
