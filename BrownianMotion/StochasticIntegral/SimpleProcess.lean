/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Process.Stopping
import BrownianMotion.Gaussian.BrownianMotion

/-! # Simple processes and elementary stochastic integral

-/

open MeasureTheory Filter Finset
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω E F G : Type*} [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {𝓕 : Filtration ι mΩ}

open scoped Function

/-- A simple process. TODO: more details. -/
structure SimpleProcess (ι F : Type*) [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] (𝓕 : Filtration ι mΩ) where
  /-- The intervals over which we sum to define the integral. -/
  intervals : Finset (ι × ι)
  /-- The values of the process at the left endpoints of the intervals. -/
  value : ι → Ω → F -- only the values at left endpoints of intervals are used
  measurable_value_bot : Measurable[𝓕 ⊥] (value ⊥)
  measurable_value : ∀ p ∈ intervals, Measurable[𝓕 p.1] (value p.1)

noncomputable
instance : CoeFun (SimpleProcess ι F 𝓕) (fun _ ↦ ι → Ω → F) where
  coe V := fun i ω ↦ ({⊥} : Set ι).indicator (fun _ ↦ V.value ⊥ ω) i
    + ∑ p ∈ V.intervals, (Set.Ioc p.1 p.2).indicator (fun _ ↦ V.value p.1 ω) i

-- TODO: write stoppedProcess as a min?
/-- The elementary stochastic integral. -/
noncomputable
def SimpleProcess.integral (B : E →L[ℝ] F →L[ℝ] G) (X : ι → Ω → E) (V : SimpleProcess ι F 𝓕) :
    ι → Ω → G :=
  fun i ω ↦ ∑ p ∈ V.intervals,
    B (stoppedProcess X (fun _ ↦ i) p.2 ω - stoppedProcess X (fun _ ↦ i) p.1 ω) (V.value p.1 ω)

-- TODO: possible notation V●X, possibly for more general integrals

end ProbabilityTheory
