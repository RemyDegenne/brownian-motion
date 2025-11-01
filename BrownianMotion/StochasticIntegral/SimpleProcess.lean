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

variable {ι Ω E F : Type*} [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

open scoped Function

/-- A simple process. TODO: more details. -/
structure SimpleProcess (ι Ω E F : Type*) [LinearOrder ι] [OrderBot ι]
    [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- The intervals over which we sum to define the integral. -/
  intervals : Finset (ι × ι)
  disjoint_intervals : Pairwise (Disjoint on (fun p : intervals ↦ Set.Ioc p.1.1 p.1.2))
  /-- The values of the process at the left endpoints of the intervals. -/
  value : ι → Ω → E →L[ℝ] F -- only the values at left endpoints of intervals are used

noncomputable
instance : CoeFun (SimpleProcess ι Ω E F) (fun _ ↦ ι → Ω → E →L[ℝ] F) where
  coe V := fun i ω ↦ ∑ p ∈ V.intervals, (Set.Ioc p.1 p.2).indicator (fun _ ↦ V.value p.1 ω) i

-- todo: write stoppedProcess as a min?
/-- The elementary stochastic integral. -/
noncomputable
def SimpleProcess.integral (V : SimpleProcess ι Ω E F) (X : ι → Ω → E) : ι → Ω → F :=
  fun i ω ↦ ∑ p ∈ V.intervals,
    V.value p.1 ω (stoppedProcess X (fun _ ↦ i) p.2 ω - stoppedProcess X (fun _ ↦ i) p.1 ω)

-- todo: possible notation V●X, possibly for more general integrals

end ProbabilityTheory
