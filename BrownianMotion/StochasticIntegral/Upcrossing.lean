/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Wojciech Czernous
-/
import BrownianMotion.Auxiliary.Martingale
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Upcrossing


/-! # Doob's upcrossing inequality

-/

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

#check Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [InfSet ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
  {Y : ι → Ω → ℝ}

/-- **Doob's upcrossing estimate**: given a real-valued discrete submartingale `f` and real
values `a` and `b`, we have `(b - a) * 𝔼[upcrossingsBefore a b f N] ≤ 𝔼[(f N - a)⁺]` where
`upcrossingsBefore a b f N` is the number of times the process `f` crossed from below `a` to above
`b` before the time `N`. -/
-- This is the version for countable time index. The original version for natural time index is in
--  .lake/packages/mathlib/Mathlib/Probability/Martingale/Upcrossing.lean
-- We shall extend the result "mul_integral_upcrossingsBefore_le_integral_pos_part",
-- which works for `ℕ` as time index, i.e., finite time index - as it is up to the time `N`.
-- By repeating the claim on a finite time index,
-- for denser and denser finite subsets of `Iic N`, we get the result for countable time index.
-- The result then follows thanks to monotone convergence theorem.
-- The point is to show that the number of upcrossings is:
-- - growing when we add more time points,
-- - converging to the number of upcrossings on the whole countable index set.
-- By inductively densening the time index, we mean adding one time point at a time.
theorem Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part_countable
    [Countable ι]
    (a b : ℝ) (hf : Submartingale X 𝓕 P) (N : ι) :
    (b - a) * P[upcrossingsBefore a b X N] ≤ P[fun ω => (X N ω - a)⁺] := by

end ProbabilityTheory
