/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Process.HittingTime

/-!
# Hitting times

Complements to `Mathlib.Probability.Process.HittingTime`.

## Main definitions

* `MeasureTheory.leastGT f r`: the first time that the process `f` is greater than `r`.

## Main statements

* `MeasureTheory.StronglyAdapted.isStoppingTime_leastGT`: in discrete time, `leastGT f r` is a
  stopping time if `f` is adapted.
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω β : Type*}

/-- `leastGT f r` is the stopping time corresponding to the first time `f > r`. -/
noncomputable def leastGT [Preorder ι] [OrderBot ι] [InfSet ι] [Preorder β]
    (f : ι → Ω → β) (r : β) : Ω → WithTop ι :=
  hittingAfter f (Set.Ioi r) ⊥

lemma leastGT_lt_iff [ConditionallyCompleteLinearOrder ι] [OrderBot ι] [Preorder β]
    {f : ι → Ω → β} {r : β} {t : ι} {ω : Ω} :
    leastGT f r ω < t ↔ ∃ s < t, r < f s ω := by
  simp [leastGT, hittingAfter_lt_iff]

theorem StronglyAdapted.isStoppingTime_leastGT [ConditionallyCompleteLinearOrderBot ι]
    {m0 : MeasurableSpace Ω} {ℱ : Filtration ι m0} [WellFoundedLT ι] [Countable ι]
    [TopologicalSpace β] [LinearOrder β] [ClosedIicTopology β]
    [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    {f : ι → Ω → β} (r : β) (hf : StronglyAdapted ℱ f) :
    IsStoppingTime ℱ (leastGT f r) :=
  hf.adapted.isStoppingTime_hittingAfter measurableSet_Ioi

end MeasureTheory
