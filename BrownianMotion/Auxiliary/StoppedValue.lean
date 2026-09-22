/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import BrownianMotion.Auxiliary.LimitProcess
public import BrownianMotion.StochasticIntegral.Cadlag
public import Mathlib.Probability.Process.Stopping

import BrownianMotion.Auxiliary.StronglyMeasurablePath

/-!

# Stopped value of a stochastic process

In mathlib, given a stochastic process `X : ι → Ω → E` and `τ : Ω → WithTop ι` a stopping time,
we define `stoppedValue X τ ω` as `X (τ ω)` if `τ ω ≠ ⊤`, and an arbitrary value otherwise.
This is not well suited in a number of context where `X` converges almost surely at infinity,
and we would expect the stopped value to be equal to the limit random variable when `τ ω = ⊤`
(this is for example true if `X` is a uniformly integrable martingale).

This limit process is always defined in mathlib as `𝓕.limitProcess X P`, with a default value
when it does not make sense. In this file we define `𝓕.stoppedValue' X τ P ω` to be equal
to `X (τ ω)` if `τ ω ≠ ⊤`, and `𝓕.limitProcess X P ω` otherwise.

-/

public section

open MeasureTheory

namespace MeasureTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω} {t : ι}

namespace Filtration

section Def

/-! ### Definition of the stopped value -/

variable [TopologicalSpace E] [Zero E] [Preorder ι] {𝓕 : Filtration ι mΩ}

open scoped Classical in
/-- Given a stochastic process `X` and a stopping time `τ` `𝓕.stoppedValue' X τ P` is the process
given by `X (τ ω)`, where `X ⊤` is given by `𝓕.limitProcess X P`. -/
noncomputable def stoppedValue' (X : ι → Ω → E) (τ : Ω → WithTop ι)
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) (ω : Ω) : E :=
  if h : τ ω = ⊤
    then 𝓕.limitProcess X P ω
    else
      X ((τ ω).untop h) ω

@[simp]
lemma stoppedValue'_of_eq_top (hτ : τ ω = ⊤) :
    𝓕.stoppedValue' X τ P ω = 𝓕.limitProcess X P ω := by
  rw [stoppedValue', dif_pos hτ]

lemma stoppedValue'_of_ne_top (hτ : τ ω ≠ ⊤) :
    𝓕.stoppedValue' X τ P ω = X ((τ ω).untop hτ) ω := by
  rw [stoppedValue', dif_neg hτ]

@[simp]
lemma stoppedValue'_of_eq_coe (hτ : τ ω = t) :
    𝓕.stoppedValue' X τ P ω = X t ω := by
  rw! [stoppedValue'_of_ne_top, hτ]
  · simp
  · simp [hτ]

lemma stoppedValue'_eq_stoppedValue [Nonempty ι] (hτ : τ ω ≠ ⊤) :
    𝓕.stoppedValue' X τ P ω = stoppedValue X τ ω := by
  rw [stoppedValue'_of_ne_top hτ, stoppedValue, WithTop.untopA_eq_untop hτ]

end Def

@[gcongr]
lemma stoppedValue'_congr [TopologicalSpace E] [Zero E] [T2Space E] [LinearOrder ι]
    {𝓕 : Filtration ι mΩ} (h : X ≡ᵐ[P] Y) :
    𝓕.stoppedValue' X τ P =ᵐ[P] 𝓕.stoppedValue' Y τ P := by
  filter_upwards [h, 𝓕.limitProcess_congr h] with ω h1 h2
  obtain _ | _ := eq_or_ne (τ ω) ⊤ <;> simp_all [stoppedValue'_of_ne_top]

end Filtration

section Measurability

/-! ### Strong measurability of the stopped value with respect to the stopped sigma-algebra -/

variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  {𝓕 : Filtration ι mΩ} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]

private lemma IsStoppingTime.stronglyMeasurable_limitProcess_indicator_eq_top
    [Zero E] (hτ : IsStoppingTime 𝓕 τ) :
    StronglyMeasurable[hτ.measurableSpace] ({ω | τ ω = ⊤}.indicator (𝓕.limitProcess X P)) := by
  borelize E
  rw [stronglyMeasurable_iff_measurable_separable]
  refine ⟨fun s hs ↦ (hτ.measurableSet _).2 ⟨?_, fun t ↦ ?_⟩,
    (𝓕.stronglyMeasurable_limit_process'.indicator hτ.measurableSet_eq_top).isSeparable_range⟩
  · exact hs.preimage (𝓕.stronglyMeasurable_limitProcess.measurable.indicator
      hτ.measurableSet_eq_top')
  have : MeasurableSet[𝓕 t] ({ω | 0 ∈ s} ∩ {ω | τ ω ≤ t}) := by
    by_cases h : 0 ∈ s
    · simpa [h] using hτ t
    · simp [h]
  convert this using 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, and_congr_left_iff]
  intro h
  have : τ ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
  simp [Set.indicator, this]

variable [MeasurableSpace ι] [BorelSpace ι]

lemma stronglyMeasurable_stoppedValue [Nonempty ι]
    (h : IsStronglyProgressive 𝓕 X)
    (hRC : ∀ ω, _root_.IsRightContinuous (X · ω)) (hτ : IsStoppingTime 𝓕 τ) :
    StronglyMeasurable[hτ.measurableSpace] (stoppedValue X τ) := by
  borelize E
  refine stronglyMeasurable_iff_measurable_separable.2 ⟨measurable_stoppedValue h hτ, ?_⟩
  refine (isSeparable_iUnion_range_of_stronglyMeasurable_of_isRightContinuous ?_ hRC).mono ?_
  · intro t
    exact h.stronglyAdapted t |>.mono (𝓕.le t)
  rintro - ⟨ω, rfl⟩
  simp [stoppedValue]

lemma Filtration.stronglyMeasurable_stoppedValue' [Zero E] [OrderBot ι]
    (hX : IsStronglyProgressive 𝓕 X) (hRC : ∀ ω, _root_.IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) :
    StronglyMeasurable[hτ.measurableSpace] (𝓕.stoppedValue' X τ P) := by
  have : 𝓕.stoppedValue' X τ P = {ω | τ ω = ⊤}.piecewise
      ({ω | τ ω = ⊤}.indicator (𝓕.limitProcess X P)) (stoppedValue X τ) := by
    ext ω
    obtain h | h := eq_or_ne (τ ω) ⊤
    · simp [h]
    · simp [h, stoppedValue'_eq_stoppedValue]
  rw [this]
  refine hτ.stronglyMeasurable_limitProcess_indicator_eq_top.piecewise ?_
    (stronglyMeasurable_stoppedValue hX hRC hτ)
  refine (hτ.measurableSet _).2 ⟨hτ.measurableSet_eq_top', fun t ↦ ?_⟩
  convert MeasurableSet.empty
  ext
  simp +contextual

end Measurability

end MeasureTheory
