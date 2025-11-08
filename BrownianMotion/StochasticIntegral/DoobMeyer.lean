/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.StochasticIntegral.Cadlag
import BrownianMotion.StochasticIntegral.ClassD
import BrownianMotion.StochasticIntegral.LocalMartingale

/-! # Doob-Meyer decomposition theorem

-/

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}

namespace IsLocalSubmartingale

-- the sorry is locally integrable
theorem doob_meyer (hX : IsLocalSubmartingale X 𝓕 P) :
    ∃ (M A : ι → Ω → ℝ), X = M + A ∧ IsLocalMartingale M 𝓕 P ∧ (∀ ω, cadlag (M · ω)) ∧
      IsPredictable 𝓕 A ∧ (∀ ω, cadlag (A · ω)) ∧ (HasLocallyIntegrableSup A 𝓕 P)
      ∧ (∀ ω, Monotone (A · ω)) := by
  sorry

/-- The martingale part of the local submartingale. -/
noncomputable
def martingalePart (hX : IsLocalSubmartingale X 𝓕 P) :
    ι → Ω → ℝ :=
  hX.doob_meyer.choose

/-- The predictable part of the local submartingale. -/
noncomputable
def predictablePart (hX : IsLocalSubmartingale X 𝓕 P) :
    ι → Ω → ℝ :=
  hX.doob_meyer.choose_spec.choose

lemma martingalePart_add_predictablePart (hX : IsLocalSubmartingale X 𝓕 P) :
    X = hX.martingalePart + hX.predictablePart :=
  hX.doob_meyer.choose_spec.choose_spec.1

lemma isLocalMartingale_martingalePart (hX : IsLocalSubmartingale X 𝓕 P) :
    IsLocalMartingale hX.martingalePart 𝓕 P :=
  hX.doob_meyer.choose_spec.choose_spec.2.1

lemma cadlag_martingalePart (hX : IsLocalSubmartingale X 𝓕 P) :
    ∀ ω, cadlag (hX.martingalePart · ω) :=
  hX.doob_meyer.choose_spec.choose_spec.2.2.1

lemma isPredictable_predictablePart (hX : IsLocalSubmartingale X 𝓕 P) :
    IsPredictable 𝓕 hX.predictablePart :=
  hX.doob_meyer.choose_spec.choose_spec.2.2.2.1

lemma cadlag_predictablePart (hX : IsLocalSubmartingale X 𝓕 P) :
    ∀ ω, cadlag (hX.predictablePart · ω) :=
  hX.doob_meyer.choose_spec.choose_spec.2.2.2.2.1

lemma hasLocallyIntegrableSup_predictablePart (hX : IsLocalSubmartingale X 𝓕 P) :
    HasLocallyIntegrableSup hX.predictablePart 𝓕 P :=
  hX.doob_meyer.choose_spec.choose_spec.2.2.2.2.2.1

lemma monotone_predictablePart (hX : IsLocalSubmartingale X 𝓕 P) :
    ∀ ω, Monotone (hX.predictablePart · ω) :=
  hX.doob_meyer.choose_spec.choose_spec.2.2.2.2.2.2

end IsLocalSubmartingale

end ProbabilityTheory
