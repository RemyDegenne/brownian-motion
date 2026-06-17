/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.DoobMeyer
public import BrownianMotion.StochasticIntegral.SquareIntegrable

/-! # Quadratic variation of locally square-integrable martingales

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

section StoppedProcessSqNorm

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [NormedAddCommGroup E]
  {X : ι → Ω → E}

/-- Stopping the indicator-truncated squared norm is the squared norm of the stopped
indicator-truncated process. -/
private lemma stoppedProcess_indicator_sq_norm {τ : Ω → WithTop ι} :
    stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (fun ω ↦ ‖X t ω‖ ^ 2)) τ =
      fun t ω ↦ ‖stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ t ω‖ ^ 2 := by
  ext t ω
  by_cases hτ : ⊥ < τ ω <;> simp [stoppedProcess, hτ]

end StoppedProcessSqNorm

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

/-- A locally square-integrable martingale has locally submartingale squared norm. -/
lemma IsLocallySquareIntegrable.isLocalSubmartingale_sq_norm
    [SigmaFiniteFiltration P 𝓕]
    (hX_sq : IsLocallySquareIntegrable X 𝓕 P) :
    IsLocalSubmartingale (fun t ω ↦ ‖X t ω‖ ^ 2) 𝓕 P := by
  let X2 : ι → Ω → ℝ := fun t ω ↦ ‖X t ω‖ ^ 2
  unfold IsLocalSubmartingale
  change Locally (fun Y : ι → Ω → ℝ ↦ Submartingale Y 𝓕 P ∧
      ∀ ω, IsCadlag (Y · ω)) 𝓕 X2 P
  refine ⟨hX_sq.localSeq, hX_sq.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [X2, stoppedProcess_indicator_sq_norm] using
      (hX_sq.stoppedProcess_localSeq n).submartingale_sq_norm
  · intro ω
    simpa [X2, stoppedProcess_indicator_sq_norm] using
      IsCadlag.norm_sq ((hX_sq.stoppedProcess_localSeq n).cadlag ω)

variable [MeasurableSpace ι]

/-- The quadratic variation of a locally square-integrable martingale, defined as the predictable
part of the Doob-Meyer decomposition of its squared norm.

The explicit càdlàg hypothesis remains because `predictablePart` requires càdlàg paths for
every `ω`. -/
noncomputable
def quadraticVariation [SigmaFiniteFiltration P 𝓕]
    (hX_sq : IsLocallySquareIntegrable X 𝓕 P)
    (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ :=
  have hX2_cadlag : ∀ ω, IsCadlag (fun t ↦ ‖X t ω‖ ^ 2) :=
    fun ω ↦ IsCadlag.norm_sq (hX_cadlag ω)
  (hX_sq.isLocalSubmartingale_sq_norm).predictablePart
    (fun t ω ↦ ‖X t ω‖ ^ 2) hX2_cadlag

end ProbabilityTheory
