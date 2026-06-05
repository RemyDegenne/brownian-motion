/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.DoobMeyer

/-! # Quadratic variation of local martingales

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [MeasurableSpace ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

omit [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [NormedSpace ℝ E]
  [CompleteSpace E] in
/-- Stopping commutes with taking the squared norm. -/
lemma stoppedProcess_sq_norm {τ : Ω → WithTop ι} :
    stoppedProcess (fun t ω ↦ ‖X t ω‖ ^ 2) τ =
      fun t ω ↦ ‖stoppedProcess X τ t ω‖ ^ 2 := by
  ext t ω
  simp [stoppedProcess]

omit [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [NormedSpace ℝ E]
  [CompleteSpace E] in
/-- Stopping the indicator-truncated squared norm is the squared norm of the stopped
indicator-truncated process. -/
lemma stoppedProcess_indicator_sq_norm {τ : Ω → WithTop ι} :
    stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (fun ω ↦ ‖X t ω‖ ^ 2)) τ =
      fun t ω ↦ ‖stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ t ω‖ ^ 2 := by
  ext t ω
  by_cases hτ : ⊥ < τ ω <;> simp [stoppedProcess, hτ]

lemma IsLocalMartingale.isLocalSubmartingale_sq_norm
    (hX : IsLocalMartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    IsLocalSubmartingale (fun t ω ↦ ‖X t ω‖ ^ 2) 𝓕 P := by
  let X2 : ι → Ω → ℝ := fun t ω ↦ ‖X t ω‖ ^ 2
  have hX2_cadlag : ∀ ω, IsCadlag (X2 · ω) := by
    intro ω
    simpa [X2, Function.comp_def] using
      ((hX_cadlag ω).continuous_comp (continuous_norm.pow 2))
  unfold IsLocalSubmartingale
  change Locally (fun Y : ι → Ω → ℝ ↦ Submartingale Y 𝓕 P ∧
      ∀ ω, IsCadlag (Y · ω)) 𝓕 X2 P
  have hX2_sub_local : Locally (fun Y : ι → Ω → ℝ ↦ Submartingale Y 𝓕 P) 𝓕 X2 P := by
    -- A direct use of `IsSquareIntegrable.submartingale_sq_norm` requires a further
    -- localization making the stopped local martingales square-integrable. After that,
    -- `stoppedProcess_indicator_sq_norm` converts the localized square to the square of
    -- the localized martingale.
    sorry
  refine ⟨hX2_sub_local.localSeq, hX2_sub_local.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  exact ⟨hX2_sub_local.stoppedProcess_localSeq n,
    isStable_isCadlag X2 hX2_cadlag (hX2_sub_local.localSeq n)
      (hX2_sub_local.isLocalizingSequence_localSeq.isStoppingTime n)⟩

/-- The quadratic variation of a local martingale, defined as the predictable part of the Doob-Meyer
decomposition of its squared norm. -/
noncomputable
def quadraticVariation (hX : IsLocalMartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ :=
  have hX2_cadlag : ∀ ω, IsCadlag (fun t ↦ ‖X t ω‖ ^ 2) := by
    intro ω
    simpa [Function.comp_def] using
      ((hX_cadlag ω).continuous_comp (continuous_norm.pow 2))
  (hX.isLocalSubmartingale_sq_norm hX_cadlag).predictablePart (fun t ω ↦ ‖X t ω‖ ^ 2) hX2_cadlag

end ProbabilityTheory
