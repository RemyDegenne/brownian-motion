/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.DoobMeyer
public import BrownianMotion.StochasticIntegral.SquareIntegrable

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
/-- Stopping the indicator-truncated squared norm is the squared norm of the stopped
indicator-truncated process. -/
lemma stoppedProcess_indicator_sq_norm {τ : Ω → WithTop ι} :
    stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (fun ω ↦ ‖X t ω‖ ^ 2)) τ =
      fun t ω ↦ ‖stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ t ω‖ ^ 2 := by
  ext t ω
  by_cases hτ : ⊥ < τ ω <;> simp [stoppedProcess, hτ]

omit [MeasurableSpace ι] in
/-- The squared norm of a square-integrable martingale is a local submartingale. -/
lemma IsSquareIntegrable.isLocalSubmartingale_sq_norm [SigmaFiniteFiltration P 𝓕]
    (hX : IsSquareIntegrable X 𝓕 P) :
    IsLocalSubmartingale (fun t ω ↦ ‖X t ω‖ ^ 2) 𝓕 P := by
  refine .of_prop ⟨hX.submartingale_sq_norm, fun ω ↦ ?_⟩
  simpa [Function.comp_def] using
    ((hX.cadlag ω).continuous_comp (continuous_norm.pow 2))

omit [MeasurableSpace ι] in
/-- A locally square-integrable process has locally submartingale squared norm. -/
lemma Locally.isSquareIntegrable_submartingale_sq_norm [SigmaFiniteFiltration P 𝓕]
    (hX : Locally (fun Y : ι → Ω → E ↦ IsSquareIntegrable Y 𝓕 P) 𝓕 X P) :
    Locally (fun Y : ι → Ω → ℝ ↦ Submartingale Y 𝓕 P) 𝓕
      (fun t ω ↦ ‖X t ω‖ ^ 2) P := by
  refine ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  simpa [stoppedProcess_indicator_sq_norm] using
    (hX.stoppedProcess_localSeq n).submartingale_sq_norm

omit [MeasurableSpace ι] in
/-- A locally square-integrable local martingale has locally submartingale squared norm. -/
lemma IsLocalMartingale.isLocalSubmartingale_sq_norm_of_localSquareIntegrable
    [SigmaFiniteFiltration P 𝓕]
    (_hX : IsLocalMartingale X 𝓕 P)
    (hX_sq : Locally (fun Y : ι → Ω → E ↦ IsSquareIntegrable Y 𝓕 P) 𝓕 X P)
    (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
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
    simpa [X2] using hX_sq.isSquareIntegrable_submartingale_sq_norm
  refine ⟨hX2_sub_local.localSeq, hX2_sub_local.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  exact ⟨hX2_sub_local.stoppedProcess_localSeq n,
    isStable_isCadlag X2 hX2_cadlag (hX2_sub_local.localSeq n)
      (hX2_sub_local.isLocalizingSequence_localSeq.isStoppingTime n)⟩

omit [MeasurableSpace ι] in
lemma IsLocalMartingale.isLocalSubmartingale_sq_norm
    [SigmaFiniteFiltration P 𝓕]
    (hX : IsLocalMartingale X 𝓕 P)
    (hX_sq : Locally (fun Y : ι → Ω → E ↦ IsSquareIntegrable Y 𝓕 P) 𝓕 X P)
    (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    IsLocalSubmartingale (fun t ω ↦ ‖X t ω‖ ^ 2) 𝓕 P := by
  exact hX.isLocalSubmartingale_sq_norm_of_localSquareIntegrable hX_sq hX_cadlag

section QuadraticVariation

variable {κ Ω' E' : Type*} [ConditionallyCompleteLinearOrderBot κ] [TopologicalSpace κ]
  [OrderTopology κ] [MeasurableSpace κ] [BorelSpace κ] [PolishSpace κ]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} {X' : κ → Ω' → E'}
  {𝓕' : Filtration κ mΩ'} [IsFiniteMeasure P'] [Approximable 𝓕' P']
  [𝓕'.IsComplete P'] [𝓕'.IsRightContinuous]

/-- The quadratic variation of a local martingale, defined as the predictable part of the Doob-Meyer
decomposition of its squared norm. -/
noncomputable
def quadraticVariation (hX : IsLocalMartingale X' 𝓕' P')
    (hX_sq : Locally (fun Y : κ → Ω' → E' ↦ IsSquareIntegrable Y 𝓕' P') 𝓕' X' P')
    (hX_cadlag : ∀ ω, IsCadlag (X' · ω)) :
    κ → Ω' → ℝ :=
  have hX2_cadlag : ∀ ω, IsCadlag (fun t ↦ ‖X' t ω‖ ^ 2) := by
    intro ω
    simpa [Function.comp_def] using
      ((hX_cadlag ω).continuous_comp (continuous_norm.pow 2))
  IsLocalSubmartingale.normalizedPredictablePart
    (fun t ω ↦ ‖X' t ω‖ ^ 2)
    (hX.isLocalSubmartingale_sq_norm hX_sq hX_cadlag) hX2_cadlag

end QuadraticVariation

end ProbabilityTheory
