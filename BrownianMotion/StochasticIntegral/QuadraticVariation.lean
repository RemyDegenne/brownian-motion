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

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [MeasurableSpace ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration P 𝓕]
  {X : ι → Ω → E}

open Classical in
/-- The predictable quadratic variation of a locally square-integrable martingale,
defined as the predictable part of the Doob-Meyer decomposition of its squared norm. -/
noncomputable
def predQuadVariation (X : ι → Ω → E) (P : Measure Ω) (𝓕 : Filtration ι mΩ)
    [SigmaFiniteFiltration P 𝓕] :
    ι → Ω → ℝ :=
  if hX : IsLocallySquareIntegrable X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω) then
    hX.1.isLocalSubmartingale_sq_norm.predictablePart (fun t ω ↦ ‖X t ω‖ ^ 2)
      (fun ω ↦ (hX.2 ω).norm_sq)
  else fun _ _ ↦ 0

scoped notation "⟨" X " ; " P ", " 𝓕 "⟩ₘ" => predQuadVariation X P 𝓕

@[simp]
lemma predQuadVariation_of_not_isLocallySquareIntegrable (hX : ¬IsLocallySquareIntegrable X 𝓕 P) :
    ⟨X ; P, 𝓕⟩ₘ = fun _ _ ↦ 0 := by
  unfold predQuadVariation
  simp [hX]

@[simp]
lemma predQuadVariation_of_not_cadlag (hX_cadlag : ¬∀ ω, IsCadlag (X · ω)) :
    ⟨X ; P, 𝓕⟩ₘ = fun _ _ ↦ 0 := by
  unfold predQuadVariation
  simp [hX_cadlag]

lemma isStronglyProgressive_predQuadVariation : IsStronglyProgressive 𝓕 ⟨X ; P, 𝓕⟩ₘ := by
  by_cases hX : IsLocallySquareIntegrable X 𝓕 P
  swap
  · rw [predQuadVariation_of_not_isLocallySquareIntegrable hX]
    exact isStronglyProgressive_const _ _
  by_cases hX_cadlag : ∀ ω, IsCadlag (X · ω)
  swap
  · rw [predQuadVariation_of_not_cadlag hX_cadlag]
    exact isStronglyProgressive_const _ _
  unfold predQuadVariation
  rw [dif_pos ⟨hX, hX_cadlag⟩]
  exact hX.isLocalSubmartingale_sq_norm.isStronglyProgressive_predictablePart
    (fun ω ↦ (hX_cadlag ω).norm_sq)

lemma isCadlag_predQuadVariation (ω : Ω) : IsCadlag (⟨X ; P, 𝓕⟩ₘ · ω) := by
  by_cases hX : IsLocallySquareIntegrable X 𝓕 P
  swap; · simp [hX]
  by_cases hX_cadlag : ∀ ω, IsCadlag (X · ω)
  swap; · simp [hX_cadlag]
  unfold predQuadVariation
  rw [dif_pos ⟨hX, hX_cadlag⟩]
  exact hX.isLocalSubmartingale_sq_norm.cadlag_predictablePart (fun ω ↦ (hX_cadlag ω).norm_sq) ω

lemma hasLocallyIntegrableSup_predQuadVariation :
    HasLocallyIntegrableSup ⟨X ; P, 𝓕⟩ₘ 𝓕 P := by
  by_cases hX : IsLocallySquareIntegrable X 𝓕 P
  swap
  · rw [predQuadVariation_of_not_isLocallySquareIntegrable hX]
    exact hasLocallyIntegrableSup_const 0 𝓕
  by_cases hX_cadlag : ∀ ω, IsCadlag (X · ω)
  swap
  · rw [predQuadVariation_of_not_cadlag hX_cadlag]
    exact hasLocallyIntegrableSup_const 0 𝓕
  unfold predQuadVariation
  rw [dif_pos ⟨hX, hX_cadlag⟩]
  exact hX.isLocalSubmartingale_sq_norm.hasLocallyIntegrableSup_predictablePart
    (fun ω ↦ (hX_cadlag ω).norm_sq)

lemma monotone_predQuadVariation (ω : Ω) : Monotone (⟨X ; P, 𝓕⟩ₘ · ω) := by
  by_cases hX : IsLocallySquareIntegrable X 𝓕 P
  swap; · rw [predQuadVariation_of_not_isLocallySquareIntegrable hX]; exact monotone_const
  by_cases hX_cadlag : ∀ ω, IsCadlag (X · ω)
  swap; · rw [predQuadVariation_of_not_cadlag hX_cadlag]; exact monotone_const
  unfold predQuadVariation
  rw [dif_pos ⟨hX, hX_cadlag⟩]
  exact hX.isLocalSubmartingale_sq_norm.monotone_predictablePart (fun ω ↦ (hX_cadlag ω).norm_sq) ω

end ProbabilityTheory
