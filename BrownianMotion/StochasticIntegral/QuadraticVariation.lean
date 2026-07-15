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
  {X Y : ι → Ω → E}

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

@[inherit_doc predQuadVariation]
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

lemma isStronglyPredictable_const {ι E : Type*} [Preorder ι] [OrderBot ι] [MeasurableSpace ι]
    [TopologicalSpace E] (c : E) (𝓕 : Filtration ι mΩ) :
    IsStronglyPredictable 𝓕 (fun _ _ ↦ c : ι → Ω → E) := by
  unfold IsStronglyPredictable
  fun_prop

lemma isStronglyPredictable_predQuadVariation : IsStronglyPredictable 𝓕 ⟨X ; P, 𝓕⟩ₘ := by
  by_cases hX : IsLocallySquareIntegrable X 𝓕 P
  swap
  · rw [predQuadVariation_of_not_isLocallySquareIntegrable hX]
    exact isStronglyPredictable_const _ _
  by_cases hX_cadlag : ∀ ω, IsCadlag (X · ω)
  swap
  · rw [predQuadVariation_of_not_cadlag hX_cadlag]
    exact isStronglyPredictable_const _ _
  unfold predQuadVariation
  rw [dif_pos ⟨hX, hX_cadlag⟩]
  exact hX.isLocalSubmartingale_sq_norm.isStronglyPredictable_predictablePart
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

/-- Predictable quadratic covariation of two processes. -/
noncomputable
def predQuadCovariation (X Y : ι → Ω → E) (P : Measure Ω) (𝓕 : Filtration ι mΩ)
    [SigmaFiniteFiltration P 𝓕] :
    ι → Ω → ℝ :=
  (⟨X + Y ; P, 𝓕⟩ₘ - ⟨X ; P, 𝓕⟩ₘ - ⟨Y ; P, 𝓕⟩ₘ) / 2

@[inherit_doc predQuadCovariation]
scoped notation "⟨" X ", " Y " ; " P ", " 𝓕 "⟩ₘ" => predQuadCovariation X Y P 𝓕

lemma isStronglyPredictable_predQuadCovariation : IsStronglyPredictable 𝓕 ⟨X, Y ; P, 𝓕⟩ₘ := by
  unfold predQuadCovariation
  simp_rw [div_eq_inv_mul]
  refine IsStronglyPredictable.const_smul 2⁻¹ ?_
  refine IsStronglyPredictable.sub ?_ isStronglyPredictable_predQuadVariation
  exact isStronglyPredictable_predQuadVariation.sub isStronglyPredictable_predQuadVariation

lemma isCadlag_predQuadCovariation (ω : Ω) : IsCadlag (⟨X, Y ; P, 𝓕⟩ₘ · ω) := by
  unfold predQuadCovariation
  simp_rw [div_eq_inv_mul]
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.ofNat_apply, Pi.sub_apply]
  refine IsCadlag.const_smul ?_ _
  refine IsCadlag.sub ?_ (isCadlag_predQuadVariation ω)
  exact (isCadlag_predQuadVariation ω).sub (isCadlag_predQuadVariation ω)

lemma hasLocallyIntegrableSup_predQuadCovariation :
    HasLocallyIntegrableSup ⟨X, Y ; P, 𝓕⟩ₘ 𝓕 P := by
  sorry

end ProbabilityTheory
