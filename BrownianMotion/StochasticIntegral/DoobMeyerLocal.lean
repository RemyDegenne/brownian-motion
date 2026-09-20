/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.DoobMeyerUniqueness

/-! # Doob-Meyer decomposition of local submartingales

A càdlàg local submartingale `X` can be written as `X = M + A`, in which `M` is a càdlàg local
martingale and `A` is a predictable, càdlàg, monotone process with locally integrable supremum.

## Main definitions

* `ProbabilityTheory.IsLocalSubmartingale.martingalePart`: the local martingale part of the
  Doob-Meyer decomposition of a local submartingale.
* `ProbabilityTheory.IsLocalSubmartingale.predictablePart`: the predictable part of the
  Doob-Meyer decomposition of a local submartingale.

## Main statements

* `ProbabilityTheory.IsLocalSubmartingale.doob_meyer`: Doob-Meyer decomposition of a càdlàg local
  submartingale.
-/

@[expose] public section

open MeasureTheory Filter Order ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {ι Ω : Type*} [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
  [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] [PolishSpace ι] [DenselyOrdered ι]
  [NoMaxOrder ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous] [𝓕.IsComplete P]
  [Approximable 𝓕 P]

namespace ProbabilityTheory

namespace IsLocalSubmartingale

/-- **Doob–Meyer decomposition** of a càdlàg local submartingale.

The hypotheses are those of `IsLocalSubmartingale.locally_classD_real`, which imply the ones of
`ClassDL.doob_meyer`, `MeasureTheory.doob_meyer_unique` and `isStable_martingale`. -/
theorem doob_meyer (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∃ (M A : ι → Ω → ℝ), X = M + A ∧ IsLocalMartingale M 𝓕 P ∧ (∀ ω, IsCadlag (M · ω)) ∧
      IsStronglyPredictable 𝓕 A ∧ (∀ ω, IsCadlag (A · ω)) ∧ (HasLocallyIntegrableSup A 𝓕 P)
      ∧ (∀ ω, Monotone (A · ω)) ∧ A ⊥ = 0 := by
  -- a localizing sequence `τ` along which `X` is a càdlàg submartingale of class D
  have h_loc : Locally (fun Y ↦ (Submartingale Y 𝓕 P ∧ ∀ ω, IsCadlag (Y · ω)) ∧ ClassD Y 𝓕 P)
      𝓕 X P :=
    (isStable_submartingale.locally_and_iff isStable_classD).2 ⟨hX, hX.locally_classD_real⟩
  obtain ⟨τ, hτ, hτX⟩ := h_loc
  -- the Doob-Meyer decomposition `M' n + A' n` of `X` stopped at `τ n`
  have h_dm (n : ℕ) := ClassDL.doob_meyer (hτX n).2.classDL (hτX n).1.1 (hτX n).1.2
  choose M' A' hMA hM hMc hA hAc hAm hA0 using h_dm
  -- TODO: `A' (n + 1)` stopped at `τ n` is indistinguishable from `A' n` by `doob_meyer_unique`
  -- (this needs that a stopped strongly predictable process is strongly predictable). Glue the
  -- `A' n` into `A` on the almost sure event on which this holds for all `n` and `τ n` tends to
  -- `⊤`, with `A = 0` elsewhere, and take `M = X - A`.
  sorry

/-- The local martingale part of the Doob-Meyer decomposition of the local submartingale. -/
noncomputable
def martingalePart (X : ι → Ω → ℝ)
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ :=
  (hX.doob_meyer hX_cadlag).choose

/-- The predictable part of the Doob-Meyer decomposition of the local submartingale. -/
noncomputable
def predictablePart (X : ι → Ω → ℝ)
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose

lemma martingalePart_add_predictablePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    X = hX.martingalePart X hX_cadlag + hX.predictablePart X hX_cadlag :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.1

lemma isLocalMartingale_martingalePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    IsLocalMartingale (hX.martingalePart X hX_cadlag) 𝓕 P :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.1

lemma cadlag_martingalePart (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∀ ω, IsCadlag (hX.martingalePart X hX_cadlag · ω) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.1

lemma isStronglyPredictable_predictablePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    IsStronglyPredictable 𝓕 (hX.predictablePart X hX_cadlag) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.1

lemma cadlag_predictablePart (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∀ ω, IsCadlag (hX.predictablePart X hX_cadlag · ω) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.1

lemma hasLocallyIntegrableSup_predictablePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    HasLocallyIntegrableSup (hX.predictablePart X hX_cadlag) 𝓕 P :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.2.1

lemma monotone_predictablePart (hX : IsLocalSubmartingale X 𝓕 P)
    (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∀ ω, Monotone (hX.predictablePart X hX_cadlag · ω) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.2.2.1

lemma predictablePart_bot (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    hX.predictablePart X hX_cadlag ⊥ = 0 :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.2.2.2

end IsLocalSubmartingale

end ProbabilityTheory
