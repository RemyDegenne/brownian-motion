/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Jensen
import Mathlib.Probability.Martingale.Basic

/-! # Properties of martingales and submartingales
-/

namespace MeasureTheory

section

variable {ι Ω E : Type*} [Preorder ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

lemma Martingale.congr (hX : Martingale X 𝓕 P) (hY : Adapted 𝓕 Y) (h_eq : ∀ t, X t =ᵐ[P] Y t) :
    Martingale Y 𝓕 P := by
  refine ⟨hY, fun i j hij ↦ ?_⟩
  calc
    P[Y j | 𝓕 i] =ᵐ[P] P[X j | 𝓕 i] := (condExp_congr_ae (h_eq j)).symm
    _ =ᵐ[P] Y i := (hX.2 i j hij).trans (h_eq i)

lemma Submartingale.congr [LE E] (hX : Submartingale X 𝓕 P) (hY : Adapted 𝓕 Y)
    (h_eq : ∀ t, X t =ᵐ[P] Y t) :
    Submartingale Y 𝓕 P := by
  refine ⟨hY, ?_, ?_⟩
  · intro i j hij
    have hcond : P[X j | 𝓕 i] =ᵐ[P] P[Y j | 𝓕 i] := condExp_congr_ae (h_eq j)
    exact (Filter.eventuallyLE_congr (h_eq i) hcond).mp (ae_le_condExp hX hij)
  · exact fun i ↦ (integrable_congr (h_eq i)).mp (hX.integrable i)

end

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

lemma Martingale.submartingale_norm (hX : Martingale X 𝓕 P) :
    Submartingale (fun t ω ↦ ‖X t ω‖) 𝓕 P := by
  sorry

end MeasureTheory
