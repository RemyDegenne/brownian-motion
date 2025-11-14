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

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

lemma Martingale.congr (hX : Martingale X 𝓕 P) (hY : Adapted 𝓕 Y) (h_eq : ∀ t, X t =ᵐ[P] Y t) :
    Martingale Y 𝓕 P :=
  ⟨by aesop,
    fun i j a ↦ (condExp_congr_ae (h_eq j)).symm.trans (((hX.2 i j a).symm).symm.trans (h_eq i))⟩

lemma Submartingale.congr [LE E] (hX : Submartingale X 𝓕 P) (hY : Adapted 𝓕 Y)
    (h_eq : ∀ t, X t =ᵐ[P] Y t) :
    Submartingale Y 𝓕 P := by
  have h_cond_exp : ∀ t s, t ≤ s → (condExp (𝓕 t) P (X s)) =ᵐ[P] (condExp (𝓕 t) P (Y s)) :=
    fun t s a ↦ condExp_congr_ae (h_eq s)
  refine ⟨hY, fun i j a ↦ ?_, fun i ↦ ?_⟩
  · filter_upwards [hX.2.1 i j a, h_eq i, h_eq j, h_cond_exp i j a]
      with ω hω₁ hω₂ hω₃ hω₄ using by simp_all
  · apply MeasureTheory.Integrable.congr _ _
    exacts [X i, hX.integrable _, h_eq i]

lemma Martingale.submartingale_norm (hX : Martingale X 𝓕 P) :
    Submartingale (fun t ω ↦ ‖X t ω‖) 𝓕 P := by
  sorry

end MeasureTheory
