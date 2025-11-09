/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Martingale.Basic

/-! # Properties of martingales and submartingales
-/

namespace MeasureTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

lemma Martingale.congr (hX : Martingale X 𝓕 P) (hY : Adapted 𝓕 Y) (h_eq : ∀ t, X t =ᵐ[P] Y t) :
    Martingale Y 𝓕 P := by
  sorry

lemma Submartingale.congr [LE E] (hX : Submartingale X 𝓕 P) (hY : Adapted 𝓕 Y)
    (h_eq : ∀ t, X t =ᵐ[P] Y t) :
    Submartingale Y 𝓕 P := by
  sorry

end MeasureTheory
