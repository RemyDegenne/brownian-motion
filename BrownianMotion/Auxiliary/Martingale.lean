/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Thomas Zhu
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

variable {ι Ω E : Type*} [LinearOrder ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [SigmaFinite P] {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

lemma Martingale.submartingale_convex_comp (hX : Martingale X 𝓕 P) {φ : E → ℝ}
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : Continuous φ)
    (hφ_int : ∀ t, Integrable (fun ω ↦ φ (X t ω)) P) :
    Submartingale (fun t ω ↦ φ (X t ω)) 𝓕 P := by
  refine ⟨fun i ↦ hφ_cont.comp_stronglyMeasurable (hX.adapted i), fun i j hij ↦ ?_, hφ_int⟩
  calc
    _ =ᵐ[P] fun ω ↦ φ (P[X j | 𝓕 i] ω) := hX.condExp_ae_eq hij |>.fun_comp φ |>.symm
    _ ≤ᵐ[P] P[fun ω ↦ φ (X j ω) | 𝓕 i] :=
      conditional_jensen (𝓕.le i) hφ_cvx hφ_cont.lowerSemicontinuous (hX.integrable j) (hφ_int j)

lemma Martingale.submartingale_norm (hX : Martingale X 𝓕 P) :
    Submartingale (fun t ω ↦ ‖X t ω‖) 𝓕 P :=
  hX.submartingale_convex_comp convexOn_univ_norm continuous_norm fun i ↦ (hX.integrable i).norm

lemma Submartingale.monotone_convex_comp [Preorder E] (hX : Submartingale X 𝓕 P) {φ : E → ℝ}
    (hφ_mono : Monotone φ) (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : Continuous φ)
    (hφ_int : ∀ t, Integrable (fun ω ↦ φ (X t ω)) P) :
    Submartingale (fun t ω ↦ φ (X t ω)) 𝓕 P := by
  refine ⟨fun i ↦ hφ_cont.comp_stronglyMeasurable (hX.adapted i), fun i j hij ↦ ?_, hφ_int⟩
  calc
    _ ≤ᵐ[P] fun ω ↦ φ (P[X j | 𝓕 i] ω) := (hX.ae_le_condExp hij).mono fun ω hω ↦ hφ_mono hω
    _ ≤ᵐ[P] P[fun ω ↦ φ (X j ω) | 𝓕 i] :=
      conditional_jensen (𝓕.le i) hφ_cvx hφ_cont.lowerSemicontinuous (hX.integrable j) (hφ_int j)

end MeasureTheory
