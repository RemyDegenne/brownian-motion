/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Thomas Zhu
-/
module

public import BrownianMotion.Auxiliary.Filtration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.Probability.Martingale.Basic

/-! # Properties of martingales and submartingales
-/

@[expose] public section

namespace MeasureTheory

section

variable {ι Ω E : Type*} [Preorder ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

lemma Martingale.indicator [OrderBot ι] {s : Set Ω}
    (hX : Martingale X 𝓕 P) (hs : MeasurableSet[𝓕 ⊥] s) :
    Martingale (fun t ↦ s.indicator (X t)) 𝓕 P :=
  ⟨fun i ↦ (hX.stronglyAdapted i).indicator (𝓕.mono bot_le _ hs), fun i j hij ↦
    (condExp_indicator (hX.integrable _) (𝓕.mono bot_le _ hs)).trans (hX.2 i j hij).indicator⟩

lemma Martingale.indexComap {ι' : Type*} [Preorder ι'] (hX : Martingale X 𝓕 P) {f : ι' → ι}
    (hf : Monotone f) : Martingale (X ∘ f) (𝓕.indexComap hf) P :=
  ⟨hX.stronglyAdapted.indexComap hf, fun _ _ hij ↦ hX.condExp_ae_eq (hf hij)⟩

lemma Submartingale.indexComap {ι' : Type*} [Preorder ι'] [LE E] (hX : Submartingale X 𝓕 P)
    {f : ι' → ι} (hf : Monotone f) : Submartingale (X ∘ f) (𝓕.indexComap hf) P :=
  ⟨hX.stronglyAdapted.indexComap hf, fun _ _ hij ↦ hX.ae_le_condExp (hf hij),
    fun _ ↦ hX.integrable _⟩

end

variable {ι Ω E : Type*} [PartialOrder ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E}
  {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration P 𝓕]

lemma Martingale.submartingale_convex_comp (hX : Martingale X 𝓕 P) {φ : E → ℝ}
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : Continuous φ)
    (hφ_int : ∀ t, Integrable (fun ω ↦ φ (X t ω)) P) :
    Submartingale (fun t ω ↦ φ (X t ω)) 𝓕 P := by
  refine ⟨fun i ↦ hφ_cont.comp_stronglyMeasurable (hX.stronglyAdapted i), fun i j hij ↦ ?_, hφ_int⟩
  calc
    _ =ᵐ[P] fun ω ↦ φ (P[X j | 𝓕 i] ω) := hX.condExp_ae_eq hij |>.fun_comp φ |>.symm
    _ ≤ᵐ[P] P[fun ω ↦ φ (X j ω) | 𝓕 i] :=
      hφ_cvx.map_condExp_le_univ (𝓕.le i) hφ_cont.lowerSemicontinuous (hX.integrable j) (hφ_int j)

lemma Martingale.submartingale_norm (hX : Martingale X 𝓕 P) :
    Submartingale (fun t ω ↦ ‖X t ω‖) 𝓕 P :=
  hX.submartingale_convex_comp convexOn_univ_norm continuous_norm fun i ↦ (hX.integrable i).norm

lemma Submartingale.monotone_convex_comp [Preorder E] (hX : Submartingale X 𝓕 P) {φ : E → ℝ}
    (hφ_mono : Monotone φ) (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : Continuous φ)
    (hφ_int : ∀ t, Integrable (fun ω ↦ φ (X t ω)) P) :
    Submartingale (fun t ω ↦ φ (X t ω)) 𝓕 P := by
  refine ⟨fun i ↦ hφ_cont.comp_stronglyMeasurable (hX.stronglyAdapted i), fun i j hij ↦ ?_, hφ_int⟩
  calc
    _ ≤ᵐ[P] fun ω ↦ φ (P[X j | 𝓕 i] ω) := (hX.ae_le_condExp hij).mono fun ω hω ↦ hφ_mono hω
    _ ≤ᵐ[P] P[fun ω ↦ φ (X j ω) | 𝓕 i] :=
      hφ_cvx.map_condExp_le_univ (𝓕.le i) hφ_cont.lowerSemicontinuous (hX.integrable j) (hφ_int j)

end MeasureTheory
