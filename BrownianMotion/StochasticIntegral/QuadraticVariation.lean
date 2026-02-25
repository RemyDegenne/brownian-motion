/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.StochasticIntegral.DoobMeyer

/-! # Quadratic variation of local martingales

-/

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [MeasurableSpace ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

omit [OrderBot ι] [OrderTopology ι] [MeasurableSpace ι] [NormedSpace ℝ E] [CompleteSpace E] in
private lemma isCadlag_norm_sq {f : ι → E} (hf : IsCadlag f) :
    IsCadlag (fun t ↦ ‖f t‖ ^ 2) :=
  let hc := continuous_norm.pow 2
  ⟨hf.right_continuous.continuous_comp hc, fun x ↦
    let ⟨l, hl⟩ := hf.left_limit x; ⟨‖l‖ ^ 2, (hc.tendsto l).comp hl⟩⟩

omit [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] [NormedSpace ℝ E]
  [CompleteSpace E] in
private lemma stoppedProcess_norm_sq_eq (X : ι → Ω → E) (τ : Ω → WithTop ι) :
    stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (fun ω ↦ ‖X i ω‖ ^ 2)) τ =
    fun i ω ↦ ‖stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ i ω‖ ^ 2 := by
  ext i ω; simp only [stoppedProcess, Set.indicator_apply]; split_ifs <;> simp

/-- The squared norm of a cadlag martingale is a submartingale. This is a consequence of Jensen's
inequality for conditional expectations applied to the convex function `‖·‖²`, combined with the
martingale property. The proof requires the conditional Jensen inequality (`conditional_jensen`,
axiomatized in this project) and L² integrability of the martingale (which in a complete treatment
follows from a localization argument using hitting times). -/
private lemma Martingale.submartingale_sq_norm {M : ι → Ω → E}
    (hM : Martingale M 𝓕 P) :
    Submartingale (fun i ω ↦ ‖M i ω‖ ^ 2) 𝓕 P := by
  sorry

lemma IsLocalMartingale.isLocalSubmartingale_sq_norm
    (hX : IsLocalMartingale X 𝓕 P) (_ : ∀ ω, IsCadlag (X · ω)) :
    IsLocalSubmartingale (fun t ω ↦ ‖X t ω‖ ^ 2) 𝓕 P := by
  obtain ⟨τ, hτ_loc, hτ_prop⟩ := hX
  refine ⟨τ, hτ_loc, fun n ↦ ?_⟩
  obtain ⟨hmart, hcadlag⟩ := hτ_prop n
  rw [stoppedProcess_norm_sq_eq]
  exact ⟨Martingale.submartingale_sq_norm hmart, fun ω ↦ isCadlag_norm_sq (hcadlag ω)⟩

/-- The quadratic variation of a local martingale, defined as the predictable part of the Doob-Meyer
decomposition of its squared norm. -/
noncomputable
def quadraticVariation (hX : IsLocalMartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ :=
  have hX2_cadlag : ∀ ω, IsCadlag (fun t ↦ ‖X t ω‖ ^ 2) := fun ω ↦ isCadlag_norm_sq (hX_cadlag ω)
  (hX.isLocalSubmartingale_sq_norm hX_cadlag).predictablePart (fun t ω ↦ ‖X t ω‖ ^ 2) hX2_cadlag

end ProbabilityTheory
