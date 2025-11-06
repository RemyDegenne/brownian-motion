/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Martingale.OptionalSampling

/-!
# Uniform integrability

-/

open scoped NNReal ENNReal

namespace MeasureTheory

variable {ι Ω E : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {X : ι → Ω → ℝ}

-- todo: `X` takes values in `ℝ` because
-- `MeasureTheory.Integrable.uniformIntegrable_condExp` is written only for `ℝ`. Investigate why.
lemma UniformIntegrable.condExp (hX : UniformIntegrable X 1 μ) {𝓕 : ι → MeasurableSpace Ω}
    (h𝓕 : ∀ i, 𝓕 i ≤ mΩ) :
    UniformIntegrable (fun i ↦ μ[X i | 𝓕 i]) 1 μ := by
  sorry

variable {ι : Type*} [Nonempty ι]

theorem uniformIntegrable_subsingleton' {p : ℝ≥0∞} {f : ι → Ω → E} [NormedAddCommGroup E]
    (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (hf : ∀ i, f i =ᵐ[μ] f (Classical.arbitrary ι))
    (hfint : MemLp (f (Classical.arbitrary ι)) p μ) : UniformIntegrable f p μ := by
  refine ⟨fun i ↦ AEStronglyMeasurable.congr hfint.1 (hf i).symm, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := unifIntegrable_subsingleton hp_one hp_top
      (f := fun (i : Fin 1) ↦ f (Classical.arbitrary ι)) (fun i ↦ hfint) hε
    exact ⟨δ, hδpos, fun i s hs hμs ↦
      le_trans (le_of_eq <| eLpNorm_congr_ae (hf i).indicator) <| hδ 0 s hs hμs⟩
  · refine ⟨(eLpNorm (f (Classical.arbitrary ι)) p μ).toNNReal, fun i ↦ ?_⟩
    rw [eLpNorm_congr_ae (hf i)]
    exact le_of_eq <| (ENNReal.coe_toNNReal hfint.eLpNorm_ne_top).symm

variable [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [DiscreteTopology ι] [MeasurableSpace ι] [BorelSpace ι]
  {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕]

lemma Martingale.ae_eq_condExp_of_isStoppingTime {X : ι → Ω → ℝ}
    (hX : Martingale X 𝓕 μ) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) {n : ι}
    (hτ_le : ∀ ω, τ ω ≤ n) :
    stoppedValue X τ =ᵐ[μ] μ[X n | hτ.measurableSpace] := by
  convert stoppedValue_min_ae_eq_condExp hX (isStoppingTime_const 𝓕 n) hτ (n := n) ?_ using 2
  · ext ω
    exact (min_eq_left (hτ_le ω)).symm
  exact fun _ ↦ le_rfl

lemma Martingale.uniformIntegrable_stoppedValue {X : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ}
    [SigmaFiniteFiltration μ 𝓕]
    (hX : Martingale X 𝓕 μ) (τ : ℕ → Ω → ℕ∞) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ℕ} (hτ_le : ∀ i ω, τ i ω ≤ n) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ :=
  ((uniformIntegrable_subsingleton' (f := fun (_ : ℕ) ↦ X n) le_rfl ENNReal.one_ne_top
    (fun _ ↦ Eq.eventuallyEq rfl) <| memLp_one_iff_integrable.2 <| hX.integrable n).condExp
    (fun i ↦ (hτ i).measurableSpace_le)).ae_eq <| fun m ↦
      (hX.ae_eq_condExp_of_isStoppingTime (hτ m) (hτ_le m)).symm

end MeasureTheory
