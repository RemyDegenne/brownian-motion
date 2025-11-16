import BrownianMotion.StochasticIntegral.Centering
import Mathlib.Probability.Martingale.Basic

open ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section Nat

variable {σ τ : Ω → WithTop ℕ} {X : ℕ → Ω → E} (𝓕 : Filtration ℕ mΩ)

theorem Submartingale.stoppedValue_min_ae_le_condExp_nat [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    (hX : Submartingale X 𝓕 P) {k : ℕ} (hτk : ∀ᵐ ω ∂P, τ ω ≤ k)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] := by
  sorry

theorem Supermartingale.condExp_ae_le_stoppedValue_min_nat [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    (hX : Supermartingale X 𝓕 P) {k : ℕ} (hτk : ∀ᵐ ω ∂P, τ ω ≤ k)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    P[stoppedValue X τ|hσ.measurableSpace] ≤ᵐ[P] stoppedValue X (τ ⊓ σ) := by
  sorry

end Nat

variable {ι : Type*} [LinearOrder ι] [Nonempty ι]
  {σ τ : Ω → WithTop ι} {X : ι → Ω → E} (𝓕 : Filtration ι mΩ)

theorem Submartingale.stoppedValue_min_ae_le_condExp [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    (hX : Submartingale X 𝓕 P) {k : ι} (hτk : ∀ᵐ ω ∂P, τ ω ≤ k)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] := by
  sorry

end MeasureTheory
