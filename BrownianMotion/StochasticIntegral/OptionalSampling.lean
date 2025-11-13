import BrownianMotion.StochasticIntegral.Centering
import Mathlib.Probability.Martingale.Basic

open ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {σ τ : Ω → WithTop ℕ} {X : ℕ → Ω → E} (𝓕 : Filtration ℕ mΩ)

theorem Submartingale.stoppedValue_min_ae_le_condExp [PartialOrder E] [IsOrderedModule ℝ E]
    (hX : Submartingale X 𝓕 P) {k : ℕ} (hτk : ∀ᵐ ω ∂P, τ ω ≤ k)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] := sorry
