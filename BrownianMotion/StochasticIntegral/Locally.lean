/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.StochasticIntegral.MathlibImports

/-! # Local properties of processes

-/

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ι mΩ} {τ : ℕ → Ω → ι}

structure IsLocalizingSequence (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → ι) : Prop where
  isStoppingTime : ∀ n, IsStoppingTime 𝓕 (τ n)
  mono : ∀ᵐ ω ∂P, Monotone (τ · ω)
  tendsto_top : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop atTop

end ProbabilityTheory
