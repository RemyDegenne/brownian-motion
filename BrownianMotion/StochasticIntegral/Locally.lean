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

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

structure IsLocalizingSequence [Preorder ι] (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → ι)
    (P : Measure Ω := by volume_tac) :
    Prop where
  isStoppingTime : ∀ n, IsStoppingTime 𝓕 (τ n)
  mono : ∀ᵐ ω ∂P, Monotone (τ · ω)
  tendsto_top : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop atTop

variable [LinearOrder ι] [OrderBot ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
  {p : (ι → Ω → E) → Prop}

/-- A stochastic process `X` is said to satisfy a property `p` locally with respect to a
filtration `𝓕` if there exists a localizing sequence `(τ_n)` such that for all `n`, the stopped
process of `fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)` satisfies `p`. -/
def Locally [Zero E] (p : (ι → Ω → E) → Prop) (𝓕 : Filtration ι mΩ)
    (X : ι → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∃ τ : ℕ → Ω → ι, IsLocalizingSequence 𝓕 τ P ∧
    ∀ n, p (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))

/-- A localizing sequence, witness of the local property of the stochastic process. -/
noncomputable
def Locally.localizingSequence [Zero E] (hX : Locally p 𝓕 X P) :
    ℕ → Ω → ι :=
  hX.choose

lemma Locally.IsLocalizingSequence [Zero E] (hX : Locally p 𝓕 X P) :
    IsLocalizingSequence 𝓕 (hX.localizingSequence) P :=
  hX.choose_spec.1

lemma Locally.stoppedProcess [Zero E] (hX : Locally p 𝓕 X P) (n : ℕ) :
    p (stoppedProcess (fun i ↦ {ω | ⊥ < hX.localizingSequence n ω}.indicator (X i))
      (hX.localizingSequence n)) :=
  hX.choose_spec.2 n

-- needs the stopping time refactor
lemma locally_of_prop [Zero E] (hp : p X) : Locally p 𝓕 X P := by
  sorry

/-- A property of stochastic processes is said to be stable if it is preserved under taking
the stopped process by a stopping time. -/
def IsStable [Zero E] (p : (ι → Ω → E) → Prop) (𝓕 : Filtration ι mΩ) : Prop :=
  ∀ X : ι → Ω → E, p X → ∀ τ : Ω → ι, IsStoppingTime 𝓕 τ → p (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i))

end ProbabilityTheory
