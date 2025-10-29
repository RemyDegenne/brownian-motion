/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Process.Stopping

/-! # Local properties of processes

-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A localizing sequence is a sequence of stopping times that is almost surely increasing and
tends almost surely to infinity. -/
structure IsLocalizingSequence [Preorder ι] (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι)
    (P : Measure Ω := by volume_tac) :
    Prop where
  isStoppingTime : ∀ n, IsStoppingTime 𝓕 (τ n)
  mono : ∀ᵐ ω ∂P, Monotone (τ · ω)
  tendsto_top : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop atTop

lemma isLocalizingSequence_const_top [Preorder ι] (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    IsLocalizingSequence 𝓕 (fun _ _ ↦ ⊤) P where
  isStoppingTime n := by simp [IsStoppingTime]
  mono := ae_of_all _ fun _ _ _ _ ↦ by simp
  tendsto_top := by filter_upwards [] with ω using by simp [tendsto_atTop]

variable [LinearOrder ι] [OrderBot ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
  {p q : (ι → Ω → E) → Prop}

@[simp]
lemma stoppedProcess_const_top : stoppedProcess X (fun _ ↦ ⊤) = X := by
  unfold stoppedProcess
  simp

/-- A stochastic process `X` is said to satisfy a property `p` locally with respect to a
filtration `𝓕` if there exists a localizing sequence `(τ_n)` such that for all `n`, the stopped
process of `fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)` satisfies `p`. -/
def Locally [Zero E] (p : (ι → Ω → E) → Prop) (𝓕 : Filtration ι mΩ)
    (X : ι → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∃ τ : ℕ → Ω → WithTop ι, IsLocalizingSequence 𝓕 τ P ∧
    ∀ n, p (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))

/-- A localizing sequence, witness of the local property of the stochastic process. -/
noncomputable
def Locally.localSeq [Zero E] (hX : Locally p 𝓕 X P) :
    ℕ → Ω → WithTop ι :=
  hX.choose

lemma Locally.IsLocalizingSequence [Zero E] (hX : Locally p 𝓕 X P) :
    IsLocalizingSequence 𝓕 (hX.localSeq) P :=
  hX.choose_spec.1

lemma Locally.stoppedProcess [Zero E] (hX : Locally p 𝓕 X P) (n : ℕ) :
    p (stoppedProcess (fun i ↦ {ω | ⊥ < hX.localSeq n ω}.indicator (X i)) (hX.localSeq n)) :=
  hX.choose_spec.2 n

lemma locally_of_prop [Zero E] (hp : p X) : Locally p 𝓕 X P :=
  ⟨fun n _ ↦ (⊤ : WithTop ι), isLocalizingSequence_const_top _ _, by simpa⟩

lemma Locally.mono [Zero E] (hpq : ∀ X, p X → q X) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  ⟨hpX.localSeq, hpX.IsLocalizingSequence, fun n ↦ hpq _ <| hpX.stoppedProcess n⟩

/-- A property of stochastic processes is said to be stable if it is preserved under taking
the stopped process by a stopping time. -/
def IsStable [Zero E] (p : (ι → Ω → E) → Prop) (𝓕 : Filtration ι mΩ) : Prop :=
  ∀ X : ι → Ω → E, p X → ∀ τ : Ω → WithTop ι, IsStoppingTime 𝓕 τ →
    p (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i))

lemma locally_and [Zero E] (hp : IsStable p 𝓕) (hq : IsStable q 𝓕) :
    Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P ↔ Locally p 𝓕 X P ∧ Locally q 𝓕 X P := by
  sorry

lemma locally_locally [Zero E] (hp : IsStable p 𝓕) :
    Locally (fun Y ↦ Locally p 𝓕 Y P) 𝓕 X P ↔ Locally p 𝓕 X P := by
  sorry

/-- If `p` implies `q` locally, then `p` locally implies `q` locally. -/
lemma locally_induction [Zero E] (hpq : ∀ Y, p Y → Locally q 𝓕 Y P) (hq : IsStable q 𝓕)
    (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P := by
  sorry

end ProbabilityTheory
