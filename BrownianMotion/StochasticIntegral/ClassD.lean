/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Martingale
import BrownianMotion.StochasticIntegral.ApproxSeq
import BrownianMotion.StochasticIntegral.Locally

/-! # Locally integrable, class D, class DL

-/

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

/-- A stochastic process has locally integrable supremum if it satisfies locally the property that
for all `t`, the random variable `ω ↦ sup_{s ≤ t} ‖X s ω‖` is integrable. -/
def HasLocallyIntegrableSup (X : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω := by volume_tac) : Prop :=
  Locally (fun Y ↦ ∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖Y s ω‖) P) 𝓕 X P

section Classes

variable {ι : Type*} [Preorder ι] [Nonempty ι]

/-- A stochastic process $(X_t)$ is of class D (or in the Doob-Meyer class) if it is adapted
and the set $\{X_\tau \mid \tau \text{ is a finite stopping time}\}$ is uniformly integrable. -/
structure ClassD (𝓕 : Filtration ι mΩ) (X : ι → Ω → E) (P : Measure Ω) :
    Prop where
  adapted : Adapted 𝓕 X
  uniformIntegrable : UniformIntegrable
    (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}) ↦ stoppedValue X τ.1) 1 P

/-- A stochastic process $(X_t)$ is of class DL if it is adapted and for all $t$, the set
$\{X_\tau \mid \tau \text{ is a stopping time with } \tau \le t\}$ is uniformly integrable. -/
structure ClassDL (𝓕 : Filtration ι mΩ) (X : ι → Ω → E) (P : Measure Ω) :
    Prop where
  adapted : Adapted 𝓕 X
  uniformIntegrable (t : ι) : UniformIntegrable
    (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ t}) ↦ stoppedValue X τ.1) 1 P

lemma ClassD.classDL {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} (hX : ClassD 𝓕 X P) :
    ClassDL 𝓕 X P := by
  sorry

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [OrderBot ι] [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι] [MetrizableSpace ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}

section Order

variable [PartialOrder E] [OrderClosedTopology E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]

lemma Submartingale.classDL (hX1 : Submartingale X 𝓕 P) (hX2 : RightContinuous X)
    (hX3 : 0 ≤ X) :
    ClassDL 𝓕 X P := sorry

lemma Submartingale.classD_iff_uniformIntegrable (hX1 : Submartingale X 𝓕 P)
    (hX2 : RightContinuous X) (hX3 : 0 ≤ X) :
    ClassD 𝓕 X P ↔ UniformIntegrable X 1 P := sorry

end Order

lemma Martingale.classDL (hX1 : Martingale X 𝓕 P) (hX2 : RightContinuous X) :
    ClassDL 𝓕 X P := sorry

lemma Martingale.classD_iff_uniformIntegrable (hX1 : Martingale X 𝓕 P) (hX2 : RightContinuous X) :
    ClassD 𝓕 X P ↔ UniformIntegrable X 1 P := sorry

lemma isStable_classD : IsStable 𝓕 (ClassD (E := E) 𝓕 · P) := by
  sorry

end Classes

end ProbabilityTheory
