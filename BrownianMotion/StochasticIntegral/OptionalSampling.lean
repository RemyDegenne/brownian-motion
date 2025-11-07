/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import BrownianMotion.StochasticIntegral.Locally
import BrownianMotion.StochasticIntegral.UniformIntegrable
import Mathlib.Probability.Martingale.OptionalSampling

open Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} [TopologicalSpace ι] [TopologicalSpace E]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → ℝ} {τ : Ω → WithTop ι} {n : ι}

-- Find better name? `RightContinuous` already taken in the context of filtrations
def rightContinuous [PartialOrder ι] (X : ι → Ω → E) (μ : Measure Ω := by volume_tac) :=
    ∀ᵐ ω ∂μ, ∀ a, ContinuousWithinAt (X · ω) (Set.Ioi a) a

variable [LinearOrder ι] [OrderTopology ι] {𝓕 : Filtration ι mΩ}

structure DiscreteApproxSequence (𝓕 : Filtration ι mΩ) (μ : Measure Ω := by volume_tac)
    (τ : Ω → WithTop ι) where
  seq : ℕ → Ω → WithTop ι
  isStoppingTime : ∀ n, IsStoppingTime 𝓕 (seq n)
  discrete : ∀ n, (Set.range (seq n)).Countable
  antitone : Antitone seq
  le : ∀ n, τ ≤ seq n
  tendsto : ∀ᵐ ω ∂μ, Tendsto (seq · ω) atTop (𝓝 (τ ω))

instance : FunLike (DiscreteApproxSequence 𝓕 μ τ) ℕ (Ω → WithTop ι) where
  coe s := s.seq
  coe_injective' s t h := by
    cases s; cases t; congr;

def discreteApproxSequence_of (𝓕 : Filtration ι mΩ) (μ : Measure Ω := by volume_tac)
    {n : ι} (hτ : ∀ ω, τ ω ≤ n) (τn : DiscreteApproxSequence 𝓕 μ τ) :
    DiscreteApproxSequence 𝓕 μ τ where
  seq := fun m ↦ min (τn m) (Function.const _ n)
  isStoppingTime := fun m ↦ (τn.isStoppingTime m).min (isStoppingTime_const _ _)
  discrete := fun m ↦ by
    have : Set.range ((τn m) ⊓ (Function.const _ n))
      ⊆ Set.range (τn m) ∪ {(n : WithTop ι)} := fun _ ↦ by simp; grind
    · refine Set.Countable.mono (this) ?_
      rw [Set.union_singleton, Set.countable_insert]
      exact τn.discrete m
  antitone := τn.antitone.inf antitone_const
  le := fun m ↦ le_inf (τn.le m) <| fun ω ↦ hτ ω
  tendsto := by
    filter_upwards [τn.tendsto] with ω hω
    convert hω.min (tendsto_const_nhds (x := (n : WithTop ι)))
    exact (min_eq_left (hτ ω)).symm

lemma discreteApproxSequence_of_le {n : ι}
    (hτ : ∀ ω, τ ω ≤ n) (τn : DiscreteApproxSequence 𝓕 μ τ) (m : ℕ) (ω : Ω) :
    discreteApproxSequence_of 𝓕 μ hτ τn m ω ≤ n :=
  min_le_right _ _


-- See what kind of indices has `DiscreteApproxSequence`
-- #check exists_seq_strictAnti_tendsto
-- def DyadicApprox [LinearOrder ι] [OrderTopology ι] [DenselyOrdered ι] [NoMaxOrder ι]
--     (τ : Ω → WithTop ι) (n : ℕ) (ω : Ω) : WithTop ι :=
--   sorry

#check Martingale.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range

variable [Nonempty ι] [FirstCountableTopology ι] [IsFiniteMeasure μ]

theorem stoppedValue_ae_eq_condExp_of_le_const_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : rightContinuous X μ)
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) (τn : DiscreteApproxSequence 𝓕 μ τ) :
    stoppedValue X τ =ᵐ[μ] μ[X n|hτ.measurableSpace] := by
  set τn' := discreteApproxSequence_of 𝓕 μ hτ_le τn
  have : ∀ᵐ ω ∂μ, ∀ m, stoppedValue X (τn' m) ω
      = μ[X n|(τn'.isStoppingTime m).measurableSpace] ω := by
    rw [ae_all_iff]
    intro m
    exact h.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (τn'.isStoppingTime m)
      (fun ω ↦ discreteApproxSequence_of_le hτ_le τn m ω) (τn'.discrete m)
  filter_upwards [this, τn'.tendsto] with ω hstopped htendsto
  sorry

end MeasureTheory
