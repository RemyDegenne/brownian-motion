/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import BrownianMotion.StochasticIntegral.Locally
import BrownianMotion.StochasticIntegral.UniformIntegrable
import BrownianMotion.Auxiliary.Adapted
import Mathlib.Probability.Martingale.OptionalSampling

/-! # Discrete approximation of a stopping time

-- What kind of indices has `DiscreteApproxSequence`?

-/

open Filter TopologicalSpace
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} [TopologicalSpace ι] [TopologicalSpace E]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → ℝ} {τ : Ω → WithTop ι} {n : ι}

-- Find better name? `RightContinuous` already taken in the context of filtrations
def rightContinuous [PartialOrder ι] (X : ι → Ω → E) (μ : Measure Ω := by volume_tac) :=
    ∀ᵐ ω ∂μ, ∀ a, ContinuousWithinAt (X · ω) (Set.Ioi a) a

lemma rightContinuous_of_all [PartialOrder ι] {X : ι → Ω → E}
    (h : ∀ ω a, ContinuousWithinAt (X · ω) (Set.Ioi a) a) (μ : Measure Ω) :
    rightContinuous X μ :=
  ae_of_all _ h

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
    cases s; cases t; congr

lemma tendsto_stoppedValue_discreteApproxSequence [Nonempty ι]
    (τn : DiscreteApproxSequence 𝓕 μ τ) (hX : rightContinuous X μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ stoppedValue X (τn.seq n) ω) atTop (𝓝 (stoppedValue X τ ω)) := by
  filter_upwards [τn.tendsto] with ω hτ
  simp_rw [stoppedValue]
  sorry

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


-- What kind of indices has `DiscreteApproxSequence`?
-- #check exists_seq_strictAnti_tendsto

-- def DyadicApprox [LinearOrder ι] [OrderTopology ι] [DenselyOrdered ι] [NoMaxOrder ι]
--     (τ : Ω → WithTop ι) (n : ℕ) (ω : Ω) : WithTop ι :=
--   sorry

#check tendsto_Lp_finite_of_tendstoInMeasure -- Vitali
#check lintegral_liminf_le' -- Fatou
-- Actually, missing that UI + convergence in measure implies limit is integrable
#check AEStronglyMeasurable
variable [Nonempty ι] [FirstCountableTopology ι] [IsFiniteMeasure μ]

#check Martingale.uniformIntegrable_stoppedValue

lemma ae_tendsto_stoppedValue_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : rightContinuous X μ)
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) (τn : DiscreteApproxSequence 𝓕 μ τ) :
    ∀ᵐ ω ∂μ, Tendsto (fun m ↦ stoppedValue X (τn m) ω) atTop (𝓝 (stoppedValue X τ ω)) := by
  sorry

lemma uniformIntegrable_stoppedValue_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : rightContinuous X μ)
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) (τn : DiscreteApproxSequence 𝓕 μ τ) :
    UniformIntegrable (fun m ↦ stoppedValue X (τn m)) 1 μ := by
  sorry

lemma integrable_stoppedValue_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : rightContinuous X μ)
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) (τn : DiscreteApproxSequence 𝓕 μ τ) (m : ℕ) :
    Integrable (stoppedValue X (τn m)) μ :=
  ((uniformIntegrable_stoppedValue_discreteApproxSequence h hRC hτ hτ_le τn).memLp m).integrable
    le_rfl

lemma UniformIntegrable.memLp_of_tendsto_in_measure
    {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ℕ → α → β} {f : α → β} (p : ℝ≥0∞) (hUI : UniformIntegrable fn p μ)
    (htends : TendstoInMeasure μ fn atTop f) :
    MemLp f p μ := by
  sorry

lemma UniformIntegrable.integrable_of_tendsto_in_measure
    {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ℕ → α → β} {f : α → β} (hUI : UniformIntegrable fn 1 μ)
    (htends : TendstoInMeasure μ fn atTop f) :
    Integrable f μ := by
  rw [← memLp_one_iff_integrable]
  exact hUI.memLp_of_tendsto_in_measure 1 htends

lemma tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : rightContinuous X μ)
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) (τn : DiscreteApproxSequence 𝓕 μ τ) :
    Tendsto (fun i ↦ eLpNorm (stoppedValue X (τn i) - stoppedValue X τ) 1 μ) atTop (𝓝 0) := by
  sorry

end MeasureTheory
