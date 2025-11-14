/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import BrownianMotion.StochasticIntegral.UniformIntegrable

/-! # Discrete approximation of a stopping time

-/

open Filter TopologicalSpace Function
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} [TopologicalSpace ι] [TopologicalSpace E]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → ℝ} {τ : Ω → WithTop ι} {i : ι}

-- Find better name, `RightContinuous` already exists for filtrations
/-- A stochastic process is right continuous if each of its realizations is right continuous. -/
abbrev _root_.Function.rightContinuous [PartialOrder ι] (X : ι → Ω → E) :=
  ∀ ω a, ContinuousWithinAt (X · ω) (Set.Ioi a) a

variable [LinearOrder ι] [OrderTopology ι] {𝓕 : Filtration ι mΩ}

/-- Given a random time `τ`, a discrete approximation sequence `τn` of `τ` is a sequence of
stopping times with countable range that converges to `τ` from above almost surely. -/
structure DiscreteApproxSequence (𝓕 : Filtration ι mΩ) (τ : Ω → WithTop ι)
    (μ : Measure Ω := by volume_tac) where
  /-- The sequence of stopping times approximating `τ`. -/
  seq : ℕ → Ω → WithTop ι
  /-- Each `τn` is a stopping time. -/
  isStoppingTime : ∀ n, IsStoppingTime 𝓕 (seq n)
  /-- Each `τn` has countable range. -/
  countable : ∀ n, (Set.range (seq n)).Countable
  /-- The sequence is antitone. -/
  antitone : Antitone seq
  /-- Each `τn` is greater than or equal to `τ`. -/
  le : ∀ n, τ ≤ seq n
  /-- The sequence converges to `τ` almost surely. -/
  tendsto : ∀ᵐ ω ∂μ, Tendsto (seq · ω) atTop (𝓝 (τ ω))

instance : FunLike (DiscreteApproxSequence 𝓕 τ μ) ℕ (Ω → WithTop ι) where
  coe s := s.seq
  coe_injective' s t h := by
    cases s; cases t; congr

lemma tendsto_stoppedValue_discreteApproxSequence [Nonempty ι]
    (τn : DiscreteApproxSequence 𝓕 τ μ) (hX : rightContinuous X) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ stoppedValue X (τn.seq n) ω) atTop (𝓝 (stoppedValue X τ ω)) := by
  sorry

/-- For `τ` a time bounded by `i` and `τn` a discrete approximation sequence of `τ`,
`discreteApproxSequence_of` is the discrete approximation sequence of `τ` defined by `τn ∧ i`. -/
def discreteApproxSequence_of {i : ι}
    (𝓕 : Filtration ι mΩ) (hτ : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) :
    DiscreteApproxSequence 𝓕 τ μ where
  seq := fun m ↦ min (τn m) (Function.const _ i)
  isStoppingTime := fun m ↦ (τn.isStoppingTime m).min (isStoppingTime_const _ _)
  countable := fun m ↦ by
    have : Set.range ((τn m) ⊓ (Function.const _ i))
      ⊆ Set.range (τn m) ∪ {(i : WithTop ι)} := fun _ ↦ by simp; grind
    · refine Set.Countable.mono (this) ?_
      rw [Set.union_singleton, Set.countable_insert]
      exact τn.countable m
  antitone := τn.antitone.inf antitone_const
  le := fun m ↦ le_inf (τn.le m) <| fun ω ↦ hτ ω
  tendsto := by
    filter_upwards [τn.tendsto] with ω hω
    convert hω.min (tendsto_const_nhds (x := (i : WithTop ι)))
    exact (min_eq_left (hτ ω)).symm

lemma discreteApproxSequence_of_le {i : ι}
    (hτ : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) (m : ℕ) (ω : Ω) :
    discreteApproxSequence_of 𝓕 hτ τn m ω ≤ i :=
  min_le_right _ _

variable [Nonempty ι] [OrderBot ι] [FirstCountableTopology ι] [IsFiniteMeasure μ]

lemma uniformIntegrable_stoppedValue_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) :
    UniformIntegrable (fun m ↦ stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m)) 1 μ := by
  refine h.uniformIntegrable_stoppedValue_of_countable_range _
    (discreteApproxSequence_of 𝓕 hτ_le τn).isStoppingTime
    (discreteApproxSequence_of_le hτ_le τn) (discreteApproxSequence_of 𝓕 hτ_le τn).countable

lemma integrable_stoppedValue_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) (m : ℕ) :
    Integrable (stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m)) μ :=
  ((uniformIntegrable_stoppedValue_discreteApproxSequence h hτ_le τn).memLp m).integrable
    le_rfl

lemma aestronglyMeasurable_stoppedValue_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : rightContinuous X)
    (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) :
    AEStronglyMeasurable (stoppedValue X τ) μ :=
  aestronglyMeasurable_of_tendsto_ae _
    (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1)
    (tendsto_stoppedValue_discreteApproxSequence (discreteApproxSequence_of 𝓕 hτ_le τn) hRC)

theorem stoppedValue_ae_eq_condExp_discreteApproxSequence_of
    (h : Martingale X 𝓕 μ) (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) (m : ℕ) :
    stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m)
    =ᵐ[μ] μ[X i|((discreteApproxSequence_of 𝓕 hτ_le τn).isStoppingTime m).measurableSpace] :=
  h.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      (DiscreteApproxSequence.isStoppingTime _ m)
      (fun ω ↦ discreteApproxSequence_of_le hτ_le τn m ω) (DiscreteApproxSequence.countable _ m)

lemma tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : rightContinuous X)
    (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) :
    Tendsto (fun i ↦
      eLpNorm (stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn i) - stoppedValue X τ) 1 μ)
      atTop (𝓝 0) :=
  tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1)
    ((uniformIntegrable_stoppedValue_discreteApproxSequence h hτ_le
    τn).memLp_of_tendstoInMeasure 1 (tendstoInMeasure_of_tendsto_ae
      (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1) <|
      tendsto_stoppedValue_discreteApproxSequence _ hRC))
    (uniformIntegrable_stoppedValue_discreteApproxSequence h hτ_le τn).2.1
    (tendstoInMeasure_of_tendsto_ae
      (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1) <|
      tendsto_stoppedValue_discreteApproxSequence _ hRC)

end MeasureTheory
