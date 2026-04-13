/-
Copyright (c) 2026 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import BrownianMotion.StochasticIntegral.Cadlag
public import BrownianMotion.StochasticIntegral.SimpleProcess
public import BrownianMotion.StochasticIntegral.OptionalSampling
public import Mathlib.Probability.Notation

/-! # Cadlag modification stochastic processes -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [TopologicalSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTopology ι]
  [FirstCountableTopology ι] -- required for ∀ t : ι, (𝓝[>] t).IsCountablyGenerated
  [DenselyOrdered ι] [NoMaxOrder ι] -- required for ∀ t : ι, (𝓝[>] t).NeBot)
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

-- Is this the correct time index?
variable [Approximable 𝓕 μ]

local notation:25 V " ● " X => SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ) V X

/-- If `X` is an adapted integrable stochastic process such that the sets
`{𝔼[(𝟙_A ● X) t] | A elementary predicatable}` is bounded for any t, then it has a modification `Y`
which has left and right limits everywhere and is right continuous on a cofinite set `s : Set ι`. -/
lemma exists_modification_left_right_limit [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ t, Integrable (X t) μ)
    (hXbdd : ∀ t : ι, ∃ C, ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C) :
    ∃ Y : ι → Ω → ℝ, (∀ t, Y t =ᵐ[μ] X t) ∧
      (∀ x ω, ∃ l, Tendsto (Y · ω) (𝓝[<] x) (𝓝 l)) ∧ -- left limit
      (∀ x ω, ∃ l, Tendsto (Y · ω) (𝓝[>] x) (𝓝 l)) ∧ -- right limit
      ∃ s : Set ι, s.Countable ∧ ∀ x ∉ s, ∀ ω, ContinuousWithinAt (Y · ω) (Set.Ioi x) x := by
  sorry

/-- If `X` is an adapted integrable stochastic process which is right continuous in probability,
and is such that the set `{𝔼[(𝟙_A ● X) t] | A elementary predicatable}` is bounded for any t,
then it admits a cadlag modification. -/
lemma exists_modification_isCadlag [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ t, Integrable (X t) μ)
    (hXRC : ∀ t, TendstoInMeasure μ X (𝓝[>] t) (X t))
    (hXbdd : ∀ t : ι, ∃ C, ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C) :
    ∃ Y : ι → Ω → ℝ, (∀ t, Y t =ᵐ[μ] X t) ∧ (∀ t, Integrable (Y t) μ) ∧ ∀ ω, IsCadlag (Y · ω) := by
  classical
  obtain ⟨Y, hY, hYLL, hYRL, s, hs, hYCont⟩ := exists_modification_left_right_limit hX hXint hXbdd
  set S := ⋃ t ∈ s, {ω | ¬ ContinuousWithinAt (Y · ω) (Set.Ioi t) t} with hSdef
  have hS : ∀ᵐ ω ∂μ, ω ∉ S := by
    simp only [ae_iff, not_not, Set.setOf_mem_eq, hSdef, measure_biUnion_null_iff hs]
    refine fun t ht ↦ ae_iff.1 ?_
    choose l hl using hYRL t
    suffices l =ᵐ[μ] X t by
      have : ∀ᵐ ω ∂μ, Tendsto (fun x ↦ Y x ω) (𝓝[>] t) (𝓝 (X t ω)) := by
        filter_upwards [this] with ω hω using by simp [← hω, hl _]
      filter_upwards [this, hY t] with ω hω₁ hω₂ using by rwa [ContinuousWithinAt, hω₂]
    obtain ⟨_, hseq⟩ := exists_seq_tendsto (𝓝[>] t)
    exact tendstoInMeasure_ae_unique ((tendstoInMeasure_of_tendsto_ae
      (fun _ ↦ (hXint _).1.congr (hY _).symm)
      (ae_of_all _ <| fun ω ↦ (hl ω).comp hseq)).congr (fun _ ↦ hY _) (by rfl))
      ((hXRC t).comp hseq)
  set Z := fun t ω ↦ if ω ∈ S then 0 else Y t ω
  have hZ : ∀ t, Z t =ᵐ[μ] X t :=
    fun t ↦ EventuallyEq.trans
      (by filter_upwards [hS] with ω hω using by simp [Z, if_neg hω]) (hY t)
  refine ⟨Z, hZ, fun t ↦ (hXint t).congr <| (hZ _).symm,
    fun ω ↦ ⟨?_, fun x ↦ by_cases (p := ω ∈ S)
      (fun hω ↦ ⟨0, by simp [Z, if_pos hω, tendsto_const_nhds]⟩)
      (fun hω ↦ by simp [Z, if_neg hω, hYLL x ω])⟩⟩
  by_cases hω : ω ∈ S
  · simpa [Z, if_pos hω] using Function.isRightContinuous_const _
  · simp_rw [Z, if_neg hω]
    intro t
    simp only [hSdef, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, not_exists,
      not_and, not_not] at hω
    exact by_cases (p := t ∈ s) (fun ht ↦ hω _ ht) <| fun ht ↦ hYCont t ht ω

end ProbabilityTheory
