/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.EMetricSpace.BoundedVariation

public import BrownianMotion.Auxiliary.ContinuousBilinForm
public import BrownianMotion.StochasticIntegral.DoobMeyer
public import BrownianMotion.StochasticIntegral.LocalMartingale

/-!
# Finite-Variation Processes

This file shows that a continuous local martingale of locally finite variation is almost surely
constant.
-/

@[expose] public section

open Filter MeasureTheory Finset Set
open scoped BigOperators NNReal ENNReal InnerProductSpace Topology

/-- A finite ordered partition of `[a, b]` in a ordered space. -/
structure IccPartition (ι : Type*) [Preorder ι] (a b : ι) where
  card : ℕ
  /-- The ordered partition points. -/
  point : ℕ → ι
  /-- The first partition point is the left endpoint. -/
  left_eq : point 0 = a
  /-- The last partition point is the right endpoint. -/
  right_eq : point card = b
  /-- The partition points are monotone. -/
  mono : Monotone point
  /-- All partition points lie in the interval. -/
  point_mem_Icc i : point i ∈ Set.Icc a b

section -- Existence of an IccPartition with small mesh size

def trivialIccPartition {ι} [Preorder ι] {a : ι} : IccPartition ι a a where
  card := 1
  point _ := a
  left_eq := rfl
  right_eq := rfl
  mono _ _ _ := refl _
  point_mem_Icc _ := ⟨refl _, refl _⟩

theorem exists_IccPartition {ι E} [TopologicalSpace ι] [ConditionallyCompleteLinearOrder ι]
    [OrderTopology ι] {a b : ι} [PseudoEMetricSpace E] (hab : a ≤ b) {f : ι → E} (hc : Continuous f)
    (ε : ℝ≥0∞) :
    ∃ π : IccPartition ι a b, ∀ n, edist (f (π.point (n + 1))) (f (π.point n)) ≤ ε := by
  -- Define the reacheable set and then use continuous induction.
  let S := {x | x ∈ Icc a b ∧ ∃ π : IccPartition ι a x, ∀ n,
    ∀ᵉ (y ∈ Icc (π.point n) (π.point (n + 1))) (z ∈ Icc (π.point n) (π.point (n + 1))),
      edist (f y) (f z) ≤ ε}
  suffices hb : b ∈ S from by
    obtain ⟨π, hπ⟩ := hb.2
    exact ⟨π, fun n => hπ n (π.point (n + 1)) ⟨π.mono (Nat.le_succ n), refl _⟩
      (π.point n) ⟨refl _, π.mono (Nat.le_succ n)⟩⟩
  refine IsClosed.mem_of_ge_of_forall_exists_gt ?_ ?_ hab (fun x hx => ?_)
  · sorry
  · refine ⟨⟨refl _, hab⟩, ⟨trivialIccPartition, fun n => ?_⟩⟩
    simp [trivialIccPartition]
  · sorry

end

variable {ι Ω E : Type*}

/-- The quadratic sum along a finite ordered partition. -/
noncomputable def partitionQuadraticVariation [LinearOrder ι]
    [PseudoEMetricSpace E] (X : ι → Ω → E) {a b : ι} (π : IccPartition ι a b) : Ω → ℝ≥0∞ :=
  fun ω ↦ ∑ i ∈ Finset.range π.card, (edist (X (π.point (i + 1)) ω) (X (π.point i) ω)) ^ 2

/-- The largest size of a process increment along a finite ordered partition. -/
noncomputable def partitionOscillation [LinearOrder ι]
    [PseudoEMetricSpace E] (X : ι → Ω → E) {a b : ι} (π : IccPartition ι a b) : Ω → ℝ≥0∞ :=
  fun ω ↦ ⨆ i, edist (X (π.point (i + 1)) ω) (X (π.point i) ω)

theorem edist_le_variation [LinearOrder ι] [PseudoEMetricSpace E]
    (X : ι → Ω → E) {a b : ι} (ω : Ω) :
    edist (X a ω) (X b ω) ≤ eVariationOn (X · ω) Set.univ := by
  sorry

def increment [LinearOrder ι] [AddCommGroup E] (X : ι → Ω → E) {a b : ι}
    (π : IccPartition ι a b) (i : ℕ) : Ω → E :=
  X (π.point (i + 1)) - X (π.point i)

theorem increment_le_variation [LinearOrder ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : ι → Ω → E) {a b : ι} (π : IccPartition ι a b) (i j : ℕ) (ω : Ω) :
    ENNReal.ofReal |⟪increment X π i ω, increment X π j ω⟫_ℝ| ≤
      (eVariationOn (X · ω) Set.univ) ^ 2 := by
  sorry

theorem process_eq_sum_of_increments [LinearOrder ι] [OrderBot ι]
    [AddCommGroup E] (X : ι → Ω → E) {t : ι} (π : IccPartition ι ⊥ t) :
    X t = ∑ i ∈ range π.card, increment X π i := by
  sorry

theorem process_inner_equality [LinearOrder ι] [OrderBot ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (X : ι → Ω → E) {t : ι}
    (π : IccPartition ι ⊥ t) (ω : Ω) :
    ⟪X t ω, X t ω⟫_ℝ = ∑ i ∈ range π.card, ⟪increment X π i ω, increment X π i ω⟫_ℝ +
      ∑ i ∈ range π.card, ∑ j ∈ (range π.card).filter (i < ·),
        ⟪increment X π i ω, increment X π j ω⟫_ℝ := by
  sorry

variable {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Pull-out property for conditional expectation with a Hilbert-space inner product. -/
theorem condExp_inner_of_stronglyMeasurable_left [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f g : Ω → E} (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (fun ω ↦ ⟪f ω, g ω⟫_ℝ) μ) (hg : Integrable g μ) :
    μ[fun ω ↦ ⟪f ω, g ω⟫_ℝ | m] =ᵐ[μ] fun ω ↦ ⟪f ω, μ[g | m] ω⟫_ℝ :=
  condExp_bilin_of_aestronglyMeasurable_left (ContinuousBilinForm.inner E)
    hf.aestronglyMeasurable hfg hg

/-- Proof outline: This theorem is trivial if `fun ω ↦ ⟪increment X π i ω, increment X π j ω⟫_ℝ` is
not integrable. If it is indeed integrable, then use the martingale property together with
`condExp_inner_of_stronglyMeasurable_left` to finish the proof. -/
theorem increment_orthogonal [LinearOrder ι] [OrderBot ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
    (hX : Martingale X 𝓕 μ) {t : ι} (π : IccPartition ι ⊥ t) (i j : ℕ) (hij : i < j) :
    ∫ ω, ⟪increment X π i ω, increment X π j ω⟫_ℝ ∂μ = 0 := by
  sorry

/-- I believe we need the evariation to be uniformly bounded and `IsProbabilityMeasure μ` to obtain
integrability of these processes. -/
theorem integral_process_inner_equality [LinearOrder ι] [OrderBot ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [IsProbabilityMeasure μ] {X : ι → Ω → E}
    {𝓕 : Filtration ι mΩ} (hX : Martingale X 𝓕 μ) {C : ℝ≥0}
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) Set.univ ≤ C) {t : ι} (π : IccPartition ι ⊥ t) :
    ∫ ω, ⟪X t ω, X t ω⟫_ℝ ∂μ =
      ∑ i ∈ range π.card, ∫ ω, ⟪increment X π i ω, increment X π i ω⟫_ℝ ∂μ := by
  sorry
