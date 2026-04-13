/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import BrownianMotion.StochasticIntegral.Cadlag
public import BrownianMotion.StochasticIntegral.UniformIntegrable

/-! # Discrete approximation of a stopping time

-/

@[expose] public section

open Filter TopologicalSpace Function Bornology
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} [TopologicalSpace ι] [LinearOrder ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → E} {τ σ : Ω → WithTop ι} {i : ι}

/-- Given a random time `τ`, a discrete approximation sequence `τn` of `τ` is a sequence of
stopping times with countable range that converges to `τ` from above almost surely. -/
@[ext]
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

-- Should replace `isStoppingTime_const`
theorem isStoppingTime_const' {ι : Type*} [Preorder ι] (f : Filtration ι mΩ) (i : WithTop ι) :
    IsStoppingTime f fun _ => i := fun j => by simp only [MeasurableSet.const]

/-- A time index `ι` is said to be approximable if for any stopping time `τ` on `ι`, there exists
a discrete approximation sequence of `τ`. -/
class Approximable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace ι] [LinearOrder ι]
    [OrderTopology ι] (𝓕 : Filtration ι mΩ) (μ : Measure Ω := by volume_tac) where
  /-- For any stopping time `τ`, there exists a discrete approximation sequence of `τ`. -/
  approxSeq : ∀ τ : Ω → WithTop ι, IsStoppingTime 𝓕 τ → DiscreteApproxSequence 𝓕 τ μ

/-- Given a stopping time `τ` on an approximable time index, we obtain an associated discrete
approximation sequence. -/
def IsStoppingTime.discreteApproxSequence
    (h : IsStoppingTime 𝓕 τ) (μ : Measure Ω) [Approximable 𝓕 μ] :
    DiscreteApproxSequence 𝓕 τ μ := Approximable.approxSeq τ h

instance _root_.Nat.approximable {𝓕 : Filtration ℕ mΩ} : Approximable 𝓕 μ := by
  refine ⟨fun τ hτ ↦ ?_⟩
  refine ⟨fun _ ↦ τ, fun _ ↦ hτ, ?_, antitone_const, fun _ ↦ le_rfl, ae_of_all _ fun _ ↦ by simp⟩
  simp only [forall_const]
  exact (Set.range τ).to_countable

section NNRealApprox

/-- The approximation sequence for a stopping time `τ` taking values in `ℝ≥0` defined by
`nnrealApproxSeq τ n ω = ⌈(τ ω) * 2^n⌉ / 2^n`. -/
noncomputable def nnrealApproxSeq (τ : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) :
    WithTop ℝ≥0 :=
  WithTop.map (fun x : ℝ≥0 ↦ ⌈x * (2 : ℝ≥0) ^ n⌉₊ / (2 : ℝ≥0) ^ n) (τ ω)

lemma nnrealApproxSeq_le_iff (τ : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) (t : ℝ≥0) :
    nnrealApproxSeq τ n ω ≤ t ↔ τ ω ≤ (⌊t * (2 : ℝ≥0) ^ n⌋₊ / (2 : ℝ≥0) ^ n : ℝ≥0) := by
  unfold nnrealApproxSeq
  cases hτ : τ ω with
  | top => simp only [WithTop.map_top, top_le_iff, WithTop.coe_ne_top]
  | coe x =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    rw [div_le_iff₀ (by positivity), le_div_iff₀ (by positivity)]
    exact ⟨fun h ↦ le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (Nat.le_floor h)),
           fun h ↦ le_trans (Nat.cast_le.mpr (Nat.ceil_le.mpr h)) (Nat.floor_le (by positivity))⟩

lemma nnrealApproxSeq_isStoppingTime (𝓕 : Filtration ℝ≥0 mΩ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) (n : ℕ) :
    IsStoppingTime 𝓕 (nnrealApproxSeq τ n) := by
  intro t
  have h2 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ n := pow_pos (by norm_num) n
  set s := ((⌊t * (2 : ℝ≥0) ^ n⌋₊ : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n
  suffices MeasurableSet[𝓕 t] {ω | τ ω ≤ s} by
    convert this using 1
    ext ω
    simp only [Set.mem_setOf_eq]
    exact nnrealApproxSeq_le_iff τ n ω t
  exact 𝓕.mono' (div_le_of_le_mul₀ h2.le (by positivity) (Nat.floor_le (by positivity))) _ (hτ s)

lemma nnrealApproxSeq_countable (τ : Ω → WithTop ℝ≥0) (n : ℕ) :
    (Set.range (nnrealApproxSeq τ n)).Countable := by
  apply (Set.countable_range
    (fun k : ℕ ↦ ((k : ℝ≥0) / (2 : ℝ≥0) ^ n : WithTop ℝ≥0)) |>.insert ⊤).mono
  rintro _ ⟨ω, rfl⟩
  simp only [nnrealApproxSeq]
  cases hτ : τ ω with
  | top => simp [Set.mem_insert_iff]
  | coe x =>
    simp only [WithTop.map_coe, Set.mem_insert_iff, WithTop.coe_ne_top, false_or]
    exact ⟨⌈x * 2 ^ n⌉₊, rfl⟩

lemma nnrealApproxSeq_antitone (τ : Ω → WithTop ℝ≥0) :
    Antitone (nnrealApproxSeq τ) := by
  intro m n hmn ω
  simp only [nnrealApproxSeq]
  cases hτ : τ ω with
  | top => simp
  | coe x =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    erw [div_le_div_iff₀ (by positivity) (by positivity)]
    have key : (⌈x * 2 ^ n⌉₊ : ℕ) ≤ ⌈x * 2 ^ m⌉₊ * 2 ^ (n - m) := by
      rw [Nat.ceil_le]
      calc x * (2 : ℝ≥0) ^ n = x * (2 : ℝ≥0) ^ m * (2 : ℝ≥0) ^ (n - m) := by
            rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]
        _ ≤ (⌈x * 2 ^ m⌉₊ : ℝ≥0) * (2 : ℝ≥0) ^ (n - m) :=
            mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
        _ = ((⌈x * 2 ^ m⌉₊ * 2 ^ (n - m) : ℕ) : ℝ≥0) := by push_cast; ring
    calc (⌈x * 2 ^ n⌉₊ : ℝ≥0) * 2 ^ m
        ≤ ((⌈x * 2 ^ m⌉₊ * 2 ^ (n - m) : ℕ) : ℝ≥0) * 2 ^ m :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr key) (by positivity)
      _ = (⌈x * 2 ^ m⌉₊ : ℝ≥0) * ((2 : ℝ≥0) ^ (n - m) * 2 ^ m) := by
          push_cast; ring
      _ = (⌈x * 2 ^ m⌉₊ : ℝ≥0) * 2 ^ n := by
          rw [← pow_add, Nat.sub_add_cancel hmn]

lemma nnrealApproxSeq_le (τ : Ω → WithTop ℝ≥0) (n : ℕ) :
    τ ≤ nnrealApproxSeq τ n := by
  intro ω
  simp only [nnrealApproxSeq]
  cases hτ : τ ω with
  | top => simp
  | coe x =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    rw [le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ≥0) < 2) n)]
    exact Nat.le_ceil _

lemma nnrealApproxSeq_tendsto (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    Tendsto (nnrealApproxSeq τ · ω) atTop (𝓝 (τ ω)) := by
  simp only [nnrealApproxSeq]
  cases hτ : τ ω with
  | top => simp
  | coe x =>
    simp only [WithTop.map_coe]
    apply (WithTop.continuous_coe.tendsto x).comp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    · conv_rhs => rw [← add_zero x]
      exact tendsto_const_nhds.add
        ((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt
          (by norm_num : (1 : ℝ≥0) < 2))).congr (fun n => (one_mul _).symm))
    · intro n
      rw [le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ≥0) < 2) n)]
      exact Nat.le_ceil _
    · intro n
      calc (⌈x * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n
          ≤ (x * 2 ^ n + 1) / 2 ^ n :=
            div_le_div_of_nonneg_right (Nat.ceil_lt_add_one <| by positivity).le (by positivity)
        _ = x + 1 / 2 ^ n := by
            rw [add_div, mul_div_cancel_of_imp]
            exact fun h ↦ absurd h (by positivity)

noncomputable instance _root_.NNReal.approximable {𝓕 : Filtration ℝ≥0 mΩ} : Approximable 𝓕 μ :=
  ⟨fun τ hτ ↦ ⟨nnrealApproxSeq τ, nnrealApproxSeq_isStoppingTime 𝓕 hτ,
    nnrealApproxSeq_countable τ, nnrealApproxSeq_antitone τ,
    nnrealApproxSeq_le τ, ae_of_all _ <| nnrealApproxSeq_tendsto τ⟩⟩

end NNRealApprox

/-- The constant discrete approximation sequence. -/
def discreteApproxSequence_const (𝓕 : Filtration ι mΩ) (i : WithTop ι) :
    DiscreteApproxSequence 𝓕 (Function.const _ i) μ where
  seq := fun _ ↦ fun _ ↦ i
  isStoppingTime := fun n ↦ isStoppingTime_const' 𝓕 i
  countable := fun n ↦ by
    by_cases h : Nonempty Ω
    · simp
    · rw [not_nonempty_iff] at h
      rw [Set.range_eq_empty]
      exact Set.countable_empty
  antitone := antitone_const
  le := fun n ω ↦ le_rfl
  tendsto := by simp

lemma tendsto_stoppedValue_discreteApproxSequence [Nonempty ι] [TopologicalSpace E]
    (τn : DiscreteApproxSequence 𝓕 τ μ) (hX : ∀ ω, RightContinuous (X · ω)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ stoppedValue X (τn.seq n) ω) atTop (𝓝 (stoppedValue X τ ω)) := by
  filter_upwards [τn.tendsto] with ω hω
  simp only [stoppedValue]
  by_cases hτ : τ ω = ⊤
  · have (n : ℕ) : τn.seq n ω = ⊤ := by simpa [hτ] using τn.le n ω
    simp [hτ, this, tendsto_const_nhds]
  · have : Tendsto (WithTop.untopA ∘ fun x ↦ τn.seq x ω) atTop (𝓝[≥] (τ ω).untopA) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ((WithTop.untopA ∘ fun x ↦
        τn.seq x ω)) ((WithTop.tendsto_untopA hτ).comp hω) ?_
      have : {n : ℕ | τn.seq n ω ≠ ⊤} ∈ atTop := by
        simp only [ne_eq, mem_atTop_sets, ge_iff_le, Set.mem_setOf_eq]
        by_contra!
        have : Tendsto (fun x ↦ τn.seq x ω) atTop (𝓝 ⊤) := by
          simp only [tendsto_atTop_nhds]
          intro _ _ _
          obtain ⟨N, hN⟩ := this 0
          refine ⟨N, fun n hn => ?_⟩
          obtain ⟨M, hM⟩ := this n
          have : τn.seq n ω = ⊤ := by simpa [hM.2] using (τn.antitone hM.1 ω)
          grind
        exact hτ (tendsto_nhds_unique hω this)
      filter_upwards [this] with n hn
      simpa using WithTop.untopA_mono hn (τn.le n ω)
    simpa using (continuousWithinAt_Ioi_iff_Ici.mp (hX ω (τ ω).untopA)).tendsto.comp this

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

/-- The minimum of two discrete approximation sequences is a discrete approximation sequence of the
minimum of the two stopping times. -/
def DiscreteApproxSequence.inf
    (τn : DiscreteApproxSequence 𝓕 τ μ) (σn : DiscreteApproxSequence 𝓕 σ μ) :
    DiscreteApproxSequence 𝓕 (τ ⊓ σ) μ where
  seq := fun m ↦ min (τn m) (σn m)
  isStoppingTime := fun m ↦ (τn.isStoppingTime m).min (σn.isStoppingTime m)
  countable := fun m ↦ by
    refine ((τn.countable m).union (σn.countable m)).mono <| fun i ↦ ?_
    simp only [Set.mem_range, Pi.inf_apply, Set.mem_union, forall_exists_index, min_eq_iff]
    rintro ω (⟨rfl, -⟩ | ⟨rfl, -⟩)
    · exact Or.inl ⟨ω, rfl⟩
    · exact Or.inr ⟨ω, rfl⟩
  antitone := τn.antitone.inf σn.antitone
  le := fun m ↦ inf_le_inf (τn.le m) (σn.le m)
  tendsto := by
    filter_upwards [τn.tendsto, σn.tendsto] with ω hωτ hωσ using hωτ.min hωσ

/-- The minimum of two discrete approximation sequence of the same stopping time. -/
def DiscreteApproxSequence.inf'
    (τn : DiscreteApproxSequence 𝓕 τ μ) (τn' : DiscreteApproxSequence 𝓕 τ μ) :
    DiscreteApproxSequence 𝓕 τ μ where
  seq := fun m ↦ min (τn m) (τn' m)
  isStoppingTime := fun m ↦ (τn.isStoppingTime m).min (τn'.isStoppingTime m)
  countable := fun m ↦ by
    refine ((τn.countable m).union (τn'.countable m)).mono <| fun i ↦ ?_
    simp only [Set.mem_range, Pi.inf_apply, Set.mem_union, forall_exists_index, min_eq_iff]
    rintro ω (⟨rfl, -⟩ | ⟨rfl, -⟩)
    · exact Or.inl ⟨ω, rfl⟩
    · exact Or.inr ⟨ω, rfl⟩
  antitone := τn.antitone.inf τn'.antitone
  le := fun m ↦ le_inf (τn.le m) (τn'.le m)
  tendsto := by
    filter_upwards [τn.tendsto, τn'.tendsto] with ω hωτ hωσ using min_self (a := τ ω) ▸ hωτ.min hωσ

@[simp] lemma DiscreteApproxSequence.inf'_eq
    (τn : DiscreteApproxSequence 𝓕 τ μ) (τn' : DiscreteApproxSequence 𝓕 τ μ) (n : ℕ) :
    τn.inf' τn' n = min (τn n) (τn' n) :=
  rfl

@[simp] lemma DiscreteApproxSequence.inf'_apply
    (τn : DiscreteApproxSequence 𝓕 τ μ) (τn' : DiscreteApproxSequence 𝓕 τ μ) (n : ℕ) (ω : Ω) :
    τn.inf' τn' n ω = min (τn n ω) (τn' n ω) :=
  rfl

instance : LE (DiscreteApproxSequence 𝓕 τ μ) :=
  ⟨fun τn σn ↦ ∀ n, τn n ≤ σn n⟩

instance : PartialOrder (DiscreteApproxSequence 𝓕 τ μ) where
  le_refl := fun τn n ↦ le_rfl
  le_trans := fun τn σn ρn h₁ h₂ n ↦ (h₁ n).trans (h₂ n)
  le_antisymm := fun τn σn h₁ h₂ ↦ by
    ext n ω; exact le_antisymm (h₁ n ω) (h₂ n ω)

instance : SemilatticeInf (DiscreteApproxSequence 𝓕 τ μ) where
  inf := DiscreteApproxSequence.inf'
  inf_le_left := fun a₁ a₂ n ω ↦ by simp
  inf_le_right := fun a₁ a₂ n ω ↦ by simp
  le_inf := fun a₁ a₂ a₃ h₁ h₂ n ω ↦ by aesop

lemma DiscreteApproxSequence.discreteApproxSequence_of_le_inf_le_of_left {i : ι}
    (τn : DiscreteApproxSequence 𝓕 τ μ) (σn : DiscreteApproxSequence 𝓕 σ μ)
    (hτ : ∀ ω, τ ω ≤ i) (m : ℕ) (ω : Ω) :
    (discreteApproxSequence_of 𝓕 hτ τn).inf σn m ω ≤ i :=
  (min_le_left _ _).trans <| discreteApproxSequence_of_le hτ τn m ω

variable [Nonempty ι] [OrderBot ι] [FirstCountableTopology ι] [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma uniformIntegrable_stoppedValue_discreteApproxSequence_of_le
    (h : Martingale X 𝓕 μ) (τn : DiscreteApproxSequence 𝓕 τ μ) (hτn_le : ∀ n ω, τn n ω ≤ i) :
    UniformIntegrable (fun m ↦ stoppedValue X (τn m)) 1 μ :=
  h.uniformIntegrable_stoppedValue_of_countable_range _
    (τn.isStoppingTime) (fun n ω ↦ hτn_le n ω) (τn.countable)

lemma uniformIntegrable_stoppedValue_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) :
    UniformIntegrable (fun m ↦ stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m)) 1 μ :=
  uniformIntegrable_stoppedValue_discreteApproxSequence_of_le h _
    (discreteApproxSequence_of_le hτ_le τn)

lemma integrable_stoppedValue_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) (m : ℕ) :
    Integrable (stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m)) μ :=
  ((uniformIntegrable_stoppedValue_discreteApproxSequence h hτ_le τn).memLp m).integrable
    le_rfl

lemma aestronglyMeasurable_stoppedValue_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω))
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
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω))
    (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) :
    Tendsto (fun i ↦
      eLpNorm (stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn i) - stoppedValue X τ) 1 μ)
      atTop (𝓝 0) :=
  tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1)
    ((uniformIntegrable_stoppedValue_discreteApproxSequence h hτ_le
    τn).memLp_of_tendstoInMeasure (tendstoInMeasure_of_tendsto_ae
      (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1) <|
      tendsto_stoppedValue_discreteApproxSequence _ hRC))
    (uniformIntegrable_stoppedValue_discreteApproxSequence h hτ_le τn).2.1
    (tendstoInMeasure_of_tendsto_ae
      (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1) <|
      tendsto_stoppedValue_discreteApproxSequence _ hRC)

lemma integrable_stoppedValue_of_discreteApproxSequence'
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω))
    (hτ_le : ∀ ω, τ ω ≤ i) (τn : DiscreteApproxSequence 𝓕 τ μ) :
    Integrable (stoppedValue X τ) μ :=
  let τn' := discreteApproxSequence_of 𝓕 hτ_le τn
  UniformIntegrable.integrable_of_tendstoInMeasure
    (h.uniformIntegrable_stoppedValue_of_countable_range τn' τn'.isStoppingTime
      (discreteApproxSequence_of_le hτ_le τn) τn'.countable)
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun m ↦ (integrable_stoppedValue_of_discreteApproxSequence h hτ_le τn m).1)
      (aestronglyMeasurable_stoppedValue_of_discreteApproxSequence h hRC hτ_le τn') <|
      tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence h hRC hτ_le τn)

lemma tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence_of_le
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω))
    (τn : DiscreteApproxSequence 𝓕 τ μ) (hτn_le : ∀ n ω, τn n ω ≤ i) :
    Tendsto (fun i ↦ eLpNorm (stoppedValue X (τn i) - stoppedValue X τ) 1 μ) atTop (𝓝 0) := by
  have hτ_le : ∀ ω, τ ω ≤ i := fun ω ↦ (τn.le 0 ω).trans (hτn_le 0 ω)
  refine tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun m ↦ (((uniformIntegrable_stoppedValue_discreteApproxSequence_of_le
      h τn hτn_le).memLp m).integrable le_rfl).1) ?_
    (h.uniformIntegrable_stoppedValue_of_countable_range τn τn.isStoppingTime
      hτn_le τn.countable).2.1
    (tendstoInMeasure_of_tendsto_ae
      (fun m ↦ (((uniformIntegrable_stoppedValue_discreteApproxSequence_of_le
      h τn hτn_le).memLp m).integrable le_rfl).1) <|
      tendsto_stoppedValue_discreteApproxSequence _ hRC)
  rw [memLp_one_iff_integrable]
  exact integrable_stoppedValue_of_discreteApproxSequence' h hRC hτ_le τn

end MeasureTheory
