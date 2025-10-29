/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import Mathlib.Probability.Process.Stopping
import BrownianMotion.StochasticIntegral.Predictable

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

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
  {p q : (ι → Ω → E) → Prop}

-- Move. Can this be generalized?
theorem _root_.Filter.Tendsto.min_atTop_atTop {α β : Type*}
    [Nonempty β] [LinearOrder β] [LinearOrder α]
    {f g : β → α} (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    Tendsto (fun x ↦ f x ⊓ g x) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop] at *
  exact fun a ↦ let ⟨b₁, hb₁⟩ := hf a; let ⟨b₂, hb₂⟩ := hg a
    ⟨max b₁ b₂, fun B hB ↦ le_min (hb₁ _ (max_le_iff.1 hB).1) (hb₂ _ (max_le_iff.1 hB).2)⟩

lemma IsLocalizingSequence.min {τ σ : ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : IsLocalizingSequence 𝓕 σ P) :
    IsLocalizingSequence 𝓕 (min τ σ) P where
  isStoppingTime n := (hτ.isStoppingTime n).min (hσ.isStoppingTime n)
  mono := by filter_upwards [hτ.mono, hσ.mono] with ω hτω hσω; exact hτω.min hσω
  tendsto_top := by
    filter_upwards [hτ.tendsto_top, hσ.tendsto_top] with ω hτω hσω using hτω.min_atTop_atTop hσω

variable [OrderBot ι]

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

lemma Locally.of_and [Zero E] (hX : Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P) :
    Locally p 𝓕 X P ∧ Locally q 𝓕 X P :=
  ⟨hX.mono <| fun _ ↦ And.left, hX.mono <| fun _ ↦ And.right⟩

lemma Locally.of_and_left [Zero E] (hX : Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P) :
    Locally p 𝓕 X P :=
  hX.of_and.left

lemma Locally.of_and_right [Zero E] (hX : Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P) :
    Locally q 𝓕 X P :=
  hX.of_and.right

/-- A property of stochastic processes is said to be stable if it is preserved under taking
the stopped process by a stopping time. -/
def IsStable [Zero E] (p : (ι → Ω → E) → Prop) (𝓕 : Filtration ι mΩ) : Prop :=
  ∀ X : ι → Ω → E, p X → ∀ τ : Ω → WithTop ι, IsStoppingTime 𝓕 τ →
    p (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ)

-- Move
lemma stoppedProcess_indicator_comm {β : Type*} [Zero β] {u : ι → Ω → β}
    {τ : Ω → WithTop ι} {s : Set Ω} (i : ι) :
    stoppedProcess (fun i ↦ s.indicator (u i)) τ i
      = s.indicator (stoppedProcess u τ i) := by
  ext ω
  rw [Set.indicator]
  split_ifs with hω
  · rw [stoppedProcess, Set.indicator_of_mem hω, stoppedProcess]
  · rw [stoppedProcess, Set.indicator_of_notMem hω]

-- Move
lemma stoppedProcess_indicator_comm' {β : Type*} [Zero β] {u : ι → Ω → β}
    {τ : Ω → WithTop ι} {s : Set Ω} :
    stoppedProcess (fun i ↦ s.indicator (u i)) τ
      = fun i ↦ s.indicator (stoppedProcess u τ i) := by
  ext i ω
  rw [stoppedProcess_indicator_comm]

-- Move
theorem _root_.MeasureTheory.stoppedValue_stoppedProcess_apply
    {β : Type*} {ω : Ω} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} (hω : σ ω ≠ ⊤) :
    stoppedValue (stoppedProcess u τ) σ ω = stoppedValue u (fun ω ↦ min (σ ω) (τ ω)) ω := by
  simp only [stoppedValue_stoppedProcess, ne_eq, hω, not_false_eq_true, reduceIte]

-- Move
@[simp] theorem _root_.MeasureTheory.stoppedProcess_stoppedProcess
    {β : Type*} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (σ ⊓ τ) := by
  ext i ω
  rw [stoppedProcess, stoppedProcess, stoppedProcess]
  by_cases hτ : τ ω = ⊤
  · simp only [hτ, le_top, inf_of_le_left, WithTop.untopD_coe, Pi.inf_apply]
  by_cases hσ : σ ω = ⊤
  · simp only [hσ, le_top, inf_of_le_left, WithTop.untopD_coe, Pi.inf_apply, inf_of_le_right]
  by_cases hστ : σ ω ≤ τ ω
  · rw [min_eq_left, WithTop.untopA_eq_untop (lt_of_le_of_lt ((min_le_right _ _).trans hστ) <|
        WithTop.lt_top_iff_ne_top.2 hτ).ne, WithTop.coe_untop]
    · simp only [Pi.inf_apply, hστ, inf_of_le_left]
    · refine le_trans ?_ hστ
      rw [WithTop.untopA_eq_untop (lt_of_le_of_lt ((min_le_right _ _).trans hστ) <|
        WithTop.lt_top_iff_ne_top.2 hτ).ne, WithTop.coe_untop]
      exact min_le_right _ _
  · nth_rewrite 2 [WithTop.untopA_eq_untop ]
    · rw [WithTop.coe_untop, min_assoc]
      rfl
    · exact (lt_of_le_of_lt (min_le_right _ _) <| WithTop.lt_top_iff_ne_top.2 hσ).ne

-- Move
@[simp] theorem _root_.MeasureTheory.stoppedProcess_stoppedProcess'
    {β : Type*} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (fun ω ↦ min (σ ω) (τ ω)) := by
  simp; rfl

-- Move
theorem _root_.MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
    {β : Type*} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} (h : σ ≤ τ) :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u σ := by
  rw [stoppedProcess_stoppedProcess, inf_of_le_left h]

-- Move
theorem _root_.MeasureTheory.stoppedProcess_stoppedProcess_of_le_left
    {β : Type*} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} (h : τ ≤ σ) :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u τ := by
  rw [stoppedProcess_stoppedProcess, inf_of_le_right h]

-- Move
theorem _root_.MeasureTheory.stoppedProcess_eq_stoppedValue_apply
    {β : Type*} {u : ι → Ω → β} {τ : Ω → WithTop ι} (i : ι) (ω : Ω) :
    stoppedProcess u τ i ω = stoppedValue u (fun ω ↦ min i (τ ω)) ω := rfl

lemma locally_and [Zero E] (hp : IsStable p 𝓕) (hq : IsStable q 𝓕) :
    Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P ↔ Locally p 𝓕 X P ∧ Locally q 𝓕 X P := by
  refine ⟨Locally.of_and, fun ⟨hpX, hqX⟩ ↦
    ⟨_, hpX.IsLocalizingSequence.min hqX.IsLocalizingSequence, fun n ↦ ⟨?_, ?_⟩⟩⟩
  · convert hp _ (hpX.stoppedProcess n) _ <| hqX.IsLocalizingSequence.isStoppingTime n using 1
    ext i ω
    rw [stoppedProcess_indicator_comm]
    simp_rw [Pi.inf_apply, lt_inf_iff, inf_comm (hpX.localSeq n)]
    rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_comm,
      (_ : {ω | ⊥ < hpX.localSeq n ω ∧ ⊥ < hqX.localSeq n ω}
        = {ω | ⊥ < hpX.localSeq n ω} ∩ {ω | ⊥ < hqX.localSeq n ω}), Set.inter_comm]
    · simp_rw [← Set.indicator_indicator]
      rfl
    · rfl
  · convert hq _ (hqX.stoppedProcess n) _ <| hpX.IsLocalizingSequence.isStoppingTime n using 1
    ext i ω
    rw [stoppedProcess_indicator_comm]
    simp_rw [Pi.inf_apply, lt_inf_iff]
    rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_comm,
      (_ : {ω | ⊥ < hpX.localSeq n ω ∧ ⊥ < hqX.localSeq n ω}
        = {ω | ⊥ < hpX.localSeq n ω} ∩ {ω | ⊥ < hqX.localSeq n ω})]
    · simp_rw [← Set.indicator_indicator]
      rfl
    · rfl

end LinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [DenselyOrdered ι] [FirstCountableTopology ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

-- Move
lemma isStoppingTime_of_measurableSet_lt_of_isRightContinuous [NoMaxOrder ι]
    {τ : Ω → WithTop ι} (h𝓕 : IsRightContinuous 𝓕) (hτ : ∀ i, MeasurableSet[𝓕 i] {ω | τ ω < i}) :
    IsStoppingTime 𝓕 τ := by
  intro i
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := exists_seq_strictAnti_tendsto i
  refine MeasurableSet.of_compl ?_
  rw [(_ : {ω | τ ω ≤ i}ᶜ = ⋃ n, {ω | u n ≤ τ ω})]
  · refine measurableSet_of_isRightContinuous ?_
    simp_rw [MeasurableSpace.measurableSet_iInf]
    intros j hj
    obtain ⟨N, hN⟩ := (hu₃.eventually_le_const hj).exists
    rw [(_ : ⋃ n, {ω | u n ≤ τ ω} = ⋃ n ≥ N, {ω | u n ≤ τ ω})]
    · refine MeasurableSet.iUnion <| fun n ↦ MeasurableSet.iUnion <| fun hn ↦
        𝓕.mono ((hu₁.antitone hn).trans hN) _ <| MeasurableSet.of_compl ?_
      rw [(by ext; simp : {ω | u n ≤ τ ω}ᶜ = {ω | τ ω < u n})]
      exact hτ (u n)
    · ext ω
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, ge_iff_le, exists_prop]
      constructor
      · rintro ⟨i, hle⟩
        refine ⟨i + N, N.le_add_left i, le_trans ?_ hle⟩
        norm_cast
        exact hu₁.antitone <| i.le_add_right N
      · rintro ⟨i, -, hi⟩
        exact ⟨i, hi⟩
  · ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, Set.mem_iUnion]
    constructor
    · intro h
      by_cases hτ : τ ω = ⊤
      · exact ⟨0, hτ ▸ le_top⟩
      · have hlt : i < (τ ω).untop hτ := by
          rwa [WithTop.lt_untop_iff]
        obtain ⟨N, hN⟩ := (hu₃.eventually_le_const hlt).exists
        refine ⟨N, WithTop.coe_le_iff.2 <| fun n hn ↦ hN.trans ?_⟩
        simp only [hn, WithTop.untop_coe, le_refl]
    · rintro ⟨j, hj⟩
      refine lt_of_lt_of_le ?_ hj
      norm_cast
      exact hu₂ _

-- Move
lemma isStoppingTime_of_measurableSet_lt_of_isRightContinuous' {τ : Ω → WithTop ι}
    (h𝓕 : IsRightContinuous 𝓕) (hτ : ∀ i, ¬ IsMax i → MeasurableSet[𝓕 i] {ω | τ ω < i})
    (hτmax : ∀ i, IsMax i → MeasurableSet[𝓕 i] {ω | τ ω = ⊤}) :
    IsStoppingTime 𝓕 τ := by
  intro i
  by_cases hmax : IsMax i
  · rw [(_ : {ω | τ ω ≤ i} = {ω | τ ω = ⊤}ᶜ)]
    · exact (hτmax i hmax).compl
    · ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      constructor
      · rintro hle htop
        rw [htop] at hle
        simp only [top_le_iff, WithTop.coe_ne_top] at hle
      · intro htop
        rw [← WithTop.coe_untop _ htop]
        norm_cast
        exact not_lt.1 hmax.not_lt
  rw [not_isMax_iff] at hmax
  obtain ⟨j, hj⟩ := hmax
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := exists_seq_strictAnti_tendsto' hj
  refine MeasurableSet.of_compl ?_
  rw [(_ : {ω | τ ω ≤ i}ᶜ = ⋃ n, {ω | u n ≤ τ ω})]
  · refine measurableSet_of_isRightContinuous ?_
    simp_rw [MeasurableSpace.measurableSet_iInf]
    intros j hj
    obtain ⟨N, hN⟩ := (hu₃.eventually_le_const hj).exists
    rw [(_ : ⋃ n, {ω | u n ≤ τ ω} = ⋃ n > N, {ω | u n ≤ τ ω})]
    · refine MeasurableSet.iUnion <| fun n ↦ MeasurableSet.iUnion <| fun hn ↦
        𝓕.mono ((hu₁ hn).le.trans hN) _ <| MeasurableSet.of_compl ?_
      rw [(by ext; simp : {ω | u n ≤ τ ω}ᶜ = {ω | τ ω < u n})]
      refine hτ (u n) <| not_isMax_iff.2 ⟨u N, hu₁ hn⟩
    · ext ω
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, gt_iff_lt, exists_prop]
      constructor
      · rintro ⟨i, hle⟩
        refine ⟨i + N + 1, by linarith, le_trans ?_ hle⟩
        norm_cast
        exact hu₁.antitone (by linarith)
      · rintro ⟨i, -, hi⟩
        exact ⟨i, hi⟩
  · ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, Set.mem_iUnion]
    constructor
    · intro h
      by_cases hτ : τ ω = ⊤
      · exact ⟨0, hτ ▸ le_top⟩
      · have hlt : i < (τ ω).untop hτ := by
          rwa [WithTop.lt_untop_iff]
        obtain ⟨N, hN⟩ := (hu₃.eventually_le_const hlt).exists
        refine ⟨N, WithTop.coe_le_iff.2 <| fun n hn ↦ hN.trans ?_⟩
        simp only [hn, WithTop.untop_coe, le_refl]
    · rintro ⟨j, hj⟩
      refine lt_of_lt_of_le ?_ hj
      norm_cast
      exact (hu₂ j).1

variable [NoMaxOrder ι]

-- Move. Weaken the lattice assumption?
lemma IsStoppingTime.iInf {𝓕 : Filtration ι mΩ} {τ : ℕ → Ω → WithTop ι}
    (s : Set ℕ) (h𝓕 : IsRightContinuous 𝓕) (hτ : ∀ n, IsStoppingTime 𝓕 (τ n)) :
    IsStoppingTime 𝓕 (fun ω ↦ ⨅ (n) (_ : n ∈ s), τ n ω) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous h𝓕 <| fun i ↦ ?_
  refine MeasurableSet.of_compl ?_
  rw [(_ : {ω | ⨅ n ∈ s, τ n ω < i}ᶜ = ⋂ n ∈ s, {ω | i ≤ τ n ω})]
  · exact MeasurableSet.iInter <| fun n ↦ MeasurableSet.iInter <| fun hn ↦ (hτ n).measurableSet_ge i
  · ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, le_iInf_iff, Set.mem_iInter]

-- 1: IsStoppingTime.iInf
-- 2: Given a sequence of stopping times `τₙ` which converge to infinity,
--  `σₙ := inf_{k ≤ n} τₖ` defines a localizing sequence.

lemma IsLocalizingSequence.exists_subseq_isStoppingTime_tendsto_atTop
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, StrictMono nk
      ∧ ∀ᵐ ω ∂P, Tendsto (fun i ↦ (τ i ω) ⊓ (σ i (nk i) ω)) atTop atTop := by
  sorry

lemma isLocalizingSequence_of_isStoppingTime_tendsto_atTop
    {τ : ℕ → Ω → WithTop ι} (h𝓕 : IsRightContinuous 𝓕)
    (hτ : ∀ n, IsStoppingTime 𝓕 (τ n)) (hTends : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop atTop) :
    IsLocalizingSequence 𝓕 (fun i ω ↦ ⨅ j ≥ i, τ j ω) P where
  isStoppingTime (n : ℕ) := IsStoppingTime.iInf {j | j ≥ n} h𝓕 (fun j ↦ hτ j)
  mono :=  ae_of_all _ <| fun ω n m hnm ↦ iInf_le_iInf_of_subset <| fun k hk ↦ hnm.trans hk
  tendsto_top := by
    filter_upwards [hTends] with ω hω
    rw [tendsto_atTop_atTop] at ⊢ hω
    intro C
    obtain ⟨i, hi⟩ := hω C
    exact ⟨i, fun j hij ↦ le_iInf <| fun k ↦ le_iInf fun hk ↦ hi _ <| hij.trans hk⟩

lemma IsLocalizingSequence.exists_subseq_isLocalizingSequence_tendsto_atTop
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι} (h𝓕 : IsRightContinuous 𝓕)
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, IsLocalizingSequence 𝓕 (fun i ω ↦ ⨅ j ≥ i, (τ j ω) ⊓ (σ j (nk j) ω)) P := by
  obtain ⟨nk, hnk₁, hnk₂⟩ := hτ.exists_subseq_isStoppingTime_tendsto_atTop hσ
  exact ⟨nk, isLocalizingSequence_of_isStoppingTime_tendsto_atTop h𝓕
    (fun j ↦ (hτ.isStoppingTime j).min <| (hσ j).isStoppingTime (nk j)) hnk₂⟩

/-- A stable property holding locally is idempotent. -/
lemma locally_locally [Zero E] (h𝓕 : IsRightContinuous 𝓕) (hp : IsStable p 𝓕) :
    Locally (fun Y ↦ Locally p 𝓕 Y P) 𝓕 X P ↔ Locally p 𝓕 X P := by
  refine ⟨fun hL ↦ ?_, fun hL ↦ ?_⟩
  · have hLL := hL.stoppedProcess
    choose τ hτ₁ hτ₂ using hLL
    obtain ⟨nk, hnk⟩ :=
      hL.IsLocalizingSequence.exists_subseq_isLocalizingSequence_tendsto_atTop h𝓕 hτ₁
    refine ⟨_, hnk, fun n ↦ ?_⟩
    have := hp _ (hτ₂ n (nk n)) (fun ω ↦ ⨅ j ≥ n, (hL.localSeq j ω) ⊓ (τ j (nk j) ω)) ?_
    · rw [stoppedProcess_indicator_comm', ← stoppedProcess_stoppedProcess_of_le_right
        (τ := fun ω ↦ (hL.localSeq n ω) ⊓ (τ n (nk n) ω))
        (fun _ ↦ (iInf_le _ n).trans <| iInf_le _ le_rfl), ← stoppedProcess_indicator_comm']
      convert this using 2
      ext i ω
      rw [stoppedProcess_indicator_comm', stoppedProcess_indicator_comm',
        stoppedProcess_indicator_comm', Set.indicator_indicator, Set.indicator_indicator]
      · congr 1
        · ext ω'
          simp only [ge_iff_le, Set.mem_setOf_eq, Set.mem_inter_iff]
          exact ⟨fun h ↦ ⟨⟨h, lt_of_lt_of_le h <| (iInf_le _ n).trans <|
              (iInf_le _ le_rfl).trans <| min_le_right _ _⟩,
            lt_of_lt_of_le h <| (iInf_le _ n).trans <| (iInf_le _ le_rfl).trans <| min_le_left _ _⟩,
            fun h ↦ h.1.1⟩
        · rw [stoppedProcess_stoppedProcess, inf_comm]; rfl
    · exact IsStoppingTime.iInf {j | j ≥ n} h𝓕 <| fun j ↦
        (hL.IsLocalizingSequence.isStoppingTime j).min <| (hτ₁ j).isStoppingTime (nk j)
  · exact ⟨hL.localSeq, hL.IsLocalizingSequence, fun n ↦ locally_of_prop <| hL.stoppedProcess n⟩

/-- If `p` implies `q` locally, then `p` locally implies `q` locally. -/
lemma locally_induction [Zero E] (h𝓕 : IsRightContinuous 𝓕)
    (hpq : ∀ Y, p Y → Locally q 𝓕 Y P) (hq : IsStable q 𝓕) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  (locally_locally h𝓕 hq).1 <| hpX.mono hpq

end ConditionallyCompleteLinearOrderBot

end ProbabilityTheory
