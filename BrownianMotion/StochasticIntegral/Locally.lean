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

section ToMove

-- This section contains lemmas that should be moved files which already exist in mathlib.

section Tendsto

theorem _root_.Filter.Tendsto.min_atTop_atTop {α β : Type*}
    [Nonempty β] [LinearOrder β] [LinearOrder α]
    {f g : β → α} (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    Tendsto (fun x ↦ f x ⊓ g x) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop] at *
  exact fun a ↦ let ⟨b₁, hb₁⟩ := hf a; let ⟨b₂, hb₂⟩ := hg a
    ⟨max b₁ b₂, fun B hB ↦ le_min (hb₁ _ (max_le_iff.1 hB).1) (hb₂ _ (max_le_iff.1 hB).2)⟩

lemma _root_.WithTop.tendsto_nhds_top_iff {α : Type*}
    [Nonempty ι] [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] {f : Filter α}
    (x : α → WithTop ι) :
    Tendsto x f (𝓝 ⊤) ↔ ∀ (i : ι), ∀ᶠ (a : α) in f, i < x a := by
  refine nhds_top_basis.tendsto_right_iff.trans ?_
  simp only [Set.mem_Ioi]
  refine ⟨fun h i ↦ h i trivial, fun h i hi ↦ ?_⟩
  specialize h (i.untop hi.ne)
  filter_upwards [h] with a ha
  simpa using ha

lemma _root_.WithTop.tendsto_atTop_nhds_top_iff {α : Type*}
    [Nonempty ι] [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    [Nonempty α] [inst : Preorder α] [IsDirected α fun x1 x2 ↦ x1 ≤ x2] (x : α → WithTop ι) :
    Tendsto x atTop (𝓝 ⊤) ↔ ∀ (i : ι), ∃ N, ∀ n ≥ N, i < x n := by
  rw [WithTop.tendsto_nhds_top_iff]
  simp only [eventually_atTop, ge_iff_le]

lemma _root_.Filter.Tendsto.tendsto_withTop_atTop_nhds_top
    [Nonempty ι] [LinearOrder ι] [NoMaxOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    {a : ℕ → ι} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n ↦ (a n : WithTop ι)) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_atTop_nhds_top_iff]
  rw [tendsto_atTop_atTop] at ha
  norm_cast
  intro i
  obtain ⟨i', hi'⟩ := NoMaxOrder.exists_gt i
  obtain ⟨j, hj⟩ := ha i'
  exact ⟨j, fun n hn ↦ lt_of_lt_of_le hi' <| hj _ hn⟩

end Tendsto

section StoppedProcess

variable [Nonempty ι] [LinearOrder ι]

lemma stoppedProcess_indicator_comm {β : Type*} [Zero β] {u : ι → Ω → β}
    {τ : Ω → WithTop ι} {s : Set Ω} (i : ι) :
    stoppedProcess (fun i ↦ s.indicator (u i)) τ i
      = s.indicator (stoppedProcess u τ i) := by
  ext ω
  rw [Set.indicator]
  split_ifs with hω
  · rw [stoppedProcess, Set.indicator_of_mem hω, stoppedProcess]
  · rw [stoppedProcess, Set.indicator_of_notMem hω]

lemma stoppedProcess_indicator_comm' {β : Type*} [Zero β] {u : ι → Ω → β}
    {τ : Ω → WithTop ι} {s : Set Ω} :
    stoppedProcess (fun i ↦ s.indicator (u i)) τ
      = fun i ↦ s.indicator (stoppedProcess u τ i) := by
  ext i ω
  rw [stoppedProcess_indicator_comm]

theorem _root_.MeasureTheory.stoppedValue_stoppedProcess_apply
    {β : Type*} {ω : Ω} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} (hω : σ ω ≠ ⊤) :
    stoppedValue (stoppedProcess u τ) σ ω = stoppedValue u (fun ω ↦ min (σ ω) (τ ω)) ω := by
  simp only [stoppedValue_stoppedProcess, ne_eq, hω, not_false_eq_true, reduceIte]

@[simp]
theorem _root_.MeasureTheory.stoppedProcess_stoppedProcess
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

theorem _root_.MeasureTheory.stoppedProcess_stoppedProcess'
    {β : Type*} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (fun ω ↦ min (σ ω) (τ ω)) := by
  simp; rfl

theorem _root_.MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
    {β : Type*} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} (h : σ ≤ τ) :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u σ := by
  rw [stoppedProcess_stoppedProcess, inf_of_le_left h]

theorem _root_.MeasureTheory.stoppedProcess_stoppedProcess_of_le_left
    {β : Type*} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} (h : τ ≤ σ) :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u τ := by
  rw [stoppedProcess_stoppedProcess, inf_of_le_right h]

theorem _root_.MeasureTheory.stoppedProcess_eq_stoppedValue_apply
    {β : Type*} {u : ι → Ω → β} {τ : Ω → WithTop ι} (i : ι) (ω : Ω) :
    stoppedProcess u τ i ω = stoppedValue u (fun ω ↦ min i (τ ω)) ω := rfl

end StoppedProcess

section IsStoppingTime

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [DenselyOrdered ι] [FirstCountableTopology ι] {𝓕 : Filtration ι mΩ}

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

-- This lemma will change when we decide on the correct definition of `IsRightContinuous`
lemma isStoppingTime_of_measurableSet_lt_of_isRightContinuous' {τ : Ω → WithTop ι}
    (h𝓕 : IsRightContinuous 𝓕) (hτ : ∀ i, ¬ IsMax i → MeasurableSet[𝓕 i] {ω | τ ω < i}) :
    IsStoppingTime 𝓕 τ := by
  intro i
  by_cases hmax : IsMax i
  · have := IsRightContinuous.RC (𝓕 := 𝓕) i
    rw [iInf₂_eq_top.2] at this
    · exact this.le _ trivial
    · exact fun j hj ↦ False.elim <| hmax.not_lt hj
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

lemma IsStoppingTime.iInf {𝓕 : Filtration ι mΩ} {τ : ℕ → Ω → WithTop ι}
    (s : Set ℕ) (h𝓕 : IsRightContinuous 𝓕) (hτ : ∀ n, IsStoppingTime 𝓕 (τ n)) :
    IsStoppingTime 𝓕 (fun ω ↦ ⨅ (n) (_ : n ∈ s), τ n ω) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous h𝓕 <| fun i ↦ ?_
  refine MeasurableSet.of_compl ?_
  rw [(_ : {ω | ⨅ n ∈ s, τ n ω < i}ᶜ = ⋂ n ∈ s, {ω | i ≤ τ n ω})]
  · exact MeasurableSet.iInter <| fun n ↦ MeasurableSet.iInter <| fun hn ↦ (hτ n).measurableSet_ge i
  · ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, le_iInf_iff, Set.mem_iInter]

end IsStoppingTime

end ToMove

/-- A localizing sequence is a sequence of stopping times that tends almost surely to infinity. -/
structure IsPreLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι) (P : Measure Ω := by volume_tac) :
    Prop where
  isStoppingTime : ∀ n, IsStoppingTime 𝓕 (τ n)
  tendsto_top : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤)

/-- A localizing sequence is a sequence of stopping times that is almost surely increasing and
tends almost surely to infinity. -/
structure IsLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι)
    (P : Measure Ω := by volume_tac) extends IsPreLocalizingSequence 𝓕 τ P where
  mono : ∀ᵐ ω ∂P, Monotone (τ · ω)

lemma isLocalizingSequence_const_top [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) : IsLocalizingSequence 𝓕 (fun _ _ ↦ ⊤) P where
  isStoppingTime n := by simp [IsStoppingTime]
  mono := ae_of_all _ fun _ _ _ _ ↦ by simp
  tendsto_top := by filter_upwards [] with ω using tendsto_const_nhds

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

lemma IsLocalizingSequence.min [TopologicalSpace ι] [OrderTopology ι] {τ σ : ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : IsLocalizingSequence 𝓕 σ P) :
    IsLocalizingSequence 𝓕 (min τ σ) P where
  isStoppingTime n := (hτ.isStoppingTime n).min (hσ.isStoppingTime n)
  mono := by filter_upwards [hτ.mono, hσ.mono] with ω hτω hσω; exact hτω.min hσω
  tendsto_top := by
    filter_upwards [hτ.tendsto_top, hσ.tendsto_top] with ω hτω hσω using hτω.min hσω

variable [OrderBot ι]

@[simp]
lemma stoppedProcess_const_top : stoppedProcess X (fun _ ↦ ⊤) = X := by
  unfold stoppedProcess
  simp

/-- A stochastic process `X` is said to satisfy a property `p` locally with respect to a
filtration `𝓕` if there exists a localizing sequence `(τ_n)` such that for all `n`, the stopped
process of `fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)` satisfies `p`. -/
def Locally [TopologicalSpace ι] [OrderTopology ι] [Zero E]
    (p : (ι → Ω → E) → Prop) (𝓕 : Filtration ι mΩ)
    (X : ι → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∃ τ : ℕ → Ω → WithTop ι, IsLocalizingSequence 𝓕 τ P ∧
    ∀ n, p (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))

section Locally

variable [TopologicalSpace ι] [OrderTopology ι]

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

end Locally

/-- A property of stochastic processes is said to be stable if it is preserved under taking
the stopped process by a stopping time. -/
def IsStable [Zero E]
    (𝓕 : Filtration ι mΩ) (p : (ι → Ω → E) → Prop) : Prop :=
    ∀ X : ι → Ω → E, p X → ∀ τ : Ω → WithTop ι, IsStoppingTime 𝓕 τ →
      p (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ)

variable [TopologicalSpace ι] [OrderTopology ι]

lemma locally_and [Zero E] (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q) :
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
  [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

lemma measure_iInter_of_ae_antitone {ι : Type*}
    [Countable ι] [Preorder ι] [IsDirected ι fun (x1 x2 : ι) ↦ x1 ≤ x2]
    {s : ι → Set Ω} (hs : ∀ᵐ ω ∂P, Antitone (s · ω))
    (hsm : ∀ (i : ι), MeasureTheory.NullMeasurableSet (s i) P) (hfin : ∃ (i : ι), P (s i) ≠ ⊤) :
    P (⋂ (i : ι), s i) = ⨅ (i : ι), P (s i) := by
  set t : ι → Set Ω := fun i ↦ ⋂ j ≤ i, s j with ht
  have hst (i : ι) : s i =ᵐ[P] t i := by
    filter_upwards [hs] with ω hω
    suffices ω ∈ s i ↔ ω ∈ t i by
      exact propext this
    simp only [ht, Set.mem_iInter]
    refine ⟨fun (h : s i ω) j hj ↦ ?_, fun h ↦ h i le_rfl⟩
    change s j ω
    specialize hω hj
    simp only [le_Prop_eq] at hω
    exact hω h
  rw [measure_congr <| EventuallyEq.countable_iInter hst, Antitone.measure_iInter]
  · exact iInf_congr <| fun i ↦ measure_congr <| (hst i).symm
  · intros i j hij
    simp only [ht]
    rw [(_ : ⋂ k ≤ j, s k = (⋂ k ≤ i, s k) ∩ (⋂ k ∈ {k | k ≤ j ∧ ¬ k ≤ i}, s k))]
    · exact Set.inter_subset_left
    · ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_inter_iff, and_imp]
      grind
  · exact fun _ ↦ NullMeasurableSet.iInter <| fun j ↦ NullMeasurableSet.iInter <| fun _ ↦ hsm j
  · obtain ⟨i, hi⟩ := hfin
    refine ⟨i, (lt_of_le_of_lt ?_ <| lt_top_iff_ne_top.2 hi).ne⟩
    rw [measure_congr (hst i)]

lemma isLocalizingSequence_of_isPreLocalizingSequence
    {τ : ℕ → Ω → WithTop ι} (h𝓕 : IsRightContinuous 𝓕) (hτ : IsPreLocalizingSequence 𝓕 τ P) :
    IsLocalizingSequence 𝓕 (fun i ω ↦ ⨅ j ≥ i, τ j ω) P where
  isStoppingTime (n : ℕ) := IsStoppingTime.iInf {j | j ≥ n} h𝓕 (fun j ↦ hτ.isStoppingTime j)
  mono :=  ae_of_all _ <| fun ω n m hnm ↦ iInf_le_iInf_of_subset <| fun k hk ↦ hnm.trans hk
  tendsto_top := by
    filter_upwards [hτ.tendsto_top] with ω hω
    replace hω := hω.liminf_eq
    rw [liminf_eq_iSup_iInf_of_nat] at hω
    rw [← hω]
    refine tendsto_atTop_iSup ?_
    intro n m hnm
    simp only [ge_iff_le, le_iInf_iff, iInf_le_iff]
    intro k hk i hi
    grind

/-- A stable property holds locally `p` for `X` if there exists a pre-localizing sequence `τ` for
which the stopped process of `fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)` satisfies `p`. -/
lemma locally_of_isPreLocalizingSequence [Zero E] {τ : ℕ → Ω → WithTop ι}
    (hp : IsStable 𝓕 p) (h𝓕 : IsRightContinuous 𝓕) (hτ : IsPreLocalizingSequence 𝓕 τ P)
    (hpτ : ∀ n, p (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))) :
    Locally p 𝓕 X P := by
  refine ⟨_, isLocalizingSequence_of_isPreLocalizingSequence h𝓕 hτ, fun n ↦ ?_⟩
  have := hp _ (hpτ n) (fun ω ↦ ⨅ j ≥ n, τ j ω) <|
    (isLocalizingSequence_of_isPreLocalizingSequence h𝓕 hτ).isStoppingTime n
  rw [stoppedProcess_indicator_comm', ← stoppedProcess_stoppedProcess_of_le_right
    (τ := fun ω ↦ τ n ω) (fun _ ↦ (iInf_le _ n).trans <| iInf_le _ le_rfl),
    ← stoppedProcess_indicator_comm']
  convert this using 2
  ext i ω
  rw [stoppedProcess_indicator_comm', Set.indicator_indicator]
  congr 1
  ext ω'
  simp only [ge_iff_le, Set.mem_setOf_eq, Set.mem_inter_iff]
  exact ⟨fun h ↦ ⟨h, lt_of_lt_of_le h <| (iInf_le _ n).trans (iInf_le _ le_rfl)⟩, fun h ↦ h.1⟩

section

omit [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
variable [SecondCountableTopology ι] [IsFiniteMeasure P]

lemma isPreLocalizingSequence_of_isLocalizingSequence_aux'
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ T : ℕ → ι, Tendsto T atTop atTop
      ∧ ∀ n, ∃ k, P {ω | σ n k ω < min (τ n ω) (T n)} ≤ (1 / 2) ^ n := by
  obtain ⟨T, -, hT⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop ι
  refine ⟨T, hT, fun n ↦ ?_⟩
  by_contra hn; push_neg at hn
  suffices (1 / 2) ^ n ≤ P (⋂ k : ℕ, {ω | σ n k ω < min (τ n ω) (T n)}) by
    refine (by simp : ¬ (1 / 2 : ℝ≥0∞) ^ n ≤ 0) <| this.trans <| nonpos_iff_eq_zero.2 ?_
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [(hσ n).tendsto_top] with ω hTop hmem
    rw [WithTop.tendsto_atTop_nhds_top_iff] at hTop
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hmem
    obtain ⟨N, hN⟩ := hTop (T n)
    specialize hN N le_rfl
    specialize hmem N
    grind
  rw [measure_iInter_of_ae_antitone, le_iInf_iff]
  · exact fun k ↦ (hn k).le
  · filter_upwards [(hσ n).mono] with ω hω
    intros i j hij
    specialize hω hij
    simp only [lt_inf_iff, le_Prop_eq] at *
    change σ n j ω < τ n ω ∧ σ n j ω < T n → σ n i ω < τ n ω ∧ σ n i ω < T n
    grind
  · intro i
    refine MeasurableSet.nullMeasurableSet ?_
    have hMσ := ((hσ n).isStoppingTime i).measurable
    have hMτ := (hτ.isStoppingTime n).measurable
    simp_rw [lt_inf_iff]
    rw [(_ : {ω | σ n i ω < τ n ω ∧ σ n i ω < T n} = {ω | σ n i ω < τ n ω} ∩ {ω | σ n i ω < T n})]
    · exact MeasurableSet.inter
        (measurableSet_lt ((hσ n).isStoppingTime i).measurable' (hτ.isStoppingTime n).measurable')
        <| measurableSet_lt ((hσ n).isStoppingTime i).measurable' measurable_const
    · rfl
  · exact ⟨0, measure_ne_top P _⟩

/-- Auxliary defintion for `isPreLocalizingSequence_of_isLocalizingSequence` which constructs a
strictly increasing sequence from a given sequence. -/
def mkStrictMonoAux (x : ℕ → ℕ) : ℕ → ℕ
| 0 => x 0
| n + 1 => max (x (n + 1)) (mkStrictMonoAux x n) + 1

lemma mkStrictMonoAux_strictMono (x : ℕ → ℕ) : StrictMono (mkStrictMonoAux x) := by
  refine strictMono_nat_of_lt_succ <| fun n ↦ ?_
  simp only [mkStrictMonoAux]
  exact lt_of_le_of_lt (le_max_right (x (n + 1)) _) (lt_add_one (max (x (n + 1)) _))

lemma le_mkStrictMonoAux (x : ℕ → ℕ) : ∀ n, x n ≤ mkStrictMonoAux x n
| 0 => by simp [mkStrictMonoAux]
| n + 1 => by
    simp only [mkStrictMonoAux]
    exact (le_max_left (x (n + 1)) (mkStrictMonoAux x n)).trans <|
       Nat.le_add_right (max (x (n + 1)) (mkStrictMonoAux x n)) 1

lemma isPreLocalizingSequence_of_isLocalizingSequence_aux
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, StrictMono nk ∧ ∃ T : ℕ → ι, Tendsto T atTop atTop
      ∧ ∀ n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} ≤ (1 / 2) ^ n := by
  obtain ⟨T, hT, h⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux' hτ hσ
  choose nk hnk using h
  refine ⟨mkStrictMonoAux nk, mkStrictMonoAux_strictMono nk, T, hT, fun n ↦
    le_trans (EventuallyLE.measure_le ?_) (hnk n)⟩
  filter_upwards [(hσ n).mono] with ω hω
  specialize hω (le_mkStrictMonoAux nk n)
  simp only [lt_inf_iff, le_Prop_eq]
  change σ n (mkStrictMonoAux nk n) ω < τ n ω ∧ σ n (mkStrictMonoAux nk n) ω < T n →
    σ n (nk n) ω < τ n ω ∧ σ n (nk n) ω < T n
  grind

lemma isPreLocalizingSequence_of_isLocalizingSequence
    [NoMaxOrder ι] {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, StrictMono nk
      ∧ IsPreLocalizingSequence 𝓕 (fun i ω ↦ (τ i ω) ⊓ (σ i (nk i) ω)) P := by
  obtain ⟨nk, hnk, T, hT, hP⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux hτ hσ
  refine ⟨nk, hnk, fun n ↦ (hτ.isStoppingTime n).min ((hσ _).isStoppingTime _), ?_⟩
  have : ∑' n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} < ∞ :=
    lt_of_le_of_lt (ENNReal.summable.tsum_mono ENNReal.summable hP)
      (tsum_geometric_lt_top.2 <| by norm_num)
  have hτTop := hτ.tendsto_top
  filter_upwards [ae_eventually_notMem this.ne, hτTop] with ω hω hωτ
  replace hT := hωτ.min hT.tendsto_withTop_atTop_nhds_top
  simp_rw [eventually_atTop, not_lt, ← eventually_atTop] at hω
  rw [min_self] at hT
  rw [← min_self ⊤]
  refine hωτ.min <| tendsto_of_tendsto_of_tendsto_of_le_of_le' hT tendsto_const_nhds hω ?_
  simp only [le_top, eventually_atTop, ge_iff_le, implies_true, exists_const]

variable [DenselyOrdered ι] [NoMaxOrder ι] [Zero E]

/-- A stable property holding locally is idempotent. -/
lemma locally_locally
    (h𝓕 : IsRightContinuous 𝓕) (hp : IsStable 𝓕 p) :
    Locally (fun Y ↦ Locally p 𝓕 Y P) 𝓕 X P ↔ Locally p 𝓕 X P := by
  refine ⟨fun hL ↦ ?_, fun hL ↦ ?_⟩
  · have hLL := hL.stoppedProcess
    choose τ hτ₁ hτ₂ using hLL
    obtain ⟨nk, hnk, hpre⟩ := isPreLocalizingSequence_of_isLocalizingSequence
      hL.IsLocalizingSequence hτ₁
    refine locally_of_isPreLocalizingSequence hp h𝓕 hpre <| fun n ↦ ?_
    specialize hτ₂ n (nk n)
    convert hτ₂ using 1
    ext i ω
    rw [stoppedProcess_indicator_comm', stoppedProcess_indicator_comm',
      stoppedProcess_stoppedProcess, stoppedProcess_indicator_comm']
    simp only [lt_inf_iff, Set.indicator_indicator]
    congr 1
    · ext ω'; simp only [And.comm, Set.mem_setOf_eq, Set.mem_inter_iff]
    · simp_rw [inf_comm]
      rfl
  · exact ⟨hL.localSeq, hL.IsLocalizingSequence, fun n ↦ locally_of_prop <| hL.stoppedProcess n⟩

/-- If `p` implies `q` locally, then `p` locally implies `q` locally. -/
lemma locally_induction (h𝓕 : IsRightContinuous 𝓕)
    (hpq : ∀ Y, p Y → Locally q 𝓕 Y P) (hq : IsStable 𝓕 q) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  (locally_locally h𝓕 hq).1 <| hpX.mono hpq

end

end ConditionallyCompleteLinearOrderBot

end ProbabilityTheory
