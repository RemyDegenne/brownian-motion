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
    Tendsto (fun x => f x ⊓ g x) atTop atTop := by
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
lemma stoppedProcess_indicator_apply_comm {β : Type*} [Zero β] {u : ι → Ω → β}
    {τ : Ω → WithTop ι} {s : Set Ω} (i : ι) :
    stoppedProcess (fun i ↦ s.indicator (u i)) τ i
      = s.indicator (stoppedProcess u τ i) := by
  ext ω
  rw [Set.indicator]
  split_ifs with hω
  · rw [stoppedProcess, Set.indicator_of_mem hω, stoppedProcess]
  · rw [stoppedProcess, Set.indicator_of_notMem hω]

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
theorem _root_.MeasureTheory.stoppedProcess_eq_stoppedValue_apply
    {β : Type*} {u : ι → Ω → β} {τ : Ω → WithTop ι} (i : ι) (ω : Ω) :
    stoppedProcess u τ i ω = stoppedValue u (fun ω ↦ min i (τ ω)) ω := rfl

lemma locally_and [Zero E] (hp : IsStable p 𝓕) (hq : IsStable q 𝓕) :
    Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P ↔ Locally p 𝓕 X P ∧ Locally q 𝓕 X P := by
  refine ⟨Locally.of_and, fun ⟨hpX, hqX⟩ ↦
    ⟨_, hpX.IsLocalizingSequence.min hqX.IsLocalizingSequence, fun n ↦ ⟨?_, ?_⟩⟩⟩
  · convert hp _ (hpX.stoppedProcess n) _ <| hqX.IsLocalizingSequence.isStoppingTime n using 1
    ext i ω
    rw [stoppedProcess_indicator_apply_comm]
    simp_rw [Pi.inf_apply, lt_inf_iff, inf_comm (hpX.localSeq n)]
    rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_apply_comm,
      (_ : {ω | ⊥ < hpX.localSeq n ω ∧ ⊥ < hqX.localSeq n ω}
        = {ω | ⊥ < hpX.localSeq n ω} ∩ {ω | ⊥ < hqX.localSeq n ω}), Set.inter_comm]
    · simp_rw [← Set.indicator_indicator]
      rfl
    · rfl
  · convert hq _ (hqX.stoppedProcess n) _ <| hpX.IsLocalizingSequence.isStoppingTime n using 1
    ext i ω
    rw [stoppedProcess_indicator_apply_comm]
    simp_rw [Pi.inf_apply, lt_inf_iff]
    rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_apply_comm,
      (_ : {ω | ⊥ < hpX.localSeq n ω ∧ ⊥ < hqX.localSeq n ω}
        = {ω | ⊥ < hpX.localSeq n ω} ∩ {ω | ⊥ < hqX.localSeq n ω})]
    · simp_rw [← Set.indicator_indicator]
      rfl
    · rfl

end LinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

-- Move. Weaken the lattice assumption?
lemma IsStoppingTime.iInf {𝓕 : Filtration ι mΩ} {τ : ℕ → Ω → WithTop ι}
    (s : Set ℕ) (h𝓕 : IsRightContinuous 𝓕) (hτ : ∀ n, IsStoppingTime 𝓕 (τ n)) :
    IsStoppingTime 𝓕 (fun ω ↦ ⨅ (n) (_ : n ∈ s), τ n ω) := by
  sorry

-- 1: IsStoppingTime.iInf
-- 2: Given a sequence of stopping times `τₙ` which converge to infinity,
--  `σₙ := inf_{k ≤ n} τₖ` defines a localizing sequence.
#check sInf
#check IsStoppingTime.min

lemma IsLocalizingSequence.exists_subseq_isStoppingTime_tendsto_atTop
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, StrictMono nk
      ∧ ∀ᵐ ω ∂P, Tendsto (fun i ω ↦ (τ i ω) ⊓ (σ i (nk i) ω)) atTop atTop := by
  sorry

lemma IsLocalizingSequence.exists_subseq_isLocalizingSequence_tendsto_atTop
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι} (h𝓕 : IsRightContinuous 𝓕)
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, IsLocalizingSequence 𝓕 (fun i ω ↦ ⨅ j ≥ i, (τ j ω) ⊓ (σ j (nk j) ω)) P := by
  obtain ⟨nk, hnk₁, hnk₂⟩ := hτ.exists_subseq_isStoppingTime_tendsto_atTop hσ
  refine ⟨nk, fun n ↦ IsStoppingTime.iInf {j | j ≥ n} h𝓕 <|
      fun j ↦ (hτ.isStoppingTime j).min <| (hσ j).isStoppingTime (nk j),
      ae_of_all _ <| fun ω n m hnm ↦ iInf_le_iInf_of_subset <| fun k hk ↦ hnm.trans hk, ?_⟩
  · sorry

lemma locally_locally [Zero E] (hp : IsStable p 𝓕) :
    Locally (fun Y ↦ Locally p 𝓕 Y P) 𝓕 X P ↔ Locally p 𝓕 X P := by
  refine ⟨fun hL ↦ ?_, fun hL ↦ ?_⟩
  · have hLL := hL.stoppedProcess
    choose τ hτ using hLL
    simp_rw [Locally] at *
    sorry
  · exact ⟨hL.localSeq, hL.IsLocalizingSequence, fun n ↦ locally_of_prop <| hL.stoppedProcess n⟩

/-- If `p` implies `q` locally, then `p` locally implies `q` locally. -/
lemma locally_induction [Zero E] (hpq : ∀ Y, p Y → Locally q 𝓕 Y P) (hq : IsStable q 𝓕)
    (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  (locally_locally hq).1 <| hpX.mono hpq

end ConditionallyCompleteLinearOrderBot

end ProbabilityTheory
