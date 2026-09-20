/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import BrownianMotion.Auxiliary.IsStoppingTime
public import BrownianMotion.Auxiliary.StoppedProcess
public import BrownianMotion.StochasticIntegral.Predictable
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Process.LocalProperty

/-! # Localizing sequences of stopping times

-/

@[expose] public section

open MeasureTheory Filter Filtration
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

end LinearOrder

section ConditionallyCompleteLinearOrderBot

/-! The lemmas of this section with a name ending in `'` are versions of the Mathlib lemmas of the
same name without the hypothesis `DenselyOrdered ι`. They use `IsStoppingTime.biInf'`. -/

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

lemma IsPreLocalizingSequence.isLocalizingSequence_biInf' [FirstCountableTopology ι]
    {τ : ℕ → Ω → WithTop ι} [IsRightContinuous 𝓕] (hτ : IsPreLocalizingSequence 𝓕 τ P) :
    IsLocalizingSequence 𝓕 (fun i ω ↦ ⨅ j ≥ i, τ j ω) P where
  isStoppingTime n := IsStoppingTime.biInf' (Set.to_countable {j | j ≥ n})
    (fun j _ ↦ hτ.isStoppingTime j)
  mono := ae_of_all _ <| fun ω n m hnm ↦ iInf_le_iInf_of_subset <| fun k hk ↦ hnm.trans hk
  tendsto_top := by
    filter_upwards [hτ.tendsto_top] with ω hω
    replace hω := hω.liminf_eq
    rw [liminf_eq_iSup_iInf_of_nat] at hω
    rw [← hω]
    refine tendsto_atTop_iSup fun n m hnm ↦ ?_
    simp [iInf_le_iff]
    grind

lemma isLocalizingSequence_of_isPreLocalizingSequence [FirstCountableTopology ι]
    {τ : ℕ → Ω → WithTop ι} (h𝓕 : IsRightContinuous 𝓕) (hτ : IsPreLocalizingSequence 𝓕 τ P) :
    IsLocalizingSequence 𝓕 (fun i ω ↦ ⨅ j ≥ i, τ j ω) P :=
  hτ.isLocalizingSequence_biInf'

/-- A process `X` satisfies a stable property `p` locally if there exists a pre-localizing
sequence `τ` for which the stopped processes of `fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)` satisfy
`p`. -/
lemma IsStable.locally_of_isPreLocalizingSequence'
    [Zero E] [FirstCountableTopology ι] {τ : ℕ → Ω → WithTop ι}
    (hp : IsStable 𝓕 p) [IsRightContinuous 𝓕] (hτ : IsPreLocalizingSequence 𝓕 τ P)
    (hpτ : ∀ n, p (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))) :
    Locally p 𝓕 X P := by
  refine ⟨_, hτ.isLocalizingSequence_biInf', fun n ↦ ?_⟩
  rw [stoppedProcess_indicator_comm', ← stoppedProcess_stoppedProcess_of_le_right
    (τ := fun ω ↦ τ n ω) (fun _ ↦ (iInf_le _ n).trans <| iInf_le _ le_rfl),
    ← stoppedProcess_indicator_comm']
  convert!
    hp _ (hpτ n) (fun ω ↦ ⨅ j ≥ n, τ j ω) <| hτ.isLocalizingSequence_biInf'.isStoppingTime n using 2
  ext i ω
  rw [stoppedProcess_indicator_comm', Set.indicator_indicator]
  congr with ω
  exact ⟨fun h ↦ ⟨h, lt_of_lt_of_le h <| (iInf_le _ n).trans (iInf_le _ le_rfl)⟩, fun h ↦ h.1⟩

/-- A stable property which holds locally holds along a localizing sequence which is monotone
everywhere, and not only almost surely. -/
lemma IsStable.exists_monotone_localSeq [Zero E] [FirstCountableTopology ι]
    [IsRightContinuous 𝓕] (hp : IsStable 𝓕 p) (hX : Locally p 𝓕 X P) :
    ∃ τ : ℕ → Ω → WithTop ι, IsLocalizingSequence 𝓕 τ P ∧ (∀ ω, Monotone (τ · ω)) ∧
      ∀ n, p (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n)) := by
  obtain ⟨τ, hτ, hpτ⟩ := hX
  have hτ' := hτ.toIsPreLocalizingSequence.isLocalizingSequence_biInf'
  refine ⟨_, hτ', fun ω n m hnm ↦ iInf_le_iInf_of_subset fun k hk ↦ hnm.trans hk, fun n ↦ ?_⟩
  have h_le : (fun ω ↦ ⨅ j ≥ n, τ j ω) ≤ τ n := fun _ ↦ (iInf_le _ n).trans <| iInf_le _ le_rfl
  rw [← stoppedProcess_indicator_stoppedProcess_indicator_of_le h_le]
  exact hp _ (hpτ n) _ (hτ'.isStoppingTime n)

section

variable [SecondCountableTopology ι] [IsFiniteMeasure P]

lemma isPreLocalizingSequence_of_isLocalizingSequence
    [NoMaxOrder ι] {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, StrictMono nk
      ∧ IsPreLocalizingSequence 𝓕 (fun i ω ↦ (τ i ω) ⊓ (σ i (nk i) ω)) P := by
  exact IsLocalizingSequence.isPrelocalizingSequence_inf_extraction hτ hσ

variable [NoMaxOrder ι] [Zero E]

/-- A stable property holding locally is idempotent. -/
lemma IsStable.locally_locally_iff' [IsRightContinuous 𝓕] (hp : IsStable 𝓕 p) :
    Locally (fun Y ↦ Locally p 𝓕 Y P) 𝓕 X P ↔ Locally p 𝓕 X P := by
  refine ⟨fun hL ↦ ?_, fun hL ↦ ⟨hL.localSeq, hL.isLocalizingSequence_localSeq,
    fun n ↦ .of_prop <| hL.stoppedProcess_localSeq n⟩⟩
  choose τ hτ₁ hτ₂ using hL.stoppedProcess_localSeq
  obtain ⟨nk, hnk, hpre⟩ :=
    hL.isLocalizingSequence_localSeq.isPrelocalizingSequence_inf_extraction hτ₁
  refine hp.locally_of_isPreLocalizingSequence' hpre <| fun n ↦ ?_
  convert! hτ₂ n (nk n) using 1 with
  ext i ω
  rw [stoppedProcess_indicator_comm', stoppedProcess_indicator_comm',
    stoppedProcess_stoppedProcess, stoppedProcess_indicator_comm']
  simp only [lt_inf_iff, Set.indicator_indicator]
  congr 1
  · ext; grind
  · simp_rw [inf_comm]
    rfl

/-- If `q` is a stable property and `p` implies `q` locally, then `p` locally implies
`q` locally. -/
lemma IsStable.locally_induction' [IsRightContinuous 𝓕]
    (hq : IsStable 𝓕 q) (hpq : ∀ Y, p Y → Locally q 𝓕 Y P) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  hq.locally_locally_iff'.1 <| hpX.mono hpq

/-- If `p, q, r` are stable properties and `r` and `p` implies locally `q`, then `r` locally
and `p` locally imply `q` locally. -/
lemma IsStable.locally_induction₂' {r : (ι → Ω → E) → Prop} [IsRightContinuous 𝓕]
    (hrpq : ∀ Y, r Y → p Y → Locally q 𝓕 Y P)
    (hr : IsStable 𝓕 r) (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q)
    (hrX : Locally r 𝓕 X P) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  hq.locally_induction' (p := fun Y ↦ r Y ∧ p Y) (and_imp.2 <| hrpq ·) <|
    (hr.locally_and_iff hp).2 ⟨hrX, hpX⟩

end

end ConditionallyCompleteLinearOrderBot

section cadlag

section LinearOrder

variable [LinearOrder ι] [OrderBot ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p : (ι → Ω → E) → Prop}

open Classical in
/-- Given a property on paths which holds almost surely for a stochastic process, we construct a
localizing sequence by setting the stopping time to be ∞ whenever the property holds. -/
noncomputable
def LocalizingSequenceOfProp (X : ι → Ω → E) (p : (ι → E) → Prop) : ℕ → Ω → WithTop ι :=
  Function.const _ <| fun ω ↦ if p (X · ω) then ⊤ else ⊥

omit [OrderBot ι] in
lemma isStoppingTime_ae_const [IsComplete 𝓕 P] (τ : Ω → WithTop ι) (c : WithTop ι)
    (hτ : τ =ᵐ[P] Function.const _ c) :
    IsStoppingTime 𝓕 τ := by
  intros i
  suffices P {ω | τ ω ≤ i} = 0 ∨ P {ω | τ ω ≤ ↑i}ᶜ = 0 by
    obtain h | h := this
    · exact IsComplete.measurableSet_of_null h i
    · exact (IsComplete.measurableSet_of_null h i).of_compl
  obtain hle | hgt := le_or_gt c i
  · refine Or.inr <| ae_iff.1 ?_
    filter_upwards [hτ] with ω rfl using hle
  · refine Or.inl ?_
    rw [← compl_compl {ω | τ ω ≤ i}]
    refine ae_iff.1 ?_
    filter_upwards [hτ] with ω hω
    simp [hω, hgt]

variable [TopologicalSpace ι] [OrderTopology ι]

lemma isLocalizingSequence_localizingSequenceOfProp [IsComplete 𝓕 P] {p : (ι → E) → Prop}
    (hpX : ∀ᵐ ω ∂P, p (X · ω)) :
    IsLocalizingSequence 𝓕 (LocalizingSequenceOfProp X p) P where
  isStoppingTime n := by
    refine isStoppingTime_ae_const (P := P) _ ⊤ ?_
    filter_upwards [hpX] with ω hω
    rw [LocalizingSequenceOfProp, Function.const_apply, Function.const_apply, if_pos hω]
  mono := ae_of_all _ <| fun ω i j hij ↦ by simp [LocalizingSequenceOfProp]
  tendsto_top := by
    filter_upwards [hpX] with ω hω
    simp [LocalizingSequenceOfProp, if_pos hω]

end LinearOrder

end cadlag

end ProbabilityTheory
