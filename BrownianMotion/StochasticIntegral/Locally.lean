/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import BrownianMotion.StochasticIntegral.Cadlag
public import BrownianMotion.StochasticIntegral.LocalizingSequence

/-! # Local properties of processes

-/

@[expose] public section

open MeasureTheory Filter Filtration
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section LinearOrder

variable [Zero E] [TopologicalSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTopology ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

lemma locally_and_of_isStable (hp : IsStable 𝓕 p) (hpX : p X) (hqX : Locally q 𝓕 X P) :
    Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P := by
  refine ⟨hqX.localSeq, hqX.isLocalizingSequence_localSeq,
    fun n ↦ ⟨?_, hqX.stoppedProcess_localSeq n⟩⟩
  convert hp _ hpX _ <| hqX.isLocalizingSequence_localSeq.isStoppingTime n using 1

end LinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

end ConditionallyCompleteLinearOrderBot

section cadlag

section LinearOrder

variable [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [Zero E] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p : (ι → Ω → E) → Prop}

open Classical in
/-- If the filtration satisfies the usual conditions, then a property of the paths of a process
that holds almost surely holds locally. -/
lemma locally_of_ae [𝓕.IsComplete P] {p : (ι → E) → Prop} (hpX : ∀ᵐ ω ∂P, p (X · ω))
    (hp₀ : p (0 : ι → E)) :
    Locally (fun X ↦ ∀ ω, p (X · ω)) 𝓕 X P := by
  refine ⟨_, isLocalizingSequence_localizingSequenceOfProp hpX, fun _ ω ↦ ?_⟩
  by_cases hω : p (X · ω)
  · convert hω using 2
    rw [stoppedProcess_eq_of_le, Set.indicator_of_mem]
    · simp [LocalizingSequenceOfProp, if_pos hω]
    · simp [LocalizingSequenceOfProp, if_pos hω]
  · convert hp₀ using 2
    rw [stoppedProcess_eq_of_ge, Set.indicator_of_notMem]
    · rfl
    · simp [LocalizingSequenceOfProp, if_neg hω]
    · simp [LocalizingSequenceOfProp, if_neg hω]

section TopologicalSpace

lemma Locally.ae (p : (ι → E) → ι → Prop)
    (hp_congr : ∀ X Y i, (∃ k, i < k ∧ ∀ j < k, X j = Y j) → (p X i ↔ p Y i))
    (hX : Locally (fun X ↦ ∀ ω i, p (X · ω) i) 𝓕 X P) :
    ∀ᵐ ω ∂P, ∀ i, p (X · ω) i := by
  obtain ⟨τ, hτ⟩ := hX
  filter_upwards [hτ.1.tendsto_top] with ω hω i
  simp only [tendsto_atTop_nhds] at hω
  obtain ⟨N, hN⟩ := hω (Set.Ioi i) (by simp) isOpen_Ioi
  have hNi := hN N (le_refl N)
  have hτ_ne_bot : τ N ω ≠ ⊥ := by
    intro h_eq
    simp [h_eq] at hNi
  have h := hτ.2 N ω i
  by_cases hτ_top : τ N ω = ⊤
  · simpa [stoppedProcess, hτ_top] using h
  simp only [stoppedProcess, Set.mem_setOf_eq, Ne.bot_lt hτ_ne_bot, Set.indicator_of_mem] at h
  refine (hp_congr _ _ i ?_).mp h
  simp only [Set.mem_Ioi] at hNi
  have hNi' : i < (τ N ω).untopA := by rwa [WithTop.lt_untopA_iff hτ_top]
  refine ⟨(τ N ω).untopA, hNi', fun j hj ↦ ?_⟩
  rw [min_eq_left]
  · simp
  · rw [WithTop.lt_untopA_iff hτ_top] at hj
    exact hj.le

omit [TopologicalSpace ι] [OrderTopology ι] in
lemma isStable_pathwise (p : (ι → E) → ι → Prop)
    (hp_zero : ∀ i, p 0 i) (hp_stop : ∀ X a, (∀ i, p X i) → ∀ i, a ≤ i → p (fun x ↦ X (min x a)) i)
    (hp_congr : ∀ X Y i, (∃ k, i < k ∧ ∀ j < k, X j = Y j) → (p X i ↔ p Y i)) :
    IsStable 𝓕 (fun X ↦ ∀ ω i, p (X · ω) i) := by
  intro X hX τ hτ ω i
  by_cases hτ_bot : τ ω = ⊥
  · simp only [stoppedProcess, hτ_bot, bot_le, inf_of_le_right, Set.mem_setOf_eq,
      lt_self_iff_false, not_false_eq_true, Set.indicator_of_notMem]
    exact hp_zero i
  simp only [stoppedProcess, Set.mem_setOf_eq, Ne.bot_lt hτ_bot, Set.indicator_of_mem]
  specialize hX ω
  by_cases hτ_top : τ ω = ⊤
  · simpa [hτ_top] using hX i
  rcases lt_or_ge i (τ ω).untopA with hlt | hge
  · refine (hp_congr _ _ i ?_).mp (hX i)
    refine ⟨(τ ω).untopA, hlt, fun j hj ↦ ?_⟩
    rw [min_eq_left]
    · simp
    · rw [WithTop.lt_untopA_iff hτ_top] at hj
      exact hj.le
  · convert hp_stop (X · ω) (τ ω).untopA hX i hge with j
    rcases le_total j (τ ω).untopA with h | h
    · rw [min_eq_left h, min_eq_left]
      · simp
      · rwa [WithTop.le_untopA_iff hτ_top] at h
    · rw [min_eq_right h, min_eq_right]
      rwa [WithTop.untopA_le_iff hτ_top] at h

lemma locally_iff_ae [𝓕.IsComplete P] (p : (ι → E) → ι → Prop) (hp_zero : ∀ i, p 0 i)
    (hp_congr : ∀ X Y i, (∃ k, i < k ∧ ∀ j < k, X j = Y j) → (p X i ↔ p Y i)) :
    Locally (fun X ↦ ∀ ω i, p (X · ω) i) 𝓕 X P ↔ ∀ᵐ ω ∂P, ∀ i, p (X · ω) i :=
  ⟨fun h ↦ h.ae p hp_congr, fun h ↦ locally_of_ae (p := fun X ↦ ∀ i, p X i) h hp_zero⟩

variable [TopologicalSpace E]

lemma Locally.rightContinuous
    (hX : Locally (fun X ↦ ∀ ω, Function.IsRightContinuous (X · ω)) 𝓕 X P) :
    ∀ᵐ ω ∂P, Function.IsRightContinuous (X · ω) := by
  refine Locally.ae (fun X i ↦ ContinuousWithinAt X (Set.Ioi i) i) (fun X Y i hXY ↦ ?_) hX
  refine EventuallyEq.congr_continuousWithinAt ?_ ?_
  · rw [eventuallyEq_nhdsWithin_iff]
    obtain ⟨k, hik, hk⟩ := hXY
    filter_upwards [eventually_lt_nhds hik] with j hjk _
    exact hk j hjk
  · obtain ⟨k, hik, hk⟩ := hXY
    exact hk i hik

lemma Locally.left_limit
    (hX : Locally (fun X ↦ ∀ ω, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[<] x) (𝓝 l)) 𝓕 X P) :
    ∀ᵐ ω ∂P, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[<] x) (𝓝 l) := by
  refine Locally.ae (fun X i ↦ ∃ l, Tendsto X (𝓝[<] i) (𝓝 l)) (fun X Y i hXY ↦ ?_) hX
  have h_eq : X =ᶠ[𝓝[<] i] Y := by
    rw [eventuallyEq_nhdsWithin_iff]
    obtain ⟨k, hik, hk⟩ := hXY
    filter_upwards [eventually_lt_nhds hik] with j hjk _
    exact hk j hjk
  constructor <;> rintro ⟨l, hl⟩ <;> refine ⟨l, hl.congr' ?_⟩
  · exact h_eq
  · exact h_eq.symm

lemma Locally.isCadlag
    (hX : Locally (fun X ↦ ∀ ω, IsCadlag (X · ω)) 𝓕 X P) :
    ∀ᵐ ω ∂P, IsCadlag (X · ω) := by
  filter_upwards [(hX.mono <| fun X h ω ↦ (h ω).right_continuous).rightContinuous,
    (hX.mono <| fun X h ω ↦ (h ω).left_limit).left_limit] with _ hω₁ hω₂ using ⟨hω₁, hω₂⟩

lemma Locally.continuous (hX : Locally (fun X ↦ ∀ ω, Continuous (X · ω)) 𝓕 X P) :
    ∀ᵐ ω ∂P, Continuous (X · ω) := by
  simp_rw [continuous_iff_continuousAt] at hX ⊢
  refine Locally.ae (fun X i ↦ ContinuousAt X i) (fun X Y i hXY ↦ ?_) hX
  rw [continuousAt_congr]
  obtain ⟨k, hik, hk⟩ := hXY
  filter_upwards [eventually_lt_nhds hik] with j hjk
  exact hk j hjk

/-- The processes with right-continuous paths are a stable class. -/
lemma isStable_rightContinuous :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ ∀ ω, Function.IsRightContinuous (X · ω)) := by
  refine isStable_pathwise (fun X i ↦ ContinuousWithinAt X (Set.Ioi i) i) (fun _ ↦ by fun_prop)
    ?_ ?_
  · intro X a hX i hai
    specialize hX i
    have h_eq : (fun x ↦ X (min x a)) =ᶠ[𝓝[>] i] fun _ ↦ X a := by
      rw [eventuallyEq_nhdsWithin_iff]
      filter_upwards [] with j hji
      rw [min_eq_right]
      grind
    refine (EventuallyEq.congr_continuousWithinAt h_eq ?_).mpr ?_
    · simp [hai]
    · fun_prop
  · intro X Y i hXY
    refine EventuallyEq.congr_continuousWithinAt ?_ ?_
    · rw [eventuallyEq_nhdsWithin_iff]
      obtain ⟨k, hik, hk⟩ := hXY
      filter_upwards [eventually_lt_nhds hik] with j hjk _
      exact hk j hjk
    · obtain ⟨k, hik, hk⟩ := hXY
      exact hk i hik

/-- The processes with left limits are a stable class. -/
lemma isStable_left_limit :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ ∀ ω, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[<] x) (𝓝 l)) := by
  refine isStable_pathwise (fun X i ↦ ∃ l, Tendsto X (𝓝[<] i) (𝓝 l)) (fun i ↦ ?_) ?_ ?_
  · exact ⟨0, tendsto_const_nhds⟩
  · intro X a hX i hai
    cases lt_or_eq_of_le hai with
    | inl hai =>
      refine ⟨X a, ?_⟩
      have h_eq : (fun x ↦ X (min x a)) =ᶠ[𝓝[<] i] fun _ ↦ X a := by
        rw [eventuallyEq_nhdsWithin_iff]
        filter_upwards [eventually_gt_nhds hai] with j haj
        rw [min_eq_right haj.le]
        grind
      rw [tendsto_congr' h_eq]
      exact tendsto_const_nhds
    | inr hai =>
      simp only [hai]
      obtain ⟨l, hl⟩ := hX i
      refine ⟨l, hl.congr' ?_⟩
      rw [eventuallyEq_nhdsWithin_iff]
      filter_upwards [] with j hji
      rw [min_eq_left]
      grind
  · intro X Y i hXY
    have h_eq : X =ᶠ[𝓝[<] i] Y := by
      rw [eventuallyEq_nhdsWithin_iff]
      obtain ⟨k, hik, hk⟩ := hXY
      filter_upwards [eventually_lt_nhds hik] with j hjk _
      exact hk j hjk
    constructor <;> rintro ⟨l, hl⟩ <;> refine ⟨l, hl.congr' ?_⟩
    · exact h_eq
    · exact h_eq.symm

/-- The càdlàg processes are a stable class. -/
lemma isStable_isCadlag :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ ∀ ω, IsCadlag (X · ω)) :=
  fun X hX τ hτ ω ↦
    ⟨isStable_rightContinuous X (fun ω' ↦ (hX ω').right_continuous) τ hτ ω,
      isStable_left_limit X (fun ω' ↦ (hX ω').left_limit) τ hτ ω⟩

lemma isStable_continuous :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ ∀ ω, Continuous (X · ω)) := by
  simp_rw [continuous_iff_continuousAt]
  refine isStable_pathwise (fun X i ↦ ContinuousAt X i) (fun _ ↦ by fun_prop) ?_ ?_
  · intro X a hX i hai
    cases lt_or_eq_of_le hai with
    | inl hai =>
      have h_eq : (fun x ↦ X (min x a)) =ᶠ[𝓝 i] fun _ ↦ X a := by
        filter_upwards [eventually_gt_nhds hai] with j haj
        rw [min_eq_right haj.le]
      rw [continuousAt_congr h_eq]
      fun_prop
    | inr hai =>
      simp only [hai]
      specialize hX i
      rw [continuousAt_iff_continuous_left'_right'] at hX ⊢
      replace hX := hX.1
      constructor
      · refine (continuousWithinAt_congr ?_ (by simp)).mpr hX
        grind
      · have h_eq : (fun x ↦ X (min x i)) =ᶠ[𝓝[>] i] fun _ ↦ X i := by
          rw [eventuallyEq_nhdsWithin_iff]
          filter_upwards [] with j hij
          grind
        exact ContinuousWithinAt.congr_of_eventuallyEq (by fun_prop) h_eq (by simp)
  · intro X Y i hXY
    rw [continuousAt_congr]
    obtain ⟨k, hik, hk⟩ := hXY
    filter_upwards [eventually_lt_nhds hik] with j hjk
    exact hk j hjk

variable [𝓕.IsComplete P]

lemma locally_rightContinuous_iff :
    Locally (fun X ↦ ∀ ω, Function.IsRightContinuous (X · ω)) 𝓕 X P ↔
      ∀ᵐ ω ∂P, Function.IsRightContinuous (X · ω) :=
  ⟨fun h ↦ h.rightContinuous, fun h ↦ locally_of_ae h <| fun _ ↦ continuousWithinAt_const⟩

lemma locally_left_limit_iff :
    Locally (fun X ↦ ∀ ω, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[<] x) (𝓝 l)) 𝓕 X P ↔
      ∀ᵐ ω ∂P, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[<] x) (𝓝 l) :=
  ⟨fun h ↦ h.left_limit, fun h ↦ locally_of_ae
    (p := fun f ↦ ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)) h <| fun _ ↦ ⟨0, tendsto_const_nhds⟩⟩

lemma locally_isCadlag_iff :
    Locally (fun X ↦ ∀ ω, IsCadlag (X · ω)) 𝓕 X P ↔ ∀ᵐ ω ∂P, IsCadlag (X · ω) :=
  ⟨fun h ↦ h.isCadlag, fun h ↦ locally_of_ae h
    ⟨fun _ ↦ continuousWithinAt_const, fun _ ↦ ⟨0, tendsto_const_nhds⟩⟩⟩

end TopologicalSpace

end LinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [SecondCountableTopology ι] [DenselyOrdered ι] [NoMaxOrder ι] [NormedAddCommGroup E]
  [IsFiniteMeasure P]
  {𝓕 : Filtration ι mΩ} [𝓕.IsComplete P] [𝓕.IsRightContinuous]
  {X : ι → Ω → E} {p : (ι → Ω → E) → Prop}

lemma locally_isCadlag_iff_locally_ae :
    Locally (fun X ↦ ∀ ω, IsCadlag (X · ω)) 𝓕 X P
    ↔ Locally (fun X ↦ ∀ᵐ ω ∂P, IsCadlag (X · ω)) 𝓕 X P := by
  simp_rw [← locally_isCadlag_iff (𝓕 := 𝓕) (P := P), isStable_isCadlag.locally_locally_iff]

end ConditionallyCompleteLinearOrderBot

end cadlag

section ProgMeasurable

open Function

variable [LinearOrder ι] [NormedAddCommGroup E] {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

lemma rightContinuous_indicator [TopologicalSpace ι]
    (hC : ∀ ω, IsRightContinuous (X · ω)) (s : Set Ω) (ω : Ω) :
    IsRightContinuous fun t ↦ s.indicator (X t) ω := by
  by_cases hω : ω ∈ s
  · simpa [Set.indicator_of_mem hω] using hC ω
  · simp [Set.indicator_of_notMem hω, Function.IsRightContinuous, isRightContinuous_const]

lemma stronglyAdapted_indicator [OrderBot ι]
    (hX : StronglyAdapted 𝓕 X) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    StronglyAdapted 𝓕 fun i ↦ {ω | ⊥ < τ ω}.indicator (X i) :=
  fun i ↦ (hX i).indicator <| 𝓕.mono bot_le _ <| hτ.measurableSet_gt _

lemma isStronglyProgressive_indicator [OrderBot ι] [MeasurableSpace ι]
    (hX : IsStronglyProgressive 𝓕 X) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    IsStronglyProgressive 𝓕 fun i ↦ {ω | ⊥ < τ ω}.indicator (X i) := by
  refine fun i ↦ StronglyMeasurable.indicator (hX i) ?_
  exact MeasurableSet.preimage (𝓕.mono bot_le _ <| hτ.measurableSet_gt _) measurable_snd

variable [TopologicalSpace ι] [SecondCountableTopology ι] [TopologicalSpace.PseudoMetrizableSpace ι]
  [OrderBot ι] [OrderTopology ι]
  [MeasurableSpace ι] [BorelSpace ι]

/-- The class of strongly progressive processes is stable. -/
lemma isStable_isStronglyProgressive : IsStable 𝓕 (IsStronglyProgressive 𝓕 (β := E) ·) :=
  fun _ hX _ hτ ↦ (isStronglyProgressive_indicator hX hτ).stoppedProcess hτ

end ProgMeasurable

end ProbabilityTheory
