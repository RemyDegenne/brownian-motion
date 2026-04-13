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
lemma locally_of_ae [HasUsualConditions 𝓕 P] {p : (ι → E) → Prop} (hpX : ∀ᵐ ω ∂P, p (X · ω))
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

variable [TopologicalSpace E]

lemma Locally.rightContinuous
    (hX : Locally (fun X ↦ ∀ ω, Function.RightContinuous (X · ω)) 𝓕 X P) :
    ∀ᵐ ω ∂P, Function.RightContinuous (X · ω) := by
  obtain ⟨τ, hτ⟩ := hX
  filter_upwards [hτ.1.tendsto_top] with ω hω i
  simp only [tendsto_atTop_nhds] at hω
  obtain ⟨N, hN⟩ := hω (Set.Ioi i) (by simp) isOpen_Ioi
  have hNi := hN N (le_refl N)
  by_cases hNω : τ N ω < ⊤
  · have hs : Set.Iio (τ N ω).untopA ∈ 𝓝[Set.Ioi i] i := by
      simp only [mem_nhdsWithin]
      refine ⟨Set.Iio (τ N ω).untopA, isOpen_Iio, ?_, by grind⟩
      exact (WithTop.lt_untopA_iff (ne_of_lt hNω)).mpr hNi
    have (y : ι) (hy : y < τ N ω) : (MeasureTheory.stoppedProcess (fun i => ({ω |
      ⊥ < τ N ω}.indicator (X i))) (τ N)) y ω = X y ω := by
      simp [MeasureTheory.stoppedProcess, min_eq_left (hy.le)]; aesop
    refine (continuousWithinAt_inter' hs).mp (((hτ.2 N ω i).mono (by grind)).congr ?_ ?_)
    · exact fun y hy => (this y ((WithTop.lt_untopA_iff (ne_of_lt hNω)).mp hy.2)).symm
    · exact (this i hNi).symm
  · have := hτ.2 N ω i
    simp_all [MeasureTheory.stoppedProcess]

lemma Locally.left_limit
    (hX : Locally (fun X ↦ ∀ ω, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[<] x) (𝓝 l)) 𝓕 X P) :
    ∀ᵐ ω ∂P, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[<] x) (𝓝 l) := by
  obtain ⟨τ, hτ⟩ := hX
  filter_upwards [hτ.1.tendsto_top] with ω hω i
  simp only [tendsto_atTop_nhds] at hω
  obtain ⟨N, hN⟩ := hω (Set.Ioi i) (by simp) isOpen_Ioi
  have hNi := hN N (le_refl N)
  obtain ⟨l, hl⟩ := hτ.2 N ω i
  have (y : ι) (hy : y ∈ Set.Iio i) : (MeasureTheory.stoppedProcess (fun i => ({ω |
    ⊥ < τ N ω}.indicator (X i))) (τ N)) y ω = X y ω := by
    have : y < τ N ω := lt_trans (by simpa using hy) hNi
    simp [MeasureTheory.stoppedProcess, min_eq_left this.le]
    aesop
  exact ⟨l, tendsto_nhdsWithin_congr this hl⟩

lemma Locally.isCadlag
    (hX : Locally (fun X ↦ ∀ ω, IsCadlag (X · ω)) 𝓕 X P) :
    ∀ᵐ ω ∂P, IsCadlag (X · ω) := by
  filter_upwards [(hX.mono <| fun X h ω ↦ (h ω).right_continuous).rightContinuous,
    (hX.mono <| fun X h ω ↦ (h ω).left_limit).left_limit] with _ hω₁ hω₂ using ⟨hω₁, hω₂⟩

/-- The processes with right-continuous paths are a stable class. -/
lemma isStable_rightContinuous :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ ∀ ω, Function.RightContinuous (X · ω)) := by
  intro X hX τ hτ ω a
  dsimp [stoppedProcess]
  by_cases h_stop : (a : WithTop ι) < τ ω
  · let S := {x : ι | ↑x < τ ω}
    have hS_open : IsOpen S := isOpen_Iio.preimage WithTop.continuous_coe
    have ne_bot : ⊥ < τ ω := by
      rw [bot_lt_iff_ne_bot]
      exact ne_bot_of_gt h_stop
    have hS_mem : S ∈ 𝓝[>] a := mem_nhdsWithin_of_mem_nhds (hS_open.mem_nhds h_stop)
    apply ContinuousWithinAt.congr_of_eventuallyEq (hX ω a)
    · filter_upwards [hS_mem] with x hx
      have h_xle : x < τ ω := by exact hx
      simp_all only [Set.mem_setOf_eq, Set.indicator_of_mem, S]
      rw [min_eq_left ]
      · simp only [WithTop.untopD_coe]
      exact Std.le_of_lt h_xle
    · rw [min_eq_left h_stop.le]
      simp only [WithTop.untopD_coe, Set.indicator_apply_eq_self, Set.mem_setOf_eq, not_lt,
        le_bot_iff]
      intro h_bot
      simp_all only [not_lt_bot]
  · apply continuousWithinAt_const.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Ioi] at hx
      have h_bound : τ ω ≤ ↑x := le_trans (not_lt.mp h_stop) (le_of_lt (WithTop.coe_lt_coe.mpr hx))
      simp_all only [not_lt, inf_of_le_right]
      rfl
    simp only [min_eq_right (not_lt.mp h_stop)]

/-- The processes with left limits are a stable class. -/
lemma isStable_left_limit :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ ∀ ω, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[<] x) (𝓝 l)) := by
  intro X hX τ hτ ω x
  dsimp [stoppedProcess]
  by_cases h_stop : (x : WithTop ι) < τ ω
  · obtain ⟨l, hl⟩ := hX ω x
    use l
    let S := {y : ι | ↑y < τ ω}
    have hS_open : IsOpen S := isOpen_Iio.preimage WithTop.continuous_coe
    have ne_bot : ⊥ < τ ω := by
      rw [bot_lt_iff_ne_bot]
      exact ne_bot_of_gt h_stop
    have hS_mem : S ∈ 𝓝[<] x := mem_nhdsWithin_of_mem_nhds (hS_open.mem_nhds h_stop)
    apply Filter.Tendsto.congr' _ hl
    filter_upwards [hS_mem] with y hy
    have h_ylt : y < τ ω := hy
    simp_all only [Set.mem_setOf_eq, Set.indicator_of_mem, S]
    rw [min_eq_left]
    · simp only [WithTop.untopD_coe]
    exact Std.le_of_lt h_ylt
  · by_cases h_eq : (x : WithTop ι) = τ ω
    · obtain ⟨l, hl⟩ := hX ω x
      use l
      apply Filter.Tendsto.congr' _ hl
      have h_mem : {y : ι | ↑y < τ ω} ∈ 𝓝[<] x := by
        have : {y : ι | ↑y < τ ω} = {y : ι | y < x} := by
          ext y
          simp only [Set.mem_setOf_eq]
          rw [← h_eq, WithTop.coe_lt_coe]
        rw [this]
        exact self_mem_nhdsWithin
      filter_upwards [h_mem] with y hy
      have ne_bot : ⊥ < τ ω := by
        exact bot_lt_of_lt hy
      rw [min_eq_left (Std.le_of_lt hy)]
      simp only [WithTop.untopD_coe]
      simp_all only [lt_self_iff_false, not_false_eq_true, Set.mem_setOf_eq, Set.indicator_of_mem]
    · have h_gt : τ ω < (x : WithTop ι) := lt_of_le_of_ne (not_lt.mp h_stop) (Ne.symm h_eq)
      by_cases ne_bot : ⊥ < τ ω
      · use Set.indicator {ω' | ⊥ < τ ω'} (fun ω' ↦ X ((τ ω').untopD ⊥) ω') ω
        apply tendsto_const_nhds.congr'
        obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
            (WithTop.lt_top_iff_ne_top.mp <| lt_of_lt_of_le h_gt le_top)
        have h_t_lt_x : t < x := by
          rw [← ht] at h_gt
          exact WithTop.coe_lt_coe.mp h_gt
        have h_Ioi_mem : Set.Ioi t ∈ 𝓝[<] x :=
          mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds h_t_lt_x)
        filter_upwards [h_Ioi_mem] with y hy
        simp only [Set.mem_Ioi] at hy
        simp_all only [not_lt, Set.mem_setOf_eq, Set.indicator_of_mem]
        rw [← ht, min_eq_right <| WithTop.coe_mono hy.le]
        simp only [WithTop.untopD_coe]
      · use 0
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with y _
        simp [ne_bot]

/-- The càdlàg processes are a stable class. -/
lemma isStable_isCadlag :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ ∀ ω, IsCadlag (X · ω)) :=
  fun X hX τ hτ ω ↦
    ⟨isStable_rightContinuous X (fun ω' ↦ (hX ω').right_continuous) τ hτ ω,
      isStable_left_limit X (fun ω' ↦ (hX ω').left_limit) τ hτ ω⟩

variable [HasUsualConditions 𝓕 P]

lemma locally_rightContinuous_iff :
    Locally (fun X ↦ ∀ ω, Function.RightContinuous (X · ω)) 𝓕 X P
    ↔ ∀ᵐ ω ∂P, Function.RightContinuous (X · ω) :=
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
  {𝓕 : Filtration ι mΩ} [HasUsualConditions 𝓕 P] {X : ι → Ω → E} {p : (ι → Ω → E) → Prop}

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
    (hC : ∀ ω, RightContinuous (X · ω)) (s : Set Ω) (ω : Ω) :
    RightContinuous fun t ↦ s.indicator (X t) ω := by
  by_cases hω : ω ∈ s
  · simpa [Set.indicator_of_mem hω] using hC ω
  · simp [Set.indicator_of_notMem hω, RightContinuous, continuousWithinAt_const]

lemma stronglyAdapted_indicator [OrderBot ι]
    (hX : StronglyAdapted 𝓕 X) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    StronglyAdapted 𝓕 fun i ↦ {ω | ⊥ < τ ω}.indicator (X i) :=
  fun i ↦ (hX i).indicator <| 𝓕.mono bot_le _ <| hτ.measurableSet_gt _

lemma progMeasurable_indicator [OrderBot ι] [MeasurableSpace ι]
    (hX : ProgMeasurable 𝓕 X) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    ProgMeasurable 𝓕 fun i ↦ {ω | ⊥ < τ ω}.indicator (X i) := by
  refine fun i ↦ StronglyMeasurable.indicator (hX i) ?_
  exact MeasurableSet.preimage (𝓕.mono bot_le _ <| hτ.measurableSet_gt _) measurable_snd

variable [TopologicalSpace ι] [SecondCountableTopology ι] [TopologicalSpace.PseudoMetrizableSpace ι]
  [OrderBot ι] [OrderTopology ι]
  [MeasurableSpace ι] [BorelSpace ι]

/-- The class of progressively measurable processes is stable. -/
lemma isStable_progMeasurable : IsStable 𝓕 (ProgMeasurable 𝓕 (β := E) ·) :=
  fun _ hX _ hτ ↦ (progMeasurable_indicator hX hτ).stoppedProcess hτ

end ProgMeasurable

end ProbabilityTheory
