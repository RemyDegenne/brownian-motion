import Mathlib.Probability.Process.Stopping
import BrownianMotion.StochasticIntegral.Predictable
import BrownianMotion.Auxiliary.WithTop

open MeasureTheory Filter Filtration
open scoped ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [DenselyOrdered ι] [FirstCountableTopology ι] {𝓕 : Filtration ι mΩ}

lemma isStoppingTime_of_measurableSet_lt_of_isRightContinuous [NoMaxOrder ι]
    {τ : Ω → WithTop ι} (h𝓕 : IsRightContinuous 𝓕) (hτ : ∀ i, MeasurableSet[𝓕 i] {ω | τ ω < i}) :
    IsStoppingTime 𝓕 τ := by
  intro i
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := exists_seq_strictAnti_tendsto i
  refine MeasurableSet.of_compl ?_
  rw [(_ : {ω | τ ω ≤ i}ᶜ = ⋃ n, {ω | u n ≤ τ ω})]
  · refine h𝓕.measurableSet ?_
    suffices MeasurableSet[⨅ j > i, 𝓕 j] (⋃ n, {ω | ↑(u n) ≤ τ ω}) by
      convert this
      rw [𝓕.rightCont_eq]
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
lemma isStoppingTime_of_measurableSet_lt_of_isRightContinuous'
    {τ : Ω → WithTop ι} (h𝓕 : IsRightContinuous 𝓕)
    (hτ1 : ∀ i, ¬ IsMax i → MeasurableSet[𝓕 i] {ω | τ ω < i})
    (hτ2 : ∀ i, IsMax i → MeasurableSet[𝓕 i] {ω | τ ω ≤ i}) :
    IsStoppingTime 𝓕 τ := by
  intro i
  by_cases hmax : IsMax i
  · rw [← h𝓕.eq, 𝓕.rightCont_eq_of_isMax hmax]
    exact hτ2 i hmax
  rw [← h𝓕.eq, 𝓕.rightCont_eq_of_not_isMax hmax]
  rw [not_isMax_iff] at hmax
  obtain ⟨j, hj⟩ := hmax
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := exists_seq_strictAnti_tendsto' hj
  refine MeasurableSet.of_compl ?_
  rw [(_ : {ω | τ ω ≤ i}ᶜ = ⋃ n, {ω | u n ≤ τ ω})]
  · simp_rw [MeasurableSpace.measurableSet_iInf]
    intros j hj
    obtain ⟨N, hN⟩ := (hu₃.eventually_le_const hj).exists
    rw [(_ : ⋃ n, {ω | u n ≤ τ ω} = ⋃ n > N, {ω | u n ≤ τ ω})]
    · refine MeasurableSet.iUnion <| fun n ↦ MeasurableSet.iUnion <| fun hn ↦
        𝓕.mono ((hu₁ hn).le.trans hN) _ <| MeasurableSet.of_compl ?_
      rw [(by ext; simp : {ω | u n ≤ τ ω}ᶜ = {ω | τ ω < u n})]
      refine hτ1 (u n) <| not_isMax_iff.2 ⟨u N, hu₁ hn⟩
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

lemma stoppedProcess_min_eq_stoppedProcess {ι Ω E : Type*} [Nonempty ι] [LinearOrder ι]
    (X : ι → Ω → E) (τ : Ω → WithTop ι) {i j : ι} (hij : i ≤ j) :
    stoppedProcess X (fun ω ↦ min j (τ ω)) i = stoppedProcess X τ i := by
  simp [stoppedProcess_eq_stoppedValue, ← min_assoc, min_eq_left (WithTop.coe_le_coe.2 hij)]

end MeasureTheory
