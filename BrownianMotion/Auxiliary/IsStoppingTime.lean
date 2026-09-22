module

public import Mathlib.Probability.Process.Stopping

@[expose] public section

namespace MeasureTheory

lemma stoppedProcess_min_eq_stoppedProcess {ι Ω E : Type*} [Nonempty ι] [LinearOrder ι]
    (X : ι → Ω → E) (τ : Ω → WithTop ι) {i j : ι} (hij : i ≤ j) :
    stoppedProcess X (fun ω ↦ min j (τ ω)) i = stoppedProcess X τ i := by
  simp [stoppedProcess_eq_stoppedValue, ← min_assoc, min_eq_left (WithTop.coe_le_coe.2 hij)]

open Filter Topology in
/-- If `i` is isolated on its right, an infimum of elements of `WithTop ι` is at most `i` iff one
of them is. -/
lemma _root_.WithTop.biInf_le_coe_iff_of_nhdsGT_eq_bot {ι κ : Type*}
    [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι] {s : Set κ}
    {x : κ → WithTop ι} {i : ι} (hi : 𝓝[>] i = ⊥) :
    ⨅ n ∈ s, x n ≤ i ↔ ∃ n ∈ s, x n ≤ i := by
  refine ⟨fun h ↦ ?_, fun ⟨n, hn, hni⟩ ↦ (biInf_le _ hn).trans hni⟩
  by_contra! h_lt
  rcases nhdsGT_eq_bot_iff.1 hi with h_top | ⟨j, hij⟩
  · -- `i` is the top element of `ι`: all the `x n` are `⊤`
    have h_eq : ∀ n ∈ s, x n = ⊤ := by
      intro n hn
      by_contra h_ne
      obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.1 h_ne
      have := h_lt n hn
      rw [← hy] at this
      exact absurd (h_top y) (not_le.2 (mod_cast this))
    have : ⨅ n ∈ s, x n = ⊤ := by simp +contextual [h_eq]
    simp [this] at h
  · -- `i` has a successor `j`: all the `x n` are at least `j`
    have h_ge : (j : WithTop ι) ≤ ⨅ n ∈ s, x n := by
      refine le_iInf₂ fun n hn ↦ ?_
      have := h_lt n hn
      cases h : x n with
      | top => simp
      | coe y =>
        rw [h] at this
        exact mod_cast hij.ge_of_gt (mod_cast this)
    exact absurd (h_ge.trans h) (not_le.2 (mod_cast hij.lt))

open Filter Topology in
/-- The infimum of countably many stopping times with respect to a right-continuous filtration
is a stopping time. This is `IsStoppingTime.biInf` without the hypotheses `DenselyOrdered` and
`NoMaxOrder`: at a time which is isolated on its right, the infimum is attained. -/
lemma IsStoppingTime.biInf' {ι Ω κ : Type*} {m : MeasurableSpace Ω}
    [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] {f : Filtration ι m} {τ : κ → Ω → WithTop ι} {s : Set κ}
    (hs : s.Countable) [f.IsRightContinuous] (hτ : ∀ n ∈ s, IsStoppingTime f (τ n)) :
    IsStoppingTime f (fun ω ↦ ⨅ n ∈ s, τ n ω) := by
  have h_lt (i : ι) : MeasurableSet[f i] {ω | ⨅ n ∈ s, τ n ω < i} := by
    refine MeasurableSet.of_compl ?_
    rw [(_ : {ω | ⨅ n ∈ s, τ n ω < i}ᶜ = ⋂ n ∈ s, {ω | i ≤ τ n ω})]
    · exact MeasurableSet.biInter hs <| fun n hn ↦ (hτ n hn).measurableSet_ge i
    · ext ω
      simp
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous' h_lt fun i hi ↦ ?_
  have h_eq : {ω | ⨅ n ∈ s, τ n ω = i}
      = {ω | ⨅ n ∈ s, τ n ω < i}ᶜ ∩ ⋃ n ∈ s, {ω | τ n ω ≤ i} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt, Set.mem_iUnion,
      exists_prop, ← WithTop.biInf_le_coe_iff_of_nhdsGT_eq_bot hi]
    exact ⟨fun h ↦ ⟨h.ge, h.le⟩, fun h ↦ le_antisymm h.2 h.1⟩
  rw [h_eq]
  exact (h_lt i).compl.inter (MeasurableSet.biUnion hs fun n hn ↦ hτ n hn i)

end MeasureTheory
