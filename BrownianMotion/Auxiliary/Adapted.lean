import Mathlib.Probability.Process.Adapted
import Mathlib.Data.Setoid.Partition

open Filter TopologicalSpace
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {ι Ω β : Type*} [TopologicalSpace β] {mΩ : MeasurableSpace Ω} {X : ι → Ω → β}

lemma _root_.MeasureTheory.StronglyMeasurable.IndexedPartition {s : ι → Set Ω} [Countable ι]
    (hs : IndexedPartition s) : StronglyMeasurable (hs.piecewise X) := by sorry


variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [PseudoMetrizableSpace β]
  [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι] {μ : Measure Ω} {n : ι}

lemma Adapted.progMeasurable_of_rightContinuous {𝓕 : Filtration ι mΩ}
    (h : Adapted 𝓕 X) (hu_cont : ∀ ω a, ContinuousWithinAt (X · ω) (Set.Ioi a) a) :
    ProgMeasurable 𝓕 X := by
  intro t
  -- set of points in (-∞,t] that are isolated on the right
  let ip := {x : Set.Iic t | 𝓝[>] x = ⊥}
  have tmemip : ⟨t, le_rfl⟩ ∈ ip := by
    simp only [← not_neBot, nhdsWithin_neBot, not_forall,
      Set.not_nonempty_iff_eq_empty, Set.mem_setOf_eq, ip]
    use Set.univ
    simp [Set.univ_inter, Set.Ioi_eq_empty_iff, isMax_iff_eq_top, univ_mem, exists_const]
    rfl
  have ipc : ip.Countable := countable_setOf_isolated_right (α := Set.Iic t)
  -- set of points dense in (-∞,t]
  obtain ⟨d, dc, dd⟩ := TopologicalSpace.exists_countable_dense (Set.Iic t)
  let s := ip ∪ d
  have tmems : ⟨t, le_rfl⟩ ∈ s := Or.inl tmemip
  have nonemptys : Nonempty s := ⟨_, tmems⟩
  obtain ⟨u, hu⟩ := countable_iff_exists_surjective.mp (Set.Countable.union ipc dc)
  obtain ⟨k, hk⟩ := hu ⟨_, tmems⟩
  -- rearrange the set {u 0, ..., u (n + k)} so that it is in the increasing order
  let r (n : ℕ) : List s := ((Finset.range (n + k + 1)).image u).sort
  let f (n : ℕ) : Fin (r n).length → Set (Set.Iic t) := fun i =>
    if h0 : i = ⟨0, by simp [r]⟩ then Set.Iic (r n)[0]
    else Set.Ioc (r n)[i.val - 1] (r n)[i]
  let P (n : ℕ) : IndexedPartition (f n) := by
    refine IndexedPartition.mk' (f n) ?_ (fun i => ?_) (fun a => ?_)
    · sorry
    · sorry
    · sorry
  let U : ℕ → (Set.Iic t) × Ω → β := fun n p => (P n).piecewise (fun a => X (r n)[a] p.2) p.1
  refine stronglyMeasurable_of_tendsto (f := U) (u := atTop) (fun i => ?_) ?_
  · sorry
  · sorry

end MeasureTheory
