import Mathlib.Probability.Process.Adapted
import Mathlib.Data.Setoid.Partition
import BrownianMotion.StochasticIntegral.Cadlag

open Filter Set TopologicalSpace Function MeasureTheory
open scoped NNReal ENNReal Topology

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

variable {ι Ω β : Type*} {s : ι → Set Ω} (hs : IndexedPartition s)

theorem _root_.Set.indexedPartition_piecewise_preimage (f : ι → Ω → β) (t : Set β) :
    (hs.piecewise f) ⁻¹' t = ⋃ i, s i ∩ ((f i)⁻¹' t) := by
  refine ext fun x => ⟨fun hx => ?_, fun ⟨a, ⟨i, hi⟩, ha⟩ => ?_⟩
  · rw [mem_preimage, IndexedPartition.piecewise_apply, ← mem_preimage] at hx
    exact mem_iUnion_of_mem (s := fun i => s i ∩ ((f i)⁻¹' t)) (hs.index x)
      (mem_inter (hs.mem_index x) hx)
  · rw [← hi, ← (IndexedPartition.mem_iff_index_eq hs).mp ha.1] at ha
    simp_all [IndexedPartition.piecewise_apply]

theorem _root_.Set.range_indexedPartition_subset (f : ι → Ω → β) :
    range (hs.piecewise f) ⊆ ⋃ i, range (f i) :=
  fun x ⟨y, hy⟩ => by simpa [IndexedPartition.piecewise_apply] using ⟨hs.index y, y, hy⟩

variable {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β}

theorem Measurable.IndexedPartition [Countable ι] (hms : ∀ i, MeasurableSet (s i))
    {f : ι → Ω → β} (hmf : ∀ i, Measurable (f i)) : Measurable (hs.piecewise f) := by
  refine fun t ht => ?_
  rw [indexedPartition_piecewise_preimage]
  exact MeasurableSet.iUnion (fun i => (hms i).inter (measurableSet_preimage (hmf i) ht))

def SimpleFunc.IndexedPartition [Finite ι] (hms : ∀ i, MeasurableSet (s i)) (f : ι → Ω →ₛ β) :
    Ω →ₛ β :=
  ⟨hs.piecewise (fun i => f i), fun _ =>
    letI : MeasurableSpace β := ⊤
    Measurable.IndexedPartition hs hms (fun i => (f i).measurable) trivial,
    (Set.finite_iUnion (fun i => (f i).finite_range)).subset
    (range_indexedPartition_subset hs (fun i => f i))⟩

variable [TopologicalSpace β] {μ : Measure Ω}

lemma StronglyMeasurable.IndexedPartition [Finite ι] (hm : ∀ i, MeasurableSet (s i))
    {f : ι → Ω → β} (hf : ∀ i, StronglyMeasurable (f i)) :
    StronglyMeasurable (hs.piecewise f) := by
  refine ⟨fun n => SimpleFunc.IndexedPartition hs hm (fun i => (hf i).approx n), fun x => ?_⟩
  simp [SimpleFunc.IndexedPartition, IndexedPartition.piecewise_apply,
    StronglyMeasurable.tendsto_approx]

variable [TopologicalSpace ι] [LinearOrder ι] [OrderTopology ι] [SecondCountableTopology ι]
  [MeasurableSpace ι] [OpensMeasurableSpace ι] [PseudoMetrizableSpace β] {X : ι → Ω → β}
  {τ : Ω → WithTop ι} {n : ι}

lemma Adapted.progMeasurable_of_rightContinuous {𝓕 : Filtration ι mΩ}
    (h : Adapted 𝓕 X) (hu_cont : ∀ ω, RightContinuous (X · ω)) :
    ProgMeasurable 𝓕 X := by
  intro t
  by_cases hΩ : Nonempty Ω
  swap; · simp_all [stronglyMeasurable_const']
  -- set of points in (-∞,t] that are isolated on the right
  let ip := {x : Iic t | 𝓝[>] x = ⊥}
  have tmemip : ⟨t, le_rfl⟩ ∈ ip := by
    simp only [← not_neBot, nhdsWithin_neBot, not_forall,
      not_nonempty_iff_eq_empty, mem_setOf_eq, ip]
    use univ
    simp [univ_inter, Ioi_eq_empty_iff, isMax_iff_eq_top, univ_mem, exists_const]
    rfl
  have ipc : ip.Countable := countable_setOf_isolated_right (α := Iic t)
  -- set of points dense in (-∞,t]
  obtain ⟨d, dc, dd⟩ := TopologicalSpace.exists_countable_dense (Iic t)
  let s := ip ∪ d
  have tmems : ⟨t, le_rfl⟩ ∈ s := Or.inl tmemip
  have nonemptys : Nonempty s := ⟨_, tmems⟩
  obtain ⟨u, hu⟩ := countable_iff_exists_surjective.mp (Countable.union ipc dc)
  obtain ⟨k, hk⟩ := hu ⟨_, tmems⟩
  -- rearrange the set {u 0, ..., u (n + k)} so that it is in the increasing order
  let r (n : ℕ) : List ↑(Iic t) := ((Finset.range (n + k + 1)).image u).sort
  let f (n : ℕ) : Fin (r n).length → Set (Iic t × Ω) := fun i =>
    if h0 : i = ⟨0, by simp [r]⟩ then Iic ((r n)[0]) ×ˢ univ
    else Ioc ((r n)[i.val - 1]) ((r n)[i]) ×ˢ univ
  let P (n : ℕ) : IndexedPartition (f n) := by
    refine IndexedPartition.mk' (f n) ?_ (fun i => ?_) (fun a => ?_)
    · sorry
    · by_cases h0 : i = ⟨0, by simp [r]⟩
      · simp [f, h0]
      · simp [f, h0]
        apply List.Sorted.rel_get_of_lt
        apply List.Sorted.lt_of_le
        · simp only [r]
          sorry
        · sorry
        · sorry
    · sorry
  let U : ℕ → (Iic t) × Ω → β := fun n p => (P n).piecewise (fun m => fun q => X (r n)[m] q.2) p
  refine stronglyMeasurable_of_tendsto (f := U) (u := atTop) (fun n => ?_) ?_
  · refine StronglyMeasurable.IndexedPartition (P n) (fun m => ?_) (fun m => ?_)
    · by_cases h0 : m = ⟨0, by simp [r]⟩
      · simpa [f, h0] using MeasurableSet.prod measurableSet_Iic MeasurableSet.univ
      · simpa [f, h0] using MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ
    · exact ((h (r n)[m]).mono (𝓕.mono' (by grind))).comp_snd
  · simp only [tendsto_pi_nhds]
    intro a
    by_cases hap : a.1 ∈ ip
    · have : ∀ᶠ i in atTop, U i a = X a.1 a.2 := by
        simp only [Fin.getElem_fin, eventually_atTop, ge_iff_le, U,
          IndexedPartition.piecewise_apply]
        have has : a.1 ∈ s := Set.mem_union_left d hap
        obtain ⟨l, hl⟩ := hu ⟨_, has⟩
        refine ⟨l, fun n hn => ?_⟩
        congr
        have ma : a.1 ∈ r n := by sorry
        have := List.idxOf_lt_length_of_mem ma
        have maf : a ∈ f n ⟨List.idxOf a.1 (r n), this⟩ := by sorry
        simp [IndexedPartition.mem_iff_index_eq (P n)] at maf
        simp [maf]
        sorry
      exact tendsto_nhds_of_eventually_eq this
    · sorry

end MeasureTheory
