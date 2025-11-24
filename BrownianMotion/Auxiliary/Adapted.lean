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
  -- ip is the set of points in (-∞,t] that are isolated on the right
  let ip := {x : Iic t | 𝓝[>] x = ⊥}
  have tmemip : ⟨t, le_rfl⟩ ∈ ip := by
    simp only [← not_neBot, nhdsWithin_neBot, not_forall,
      not_nonempty_iff_eq_empty, mem_setOf_eq, ip]
    use univ; simp; rfl
  have ipc : ip.Countable := countable_setOf_isolated_right (α := Iic t)
  -- d is the set of points dense in (-∞,t]
  obtain ⟨d, dc, dd⟩ := TopologicalSpace.exists_countable_dense (Iic t)
  let s := ip ∪ d
  have tmems : ⟨t, le_rfl⟩ ∈ s := Or.inl tmemip
  have nonemptys : Nonempty s := ⟨_, tmems⟩
  obtain ⟨u, hu⟩ := countable_iff_exists_surjective.mp (Countable.union ipc dc)
  obtain ⟨k, hk⟩ := hu ⟨_, tmems⟩
  let r (n : ℕ) := (Finset.range (n + k + 1)).image (Subtype.val ∘ u)
  -- rearrange the set {u 0, ..., u (n + k)} so that it is in the increasing order
  let v (n : ℕ) := Finset.orderEmbOfFin (r n) rfl
  let f (n : ℕ) : Fin (r n).card → Set (Iic t × Ω) := fun i =>
    if h0 : i = ⟨0, by simp [r]⟩ then Iic ((v n) i) ×ˢ univ
    else Ioc ((v n) ⟨i.val - 1, lt_trans (Nat.sub_one_lt (fun h => h0 (Fin.eq_of_val_eq h))) i.2⟩)
      ((v n) i) ×ˢ univ
  -- create a partition of (Iic t) × Ω
  let P (n : ℕ) : IndexedPartition (f n) := by
    refine IndexedPartition.mk' (f n) ?_ (fun i => ?_) (fun a => ?_)
    · sorry
    · by_cases h0 : i = ⟨0, by simp [r]⟩
      · simp [f, h0]
      · simp [f, h0, Fin.lt_def, Nat.sub_one_lt (fun j => h0 (Fin.eq_of_val_eq j))]
    · have hav : ∃ (i : Fin (r n).card), a.1 ≤ v n i := by
        refine ⟨⟨(r n).card - 1, ?_⟩, ?_⟩
        · exact Nat.sub_one_lt (by simp [r])
        · have l : (v n) ⟨(r n).card - 1, Nat.sub_one_lt (by simp [r])⟩ = ⟨t, le_rfl⟩ := by
            simp only [Finset.orderEmbOfFin_last (rfl : (r n).card = (r n).card) (by simp [r]),
              Finset.max'_eq_iff, Subtype.forall, mem_Iic, Subtype.mk_le_mk, v, r,
              Finset.mem_image, Finset.mem_range, comp_apply]
            exact ⟨⟨k, by linarith, by simp [hk]⟩, fun a ha _ => ha⟩
          have q := mem_Iic.mp a.1.2
          simpa [l] using q
      have hav' := Option.isSome_iff_exists.mp (Fin.isSome_find_iff.mpr hav)
      obtain ⟨i, hi⟩ := hav'
      refine ⟨i, ?_⟩
      by_cases h0 : i = ⟨0, by simp [r]⟩
      · simp_all only [nonempty_subtype, Subtype.exists, mem_Iic, ↓reduceDIte, mem_prod, mem_univ,
          and_true, f]
        exact Fin.find_spec (fun i ↦ a.1 ≤ (v n) i) hi
      · simp_all only [nonempty_subtype, Subtype.exists, mem_Iic, ↓reduceDIte, mem_prod, mem_Ioc,
          and_true, mem_univ, f]
        constructor
        · exact lt_of_not_ge (Fin.find_min hi (Nat.sub_one_lt (fun j => h0 (Fin.eq_of_val_eq j))))
        · exact Fin.find_spec (fun i ↦ a.1 ≤ (v n) i) hi
  -- discrete approximation of X
  let U : ℕ → (Iic t) × Ω → β := fun n p => (P n).piecewise (fun m => fun q => X (v n m) q.2) p
  refine stronglyMeasurable_of_tendsto (f := U) (u := atTop) (fun n => ?_) ?_
  · refine StronglyMeasurable.IndexedPartition (P n) (fun m => ?_) (fun m => ?_)
    · by_cases h0 : m = ⟨0, by simp [r]⟩
      · simpa [f, h0] using MeasurableSet.prod measurableSet_Iic MeasurableSet.univ
      · simpa [f, h0] using MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ
    · exact ((h (v n m)).mono (𝓕.mono' (by grind))).comp_snd
  · simp only [tendsto_pi_nhds]
    intro a
    by_cases has : a.1 ∈ s
    · have : ∀ᶠ i in atTop, U i a = X a.1 a.2 := by
        have ⟨z, hz⟩ := hu ⟨_, has⟩
        refine eventually_atTop.mpr ⟨z, fun x hxz => ?_⟩
        simp only [U, IndexedPartition.piecewise_apply]
        congr
        have : ∃ y, (v x) y = a.1 := by
          have lem1 := Finset.range_orderEmbOfFin (r x) rfl
          have lem2 : a.1 ∈ (r x : Set (Iic t)) := by
            simp only [Finset.coe_image, comp_apply, Finset.coe_range, mem_image, mem_Iio, r]
            exact ⟨z, by linarith, by simp [hz]⟩
          rw [← lem1, Set.mem_range] at lem2
          exact lem2
        obtain ⟨y, hy⟩ := this
        by_cases py : y = ⟨0, by simp [r]⟩
        · have qy : a ∈ (f x) y := by simp [py, f, ← hy]
          simpa [(P x).mem_iff_index_eq.mp qy]
        · have qy : a ∈ (f x) y := by
            simp only [py, ↓reduceDIte, mem_prod, ← hy, mem_Ioc, OrderEmbedding.lt_iff_lt, le_refl,
              and_true, mem_univ, f]
            exact Nat.sub_one_lt (fun j => py (Fin.eq_of_val_eq j))
          simpa [(P x).mem_iff_index_eq.mp qy]
      exact tendsto_nhds_of_eventually_eq this
    · let w : ℕ → ι := fun n => (v n) ((P n).index a)
      have tends1 : Tendsto w atTop (𝓝[>] a.1) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_atTop_nhds.mpr fun V hV hoV => ?_,
          Eventually.of_forall fun n => ?_⟩
        · sorry
        · simp only [mem_Ioi, Subtype.coe_lt_coe, w]
          have lem1 : a.1 ≤ (v n) ((P n).index a) := by
            have := (P n).mem_iff_index_eq.mpr (rfl : (P n).index a = (P n).index a)
            by_cases hPa : (P n).index a = ⟨0, by simp [r]⟩ <;> simp_all [f]
          have lem2 : (v n) ((P n).index a) ≠ a.1 := by
            intro hva
            have m1 : a.1 ∈ (r n : Set (Iic t)) := by simp [← hva, v]
            have m2 : (r n : Set (Iic t)) ⊆ s := by
              simpa [r] using MapsTo.subset_preimage (fun _ _ => by simp)
            exact has (m2 m1)
          exact LE.le.lt_of_ne' lem1 lem2
      have tends2 := ContinuousWithinAt.tendsto (hu_cont a.2 a.1)
      have : (fun x => U x a) = (X · a.2) ∘ w := by
        ext; simp [U, w, IndexedPartition.piecewise_apply]
      simpa [this] using tends2.comp tends1

end MeasureTheory
