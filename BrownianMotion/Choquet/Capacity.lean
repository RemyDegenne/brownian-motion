/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Choquet.AnalyticSet

/-!
# Choquet capacity
-/

@[expose] public section

open Filter
open scoped ENNReal NNReal Topology

variable {𝓧 𝓚 : Type*} {x y : 𝓧} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)}
  {s t : Set 𝓧} {f : ℕ → Set 𝓧}

namespace MeasureTheory

/-- A capacity is a set function that is monotone, continuous from above for decreasing sequences
of sets satisfying `p`, and continuous from below for increasing sequences of sets.

Any finite measure defines a capacity, but capacities have only the monotonicity properties of
measures. The notable difference is that a capacity is not additive. -/
structure Capacity (p : Set (Set 𝓧)) where
  /-- The set function associated with a capacity. -/
  capacityOf : Set 𝓧 → ℝ≥0∞
  mono' (s t : Set 𝓧) (hst : s ⊆ t) : capacityOf s ≤ capacityOf t
  capacityOf_iUnion : ∀ (f : ℕ → Set 𝓧), Monotone f → capacityOf (⋃ n, f n) = ⨆ n, capacityOf (f n)
  capacityOf_iInter : ∀ (f : ℕ → Set 𝓧), Antitone f → (∀ n, f n ∈ p) →
    capacityOf (⋂ n, f n) = ⨅ n, capacityOf (f n)

variable {m : Capacity p}

namespace Capacity

instance : FunLike (Capacity p) (Set 𝓧) ℝ≥0∞ where
  coe m := m.capacityOf
  coe_injective' | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

@[simp] theorem capacityOf_eq_coe (m : Capacity p) : m.capacityOf = m := rfl

lemma mono (m : Capacity p) {s t : Set 𝓧} (hst : s ⊆ t) : m s ≤ m t := m.mono' s t hst

end Capacity

lemma capacity_iUnion (hf : Monotone f) :
    m (⋃ n, f n) = ⨆ n, m (f n) := m.capacityOf_iUnion f hf

lemma capacity_iInter (hf : Antitone f) (hp : ∀ n, f n ∈ p) :
    m (⋂ n, f n) = ⨅ n, m (f n) := m.capacityOf_iInter f hf hp

/-- The capacity defined by a finite measure. -/
def Measure.capacity {m𝓧 : MeasurableSpace 𝓧} (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    Capacity (MeasurableSet (α := 𝓧)) where
  capacityOf s := μ s
  mono' s t hst := μ.mono hst
  capacityOf_iUnion f hf := hf.measure_iUnion
  capacityOf_iInter f hf hp := hf.measure_iInter (fun i ↦ (hp i).nullMeasurableSet) ⟨0, by simp⟩

@[simp]
lemma Measure.capacity_apply {m𝓧 : MeasurableSpace 𝓧} (μ : Measure 𝓧) [IsFiniteMeasure μ]
    (s : Set 𝓧) :
    μ.capacity s = μ s := rfl

-- Bichteler A.5.8 (ii); He 1.35
/-- The capacity obtained by composition of a capacity with a projection. -/
def Capacity.comp_fst (hp_empty : ∅ ∈ p) (hp_union : SupClosed p)
    (m : Capacity p) (hq_empty : ∅ ∈ q) (hq : IsCompactSystem q) :
    Capacity (supClosure (Set.image2 (· ×ˢ ·) p q)) where
  capacityOf s := m (Prod.fst '' s)
  mono' s t hst := m.mono (Set.image_mono hst)
  capacityOf_iUnion f hf := by
    simp only [Set.image_iUnion]
    refine capacity_iUnion ?_
    exact fun i j hij ↦ Set.image_mono (hf hij)
  capacityOf_iInter f hf hp := by
    let g n := Prod.fst '' f n
    have hg : Antitone g := fun n m hnm ↦ Set.image_mono (hf hnm)
    rw [fst_iInter_of_supClosure_image2_prod_of_antitone hq_empty hq hf hp]
    refine capacity_iInter hg fun n ↦ ?_
    simp_rw [mem_supClosure_set_iff'] at hp
    obtain ⟨S, _, u, hu_prod, hf_eq⟩ := hp n
    simp_rw [hf_eq, Set.image_iUnion]
    have hS : ∀ i ∈ S, p (Prod.fst '' u i) := by
      intro i hi
      obtain ⟨A, hA, B, hB, h_eq⟩ := hu_prod i hi
      rcases Set.eq_empty_or_nonempty B with hB | hB
      · simp only [hB, Set.prod_empty] at h_eq
        simpa [← h_eq]
      · rwa [← h_eq, Set.fst_image_prod _ hB]
    clear hf_eq
    induction S using Finset.induction with
    | empty => simpa
    | insert a s has h =>
      rw [Finset.set_biUnion_insert]
      refine hp_union ?_ ?_
      · exact hS a (Finset.mem_insert_self a s)
      · rcases Finset.eq_empty_or_nonempty s with rfl | hs
        · simpa
        refine h hs ?_ ?_
        · exact fun i hi ↦ hu_prod i (Finset.mem_insert_of_mem hi)
        · exact fun i hi ↦ hS i (Finset.mem_insert_of_mem hi)

/-- A set `s` is capacitable for a capacity `m` for a property `p` if `m s` can be approximated
from above by countable intersections of sets `t n` such that `p (t n)` and `⋂ n, t n ⊆ s`. -/
def IsCapacitable (m : Capacity p) (s : Set 𝓧) : Prop :=
  ∀ a, a < m s → ∃ t, t ∈ countableInfClosure p ∧ t ⊆ s ∧ a ≤ m t

lemma isCapacitable_of_mem (hs : s ∈ p) : IsCapacitable m s :=
  fun a ha ↦ ⟨s, subset_countableInfClosure hs, by simp, ha.le⟩

-- He 1.34
lemma isCapacitable_mem_countableInfClosure_countableSupClosure (m : Capacity p)
    (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (hs : s ∈ countableInfClosure (countableSupClosure p)) :
    IsCapacitable m s := by
  obtain ⟨A, hA, hs_eq⟩ := hs
  simp_rw [hp_union.mem_countableSupClosure_iff] at hA
  choose A hpA hA_mono h_eq using hA
  simp_rw [h_eq] at hs_eq
  intro a ha
  obtain ⟨k, hk⟩ : ∃ k : ℕ → ℕ, ∀ n, a < m (s ∩ Set.dissipate (fun i ↦ A i (k i)) n) := by
    sorry
  let B n := Set.dissipate (fun i ↦ A i (k i)) n
  have hB_gt n : a < m (B n) := (hk n).trans_le (m.mono Set.inter_subset_right)
  have hB_mem n : B n ∈ p := by
    unfold B
    induction n with
    | zero => simp [hpA]
    | succ n hn =>
      rw [Set.dissipate_succ]
      exact hp_inter hn (hpA _ _)
  refine ⟨⋂ n, B n, ⟨B, hB_mem, rfl⟩, ?_, ?_⟩
  · rw [← hs_eq, Set.iInf_eq_iInter]
    gcongr with n
    calc B n
    _ ⊆ A n (k n) := Set.dissipate_subset le_rfl
    _ ⊆ ⋃ m, A n m := by intro x hx; simp only [Set.mem_iUnion]; exact ⟨k n, hx⟩
  · rw [capacity_iInter Set.antitone_dissipate hB_mem]
    simp only [le_iInf_iff]
    exact fun n ↦ (hB_gt n).le

lemma mem_countableInfClosure_fst {s : Set (𝓧 × 𝓚)}
    (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (hq_empty : ∅ ∈ q) (hq_inter : InfClosed q) (hq : IsCompactSystem q)
    (hs : s ∈ countableInfClosure (supClosure (Set.image2 (· ×ˢ ·) p q))) :
    (Prod.fst '' s) ∈ countableInfClosure p := by
  rw [InfClosed.mem_countableInfClosure_iff (InfClosed.supClosure (hp_inter.image2_prod hq_inter))]
    at hs
  obtain ⟨A, hA, hA_anti, rfl⟩ := hs
  rw [fst_iInter_of_supClosure_image2_prod_of_antitone hq_empty hq hA_anti hA]
  refine ⟨fun n ↦ Prod.fst '' A n, fun n ↦ ?_, rfl⟩
  simp only
  simp_rw [mem_supClosure_set_iff'] at hA
  obtain ⟨S, _, B, hB, h_eq⟩ := hA n
  rw [h_eq]
  simp_rw [Set.image_iUnion]
  clear h_eq
  induction S using Finset.induction with
  | empty => simpa
  | insert a s has h =>
    rw [Finset.set_biUnion_insert]
    rcases Finset.eq_empty_or_nonempty s with rfl | hs
    · simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty]
      obtain ⟨u, hu, v, hv, h_eq⟩ := hB a (Finset.mem_insert_self a _)
      simp only [← h_eq]
      rcases Set.eq_empty_or_nonempty v with rfl | hv
      · simpa
      · rwa [Set.fst_image_prod _ hv]
    refine hp_union ?_ (h hs ?_)
    · obtain ⟨u, hu, v, hv, h_eq⟩ := hB a (Finset.mem_insert_self a s)
      rcases Set.eq_empty_or_nonempty v with hv | hv
      · simp only [hv, Set.prod_empty] at h_eq
        simpa [← h_eq]
      · simpa [← h_eq, Set.fst_image_prod _ hv]
    · exact fun i hi ↦ hB i (Finset.mem_insert_of_mem hi)

lemma IsCapacitable.fst (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (m : Capacity p) (hq_empty : ∅ ∈ q) (hq_inter : InfClosed q) (hq : IsCompactSystem q)
    {s : Set (𝓧 × 𝓚)} (hs : IsCapacitable (m.comp_fst hp_empty hp_union hq_empty hq) s) :
    IsCapacitable m (Prod.fst '' s) := by
  intro a ha
  choose t ht_mono ht_subset ht_le using hs a ha
  exact ⟨Prod.fst '' t,
    mem_countableInfClosure_fst hp_empty hp_inter hp_union hq_empty hq_inter hq ht_mono,
    Set.image_mono ht_subset, ht_le⟩

/-- **Choquet's capacitability theorem**. -/
theorem IsPavingAnalyticFor.isCapacitable (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p)
    (hp_union : SupClosed p) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsCapacitable m s := by
  obtain ⟨q, hq_empty, hq, A, hA, rfl⟩ := hs
  have hq'_empty : ∅ ∈ infClosure q := subset_infClosure hq_empty
  have hq' : IsCompactSystem (infClosure q) := hq.infClosure
  refine IsCapacitable.fst hp_empty hp_inter hp_union m hq'_empty infClosed_infClosure hq' ?_
  refine isCapacitable_mem_countableInfClosure_countableSupClosure _ ?_ ?_ ?_ ?_
  · exact subset_supClosure ⟨∅, hp_empty, ∅, hq'_empty, by simp⟩
  · exact InfClosed.supClosure (hp_inter.image2_prod infClosed_infClosure)
  · exact fun s hs t ht ↦ supClosed_supClosure hs ht
  · obtain ⟨B, hB, rfl⟩ := hA
    refine ⟨B, fun n ↦ ?_, rfl⟩
    obtain ⟨C, hC, hB_eq⟩ := hB n
    simp_rw [← hB_eq]
    refine ⟨C, fun m ↦ ?_, rfl⟩
    refine subset_supClosure ?_
    obtain ⟨u, v, hu, hv, h_eq⟩ := hC m
    exact ⟨u, v, hu, subset_infClosure hv, h_eq⟩

/-- **Choquet's capacitability theorem**. Every analytic set for a paving stable by intersection
and union is capacitable. -/
theorem IsPavingAnalytic.isCapacitable (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p)
    (hp_union : SupClosed p) (hs : IsPavingAnalytic p s) :
    IsCapacitable m s := by
  obtain ⟨𝓚, h𝓚, hs𝓚⟩ := hs
  exact hs𝓚.isCapacitable hp_empty hp_inter hp_union

lemma mem_countableInfClosure_measurableSet {m𝓧 : MeasurableSpace 𝓧} {s : Set 𝓧}
    (hs : s ∈ countableInfClosure MeasurableSet) :
    MeasurableSet s := by
  obtain ⟨A, hA, rfl⟩ := hs
  exact MeasurableSet.iInter hA

lemma isCapacitable_measure_iff {m𝓧 : MeasurableSpace 𝓧} (μ : Measure 𝓧) [IsFiniteMeasure μ]
    (s : Set 𝓧) :
    IsCapacitable μ.capacity s ↔ NullMeasurableSet s μ := by
  refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
  · by_cases! hcs : μ.capacity s = 0
    · exact NullMeasurableSet.of_null hcs
    · have (n : ℕ) : μ.capacity s * (1 - (n + 1 : ℝ≥0∞)⁻¹) < μ.capacity s := by
        nth_rw 2 [← mul_one (μ.capacity s)]
        refine (ENNReal.mul_lt_mul_iff_right hcs (by simp)).2 (ENNReal.sub_lt_of_lt_add ?_ ?_)
        · simp
        · exact ENNReal.lt_add_right (by simp) (by simp)
      have (n : ℕ) := hs ((μ.capacity s) * (1 - (n + 1 : ℝ≥0∞)⁻¹)) (this n)
      choose f hf using this
      have hsub : ⋃ i, f i ⊆ s := Set.iUnion_subset fun i => (hf i).2.1
      have hm := MeasurableSet.iUnion fun i ↦ mem_countableInfClosure_measurableSet (hf i).1
      refine ⟨⋃ i, f i, hm, ae_eq_set.2 ⟨?_, ?_⟩⟩
      · rw [measure_diff hsub hm.nullMeasurableSet (by finiteness)]
        suffices μ (⋃ i, f i) = μ s from by simp_all
        refine le_antisymm (measure_mono hsub) ?_
        have : Tendsto (fun n : ℕ => μ s * (1 - (n + 1 : ℝ≥0∞)⁻¹)) atTop (𝓝 (μ s)) := by
          nth_rw 2 [← mul_one (μ s)]
          refine ENNReal.Tendsto.const_mul ?_ (by simp)
          nth_rw 3 [← tsub_zero 1]
          refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (by simp)
          convert ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1) with n
          simp
        refine le_of_tendsto_of_tendsto' this tendsto_const_nhds fun n => (hf n).2.2.trans ?_
        simpa using measure_mono (Set.subset_iUnion _ _)
      · simp_all [← Set.diff_eq_empty]
  · refine fun a ha ↦ ⟨(toMeasurable μ sᶜ)ᶜ, subset_countableInfClosure ?_, ?_, ?_⟩
    · exact (measurableSet_toMeasurable _ _).compl
    · rw [Set.compl_subset_comm]
      exact subset_toMeasurable μ sᶜ
    · simp only [Measure.capacity_apply, measurableSet_toMeasurable, measure_toMeasurable, ne_eq,
        measure_ne_top, not_false_eq_true, measure_compl] at ha ⊢
      rw [← measure_compl₀ hs.compl (by simp), compl_compl]
      exact ha.le

/-- An analytic set is universally measurable: it is null-measurable with respect to any
finite measure. -/
lemma IsPavingAnalytic.nullMeasurableSet {m𝓧 : MeasurableSpace 𝓧}
    (hs : IsPavingAnalytic MeasurableSet s) (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    NullMeasurableSet s μ := by
  rw [← isCapacitable_measure_iff μ]
  refine IsPavingAnalytic.isCapacitable (p := MeasurableSet (α := 𝓧)) MeasurableSet.empty ?_ ?_ hs
  · exact fun s hs t ht ↦ hs.inter ht
  · exact fun s hs t ht ↦ hs.union ht

/-- An analytic set is universally measurable: it is null-measurable with respect to any
finite measure. -/
lemma IsMeasurableAnalytic.nullMeasurableSet {m𝓧 : MeasurableSpace 𝓧} (hs : IsMeasurableAnalytic s)
    (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    NullMeasurableSet s μ := by
  exact hs.isPavingAnalytic.nullMeasurableSet μ

/-- **Measurable projection** theorem: the projection of a measurable set is universally measurable
(null-measurable for any finite measure). -/
theorem _root_.MeasurableSet.nullMeasurableSet_fst {𝓨 : Type*}
    {_m𝓧 : MeasurableSpace 𝓧} {_m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace 𝓨] {s : Set (𝓧 × 𝓨)}
    (hs : MeasurableSet s) (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    NullMeasurableSet (Prod.fst '' s) μ := by
  have hs_for : IsMeasurableAnalyticFor 𝓨 (Prod.fst '' s) := ⟨s, hs, rfl⟩
  exact hs_for.isMeasurableAnalytic.nullMeasurableSet μ

theorem _root_.MeasurableSet.nullMeasurableSet_snd {𝓨 : Type*}
    {_m𝓧 : MeasurableSpace 𝓧} {_m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace 𝓨] {s : Set (𝓨 × 𝓧)}
    (hs : MeasurableSet s) (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    NullMeasurableSet (Prod.snd '' s) μ := by
  convert MeasurableSet.nullMeasurableSet_fst (s := Prod.swap ⁻¹' s) (_m𝓧 := _m𝓧)
    (_m𝓨 := _m𝓨) (hs.preimage (by fun_prop)) μ
  ext
  simp

end MeasureTheory
