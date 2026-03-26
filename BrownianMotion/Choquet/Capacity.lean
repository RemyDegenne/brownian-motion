/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Choquet.AnalyticSet

/-!
# Choquet capacity
-/

open scoped ENNReal NNReal

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
    Capacity (memFiniteUnion (memProd p q)) where
  capacityOf s := m (Prod.fst '' s)
  mono' s t hst := m.mono (Set.image_mono hst)
  capacityOf_iUnion f hf := by
    simp only [Set.image_iUnion]
    refine capacity_iUnion ?_
    exact fun i j hij ↦ Set.image_mono (hf hij)
  capacityOf_iInter f hf hp := by
    let g n := Prod.fst '' f n
    have hg : Antitone g := fun n m hnm ↦ Set.image_mono (hf hnm)
    rw [fst_iInter_of_memFiniteUnion_memProd_of_antitone hq_empty hq hf hp]
    refine capacity_iInter hg fun n ↦ ?_
    obtain ⟨S, u, hu_prod, hf_eq⟩ := hp n
    simp_rw [hf_eq, Set.image_iUnion]
    have hS : ∀ i ∈ S, p (Prod.fst '' u i) := by
      intro i hi
      obtain ⟨A, B, hA, hB, h_eq⟩ := hu_prod i hi
      rcases Set.eq_empty_or_nonempty B with hB | hB
      · simp only [hB, Set.prod_empty] at h_eq
        simpa [h_eq]
      · rwa [h_eq, Set.fst_image_prod _ hB]
    clear hf_eq
    induction S using Finset.induction with
    | empty => simpa
    | insert a s has h =>
      rw [Finset.set_biUnion_insert]
      refine hp_union ?_ ?_
      · exact hS a (Finset.mem_insert_self a s)
      · refine h ?_ ?_
        · exact fun i hi ↦ hu_prod i (Finset.mem_insert_of_mem hi)
        · exact fun i hi ↦ hS i (Finset.mem_insert_of_mem hi)

lemma Capacity.comp_fst_apply {hp_empty : ∅ ∈ p} {hp_union : SupClosed p}
    (m : Capacity p) {hq_empty : ∅ ∈ q} {hq : IsCompactSystem q}
    (s : Set (𝓧 × 𝓚)) :
    m.comp_fst hp_empty hp_union hq_empty hq s = m (Prod.fst '' s) := rfl

/-- A set `s` is capacitable for a capacity `m` for a property `p` if `m s` can be approximated
from above by countable intersections of sets `t n` such that `p (t n)` and `⋂ n, t n ⊆ s`. -/
def IsCapacitable (m : Capacity p) (s : Set 𝓧) : Prop :=
  ∀ a, a < m s → ∃ t, t ∈ memDelta p ∧ t ⊆ s ∧ a ≤ m t

lemma isCapacitable_of_mem (hs : s ∈ p) : IsCapacitable m s :=
  fun a ha ↦ ⟨s, memDelta_of_mem hs, by simp, ha.le⟩

-- He 1.34
lemma isCapacitable_memDelta_memSigma (m : Capacity p)
    (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (hs : s ∈ memDelta (memSigma p)) :
    IsCapacitable m s := by
  obtain ⟨A, hA, hs_eq⟩ := hs
  simp_rw [memSigma_iff_of_supClosed hp_union] at hA
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
  · rw [hs_eq]
    gcongr with n
    calc B n
    _ ⊆ A n (k n) := Set.dissipate_subset le_rfl
    _ ⊆ ⋃ m, A n m := by intro x hx; simp only [Set.mem_iUnion]; exact ⟨k n, hx⟩
  · rw [capacity_iInter Set.antitone_dissipate hB_mem]
    simp only [le_iInf_iff]
    exact fun n ↦ (hB_gt n).le

lemma memDelta_fst {s : Set (𝓧 × 𝓚)}
    (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (hq_empty : ∅ ∈ q) (hq_inter : InfClosed q) (hq : IsCompactSystem q)
    (hs : s ∈ memDelta (memFiniteUnion (memProd p q))) :
    (Prod.fst '' s) ∈ memDelta p := by
  rw [memDelta_iff_of_infClosed (InfClosed.memFiniteUnion (hp_inter.memProd hq_inter))] at hs
  obtain ⟨A, hA, hA_anti, rfl⟩ := hs
  rw [fst_iInter_of_memFiniteUnion_memProd_of_antitone hq_empty hq hA_anti hA]
  refine ⟨fun n ↦ Prod.fst '' A n, fun n ↦ ?_, rfl⟩
  simp only
  obtain ⟨S, B, hB, h_eq⟩ := hA n
  rw [h_eq]
  simp_rw [Set.image_iUnion]
  clear h_eq
  induction S using Finset.induction with
  | empty => simpa
  | insert a s has h =>
    rw [Finset.set_biUnion_insert]
    refine hp_union ?_ (h ?_)
    · obtain ⟨u, v, hu, hv, h_eq⟩ := hB a (Finset.mem_insert_self a s)
      rcases Set.eq_empty_or_nonempty v with hv | hv
      · simp only [hv, Set.prod_empty] at h_eq
        simpa [h_eq]
      · simpa [h_eq, Set.fst_image_prod _ hv]
    · exact fun i hi ↦ hB i (Finset.mem_insert_of_mem hi)

lemma IsCapacitable.fst (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (m : Capacity p) (hq_empty : ∅ ∈ q) (hq_inter : InfClosed q) (hq : IsCompactSystem q)
    {s : Set (𝓧 × 𝓚)} (hs : IsCapacitable (m.comp_fst hp_empty hp_union hq_empty hq) s) :
    IsCapacitable m (Prod.fst '' s) := by
  intro a ha
  choose t ht_mono ht_subset ht_le using hs a ha
  exact ⟨Prod.fst '' t, memDelta_fst hp_empty hp_inter hp_union hq_empty hq_inter hq ht_mono,
    Set.image_mono ht_subset, ht_le⟩

/-- **Choquet's capacitability theorem**. -/
theorem IsPavingAnalyticFor.isCapacitable (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p)
    (hp_union : SupClosed p) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsCapacitable m s := by
  obtain ⟨q, hq_empty, hq, A, hA, rfl⟩ := hs
  have hq'_empty : ∅ ∈ memFiniteInter q := memFiniteInter_of_mem hq_empty
  have hq'_inter : InfClosed (memFiniteInter q) := fun s hs t ht ↦ memFiniteInter.inter hs ht
  have hq' : IsCompactSystem (memFiniteInter q) := hq.memFiniteInter
  refine IsCapacitable.fst hp_empty hp_inter hp_union m hq'_empty hq'_inter hq' ?_
  refine isCapacitable_memDelta_memSigma _ ?_ ?_ ?_ ?_
  · exact memFiniteUnion_of_mem ⟨∅, ∅, hp_empty, hq'_empty, by simp⟩
  · exact InfClosed.memFiniteUnion (hp_inter.memProd hq'_inter)
  · exact fun s hs t ht ↦ memFiniteUnion.union hs ht
  · obtain ⟨B, hB, rfl⟩ := hA
    refine ⟨B, fun n ↦ ?_, rfl⟩
    obtain ⟨C, hC, hB_eq⟩ := hB n
    simp_rw [hB_eq]
    refine ⟨C, fun m ↦ ?_, rfl⟩
    refine memFiniteUnion_of_mem ?_
    obtain ⟨u, v, hu, hv, h_eq⟩ := hC m
    exact ⟨u, v, hu, memFiniteInter_of_mem hv, h_eq⟩

/-- **Choquet's capacitability theorem**. Every analytic set for a paving stable by intersection
and union is capacitable. -/
theorem IsPavingAnalytic.isCapacitable (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p)
    (hp_union : SupClosed p) (hs : IsPavingAnalytic p s) :
    IsCapacitable m s := by
  obtain ⟨𝓚, h𝓚, hs𝓚⟩ := hs
  exact hs𝓚.isCapacitable hp_empty hp_inter hp_union

lemma isCapacitable_measure_iff {m𝓧 : MeasurableSpace 𝓧} (μ : Measure 𝓧) [IsFiniteMeasure μ]
    (s : Set 𝓧) :
    IsCapacitable μ.capacity s ↔ NullMeasurableSet s μ := by
  refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
  · sorry
  · refine fun a ha ↦ ⟨(toMeasurable μ sᶜ)ᶜ, memDelta_of_mem ?_, ?_, ?_⟩
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
