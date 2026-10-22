/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Choquet.AnalyticSet
public import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-!
# Choquet capacities and the capacitability theorem

A capacity for a paving `p` is a monotone set function `m : Set 𝓧 → ℝ≥0∞` that is continuous along
increasing sequences of sets, and along decreasing sequences of sets of `p`. A set `s` is
capacitable if `m s` is the supremum of `m t` over the sets `t ⊆ s` that are countable intersections
of sets of `p`.

## Main definitions

* `MeasureTheory.Capacity p`: capacities for the paving `p`.
* `MeasureTheory.Measure.capacity`: the capacity defined by a finite measure.
* `MeasureTheory.Capacity.compFst`: the composition of a capacity with the projection `Prod.fst`.
* `MeasureTheory.IsCapacitable m s`: the set `s` is capacitable for the capacity `m`.

## Main statements

* `MeasureTheory.IsPavingAnalytic.isCapacitable`: **Choquet's capacitability theorem**. If the
  paving `p` contains `∅` and is closed under binary unions and intersections, then every analytic
  set for `p` is capacitable for every capacity for `p`.
* `MeasureTheory.IsPavingAnalytic.nullMeasurableSet`: a set that is analytic for the paving of
  measurable sets is null-measurable for every s-finite measure.
* `MeasurableSet.nullMeasurableSet_fst`: **measurable projection theorem**. The projection of a
  measurable set of `𝓧 × 𝓨`, with `𝓨` a standard Borel space, is null-measurable for every
  s-finite measure on `𝓧`.

## References

* [K. Bichteler, *Stochastic integration with jumps*][bichteler2002stochastic]
* [S. He, J. Wang and J. Yan, *Semimartingale theory and stochastic calculus*][he2019semimartingale]
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
  coe_injective | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

@[simp] lemma capacityOf_eq_coe (m : Capacity p) : m.capacityOf = m := rfl

lemma mono (m : Capacity p) {s t : Set 𝓧} (hst : s ⊆ t) : m s ≤ m t := m.mono' s t hst

end Capacity

lemma capacity_iUnion (hf : Monotone f) :
    m (⋃ n, f n) = ⨆ n, m (f n) := m.capacityOf_iUnion f hf

lemma capacity_iInter (hf : Antitone f) (hp : ∀ n, f n ∈ p) :
    m (⋂ n, f n) = ⨅ n, m (f n) := m.capacityOf_iInter f hf hp

/-- The capacity defined by a finite measure. -/
def Measure.capacity {m𝓧 : MeasurableSpace 𝓧} (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    Capacity {s : Set 𝓧 | MeasurableSet s} where
  capacityOf s := μ s
  mono' s t hst := μ.mono hst
  capacityOf_iUnion f hf := hf.measure_iUnion
  capacityOf_iInter f hf hp := hf.measure_iInter (fun i ↦ (hp i).nullMeasurableSet) ⟨0, by simp⟩

@[simp]
lemma Measure.capacity_apply {m𝓧 : MeasurableSpace 𝓧} (μ : Measure 𝓧) [IsFiniteMeasure μ]
    (s : Set 𝓧) :
    μ.capacity s = μ s := rfl

/-- The capacity obtained by composition of a capacity with the projection `Prod.fst`, for the
paving of finite unions of products `A ×ˢ K` with `A ∈ p` and `K` in a compact system `q`.
See Theorem A.5.8 (ii) of [bichteler2002stochastic] and Theorem 1.35 of [he2019semimartingale]. -/
def Capacity.compFst (hp_empty : ∅ ∈ p) (hp_union : SupClosed p)
    (m : Capacity p) (hq : IsCompactSystem q) :
    Capacity (supClosure (Set.image2 (· ×ˢ ·) p q)) where
  capacityOf s := m (Prod.fst '' s)
  mono' s t hst := m.mono (Set.image_mono hst)
  capacityOf_iUnion f hf := by
    simp only [Set.image_iUnion]
    exact capacity_iUnion fun i j hij ↦ Set.image_mono (hf hij)
  capacityOf_iInter f hf hp := by
    rw [fst_iInter_of_supClosure_image2_prod_of_antitone hq hf hp]
    exact capacity_iInter (fun n m hnm ↦ Set.image_mono (hf hnm))
      fun n ↦ fst_image_mem_of_mem_supClosure_image2_prod hp_empty hp_union (hp n)

lemma Capacity.compFst_apply {hp_empty : ∅ ∈ p} {hp_union : SupClosed p}
    (m : Capacity p) {hq : IsCompactSystem q} (s : Set (𝓧 × 𝓚)) :
    m.compFst hp_empty hp_union hq s = m (Prod.fst '' s) := rfl

/-- A set `s` is capacitable for a capacity `m` for a property `p` if `m s` can be approximated
from above by countable intersections of sets `t n` such that `p (t n)` and `⋂ n, t n ⊆ s`. -/
def IsCapacitable (m : Capacity p) (s : Set 𝓧) : Prop :=
  ∀ a, a < m s → ∃ t, t ∈ countableInfClosure p ∧ t ⊆ s ∧ a ≤ m t

lemma isCapacitable_of_mem (hs : s ∈ p) : IsCapacitable m s :=
  fun a ha ↦ ⟨s, subset_countableInfClosure hs, by simp, ha.le⟩

/-- If `p` is closed under binary unions and intersections, then every countable intersection of
countable unions of sets of `p` is capacitable. This is Theorem 1.34 of [he2019semimartingale]. -/
lemma isCapacitable_of_mem_countableInfClosure_countableSupClosure (m : Capacity p)
    (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (hs : s ∈ countableInfClosure (countableSupClosure p)) :
    IsCapacitable m s := by
  rw [mem_countableInfClosure_iff_iInf] at hs
  obtain ⟨A, hA, hs_eq⟩ := hs
  simp_rw [hp_union.mem_countableSupClosure_iff] at hA
  choose A hpA hA_mono h_eq using hA
  simp_rw [h_eq] at hs_eq
  have hs_sub (n : ℕ) : s ⊆ ⋃ j, A n j := by
    rw [← hs_eq]
    exact iInf_le (fun n ↦ ⋃ j, A n j) n
  intro a ha
  -- if `t ⊆ s` and `a < m t`, then `a < m (t ∩ A n j)` for some `j`, by continuity from below
  have step (n : ℕ) (t : Set 𝓧) (ht : t ⊆ s) (hat : a < m t) : ∃ j, a < m (t ∩ A n j) := by
    rw [← Set.inter_eq_left.mpr (ht.trans (hs_sub n)), Set.inter_iUnion,
      capacity_iUnion (f := fun j ↦ t ∩ A n j)
        fun i j hij ↦ Set.inter_subset_inter_right _ (hA_mono n hij)] at hat
    exact lt_iSup_iff.mp hat
  choose! k hk using step
  -- define recursively `D 0 = s` and `D (n + 1) = D n ∩ A n (k n (D n))`
  let D : ℕ → Set 𝓧 := fun n ↦ Nat.rec s (fun n D ↦ D ∩ A n (k n D)) n
  have hD_succ (n : ℕ) : D (n + 1) = D n ∩ A n (k n (D n)) := rfl
  have hD (n : ℕ) : D n ⊆ s ∧ a < m (D n) := by
    induction n with
    | zero => exact ⟨subset_rfl, ha⟩
    | succ n ih => exact ⟨hD_succ n ▸ Set.inter_subset_left.trans ih.1, hk n (D n) ih.1 ih.2⟩
  -- the set `⋂ n, B n` is in `countableInfClosure p`, is a subset of `s`, and `a ≤ m (⋂ n, B n)`
  let B n := Set.dissipate (fun i ↦ A i (k i (D i))) n
  have hDB (n : ℕ) : D (n + 1) ⊆ B n := by
    induction n with
    | zero =>
      simp only [B, Set.dissipate_zero_nat, hD_succ]
      exact Set.inter_subset_right
    | succ n ih =>
      simp only [B, Set.dissipate_succ, hD_succ (n + 1)]
      exact Set.inter_subset_inter ih subset_rfl
  have hB_mem n : B n ∈ p := by
    induction n with
    | zero => simp [B, hpA]
    | succ n hn =>
      simp only [B, Set.dissipate_succ]
      exact hp_inter hn (hpA _ _)
  refine ⟨⋂ n, B n, ?_, ?_, ?_⟩
  · rw [mem_countableInfClosure_iff_iInf]
    exact ⟨B, hB_mem, rfl⟩
  · rw [← hs_eq, Set.iInf_eq_iInter]
    gcongr with n
    exact (Set.dissipate_subset le_rfl).trans (Set.subset_iUnion (A n) _)
  · rw [capacity_iInter Set.antitone_dissipate hB_mem]
    exact le_iInf fun n ↦ (hD (n + 1)).2.le.trans (m.mono (hDB n))

/-- If `p` is closed under binary unions and intersections, and `q` under binary intersections, then
the projection of a set of `countableInfClosure (supClosure (p × q))` is in
`countableInfClosure p`. -/
lemma mem_countableInfClosure_fst {s : Set (𝓧 × 𝓚)}
    (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (hq_inter : InfClosed q) (hq : IsCompactSystem q)
    (hs : s ∈ countableInfClosure (supClosure (Set.image2 (· ×ˢ ·) p q))) :
    (Prod.fst '' s) ∈ countableInfClosure p := by
  rw [(hp_inter.image2_prod hq_inter).supClosure.mem_countableInfClosure_iff] at hs
  obtain ⟨A, hA, hA_anti, rfl⟩ := hs
  rw [fst_iInter_of_supClosure_image2_prod_of_antitone hq hA_anti hA,
    mem_countableInfClosure_iff_iInf]
  exact ⟨fun n ↦ Prod.fst '' A n,
    fun n ↦ fst_image_mem_of_mem_supClosure_image2_prod hp_empty hp_union (hA n), rfl⟩

/-- If a set `s` of `𝓧 × 𝓚` is capacitable for the capacity `m.compFst`, then its projection is
capacitable for `m`. -/
lemma IsCapacitable.fst (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (m : Capacity p) (hq_inter : InfClosed q) (hq : IsCompactSystem q)
    {s : Set (𝓧 × 𝓚)} (hs : IsCapacitable (m.compFst hp_empty hp_union hq) s) :
    IsCapacitable m (Prod.fst '' s) := by
  intro a ha
  obtain ⟨t, ht_mem, ht_subset, ht_le⟩ := hs a ha
  exact ⟨Prod.fst '' t, mem_countableInfClosure_fst hp_empty hp_inter hp_union hq_inter hq ht_mem,
    Set.image_mono ht_subset, ht_le⟩

/-- **Choquet's capacitability theorem**, for a set that is analytic with auxiliary space `𝓚`. -/
lemma IsPavingAnalyticFor.isCapacitable (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p)
    (hp_union : SupClosed p) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsCapacitable m s := by
  obtain ⟨q, hq, A, hA, rfl⟩ := hs
  -- replace `q` by `infClosure q`, so that the paving `p × q` is closed under intersections
  refine IsCapacitable.fst hp_empty hp_inter hp_union m infClosed_infClosure hq.infClosure ?_
  refine isCapacitable_of_mem_countableInfClosure_countableSupClosure _ ?_ ?_ ?_
  · exact InfClosed.supClosure (hp_inter.image2_prod infClosed_infClosure)
  · exact fun s hs t ht ↦ supClosed_supClosure hs ht
  · unfold prodSigmaDelta at hA
    rw [mem_countableInfClosure_iff_iInf] at hA ⊢
    obtain ⟨B, hB, rfl⟩ := hA
    refine ⟨B, fun n ↦ ?_, rfl⟩
    simp_rw [mem_countableSupClosure_iff_iSup] at hB ⊢
    obtain ⟨C, hC, hB_eq⟩ := hB n
    simp_rw [← hB_eq]
    refine ⟨C, fun m ↦ ?_, rfl⟩
    refine subset_supClosure ?_
    obtain ⟨u, v, hu, hv, h_eq⟩ := hC m
    exact ⟨u, v, hu, subset_infClosure hv, h_eq⟩

/-- **Choquet's capacitability theorem**. If the paving `p` contains `∅` and is closed under binary
unions and intersections, then every analytic set for `p` is capacitable for every capacity
for `p`. -/
theorem IsPavingAnalytic.isCapacitable (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p)
    (hp_union : SupClosed p) (hs : IsPavingAnalytic p s) :
    IsCapacitable m s := by
  obtain ⟨𝓚, hs𝓚⟩ := hs
  exact hs𝓚.isCapacitable hp_empty hp_inter hp_union

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
      have hm := MeasurableSet.iUnion fun i ↦ .of_mem_countableInfClosure (hf i).1 fun _ ↦ id
      refine ⟨⋃ i, f i, hm, ae_eq_set.2 ⟨?_, ?_⟩⟩
      · rw [measure_sdiff hsub hm.nullMeasurableSet (by finiteness)]
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
      · simp_all [← Set.sdiff_eq_empty]
  · refine fun a ha ↦ ⟨(toMeasurable μ sᶜ)ᶜ, subset_countableInfClosure ?_, ?_, ?_⟩
    · exact (measurableSet_toMeasurable _ _).compl
    · rw [Set.compl_subset_comm]
      exact subset_toMeasurable μ sᶜ
    · simp only [Measure.capacity_apply, measurableSet_toMeasurable, measure_toMeasurable, ne_eq,
        measure_ne_top, not_false_eq_true, measure_compl] at ha ⊢
      rw [← measure_compl₀ hs.compl (by simp), compl_compl]
      exact ha.le

/-- An analytic set is universally measurable: it is null-measurable with respect to any
s-finite measure. -/
lemma IsPavingAnalytic.nullMeasurableSet {m𝓧 : MeasurableSpace 𝓧}
    (hs : IsPavingAnalytic {t | MeasurableSet t} s) (μ : Measure 𝓧) [SFinite μ] :
    NullMeasurableSet s μ := by
  -- reduce to the finite measure `μ.toFinite`, which has the same null sets as `μ`
  refine NullMeasurableSet.mono_ac ?_ (absolutelyContinuous_toFinite μ)
  rw [← isCapacitable_measure_iff μ.toFinite]
  exact IsPavingAnalytic.isCapacitable (p := {t : Set 𝓧 | MeasurableSet t}) MeasurableSet.empty
    infClosed_measurableSet supClosed_measurableSet hs

/-- An analytic set is universally measurable: it is null-measurable with respect to any
s-finite measure. -/
lemma IsMeasurableAnalytic.nullMeasurableSet {m𝓧 : MeasurableSpace 𝓧} (hs : IsMeasurableAnalytic s)
    (μ : Measure 𝓧) [SFinite μ] :
    NullMeasurableSet s μ :=
  hs.isPavingAnalytic.nullMeasurableSet μ

/-- The projection of an analytic set of `𝓧 × ι` is null-measurable with respect to any s-finite
measure. -/
theorem IsPavingAnalytic.nullMeasurableSet_fst {ι : Type} [LinearOrder ι] [DenselyOrdered ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] [CompactIccSpace ι]
    {_ : MeasurableSpace ι} [BorelSpace ι]
    {_m𝓧 : MeasurableSpace 𝓧} {s : Set (𝓧 × ι)}
    (hs : IsPavingAnalytic {t | MeasurableSet t} s) (μ : Measure 𝓧) [SFinite μ] :
    NullMeasurableSet (Prod.fst '' s) μ := by
  refine IsPavingAnalytic.nullMeasurableSet ?_ μ
  refine isPavingAnalytic_fst_of_image2_prod_measurableSet_Icc (s := s) ?_
  rwa [isPavingAnalytic_image2_prod_measurableSet_Icc_iff]

-- todo: swap could be any measurable embedding?
lemma isPavingAnalytic_swap {Ω 𝓧 : Type*} {s : Set (𝓧 × Ω)}
    {p : Set (Set (𝓧 × Ω))} (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic ((fun s ↦ Prod.swap '' s) '' p) (Prod.swap '' s) := by
  obtain ⟨𝓚, q, hq_compact, t, ht_mem, h_eq⟩ := hs
  refine ⟨𝓚, q, hq_compact, Prod.map Prod.swap id '' t, ?_, ?_⟩
  · rw [mem_prodSigmaDelta_iff] at ht_mem ⊢
    obtain ⟨A, hA, K, hK, rfl⟩ := ht_mem
    refine ⟨fun n m ↦ Prod.swap '' (A n m), fun n m ↦ ?_, K, hK, ?_⟩
    · simp only [Set.mem_image]
      exact ⟨A n m, hA n m, rfl⟩
    · rw [Set.image_iInter]
      swap; · exact Prod.swap_bijective.prodMap Function.bijective_id
      simp_rw [Set.image_iUnion]
      congr with n x
      simp
      grind
  · ext; simp; grind

lemma isPavingAnalytic_measurableSet_swap {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {s : Set (𝓧 × Ω)}
    (hs : IsPavingAnalytic {t | MeasurableSet t} s) :
    IsPavingAnalytic {t | MeasurableSet t} (Prod.swap '' s) := by
  convert isPavingAnalytic_swap hs
  rename_i s
  simp only [Set.mem_eq_mem, Set.mem_image]
  refine ⟨fun hs ↦ ⟨Prod.swap ⁻¹' s, MeasurableSet.preimage ?_ measurable_swap, ?_⟩,
    fun ⟨t, ht, ht_eq⟩ ↦ ?_⟩
  · exact hs
  · ext; simp; grind
  · rw [← ht_eq, Set.image_swap_eq_preimage_swap]
    refine MeasurableSet.preimage ?_ measurable_swap
    exact ht

/-- The projection of an analytic set of `ι × 𝓧` is null-measurable with respect to any s-finite
measure. -/
lemma IsPavingAnalytic.nullMeasurableSet_snd {ι : Type} [LinearOrder ι] [DenselyOrdered ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] [CompactIccSpace ι]
    {_ : MeasurableSpace ι} [BorelSpace ι]
    {_m𝓧 : MeasurableSpace 𝓧} {s : Set (ι × 𝓧)}
    (hs : IsPavingAnalytic {t | MeasurableSet t} s) (μ : Measure 𝓧) [SFinite μ] :
    NullMeasurableSet (Prod.snd '' s) μ := by
  convert IsPavingAnalytic.nullMeasurableSet_fst (s := Prod.swap ⁻¹' s) (_m𝓧 := _m𝓧) ?_ μ
  · ext; simp
  · convert isPavingAnalytic_measurableSet_swap hs
    ext; simp; grind

theorem IsMeasurableAnalytic.nullMeasurableSet_fst {𝓨 : Type*}
    {_m𝓧 : MeasurableSpace 𝓧} {_m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace 𝓨] {s : Set (𝓧 × 𝓨)}
    (hs : IsMeasurableAnalytic s) (μ : Measure 𝓧) [SFinite μ] :
    NullMeasurableSet (Prod.fst '' s) μ := by
  have hs_for : IsMeasurableAnalyticFor (𝓨 × ℝ) (Prod.fst '' s) := by
    obtain ⟨t, ht, h_eq⟩ := hs
    rw [h_eq]
    refine ⟨MeasurableEquiv.prodAssoc '' t, ?_, by ext; simp [MeasurableEquiv.prodAssoc]⟩
    exact MeasurableEquiv.prodAssoc.measurableSet_image.mpr ht
  exact hs_for.isMeasurableAnalytic.nullMeasurableSet μ

theorem IsMeasurableAnalytic.nullMeasurableSet_snd {𝓨 : Type*}
    {_m𝓧 : MeasurableSpace 𝓧} {_m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace 𝓨] {s : Set (𝓨 × 𝓧)}
    (hs : IsMeasurableAnalytic s) (μ : Measure 𝓧) [SFinite μ] :
    NullMeasurableSet (Prod.snd '' s) μ := by
  convert IsMeasurableAnalytic.nullMeasurableSet_fst (s := Prod.swap ⁻¹' s) (_m𝓧 := _m𝓧)
    (_m𝓨 := _m𝓨) ?_ μ
  · ext; simp
  · obtain ⟨t, ht, h_eq⟩ := hs
    rw [h_eq]
    refine ⟨{u | ((u.1.2, u.1.1), u.2) ∈ t}, ?_, by ext; simp [Prod.swap]⟩
    exact ht.preimage (by fun_prop)

/-- **Measurable projection theorem**: the projection of a measurable set is universally
measurable (null-measurable with respect to any s-finite measure). -/
theorem _root_.MeasurableSet.nullMeasurableSet_fst {𝓨 : Type*}
    {_m𝓧 : MeasurableSpace 𝓧} {_m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace 𝓨] {s : Set (𝓧 × 𝓨)}
    (hs : MeasurableSet s) (μ : Measure 𝓧) [SFinite μ] :
    NullMeasurableSet (Prod.fst '' s) μ :=
  hs.isMeasurableAnalytic.nullMeasurableSet_fst μ

theorem _root_.MeasurableSet.nullMeasurableSet_snd {𝓨 : Type*}
    {_m𝓧 : MeasurableSpace 𝓧} {_m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace 𝓨] {s : Set (𝓨 × 𝓧)}
    (hs : MeasurableSet s) (μ : Measure 𝓧) [SFinite μ] :
    NullMeasurableSet (Prod.snd '' s) μ :=
  hs.isMeasurableAnalytic.nullMeasurableSet_snd μ

end MeasureTheory
