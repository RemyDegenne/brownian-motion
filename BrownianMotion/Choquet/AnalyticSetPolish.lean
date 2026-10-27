/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Choquet.AnalyticSet
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Analytic sets of a Polish space as analytic sets for a paving

We prove that in a Polish space, the analytic sets (`MeasureTheory.AnalyticSet`, the continuous
images of `ℕ → ℕ`) are the sets that are analytic for the paving of closed sets
(`MeasureTheory.IsPavingAnalytic`).

## Main statements

* `PiNat.isCompactSystem_cylinder_inter`: the intersections of the cylinders of `Π n, E n` with a
  closed set form a compact system.
* `MeasureTheory.AnalyticSet.isPavingAnalytic_isClosed`: in a Hausdorff space, an analytic set is
  analytic for the paving of closed sets.
* `MeasureTheory.AnalyticSet.prod`: the product of two analytic sets is analytic.
* `MeasureTheory.IsPavingAnalytic.analyticSet`: in a Hausdorff space, a set that is analytic for a
  paving of analytic sets is analytic.
* `MeasureTheory.analyticSet_iff_isPavingAnalytic_isClosed`: in a Polish space, a set is analytic
  if and only if it is analytic for the paving of closed sets.

## Implementation notes

For the first direction, we write an analytic set `s` as the range of a continuous map
`f : (ℕ → ℕ) → X`. The graph of `f` is the intersection over `n` of the unions of the products
`closure (f '' C) ×ˢ C`, where `C` ranges over the cylinders of length `n`. The cylinders form a
compact system, and `s` is the projection of the graph.

For the converse, we write `s` as the projection of `⋂ n, ⋃ m, A n m ×ˢ K n m`. A point `x` is in
`s` if and only if there is `σ : ℕ → ℕ` such that `x ∈ A n (σ n)` for all `n` and the sets
`K n (σ n)` have a common point. Since the sets `K n m` belong to a compact system, the second
condition defines a closed set `S` of sequences. Hence `s` is the projection of the set
`⋂ n, ⋃ m, A n m ×ˢ {σ ∈ S | σ n = m}`, which is analytic.
-/

@[expose] public section

open Set Filter Topology

/-- If a set is closed under countable suprema, it contains the supremum of every family of its
elements that takes countably many values. -/
lemma CountableSupClosed.iSup_mem_of_countable_range {α ι : Type*} [CompleteLattice α]
    [Nonempty ι] {S : Set α} (hS : CountableSupClosed S) {f : ι → α} (hf : (Set.range f).Countable)
    (hfS : ∀ i, f i ∈ S) :
    ⨆ i, f i ∈ S := by
  rw [← sSup_range]
  exact hS.sSup_mem hf (Set.range_nonempty f) (Set.forall_mem_range.mpr hfS)

/-! ### Cylinders in spaces of sequences -/

namespace PiNat

open Set Topology

variable {E : ℕ → Type*}

/-- Every neighborhood of `x` contains a cylinder around `x`. -/
lemma exists_cylinder_subset_of_mem_nhds [∀ n, TopologicalSpace (E n)]
    [∀ n, DiscreteTopology (E n)] {x : ∀ n, E n} {t : Set (∀ n, E n)} (ht : t ∈ 𝓝 x) :
    ∃ n, cylinder x n ⊆ t := by
  obtain ⟨_, ⟨y, n, rfl⟩, hxy, hyt⟩ := (isTopologicalBasis_cylinders E).mem_nhds_iff.mp ht
  exact ⟨n, by rwa [mem_cylinder_iff_eq.mp hxy]⟩

/-- A set of sequences whose membership only depends on the first `N` terms is clopen. -/
lemma isClopen_of_forall_mem_cylinder [∀ n, TopologicalSpace (E n)]
    [∀ n, DiscreteTopology (E n)] {T : Set (∀ n, E n)} {N : ℕ}
    (h : ∀ x y, y ∈ cylinder x N → (x ∈ T ↔ y ∈ T)) :
    IsClopen T := by
  have h_open (U : Set (∀ n, E n)) (hU : ∀ x y, y ∈ cylinder x N → (x ∈ U ↔ y ∈ U)) :
      IsOpen U := by
    refine isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
    filter_upwards [(isOpen_cylinder E x N).mem_nhds (self_mem_cylinder x N)] with y hy
    exact (hU x y hy).mp hx
  exact ⟨isOpen_compl_iff.mp (h_open _ fun x y hy ↦ not_congr (h x y hy)), h_open T h⟩

/-- A function of sequences that only depends on the first `N` terms has countable range. -/
lemma countable_range_of_forall_mem_cylinder [∀ n, Countable (E n)] {α : Type*}
    {F : (∀ n, E n) → α} {N : ℕ} (hF : ∀ x y, y ∈ cylinder x N → F x = F y) :
    (range F).Countable := by
  rcases isEmpty_or_nonempty (∀ n, E n) with h | h
  · rw [range_eq_empty]
    exact countable_empty
  obtain ⟨z⟩ := h
  classical
  -- extend a sequence of length `N` by the terms of `z`
  let g (u : ∀ j : Fin N, E j) : ∀ n, E n := fun j ↦ if h : j < N then u ⟨j, h⟩ else z j
  refine (countable_range (F ∘ g)).mono ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨fun j ↦ x j, (hF x _ (mem_cylinder_iff.mpr fun j hj ↦ ?_)).symm⟩
  simp [g, hj]

/-- The intersections of the cylinders of `Π n, E n` with a closed set form a compact system. -/
theorem isCompactSystem_cylinder_inter [∀ n, TopologicalSpace (E n)]
    [∀ n, DiscreteTopology (E n)] {S : Set (∀ n, E n)} (hS : IsClosed S) :
    IsCompactSystem {s : Set (∀ n, E n) | ∃ x n, s = cylinder x n ∩ S} := by
  refine IsCompactSystem.of_nonempty_iInter fun C hC h_ne ↦ ?_
  choose x n hC using hC
  choose z hz using h_ne
  have hz_mem N i (hi : i ≤ N) : z N ∈ cylinder (x i) (n i) ∩ S := by
    rw [← hC i]
    exact mem_dissipate.mp (hz N) i hi
  -- two cylinders of the family agree on the coordinates where both are defined
  have h_compat i i' j (hj : j < n i) (hj' : j < n i') : x i j = x i' j := by
    rw [← mem_cylinder_iff.mp (hz_mem (max i i') i (le_max_left _ _)).1 j hj,
      mem_cylinder_iff.mp (hz_mem (max i i') i' (le_max_right _ _)).1 j hj']
  by_cases h_bdd : BddAbove (range n)
  · -- the longest cylinder of the family is contained in all the others
    obtain ⟨i₀, hi₀⟩ := Nat.sSup_mem (range_nonempty n) h_bdd
    have h_le i : n i ≤ n i₀ := hi₀ ▸ le_csSup h_bdd ⟨i, rfl⟩
    have h₀ := hz_mem i₀ i₀ le_rfl
    refine ⟨z i₀, mem_iInter.mpr fun i ↦ ?_⟩
    rw [hC i]
    refine ⟨mem_cylinder_iff.mpr fun j hj ↦ ?_, h₀.2⟩
    rw [mem_cylinder_iff.mp h₀.1 j (hj.trans_le (h_le i)),
      h_compat _ _ _ (hj.trans_le (h_le i)) hj]
  · -- the cylinders glue into a sequence, which belongs to `S` since `S` is closed
    classical
    let y : ∀ j, E j := fun j ↦ if h : ∃ i, j < n i then x (Nat.find h) j else z 0 j
    have hy i : y ∈ cylinder (x i) (n i) := by
      refine mem_cylinder_iff.mpr fun j hj ↦ ?_
      have h : ∃ i, j < n i := ⟨i, hj⟩
      simp only [y, h, ↓reduceDIte]
      exact h_compat _ _ _ (Nat.find_spec h) hj
    have hyS : y ∈ S := by
      refine hS.closure_subset (mem_closure_iff_nhds.mpr fun t ht ↦ ?_)
      obtain ⟨k, hk⟩ := exists_cylinder_subset_of_mem_nhds ht
      obtain ⟨_, ⟨i, rfl⟩, hki⟩ := not_bddAbove_iff.mp h_bdd k
      have hzi := hz_mem i i le_rfl
      rw [← mem_cylinder_iff_eq.mp (hy i)] at hzi
      exact ⟨z i, hk (cylinder_anti y hki.le hzi.1), hzi.2⟩
    refine ⟨y, mem_iInter.mpr fun i ↦ ?_⟩
    rw [hC i]
    exact ⟨hy i, hyS⟩

/-- The cylinders of `Π n, E n` form a compact system. -/
theorem isCompactSystem_cylinders :
    IsCompactSystem {s : Set (∀ n, E n) | ∃ x n, s = cylinder x n} := by
  let (n : ℕ) : TopologicalSpace (E n) := ⊥
  have (n : ℕ) : DiscreteTopology (E n) := ⟨rfl⟩
  refine (isCompactSystem_cylinder_inter isClosed_univ).mono fun _ ⟨x, n, hs⟩ ↦ ⟨x, n, ?_⟩
  rw [hs, inter_univ]

end PiNat

namespace MeasureTheory

section CompactSystem

variable {𝓧 𝓚 : Type*} {q : Set (Set 𝓚)}

/-- A point `x` is in the projection of `⋂ n, ⋃ m, A n m ×ˢ K n m`, where the sets `K n m` belong to
a compact system, if and only if there is `σ : ℕ → ℕ` such that `x ∈ A n (σ n)` for all `n` and the
finite intersections of the sets `K n (σ n)` are nonempty. -/
lemma mem_fst_image_iInter_iUnion_prod_iff (hq : IsCompactSystem q) {A : ℕ → ℕ → Set 𝓧}
    {K : ℕ → ℕ → Set 𝓚} (hK : ∀ n m, K n m ∈ q) {x : 𝓧} :
    x ∈ Prod.fst '' ⋂ n, ⋃ m, A n m ×ˢ K n m ↔
      ∃ σ : ℕ → ℕ, (∀ N, (Set.dissipate (fun n ↦ K n (σ n)) N).Nonempty) ∧
        ∀ n, x ∈ A n (σ n) := by
  simp only [Set.mem_image, Set.mem_iInter, Set.mem_iUnion, Set.mem_prod, Prod.exists,
    exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨k, hk⟩
    choose σ hσA hσK using hk
    exact ⟨σ, fun N ↦ ⟨k, Set.mem_dissipate.mpr fun n _ ↦ hσK n⟩, hσA⟩
  · rintro ⟨σ, hσ, hσA⟩
    obtain ⟨k, hk⟩ := hq.nonempty_iInter (C := fun n ↦ K n (σ n)) (fun n ↦ hK n (σ n)) hσ
    exact ⟨k, fun n ↦ ⟨σ n, hσA n, Set.mem_iInter.mp hk n⟩⟩

/-- The set of sequences `σ : ℕ → ℕ` such that the finite intersections of the sets `K n (σ n)` are
nonempty is closed. -/
lemma isClosed_setOf_forall_dissipate_nonempty (K : ℕ → ℕ → Set 𝓚) :
    IsClosed {σ : ℕ → ℕ | ∀ N, (Set.dissipate (fun n ↦ K n (σ n)) N).Nonempty} := by
  rw [Set.ofPred_forall]
  refine isClosed_iInter fun N ↦
    (PiNat.isClopen_of_forall_mem_cylinder (N := N + 1) fun σ τ hτ ↦ ?_).isClosed
  suffices Set.dissipate (fun n ↦ K n (σ n)) N = Set.dissipate (fun n ↦ K n (τ n)) N by
    simp [this]
  ext k
  simp only [Set.mem_dissipate]
  refine forall₂_congr fun n hn ↦ ?_
  rw [PiNat.mem_cylinder_iff.mp hτ n (Nat.lt_succ_of_le hn)]

end CompactSystem

variable {X : Type*} [TopologicalSpace X] {p : Set (Set X)} {s : Set X}

/-- In a Hausdorff space, an analytic set is analytic for the paving of closed sets. -/
theorem AnalyticSet.isPavingAnalytic_isClosed [T2Space X] (hs : AnalyticSet s) :
    IsPavingAnalytic {t | IsClosed t} s := by
  rw [AnalyticSet] at hs
  rcases hs with rfl | ⟨f, hf, rfl⟩
  · exact isPavingAnalytic_empty ⟨∅, isClosed_empty⟩
  -- the graph of `f` is the intersection over `n` of the unions of the products
  -- `closure (f '' C) ×ˢ C`, where `C` ranges over the cylinders of length `n`
  have h_graph : {q : X × (ℕ → ℕ) | f q.2 = q.1} =
      ⋂ n, ⋃ y : ℕ → ℕ, closure (f '' PiNat.cylinder y n) ×ˢ PiNat.cylinder y n := by
    ext ⟨x, z⟩
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_prod]
    refine ⟨fun h n ↦ ⟨z, subset_closure ⟨z, PiNat.self_mem_cylinder z n, h⟩,
      PiNat.self_mem_cylinder z n⟩, fun h ↦ ?_⟩
    -- `x` is a cluster point of `f` at `z`, hence `x = f z`
    have hx n : x ∈ closure (f '' PiNat.cylinder z n) := by
      obtain ⟨y, hxy, hzy⟩ := h n
      rwa [PiNat.mem_cylinder_iff_eq.mp hzy]
    have h_cluster : ClusterPt x (map f (𝓝 z)) := by
      rw [clusterPt_iff_forall_mem_closure]
      intro S hS
      obtain ⟨n, hn⟩ := PiNat.exists_cylinder_subset_of_mem_nhds (mem_map.mp hS)
      exact closure_mono (image_subset_iff.mpr hn) (hx n)
    exact (eq_of_nhds_neBot (h_cluster.mono hf.continuousAt)).symm
  refine IsPavingAnalyticFor.isPavingAnalytic
    ⟨_, PiNat.isCompactSystem_cylinders, {q : X × (ℕ → ℕ) | f q.2 = q.1}, ?_, by ext; simp⟩
  rw [h_graph]
  refine countableInfClosed_prodSigmaDelta.iInf_mem fun n ↦ subset_countableInfClosure ?_
  refine countableSupClosed_countableSupClosure.iSup_mem_of_countable_range
    (PiNat.countable_range_of_forall_mem_cylinder (N := n) fun y y' hy' ↦ ?_)
    fun y ↦ subset_countableSupClosure ⟨_, isClosed_closure, _, ⟨y, n, rfl⟩, rfl⟩
  rw [PiNat.mem_cylinder_iff_eq.mp hy']

/-- The product of two analytic sets is analytic. -/
theorem AnalyticSet.prod {Y : Type*} [TopologicalSpace Y] {t : Set Y} (hs : AnalyticSet s)
    (ht : AnalyticSet t) :
    AnalyticSet (s ×ˢ t) := by
  rw [AnalyticSet] at hs ht
  rcases hs with rfl | ⟨f, hf, rfl⟩
  · simpa using analyticSet_empty
  rcases ht with rfl | ⟨g, hg, rfl⟩
  · simpa using analyticSet_empty
  rw [← range_prodMap]
  exact analyticSet_range_of_polishSpace (hf.prodMap hg)

/-- In a Hausdorff space, a set that is analytic for a paving of analytic sets is analytic. -/
theorem IsPavingAnalytic.analyticSet [T2Space X] (hp : ∀ t ∈ p, AnalyticSet t)
    (hs : IsPavingAnalytic p s) :
    AnalyticSet s := by
  obtain ⟨𝓚, q, hq, t, ht, rfl⟩ := hs
  obtain ⟨A, hA, K, hK, rfl⟩ := mem_prodSigmaDelta_iff.mp ht
  -- the closed set of sequences `σ` such that the sets `K n (σ n)` have a common point
  let S := {σ : ℕ → ℕ | ∀ N, (dissipate (fun n ↦ K n (σ n)) N).Nonempty}
  -- `s` is the projection of an analytic subset of `X × (ℕ → ℕ)`
  let E := ⋂ n, ⋃ m, A n m ×ˢ ((fun σ : ℕ → ℕ ↦ σ n) ⁻¹' {m} ∩ S)
  have hE : AnalyticSet E := AnalyticSet.iInter fun n ↦ AnalyticSet.iUnion fun m ↦
    (hp _ (hA n m)).prod (((isClosed_discrete _).preimage (continuous_apply n)).inter
      (isClosed_setOf_forall_dissipate_nonempty K)).analyticSet
  suffices Prod.fst '' ⋂ n, ⋃ m, A n m ×ˢ K n m = Prod.fst '' E by
    rw [this]
    exact hE.image_of_continuous continuous_fst
  ext x
  rw [mem_fst_image_iInter_iUnion_prod_iff hq hK]
  simp only [mem_image, mem_iInter, mem_iUnion, mem_prod, mem_inter_iff, mem_preimage,
    mem_singleton_iff, Prod.exists, exists_and_right, exists_eq_right, E]
  constructor
  · rintro ⟨σ, hσS, hσA⟩
    exact ⟨σ, fun n ↦ ⟨σ n, hσA n, rfl, hσS⟩⟩
  · rintro ⟨σ, hσ⟩
    obtain ⟨-, -, -, hσS⟩ := hσ 0
    refine ⟨σ, hσS, fun n ↦ ?_⟩
    obtain ⟨m, hm, rfl, -⟩ := hσ n
    exact hm

/-- In a Polish space, a set is analytic if and only if it is analytic for the paving of closed
sets. -/
theorem analyticSet_iff_isPavingAnalytic_isClosed [PolishSpace X] :
    AnalyticSet s ↔ IsPavingAnalytic {t | IsClosed t} s :=
  ⟨AnalyticSet.isPavingAnalytic_isClosed, IsPavingAnalytic.analyticSet fun _ ht ↦ ht.analyticSet⟩

end MeasureTheory
