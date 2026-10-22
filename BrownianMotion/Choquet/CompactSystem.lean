/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Order.CountableSupClosed
public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Topology.Compactness.CompactSystem
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.Compact

/-!
# Pavings and compact systems

A paving of a type `𝓧` is a set of sets of `𝓧`, `p : Set (Set 𝓧)`. This file gathers the facts
about pavings and compact systems (`IsCompactSystem`, from Mathlib) that are needed to define
analytic sets with respect to a paving and to prove Choquet's capacitability theorem.

## Main definitions

* `MeasureTheory.prodSigmaDelta p q`: the countable intersections of countable unions of products
  `A ×ˢ K` with `A ∈ p` and `K ∈ q`.

## Main statements

* `isCompactSystem_finite`: the finite sets form a compact system.
* `IsCompactSystem.sigma`: compact systems on the fibers of a sigma type give a compact system on
  the sigma type (for sets above finitely many indices).
* `IsCompactSystem.sum`: compact systems on `𝓚` and `𝓚'` give a compact system on `𝓚 ⊕ 𝓚'`.
* `MeasureTheory.fst_iInter_of_supClosure_image2_prod_of_antitone`: if `q` is a compact system,
  the projection on the first coordinate commutes with the intersection of a decreasing sequence of
  finite unions of products `A ×ˢ K` with `K ∈ q`.

## Implementation notes

We use `IsCompactSystem`, which corresponds to the semi-compact pavings of Dellacherie and Meyer,
rather than compact pavings (the same notion with arbitrary intersections instead of countable
ones): this is sufficient for our applications and easier to work with.

## References

* [S. He, J. Wang and J. Yan, *Semimartingale theory and stochastic calculus*][he2019semimartingale]
-/

@[expose] public section

variable {𝓧 𝓨 𝓚 𝓚' ι : Type*} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)} {s t : Set 𝓧} {f : ℕ → Set 𝓧}

/-! ### Auxiliary lemmas about sets and pavings -/

section Aux

lemma Set.iInter_prod {α β ι : Type*} {s : Set α} {t : ι → Set β} [hι : Nonempty ι] :
    (⋂ i, t i) ×ˢ s = ⋂ i, t i ×ˢ s := by
  ext x
  simp only [Set.mem_prod, Set.mem_iInter]
  exact ⟨fun ⟨h1, h2⟩ i ↦ ⟨h1 i, h2⟩, fun h ↦ ⟨fun i ↦ (h i).1, (h hι.some).2⟩⟩

-- TODO: unused
lemma Set.dissipate_congr {β : Type*} {s t : ℕ → Set β} {n : ℕ}
    (h_eq : ∀ m ≤ n, s m = t m) :
    Set.dissipate s n = Set.dissipate t n := by
  simp only [Set.dissipate_def]
  congr with m x
  simp only [Set.mem_iInter]
  refine ⟨fun h h_le ↦ ?_, fun h h_le ↦ ?_⟩
    <;> specialize h h_le
  · rwa [h_eq m h_le] at h
  · rwa [h_eq m h_le]

variable {α : Type*} {S : Set (Set α)}

lemma mem_supClosure_set_iff (s : Set α) :
    s ∈ supClosure S ↔ ∃ L : Finset (Set α), L.Nonempty ∧ s = ⋃₀ L ∧ ↑L ⊆ S := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, fun h ↦ ?_⟩
  · choose hL_nonempty hL_subset hL_sup using hL
    refine ⟨L, hL_nonempty, ?_, hL_subset⟩
    rw [← hL_sup, ← Finset.sup_id_set_eq_sUnion, Finset.sup'_eq_sup]
  · obtain ⟨L, hL_nonempty, hL_eq, hL_subset⟩ := h
    refine ⟨L, hL_nonempty, hL_subset, ?_⟩
    rw [hL_eq, ← Finset.sup_id_set_eq_sUnion, Finset.sup'_eq_sup]

lemma mem_infClosure_set_iff (s : Set α) :
    s ∈ infClosure S ↔ ∃ L : Finset (Set α), L.Nonempty ∧ s = ⋂₀ L ∧ ↑L ⊆ S := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, fun h ↦ ?_⟩
  · choose hL_nonempty hL_subset hL_sup using hL
    refine ⟨L, hL_nonempty, ?_, hL_subset⟩
    rw [← hL_sup, ← Finset.inf_id_set_eq_sInter, Finset.inf'_eq_inf]
  · obtain ⟨L, hL_nonempty, hL_eq, hL_subset⟩ := h
    refine ⟨L, hL_nonempty, hL_subset, ?_⟩
    rw [hL_eq, ← Finset.inf_id_set_eq_sInter, Finset.inf'_eq_inf]

lemma mem_supClosure_set_iff' (s : Set α) :
    s ∈ supClosure S ↔ ∃ (t : Finset ℕ) (_ : t.Nonempty) (A : ℕ → Set α),
      (∀ n ∈ t, A n ∈ S) ∧ s = ⋃ n ∈ t, A n := by
  rw [mem_supClosure_set_iff]
  refine ⟨fun ⟨L, hL_nonempty, hL_eq, hL_subset⟩ ↦ ?_, fun ⟨t, ht_nonempty, A, hA, h_eq⟩ ↦ ?_⟩
  · classical
    have hcard : L.toList.length = L.card := Finset.length_toList L
    refine ⟨Finset.range L.card,
      Finset.nonempty_range_iff.mpr (Finset.card_ne_zero.mpr hL_nonempty),
      fun n ↦ if h : n < L.toList.length then L.toList[n] else ∅, ?_, ?_⟩
    · intro n hn
      rw [Finset.mem_range, ← hcard] at hn
      simp only [dite_eq_left hn]
      exact hL_subset (Finset.mem_coe.mpr (Finset.mem_toList.mp (List.getElem_mem hn)))
    · ext x
      rw [hL_eq]
      simp only [Set.mem_sUnion, Finset.mem_coe, Set.mem_iUnion, Finset.mem_range, exists_prop]
      constructor
      · rintro ⟨u, hu, hxu⟩
        obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hu)
        exact ⟨n, hcard ▸ hn, by simpa only [dite_eq_left hn]⟩
      · rintro ⟨n, hn, hxn⟩
        rw [← hcard] at hn
        rw [dite_eq_left hn] at hxn
        exact ⟨_, Finset.mem_toList.mp (List.getElem_mem hn), hxn⟩
  · exact ⟨t.image A, by simpa, by simpa, by simpa⟩

-- TODO: unused
lemma mem_supClosure_insert_empty_iff (s : Set α) :
    s ∈ supClosure (insert ∅ S) ↔ ∃ L : Finset (Set α), s = ⋃₀ L ∧ ↑L ⊆ insert ∅ S := by
  rw [mem_supClosure_set_iff]
  refine ⟨fun ⟨L, hL_nonempty, hL_eq, hL_subset⟩ ↦ ⟨L, hL_eq, hL_subset⟩,
    fun ⟨L, hL_eq, hL_subset⟩ ↦ ?_⟩
  classical
  refine ⟨if L.Nonempty then L else {∅}, ?_, ?_, fun _ ↦ by simp; grind⟩
  · split_ifs
    · simpa
    · simp
  · rcases Finset.eq_empty_or_nonempty L with (rfl | hL_nonempty)
    · simpa using hL_eq
    · simpa [hL_nonempty]

-- TODO: unused
lemma mem_infClosure_insert_univ_iff (s : Set α) :
    s ∈ infClosure (insert Set.univ S) ↔
      ∃ L : Finset (Set α), s = ⋂₀ L ∧ ↑L ⊆ insert Set.univ S := by
  rw [mem_infClosure_set_iff]
  refine ⟨fun ⟨L, hL_nonempty, hL_eq, hL_subset⟩ ↦ ⟨L, hL_eq, hL_subset⟩,
    fun ⟨L, hL_eq, hL_subset⟩ ↦ ?_⟩
  refine ⟨if L.Nonempty then L else {Set.univ}, ?_, ?_, fun _ ↦ by simp; grind⟩
  · split_ifs
    · simpa
    · simp
  · rcases Finset.eq_empty_or_nonempty L with rfl | hL_nonempty
    · simpa using hL_eq
    · simpa [hL_nonempty]

end Aux

lemma isCompactSystem_singleton_empty {α : Type*} : IsCompactSystem {(∅ : Set α)} :=
  fun C hC _ ↦ ⟨0, by simpa using hC 0⟩

lemma isCompactSystem_Icc (α : Type*) [TopologicalSpace α] [T2Space α] [Preorder α]
    [CompactIccSpace α] :
    IsCompactSystem {t | ∃ a b : α, Set.Icc a b = t} :=
  (isCompactSystem_isCompact _).mono fun _ ⟨_, _, heq⟩ ↦ heq ▸ isCompact_Icc

lemma isCompactSystem_insert_empty_Icc (α : Type*) [TopologicalSpace α] [T2Space α] [Preorder α]
    [CompactIccSpace α] :
    IsCompactSystem (insert ∅ {t | ∃ a b : α, Set.Icc a b = t}) := by
  refine (isCompactSystem_isCompact α).mono fun s hs ↦ ?_
  cases hs with
  | inl h => simp [h]
  | inr h => obtain ⟨_, _, heq⟩ := h; exact heq ▸ isCompact_Icc

lemma infClosed_insert_empty_Icc {ι : Type*} [LinearOrder ι] :
    InfClosed (insert ∅ {t | ∃ a b : ι, Set.Icc a b = t}) := by
  intro s hs t ht
  cases hs with
  | inl hs => simp [hs]
  | inr hs =>
    cases ht with
    | inl ht => simp [ht]
    | inr ht =>
      obtain ⟨a₁, b₁, rfl⟩ := hs
      obtain ⟨a₂, b₂, rfl⟩ := ht
      refine Set.mem_insert_of_mem _ ?_
      simp only [Set.inf_eq_inter, Set.mem_ofPred_eq]
      exact ⟨a₁ ⊔ a₂, b₁ ⊓ b₂, Set.Icc_inter_Icc.symm⟩

/-- The finite sets form a compact system. -/
lemma isCompactSystem_finite (𝓚 : Type*) : IsCompactSystem {t : Set 𝓚 | t.Finite} :=
  letI : TopologicalSpace 𝓚 := ⊥
  haveI : DiscreteTopology 𝓚 := ⟨rfl⟩
  (isCompactSystem_isCompact 𝓚).mono fun _ ht ↦ ht.isCompact

/-- The preimage of a compact system by a surjective map is a compact system. -/
lemma IsCompactSystem.preimage_of_surjective {f : 𝓚' → 𝓚} (hf : Function.Surjective f)
    {S : Set (Set 𝓚')} (hS : IsCompactSystem S) :
    IsCompactSystem {t : Set 𝓚 | f ⁻¹' t ∈ S} := by
  intro D hD hD_empty
  obtain ⟨N, hN⟩ := hS (fun i ↦ f ⁻¹' D i) hD (by rw [← Set.preimage_iInter, hD_empty]; rfl)
  refine ⟨N, hf.preimage_injective.eq_iff.1 ?_⟩
  simpa [Set.dissipate, Set.preimage_iInter] using hN

lemma Set.iInter_sigma_eq_empty_iff {𝓚 : ι → Type*} {β : Type*} (s : β → Set ι)
    (f : β → (i : ι) → Set (𝓚 i)) :
     ⋂ b, (s b).sigma (f b) = ∅ ↔ ∀ i ∈ ⋂ b, s b, ⋂ b, f b i = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_iInter, Set.mem_sigma_iff]
  exact ⟨fun h i hi x hx => h ⟨i, x⟩ fun b => ⟨hi b, hx b⟩,
    fun h ⟨i, x⟩ hx => h i (fun b => (hx b).1) x (fun b => (hx b).2)⟩

/-- Variant with an additional condition `p b` (e.g. `b ≤ n` for `dissipate`). -/
lemma Set.iInter₂_sigma_eq_empty_iff {𝓚 : ι → Type*} {β : Type*} {p : β → Prop}
    (s : β → Set ι) (f : β → (i : ι) → Set (𝓚 i)) :
    ⋂ (b) (_ : p b), (s b).sigma (f b) = ∅ ↔
      ∀ i ∈ ⋂ (b) (_ : p b), s b, ⋂ (b) (_ : p b), f b i = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_iInter, Set.mem_sigma_iff]
  exact ⟨fun h i hi x hx => h ⟨i, x⟩ fun b hb => ⟨hi b hb, hx b hb⟩,
    fun h ⟨i, x⟩ hx => h i (fun b hb => (hx b hb).1) x (fun b hb => (hx b hb).2)⟩

lemma IsCompactSystem.sigma {𝓚 : ι → Type*} {q : (i : ι) → Set (Set (𝓚 i))}
    (hq : ∀ i, IsCompactSystem (q i)) :
    IsCompactSystem {t : Set (Σ i, 𝓚 i) |
      ∃ s : Finset ι, t ∈ (s : Set ι).sigma '' (Set.univ.pi q)} := by
  classical
  intro C hC hC_empty
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_pi, Set.mem_univ,
    forall_const] at hC
  choose s f hf hCfs using hC
  simp_rw [Set.dissipate, ← hCfs]
  simp_rw [← hCfs, Set.iInter_sigma_eq_empty_iff] at hC_empty
  by_cases h : ⋂ b, (s b : Set ι) = ∅
  · obtain ⟨n₀, hn₀⟩ := isCompactSystem_finite ι (fun b => (s b : Set ι))
      (fun b => (s b).finite_toSet) h
    refine ⟨n₀, ?_⟩
    rw [Set.dissipate] at hn₀
    simp_rw [Set.iInter₂_sigma_eq_empty_iff, hn₀]
    simp
  · have hs : (s 0).Nonempty := by
      rw [← Finset.coe_nonempty, Set.nonempty_iff_ne_empty]
      exact fun h0 => h <| Set.subset_eq_empty (Set.iInter_subset _ 0) h0
    obtain ⟨j₀, hj₀⟩ := hs
    classical
    have key₀ : ∀ j ∈ ⋂ b, s b, ∃ N,
        ⋂ (b ≤ N), f b j = ∅ := by
      intro j hj
      exact hq j (f · j) (fun i ↦ hf i j) (hC_empty j hj)
    have key₁ : ∀ j ∉ ⋂ b, s b, ∃ N, j ∉ s N := by
      intro j hj
      simpa [Set.mem_iInter, not_forall] using hj
    -- For each j ∈ s 0, find N(j) such that the fibre over j in the bounded sigma is empty.
    have key : ∀ j ∈ s 0, ∃ N,
        ∀ x, (⟨j, x⟩ : Σ k, 𝓚 k) ∉ ⋂ y, ⋂ (_ : y ≤ N), (s y : Set ι).sigma (f y) := by
      intro j _
      by_cases hjs : j ∈ ⋂ b, s b
      · obtain ⟨N, hN⟩ := key₀ j hjs
        refine ⟨N, fun x hx => ?_⟩
        have hxslice : x ∈ ⋂ b, ⋂ _ : b ≤ N, f b j := by
          simp only [Set.mem_iInter, Set.mem_sigma_iff] at hx ⊢
          exact fun b hb => (hx b hb).2
        rw [hN] at hxslice; exact hxslice
      · obtain ⟨b, hb⟩ := key₁ j hjs
        refine ⟨b, fun x hx => ?_⟩
        have : (⟨j, x⟩ : Σ k, 𝓚 k) ∈ (s b : Set ι).sigma (f b) :=
          (Set.mem_iInter.mp (Set.mem_iInter.mp hx b) le_rfl)
        exact hb (Finset.mem_coe.mp (Set.mem_sigma_iff.mp this).1)
    choose N hN using key
    use (s 0).attach.sup fun jh => N jh.val jh.prop
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨j, x⟩ hjx
    have hj0 : j ∈ s 0 := by
      have : (⟨j, x⟩ : Σ k, 𝓚 k) ∈ (s 0 : Set ι).sigma (f 0) :=
        Set.mem_iInter.mp (Set.mem_iInter.mp hjx 0) (Nat.zero_le _)
      exact Finset.mem_coe.mp (Set.mem_sigma_iff.mp this).1
    have hle : N j hj0 ≤ ((s 0).attach.sup fun jh => N jh.val jh.prop) :=
      Finset.le_sup (f := fun jh : { x // x ∈ s 0 } => N jh.val jh.prop)
        (Finset.mem_attach _ ⟨j, hj0⟩)
    exact hN j hj0 x
      (Set.iInter₂_mono' (fun b' j' => ⟨b', j'.trans hle, Set.Subset.rfl⟩) hjx)

/-- Variant of `IsCompactSystem.sigma` for a finite index type, with sets above all indices. -/
lemma IsCompactSystem.univ_sigma [Finite ι] {𝓚 : ι → Type*}
    {q : (i : ι) → Set (Set (𝓚 i))} (hq : ∀ i, IsCompactSystem (q i)) :
    IsCompactSystem (Set.univ.sigma '' (Set.univ.pi q)) := by
  have : Fintype ι := Fintype.ofFinite ι
  intro C hC hC_empty
  refine IsCompactSystem.sigma hq C (fun i => ?_) hC_empty
  obtain ⟨f, hf, hfC⟩ := hC i
  refine ⟨(Finset.univ : Finset ι), f, fun j _ => hf j (Set.mem_univ _), ?_⟩
  rw [Finset.coe_univ]; exact hfC

lemma IsCompactSystem.sum.{u} {𝓚 𝓚' : Type u} {q : Set (Set 𝓚)} {q' : Set (Set 𝓚')}
    (hq : IsCompactSystem q) (hq' : IsCompactSystem q') :
    IsCompactSystem {t | Sum.inl ⁻¹' t ∈ q ∧ Sum.inr ⁻¹' t ∈ q'} := by
  let Q : ∀ b : Bool, Set (Set (bif b then 𝓚' else 𝓚)) :=
    fun b => match b with | true => q' | false => q
  have hQ : ∀ b, IsCompactSystem (Q b) := fun b => by cases b <;> assumption
  have h_equiv := (IsCompactSystem.univ_sigma hQ).preimage_of_surjective
    (Equiv.sumEquivSigmaBool 𝓚 𝓚').symm.surjective
  convert h_equiv using 1
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const]
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨fun | true => Sum.inr ⁻¹' t | false => Sum.inl ⁻¹' t,
      fun | true => hr | false => hl,
      by ext ⟨b, x⟩; cases b <;> · simp [Equiv.sumEquivSigmaBool]⟩
  · rintro ⟨f, hf, hfC⟩
    have slice : ∀ b x, x ∈ f b ↔ (Equiv.sumEquivSigmaBool 𝓚 𝓚').symm ⟨b, x⟩ ∈ t :=
      fun b x => by simpa using Set.ext_iff.mp hfC ⟨b, x⟩
    constructor
    · specialize hf false
      simp only [Bool.cond_false] at hf
      convert hf using 1
      ext x
      exact (slice false x).symm
    · specialize hf true
      simp only [Bool.cond_true] at hf
      convert hf using 1
      ext x
      exact (slice true x).symm

namespace MeasureTheory

lemma _root_.InfClosed.image2_prod (hp_inter : InfClosed p) (hq_inter : InfClosed q) :
    InfClosed (Set.image2 (· ×ˢ ·) p q) := by
  intro A hA B hB
  obtain ⟨u, hu, v, hv, h_eq⟩ := hA
  obtain ⟨s, hs, t, ht, h_eq'⟩ := hB
  simp only [← h_eq, ← h_eq']
  exact ⟨u ∩ s, hp_inter hu hs, v ∩ t, hq_inter hv ht, by simp; grind⟩

/-- The paving of countable intersections of countable unions of products `A ×ˢ K` with `A ∈ p`
and `K ∈ q`. See `mem_prodSigmaDelta_iff`. -/
def prodSigmaDelta (p : Set (Set 𝓧)) (q : Set (Set 𝓚)) : Set (Set (𝓧 × 𝓚)) :=
  countableInfClosure (countableSupClosure (Set.image2 (· ×ˢ ·) p q))

lemma biUnion_finset_mem_supClosure' {s : Finset ℕ} (hs_nonempty : s.Nonempty)
    {A : ℕ → Set 𝓧} (hs : ∀ n ∈ s, A n ∈ p) :
    (⋃ n ∈ s, A n) ∈ supClosure p := by
  rw [mem_supClosure_set_iff']
  exact ⟨s, hs_nonempty, A, hs, rfl⟩

-- TODO: unused
lemma biUnion_finset_mem_supClosure {s : Finset ℕ} (hs_nonempty : s.Nonempty) {A : ℕ → Set 𝓧}
    (hs : ∀ n ∈ s, A n ∈ supClosure p) :
    (⋃ n ∈ s, A n) ∈ supClosure p := by
  have := biUnion_finset_mem_supClosure' hs_nonempty hs
  rwa [supClosure_idem] at this

lemma mem_prodSigmaDelta_iff {s : Set (𝓧 × 𝓚)} :
    s ∈ prodSigmaDelta p q ↔
      ∃ (A : ℕ → ℕ → Set 𝓧) (_ : ∀ n m, A n m ∈ p) (K : ℕ → ℕ → Set 𝓚) (_ : ∀ n m, K n m ∈ q),
        s = ⋂ n, ⋃ m, A n m ×ˢ K n m := by
  unfold prodSigmaDelta
  simp only [mem_countableInfClosure_iff_iInf, mem_countableSupClosure_iff_iSup, Set.mem_image2,
    Set.iSup_eq_iUnion, Set.iInf_eq_iInter, exists_prop]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · choose A hA hs using h
    choose B hB hB' using hA
    choose C hC hC' using hB
    choose D hD hD' using hC'
    refine ⟨C, hC, D, hD, ?_⟩
    rw [← hs]
    simp_rw [hD', ← hB']
  · obtain ⟨A, hA, K, hK, rfl⟩ := h
    refine ⟨fun n ↦ ⋃ m, A n m ×ˢ K n m, fun n ↦ ⟨fun m ↦ A n m ×ˢ K n m, fun m ↦ ?_, rfl⟩, rfl⟩
    exact ⟨A n m, hA n m, ⟨K n m, hK n m, rfl⟩⟩

lemma mem_countableSupClosure_image2_prod_iff {s : Set (𝓧 × 𝓚)} :
    s ∈ countableSupClosure (Set.image2 (· ×ˢ ·) p q) ↔
      ∃ (A : ℕ → Set 𝓧) (_ : ∀ n, A n ∈ p) (K : ℕ → Set 𝓚) (_ : ∀ n, K n ∈ q),
        s = ⋃ n, A n ×ˢ K n := by
  simp only [mem_countableSupClosure_iff_iSup, Set.mem_image2]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · choose A hA hs using h
    choose B hB C hC hA_eq using hA
    refine ⟨B, hB, C, hC, ?_⟩
    simp_rw [← hs, hA_eq]
    rfl
  · obtain ⟨A, hA, K, hK, rfl⟩ := h
    exact ⟨fun n ↦ A n ×ˢ K n, fun n ↦ ⟨A n, hA n, K n, hK n, rfl⟩, rfl⟩

lemma mem_prodSigmaDelta_of_mem {s : Set 𝓧} {t : Set 𝓚} (hs : s ∈ p) (hq : t ∈ q) :
    s ×ˢ t ∈ prodSigmaDelta p q := by
  rw [mem_prodSigmaDelta_iff]
  exact ⟨fun n m ↦ s, fun _ _ ↦ hs, fun n m ↦ t, fun _ _ ↦ hq, by
    simp [Set.iInter_const, Set.iUnion_const]⟩

lemma prodSigmaDelta.mono {p' : Set (Set 𝓧)} {q' : Set (Set 𝓚)} (hp : p ⊆ p') (hq : q ⊆ q')
    {s : Set (𝓧 × 𝓚)} (hs : s ∈ prodSigmaDelta p q) :
    s ∈ prodSigmaDelta p' q' := by
  simp_rw [mem_prodSigmaDelta_iff] at hs ⊢
  obtain ⟨A, hA, K, hK, rfl⟩ := hs
  exact ⟨A, fun n m ↦ hp (hA n m), K, fun n m ↦ hq (hK n m), rfl⟩

/-- If the paving is inf-closed, elements of `countableInfClosure` can be written as countable
intersections of *antitone* sequences of sets. -/
protected
lemma _root_.InfClosed.mem_countableInfClosure_iff (hp : InfClosed p) {s : Set 𝓧} :
    s ∈ countableInfClosure p ↔ ∃ A : ℕ → Set 𝓧, (∀ n, A n ∈ p) ∧ Antitone A ∧ s = ⋂ n, A n := by
  rw [mem_countableInfClosure_iff_iInf]
  refine ⟨fun h ↦ ?_, fun ⟨A, hA, _, h_eq⟩ ↦ ⟨A, hA, h_eq.symm⟩⟩
  choose A hA hs using h
  refine ⟨Set.dissipate A, fun n ↦ ?_, Set.antitone_dissipate, ?_⟩
  · induction n with
    | zero => simp [hA]
    | succ n hn =>
      rw [Set.dissipate_succ]
      exact hp hn (hA _)
  · rw [Set.iInter_dissipate, ← hs]
    rfl

/-- If the set is sup-closed, elements of `countableSupClosure` can be written as countable
unions of *monotone* sequences of sets. -/
protected
lemma _root_.SupClosed.mem_countableSupClosure_iff (hp : SupClosed p) {s : Set 𝓧} :
    s ∈ countableSupClosure p ↔ ∃ A : ℕ → Set 𝓧, (∀ n, A n ∈ p) ∧ Monotone A ∧ s = ⋃ n, A n := by
  rw [mem_countableSupClosure_iff_iSup]
  simp only [Set.iSup_eq_iUnion]
  refine ⟨fun h ↦ ?_, fun ⟨A, hA, _, h_eq⟩ ↦ ⟨A, hA, h_eq.symm⟩⟩
  choose A hA hs using h
  refine ⟨Set.accumulate A, fun n ↦ ?_, Set.monotone_accumulate, ?_⟩
  · induction n with
    | zero => simp [hA]
    | succ n hn =>
      rw [Set.accumulate_succ]
      exact hp hn (hA _)
  · rw [Set.iUnion_accumulate, ← hs]

protected lemma _root_.IsCompactSystem.infClosure (hp : IsCompactSystem p) :
    IsCompactSystem (infClosure p) := by
  refine hp.countableInfClosure.mono ?_
  -- todo: extract lemma
  exact infClosure_min subset_countableInfClosure infClosed_countableInfClosure

/-- If `p` is closed under binary unions and contains `∅`, then the projection on the first
coordinate of a finite union of products `A ×ˢ K` with `A ∈ p` is in `p`. -/
lemma fst_image_mem_of_mem_supClosure_image2_prod (hp_empty : ∅ ∈ p) (hp_union : SupClosed p)
    {s : Set (𝓧 × 𝓚)} (hs : s ∈ supClosure (Set.image2 (· ×ˢ ·) p q)) :
    Prod.fst '' s ∈ p := by
  refine supClosure_min (t := {s | Prod.fst '' s ∈ p}) ?_ (fun s hs t ht ↦ ?_) hs
  · rintro _ ⟨A, hA, K, -, rfl⟩
    rcases K.eq_empty_or_nonempty with rfl | hK
    · simpa
    · simpa [Set.fst_image_prod _ hK]
  · simpa [Set.image_union] using hp_union hs ht

/-- If `q` is a compact system, the projection on the first coordinate commutes with the
intersection of a decreasing sequence of finite unions of products `A ×ˢ K` with `K ∈ q`.

This is equation (35.1) in the proof of Theorem 1.35 of [he2019semimartingale]. -/
lemma fst_iInter_of_supClosure_image2_prod_of_antitone (hq : IsCompactSystem q)
    {B : ℕ → Set (𝓧 × 𝓚)} (hB_anti : Antitone B)
    (hB : ∀ n, B n ∈ supClosure (Set.image2 (· ×ˢ ·) p q)) :
    Prod.fst '' (⋂ n, B n) = ⋂ n, Prod.fst '' B n := by
  -- we can assume that `∅ ∈ q`, by replacing `q` with `insert ∅ q`
  wlog hq_empty : ∅ ∈ q generalizing q
  · exact this hq.insert_empty
      (fun n ↦ supClosure_mono (Set.image2_subset_left (Set.subset_insert _ _)) (hB n)) (by simp)
  refine le_antisymm (Set.image_iInter_subset _ _) ?_
  intro x hx
  simp_rw [mem_supClosure_set_iff'] at hB
  choose S _ DC hDC hB_eq' using hB
  choose D' hD' C' hC' hDC_eq' using hDC
  let D : ℕ → ℕ → Set 𝓧 := fun n m ↦ if hm : m ∈ S n then D' n m hm else ∅
  let C : ℕ → ℕ → Set 𝓚 := fun n m ↦ if hm : m ∈ S n then C' n m hm else ∅
  have hD : ∀ n m, m ∈ S n → D n m ∈ p := by
    intro n m hm
    simp only [D, dite_eq_left hm]
    exact hD' n m hm
  have hC : ∀ n m, m ∈ S n → C n m ∈ q := by
    intro n m hm
    simp only [C, dite_eq_left hm]
    exact hC' n m hm
  have hDC_eq : ∀ n m, m ∈ S n → DC n m = D n m ×ˢ C n m := by
    intro n m hm
    simp only [D, C, dite_eq_left hm]
    exact (hDC_eq' n m hm).symm
  have hB_eq n : B n = ⋃ m ∈ S n, D n m ×ˢ C n m := by
    rw [hB_eq']
    congr with m
    by_cases hm : m ∈ S n
    · simp [hDC_eq n m hm]
    · simp [hm]
  suffices (({x} ×ˢ .univ) ∩ ⋂ n, B n).Nonempty by
    obtain ⟨u, ⟨hu_left, hu_right⟩⟩ := this
    simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true] at hu_left
    rw [← hu_left, Set.mem_image]
    exact ⟨u, hu_right, rfl⟩
  let C'' n := ⋃ (m) (hm : m ∈ S n) (hx : x ∈ D n m), C n m -- `C'' n` is `C_n` in the book
  have h_inter n : ({x} ×ˢ .univ) ∩ B n = {x} ×ˢ C'' n := by
    simp_rw [C'', hB_eq n, Set.inter_iUnion, Set.prod_iUnion]
    congr with m
    by_cases hm : m ∈ S n
    · by_cases hx : x ∈ D n m <;> simp <;> grind
    · simp [hm]
  have h_eq_C'' : {x} ×ˢ Set.univ ∩ ⋂ n, B n = {x} ×ˢ ⋂ n, C'' n := by
    simp_rw [Set.inter_iInter, h_inter, Set.prod_iInter]
  rw [h_eq_C'']
  suffices (⋂ n, C'' n).Nonempty by
    simpa only [Set.prod_nonempty_iff, Set.singleton_nonempty, true_and]
  have h_anti : Antitone C'' := by
    have h_eq : C'' = fun n ↦ Prod.snd '' ({x} ×ˢ .univ ∩ B n) := by
      ext n
      simp [h_inter n]
    rw [h_eq]
    intro n m hnm
    refine Set.image_mono ?_
    simp only [Set.subset_inter_iff, Set.inter_subset_left, true_and]
    exact Set.inter_subset_right.trans (hB_anti hnm)
  have hC''q n : C'' n ∈ supClosure q := by
    simp only [C'']
    rcases Finset.eq_empty_or_nonempty (S n) with hS_empty | hS_nonempty
    · simp only [hS_empty, Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
      exact subset_supClosure hq_empty
    refine biUnion_finset_mem_supClosure' hS_nonempty fun m hm ↦ ?_
    by_cases hx : x ∈ D n m
    · simp only [hx, Set.iUnion_true]
      exact hC n m hm
    · simpa [hx, Set.iUnion_of_empty]
  -- `C'' n` is nonempty for all `n` since `x` is in the intersection of the `B n`,
  -- and if it were empty, then the intersection would be empty, contradiction
  have hC''_nonempty n : (C'' n).Nonempty := by
    specialize h_inter n
    by_contra! hC_empty
    simp only [hC_empty, Set.prod_empty] at h_inter
    suffices x ∈ Prod.fst '' ({x} ×ˢ Set.univ ∩ B n) by simp [h_inter] at this
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ,
      and_true, Prod.exists, exists_and_right, exists_and_left, exists_eq_right, true_and]
    simp only [Set.mem_iInter, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right] at hx
    exact hx n
  -- use that `supClosure q` is a compact system
  -- if the intersection is empty, there is a finite subintersection that is empty
  -- that subintersection is just `C'' n` for some `n` since `C''` is antitone,
  -- so `C'' n` is empty, contradiction
  have hq_compact' := hq.supClosure
  refine hq_compact'.nonempty_iInter hC''q fun n ↦ ?_
  -- todo: dissipate_of_antitone?
  convert hC''_nonempty n using 1
  refine le_antisymm (Set.dissipate_subset le_rfl) ?_
  simp only [Set.dissipate, Set.subset_iInter_iff]
  exact fun i hi ↦ h_anti hi

end MeasureTheory
