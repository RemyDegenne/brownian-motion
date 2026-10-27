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
* `IsCompactSystem.image`: the image of a compact system by a map `f` is a compact system if its
  sets are saturated for `f`.
* `IsCompactSystem.fst_image_iInter`: if `q` is a compact system, the projection on the first
  coordinate commutes with the intersection of a decreasing sequence of finite unions of products
  `A ×ˢ K` with `K ∈ q`.

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

lemma biUnion_finset_mem_supClosure {s : Finset ι} (hs_nonempty : s.Nonempty) {A : ι → Set α}
    (hs : ∀ i ∈ s, A i ∈ S) :
    (⋃ i ∈ s, A i) ∈ supClosure S := by
  rw [← Finset.sup_set_eq_biUnion, ← Finset.sup'_eq_sup hs_nonempty]
  exact supClosed_supClosure.finsetSup'_mem hs_nonempty fun i hi ↦ subset_supClosure (hs i hi)

@[to_dual]
lemma supClosure_subset_countableSupClosure {β : Type*} [SemilatticeSup β] {s : Set β} :
    supClosure s ⊆ countableSupClosure s :=
  supClosure_min subset_countableSupClosure countableSupClosed_countableSupClosure.supClosed

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

/-- The image of a compact system by a map `f` is a compact system if each of its sets is the
preimage by `f` of its image. -/
lemma IsCompactSystem.image {α β : Type*} {f : α → β} {S : Set (Set α)} (hS : IsCompactSystem S)
    (hf : ∀ K ∈ S, f ⁻¹' (f '' K) = K) :
    IsCompactSystem ((f '' ·) '' S) := by
  intro C hC h_empty
  choose K hK hKC using hC
  obtain rfl : C = fun i ↦ f '' K i := funext fun i ↦ (hKC i).symm
  have h_eq : ⋂ i, K i = f ⁻¹' ⋂ i, f '' K i := by
    rw [Set.preimage_iInter]
    exact Set.iInter_congr fun i ↦ (hf _ (hK i)).symm
  obtain ⟨n, hn⟩ := hS K hK (by rw [h_eq, h_empty, Set.preimage_empty])
  refine ⟨n, Set.eq_empty_of_forall_notMem fun y hy ↦ ?_⟩
  obtain ⟨k, -, rfl⟩ := Set.mem_dissipate.mp hy 0 (Nat.zero_le n)
  have hk : k ∈ Set.dissipate K n := Set.mem_dissipate.mpr fun i hi ↦ by
    rw [← hf _ (hK i)]
    exact Set.mem_dissipate.mp hy i hi
  simp [hn] at hk

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

/-- If `q i` is a compact system on `𝓚 i` for all `i`, then the sets of `Σ i, 𝓚 i` of the form
`(s : Set ι).sigma f` with `s` finite and `f i ∈ q i` for all `i` form a compact system. -/
lemma IsCompactSystem.sigma {𝓚 : ι → Type*} {q : (i : ι) → Set (Set (𝓚 i))}
    (hq : ∀ i, IsCompactSystem (q i)) :
    IsCompactSystem {t : Set (Σ i, 𝓚 i) |
      ∃ s : Finset ι, t ∈ (s : Set ι).sigma '' (Set.univ.pi q)} := by
  classical
  intro C hC hC_empty
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const] at hC
  choose s f hf hCfs using hC
  obtain rfl : C = fun b ↦ (s b : Set ι).sigma (f b) := funext fun b ↦ (hCfs b).symm
  -- for each `j`, the fibers over `j` of the first sets have empty intersection
  have key (j : ι) :
      ∃ N, ∀ x, ⟨j, x⟩ ∉ Set.dissipate (fun b ↦ (s b : Set ι).sigma (f b)) N := by
    by_cases hj : ∀ b, j ∈ s b
    · -- `q j` is a compact system and the intersection of the fibers over `j` is empty
      obtain ⟨N, hN⟩ := hq j (fun b ↦ f b j) (fun b ↦ hf b j) <| by
        refine Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_
        refine Set.eq_empty_iff_forall_notMem.mp hC_empty ⟨j, x⟩ ?_
        simp only [Set.mem_iInter, Set.mem_sigma_iff] at hx ⊢
        exact fun b ↦ ⟨hj b, hx b⟩
      refine ⟨N, fun x hx ↦ Set.eq_empty_iff_forall_notMem.mp hN x ?_⟩
      simp only [Set.mem_dissipate, Set.mem_sigma_iff] at hx ⊢
      exact fun b hb ↦ (hx b hb).2
    · -- `j ∉ s b` for some `b`
      push Not at hj
      obtain ⟨b, hb⟩ := hj
      refine ⟨b, fun x hx ↦ hb ?_⟩
      simp only [Set.mem_dissipate, Set.mem_sigma_iff] at hx
      exact (hx b le_rfl).1
  -- only the finitely many `j ∈ s 0` matter
  choose N hN using key
  refine ⟨(s 0).sup N, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro ⟨j, x⟩ hjx
  have hj0 : j ∈ s 0 := by
    simp only [Set.mem_dissipate, Set.mem_sigma_iff] at hjx
    exact (hjx 0 (Nat.zero_le _)).1
  exact hN j x (Set.antitone_dissipate (Finset.le_sup hj0) hjx)

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

/-- If `q` and `q'` are compact systems on `𝓚` and `𝓚'`, then the sets of `𝓚 ⊕ 𝓚'` whose parts
in `𝓚` and `𝓚'` are in `q` and `q'` form a compact system. -/
lemma IsCompactSystem.sum {𝓚 𝓚' : Type*} {q : Set (Set 𝓚)} {q' : Set (Set 𝓚')}
    (hq : IsCompactSystem q) (hq' : IsCompactSystem q') :
    IsCompactSystem {t | Sum.inl ⁻¹' t ∈ q ∧ Sum.inr ⁻¹' t ∈ q'} := by
  intro C hC hC_empty
  -- the parts of `C n` in `𝓚` and in `𝓚'` have finite subintersections that are empty
  obtain ⟨N, hN⟩ := hq (fun n ↦ Sum.inl ⁻¹' C n) (fun n ↦ (hC n).1)
    (by rw [← Set.preimage_iInter, hC_empty, Set.preimage_empty])
  obtain ⟨N', hN'⟩ := hq' (fun n ↦ Sum.inr ⁻¹' C n) (fun n ↦ (hC n).2)
    (by rw [← Set.preimage_iInter, hC_empty, Set.preimage_empty])
  refine ⟨max N N', Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro (x | x) hx <;> simp only [Set.mem_dissipate] at hx
  · refine Set.eq_empty_iff_forall_notMem.mp hN x ?_
    simp only [Set.mem_dissipate, Set.mem_preimage]
    exact fun i hi ↦ hx i (hi.trans (le_max_left _ _))
  · refine Set.eq_empty_iff_forall_notMem.mp hN' x ?_
    simp only [Set.mem_dissipate, Set.mem_preimage]
    exact fun i hi ↦ hx i (hi.trans (le_max_right _ _))

namespace MeasureTheory

/-- The products `A ×ˢ K` with `A ∈ p` and `K ∈ q` form an inf-closed paving if `p` and `q` are
inf-closed. -/
lemma _root_.InfClosed.image2_prod (hp_inter : InfClosed p) (hq_inter : InfClosed q) :
    InfClosed (Set.image2 (· ×ˢ ·) p q) := by
  rintro _ ⟨u, hu, v, hv, rfl⟩ _ ⟨u', hu', v', hv', rfl⟩
  exact ⟨u ∩ u', hp_inter hu hu', v ∩ v', hq_inter hv hv', Set.prod_inter_prod.symm⟩

/-- The paving of countable intersections of countable unions of products `A ×ˢ K` with `A ∈ p`
and `K ∈ q`. See `mem_prodSigmaDelta_iff`. -/
def prodSigmaDelta (p : Set (Set 𝓧)) (q : Set (Set 𝓚)) : Set (Set (𝓧 × 𝓚)) :=
  countableInfClosure (countableSupClosure (Set.image2 (· ×ˢ ·) p q))

lemma mem_countableSupClosure_image2_prod_iff {s : Set (𝓧 × 𝓚)} :
    s ∈ countableSupClosure (Set.image2 (· ×ˢ ·) p q) ↔
      ∃ A : ℕ → Set 𝓧, (∀ n, A n ∈ p) ∧ ∃ K : ℕ → Set 𝓚, (∀ n, K n ∈ q) ∧
        ⋃ n, A n ×ˢ K n = s := by
  simp only [mem_countableSupClosure_iff_iSup, Set.mem_image2, Set.iSup_eq_iUnion]
  refine ⟨fun ⟨B, hB, hs⟩ ↦ ?_, fun ⟨A, hA, K, hK, hs⟩ ↦
    ⟨fun n ↦ A n ×ˢ K n, fun n ↦ ⟨A n, hA n, K n, hK n, rfl⟩, hs⟩⟩
  choose A hA K hK hB_eq using hB
  exact ⟨A, hA, K, hK, by simp_rw [hB_eq]; exact hs⟩

lemma mem_prodSigmaDelta_iff {s : Set (𝓧 × 𝓚)} :
    s ∈ prodSigmaDelta p q ↔
      ∃ A : ℕ → ℕ → Set 𝓧, (∀ n m, A n m ∈ p) ∧ ∃ K : ℕ → ℕ → Set 𝓚, (∀ n m, K n m ∈ q) ∧
        ⋂ n, ⋃ m, A n m ×ˢ K n m = s := by
  simp only [prodSigmaDelta, mem_countableInfClosure_iff_iInf,
    mem_countableSupClosure_image2_prod_iff, Set.iInf_eq_iInter]
  refine ⟨fun ⟨B, hB, hs⟩ ↦ ?_, fun ⟨A, hA, K, hK, hs⟩ ↦
    ⟨fun n ↦ ⋃ m, A n m ×ˢ K n m, fun n ↦ ⟨A n, hA n, K n, hK n, rfl⟩, hs⟩⟩
  choose A hA K hK hB_eq using hB
  exact ⟨A, hA, K, hK, by simp_rw [hB_eq]; exact hs⟩

lemma prod_mem_prodSigmaDelta {s : Set 𝓧} {t : Set 𝓚} (hs : s ∈ p) (ht : t ∈ q) :
    s ×ˢ t ∈ prodSigmaDelta p q :=
  subset_countableInfClosure (subset_countableSupClosure (Set.mem_image2_of_mem hs ht))

@[gcongr]
lemma prodSigmaDelta_mono {p' : Set (Set 𝓧)} {q' : Set (Set 𝓚)} (hp : p ⊆ p') (hq : q ⊆ q') :
    prodSigmaDelta p q ⊆ prodSigmaDelta p' q' :=
  countableInfClosure_mono (countableSupClosure_mono (Set.image2_subset hp hq))

lemma countableInfClosed_prodSigmaDelta : CountableInfClosed (prodSigmaDelta p q) :=
  countableInfClosed_countableInfClosure

/-- The preimage of a set of `prodSigmaDelta p q` by `Prod.map g f` belongs to the
`prodSigmaDelta` of the preimage pavings. -/
lemma preimage_prodMap_mem_prodSigmaDelta {g : 𝓨 → 𝓧} {f : 𝓚' → 𝓚} {t : Set (𝓧 × 𝓚)}
    (ht : t ∈ prodSigmaDelta p q) :
    Prod.map g f ⁻¹' t ∈ prodSigmaDelta ((g ⁻¹' ·) '' p) ((f ⁻¹' ·) '' q) := by
  obtain ⟨A, hA, K, hK, rfl⟩ := mem_prodSigmaDelta_iff.mp ht
  refine mem_prodSigmaDelta_iff.mpr ⟨fun n m ↦ g ⁻¹' A n m, fun n m ↦ ⟨A n m, hA n m, rfl⟩,
    fun n m ↦ f ⁻¹' K n m, fun n m ↦ ⟨K n m, hK n m, rfl⟩, ?_⟩
  simp [Set.preimage_iInter, Set.preimage_iUnion, Set.preimage_prod_map_prod]

/-- If `S` is closed under binary suprema, the elements of its countable supremum closure are the
suprema of monotone sequences of elements of `S`. -/
lemma _root_.SupClosed.mem_countableSupClosure_iff_monotone {α : Type*} [CompleteLattice α]
    {S : Set α} {a : α} (hS : SupClosed S) :
    a ∈ countableSupClosure S ↔ ∃ t : ℕ → α, (∀ n, t n ∈ S) ∧ Monotone t ∧ ⨆ n, t n = a := by
  rw [mem_countableSupClosure_iff_iSup]
  refine ⟨fun ⟨t, ht, h⟩ ↦ ?_, fun ⟨t, ht, _, h⟩ ↦ ⟨t, ht, h⟩⟩
  -- replace `t n` by the supremum of the `t i` for `i ≤ n`
  refine ⟨fun n ↦ (Finset.Iic n).sup' Finset.nonempty_Iic t,
    fun n ↦ hS.finsetSup'_mem _ fun i _ ↦ ht i,
    fun m n hmn ↦ Finset.sup'_mono _ (Finset.Iic_subset_Iic.mpr hmn) _, ?_⟩
  rw [← h]
  exact le_antisymm (iSup_le fun n ↦ Finset.sup'_le _ _ fun i _ ↦ le_iSup _ i)
    (iSup_le fun n ↦ le_iSup_of_le n (Finset.le_sup' t (Finset.mem_Iic.mpr le_rfl)))

/-- If `S` is closed under binary infima, the elements of its countable infimum closure are the
infima of antitone sequences of elements of `S`. -/
lemma _root_.InfClosed.mem_countableInfClosure_iff_antitone {α : Type*} [CompleteLattice α]
    {S : Set α} {a : α} (hS : InfClosed S) :
    a ∈ countableInfClosure S ↔ ∃ t : ℕ → α, (∀ n, t n ∈ S) ∧ Antitone t ∧ ⨅ n, t n = a := by
  rw [mem_countableInfClosure_iff_iInf]
  refine ⟨fun ⟨t, ht, h⟩ ↦ ?_, fun ⟨t, ht, _, h⟩ ↦ ⟨t, ht, h⟩⟩
  -- replace `t n` by the infimum of the `t i` for `i ≤ n`
  refine ⟨fun n ↦ (Finset.Iic n).inf' Finset.nonempty_Iic t,
    fun n ↦ hS.finsetInf'_mem _ fun i _ ↦ ht i,
    fun m n hmn ↦ Finset.inf'_mono _ (Finset.Iic_subset_Iic.mpr hmn) _, ?_⟩
  rw [← h]
  exact le_antisymm
    (le_iInf fun n ↦ iInf_le_of_le n (Finset.inf'_le t (Finset.mem_Iic.mpr le_rfl)))
    (le_iInf fun n ↦ Finset.le_inf' _ _ fun i _ ↦ iInf_le _ i)

/-- If `p` is a compact system, then so is the set of finite intersections of sets in `p`. -/
protected lemma _root_.IsCompactSystem.infClosure (hp : IsCompactSystem p) :
    IsCompactSystem (infClosure p) :=
  hp.countableInfClosure.mono infClosure_subset_countableInfClosure

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
lemma _root_.IsCompactSystem.fst_image_iInter (hq : IsCompactSystem q)
    {B : ℕ → Set (𝓧 × 𝓚)} (hB_anti : Antitone B)
    (hB : ∀ n, B n ∈ supClosure (Set.image2 (· ×ˢ ·) p q)) :
    Prod.fst '' (⋂ n, B n) = ⋂ n, Prod.fst '' B n := by
  refine subset_antisymm (Set.image_iInter_subset _ _) fun x hx ↦ ?_
  -- the fibers of the sets `B n` over `x` are finite unions of sets of `insert ∅ q`
  have h_fiber n : {k | (x, k) ∈ B n} ∈ supClosure (insert ∅ q) := by
    refine supClosure_min (t := {t | {k | (x, k) ∈ t} ∈ supClosure (insert ∅ q)}) ?_
      (fun t ht t' ht' ↦ supClosed_supClosure ht ht') (hB n)
    rintro _ ⟨A, -, K, hK, rfl⟩
    refine subset_supClosure ?_
    by_cases hxA : x ∈ A
    · exact Set.mem_insert_of_mem _ (by simpa [hxA] using hK)
    · exact Or.inl (by simp [hxA])
  -- the fibers are nonempty and decreasing, and `supClosure (insert ∅ q)` is a compact system
  have h_nonempty n : (Set.dissipate (fun n ↦ {k | (x, k) ∈ B n}) n).Nonempty := by
    obtain ⟨⟨x', k⟩, hk, rfl⟩ := Set.mem_iInter.mp hx n
    exact ⟨k, Set.mem_dissipate.mpr fun i hi ↦ hB_anti hi hk⟩
  obtain ⟨k, hk⟩ := hq.insert_empty.supClosure.nonempty_iInter h_fiber h_nonempty
  exact ⟨(x, k), Set.mem_iInter.mpr fun n ↦ Set.mem_iInter.mp hk n, rfl⟩

end MeasureTheory
