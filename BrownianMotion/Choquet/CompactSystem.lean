/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Choquet.CountableClosed
public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Topology.Compactness.CompactSystem
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.Compact

/-!
# Analytic sets in the sense of a paved space


TODO: we use `IsCompactSystem`, which corresponds to semi-compact pavings for D-M. We use this and
not compact pavings (which would be the same, but for arbitrary intersections instead of countable
ones), because it's sufficient for our applications, and because it's easier to work with.

-/

@[expose] public section

open scoped ENNReal NNReal

variable {𝓧 𝓨 𝓚 : Type*} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)} {s t : Set 𝓧} {f : ℕ → Set 𝓧}

section Aux

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
    s ∈ supClosure S ↔ ∃ (t : Finset ℕ) (ht : t.Nonempty) (A : ℕ → Set α),
      (∀ n ∈ t, A n ∈ S) ∧ s = ⋃ n ∈ t, A n := by
  rw [mem_supClosure_set_iff]
  refine ⟨fun ⟨L, hL_nonempty, hL_eq, hL_subset⟩ ↦ ?_, fun ⟨t, ht_nonempty, A, hA, h_eq⟩ ↦ ?_⟩
  · sorry
  · exact ⟨t.image A, by simpa, by simpa, by simpa⟩

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

lemma isCompactSystem_Icc : IsCompactSystem {t | ∃ a b : ℝ, Set.Icc a b = t} :=
  (isCompactSystem_isCompact _).mono fun _ ⟨_, _, heq⟩ ↦ heq ▸ isCompact_Icc

namespace MeasureTheory

lemma mem_image2_prod_mono {p' : Set (Set 𝓧)} (hp : p ⊆ p') {q' : Set (Set 𝓚)}
    (hq : q ⊆ q') {s : Set (𝓧 × 𝓚)} (hs : s ∈ Set.image2 (· ×ˢ ·) p q) :
    s ∈ Set.image2 (· ×ˢ ·) p' q' := by
  simp only [Set.mem_image2] at hs
  obtain ⟨A, hpA, B, hqB, rfl⟩ := hs
  exact ⟨A, hp (hpA), B, hq (hqB), rfl⟩

lemma _root_.InfClosed.image2_prod (hp_inter : InfClosed p) (hq_inter : InfClosed q) :
    InfClosed (Set.image2 (· ×ˢ ·) p q) := by
  intro A hA B hB
  obtain ⟨u, hu, v, hv, h_eq⟩ := hA
  obtain ⟨s, hs, t, ht, h_eq'⟩ := hB
  simp only [← h_eq, ← h_eq']
  exact ⟨u ∩ s, hp_inter hu hs, v ∩ t, hq_inter hv ht, by simp; grind⟩

/-- The set is a countable intersection of countable unions of sets that can be written as a
product of two sets, each satisfying a property. -/
def prodSigmaDelta (p : Set (Set 𝓧)) (q : Set (Set 𝓚)) : Set (Set (𝓧 × 𝓚)) :=
  countableInfClosure (countableSupClosure (Set.image2 (· ×ˢ ·) p q))

lemma biUnion_finset_mem_supClosure' {s : Finset ℕ} (hs_nonempty : s.Nonempty)
    {A : ℕ → Set 𝓧} (hs : ∀ n ∈ s, A n ∈ p) :
    (⋃ n ∈ s, A n) ∈ supClosure p := by
  rw [mem_supClosure_set_iff']
  exact ⟨s, hs_nonempty, A, hs, rfl⟩

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
  simp only [mem_countableInfClosure_iff, mem_countableSupClosure_iff, Set.mem_image2,
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
  simp only [mem_countableSupClosure_iff, Set.mem_image2]
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

/-- If the set is inf-closed, elements of `countablInfClosure` can be written as countable
intersections of *antitone* sequences of sets. -/
lemma _root_.InfClosed.mem_countableInfClosure_iff (hp : InfClosed p) {s : Set 𝓧} :
    s ∈ countableInfClosure p ↔ ∃ A : ℕ → Set 𝓧, (∀ n, A n ∈ p) ∧ Antitone A ∧ s = ⋂ n, A n := by
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
  rw [mem_countableSupClosure_iff]
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

-- proved in a Mathlib PR
lemma _root_.IsCompactSystem.image2_prod (hp : IsCompactSystem p) (hq : IsCompactSystem q) :
    IsCompactSystem (Set.image2 (· ×ˢ ·) p q) := by
  sorry

-- proved in a Mathlib PR
protected lemma _root_.IsCompactSystem.countableInfClosure (hp : IsCompactSystem p) :
    IsCompactSystem (countableInfClosure p) := by
  sorry

protected lemma _root_.IsCompactSystem.infClosure (hp : IsCompactSystem p) :
    IsCompactSystem (infClosure p) := by
  refine hp.countableInfClosure.mono ?_
  -- todo: extract lemma
  exact infClosure_min subset_countableInfClosure infClosed_countableInfClosure

-- proved in a Mathlib PR
protected lemma _root_.IsCompactSystem.supClosure (hp : IsCompactSystem p) :
    IsCompactSystem (supClosure p) := by
  sorry

-- He (35.1) in the proof of 1.35
lemma fst_iInter_of_supClosure_image2_prod_of_antitone (hq_empty : ∅ ∈ q) (hq : IsCompactSystem q)
    {B : ℕ → Set (𝓧 × 𝓚)} (hB_anti : Antitone B)
    (hB : ∀ n, B n ∈ supClosure (Set.image2 (· ×ˢ ·) p q)) :
    Prod.fst '' (⋂ n, B n) = ⋂ n, Prod.fst '' B n := by
  refine le_antisymm (Set.image_iInter_subset _ _) ?_
  intro x hx
  simp_rw [mem_supClosure_set_iff'] at hB
  choose S _ DC hDC hB_eq' using hB
  choose D' hD' C' hC' hDC_eq' using hDC
  let D : ℕ → ℕ → Set 𝓧 := fun n m ↦ if hm : m ∈ S n then D' n m hm else ∅
  let C : ℕ → ℕ → Set 𝓚 := fun n m ↦ if hm : m ∈ S n then C' n m hm else ∅
  have hD : ∀ n m, m ∈ S n → p (D n m) := by
    intro n m hm
    simp only [D, dif_pos hm]
    exact hD' n m hm
  have hC : ∀ n m, m ∈ S n → q (C n m) := by
    intro n m hm
    simp only [C, dif_pos hm]
    exact hC' n m hm
  have hDC_eq : ∀ n m, m ∈ S n → DC n m = D n m ×ˢ C n m := by
    intro n m hm
    simp only [D, C, dif_pos hm]
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
  simp only [Set.dissipate, Set.le_eq_subset, Set.subset_iInter_iff]
  exact fun i hi ↦ h_anti hi

end MeasureTheory
