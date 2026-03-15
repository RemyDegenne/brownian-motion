/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Data.Set.Dissipate
import KolmogorovExtension4.CompactSystem

/-!
# Analytic sets in the sense of a paved space


TODO: we use `IsCompactSystem`, which corresponds to semi-compact pavings for D-M. We use this and
not compact pavings (which would be the same, but for arbitrary intersections instead of countable
ones), because it's sufficient for our applications, and because it's easier to work with.

-/

open scoped ENNReal NNReal

variable {𝓧 𝓨 𝓚 : Type*} {p : Set 𝓧 → Prop} {q : Set 𝓚 → Prop} {s t : Set 𝓧} {f : ℕ → Set 𝓧}

namespace MeasureTheory

lemma Set.dissipate_eq_iInter_Iic {β : Type*} (s : ℕ → Set β) (n : ℕ) :
    Set.dissipate s n = ⋂ y ∈ Finset.Iic n, s y := by simp [Set.dissipate_def]

lemma _root_.isCompactSystem_isCompact_isClosed [TopologicalSpace 𝓧] :
    IsCompactSystem (fun K : Set 𝓧 ↦ IsCompact K ∧ IsClosed K) := by
  intro C hC_cc hC_inter
  by_contra! h_nonempty
  refine absurd hC_inter ?_
  rw [← ne_eq, ← Set.nonempty_iff_ne_empty, ← Set.iInter_dissipate]
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (Set.dissipate C)
    (fun n ↦ ?_) (fun n ↦ ?_) ?_ (fun n ↦ ?_)
  · exact Set.antitone_dissipate (by lia)
  · simp only [Set.dissipate_eq_iInter_Iic]
    exact h_nonempty _
  · simp only [Set.dissipate_zero_nat]
    exact (hC_cc 0).1
  · induction n with
    | zero => simp only [Set.dissipate_zero_nat]; exact (hC_cc 0).2
    | succ n hn =>
      rw [Set.dissipate_succ]
      exact hn.inter (hC_cc (n + 1)).2

lemma _root_.isCompactSystem_isCompact [TopologicalSpace 𝓧] [T2Space 𝓧] :
    IsCompactSystem (fun K : Set 𝓧 ↦ IsCompact K) := by
  convert isCompactSystem_isCompact_isClosed with s
  exact ⟨fun hs ↦ ⟨hs, hs.isClosed⟩, fun hs ↦ hs.1⟩

lemma _root_.IsCompactSystem.mono {q' : Set 𝓚 → Prop} (hq : IsCompactSystem q)
    (h_mono : ∀ s, q' s → q s) :
    IsCompactSystem q' :=
  fun C hC_cc hC_inter ↦ hq C (fun i ↦ h_mono (C i) (hC_cc i)) hC_inter

/-- Product of two sets of sets. -/
def memProd (p : Set 𝓧 → Prop) (q : Set 𝓚 → Prop) : Set (𝓧 × 𝓚) → Prop :=
  fun s ↦ ∃ A B, p A ∧ q B ∧ s = A ×ˢ B

lemma memProd_prod {A : Set 𝓧} {B : Set 𝓚} (hp : p A) (hq : q B) : memProd p q (A ×ˢ B) :=
  ⟨A, B, hp, hq, rfl⟩

lemma memProd.mono {p' : Set 𝓧 → Prop} (hp : ∀ s, p s → p' s) {q' : Set 𝓚 → Prop}
    (hq : ∀ s, q s → q' s) {s : Set (𝓧 × 𝓚)} (hs : memProd p q s) :
    memProd p' q' s := by
  obtain ⟨A, B, hpA, hqB, rfl⟩ := hs
  exact ⟨A, B, hp _ hpA, hq _ hqB, rfl⟩

/-- The set is a countable union of sets that satisfy the property. -/
def memSigma (p : Set 𝓧 → Prop) : Set 𝓧 → Prop :=
  fun s ↦ ∃ A : ℕ → Set 𝓧, (∀ n, p (A n)) ∧ s = ⋃ n, A n

lemma memSigma_of_prop (hs : p s) : memSigma p s :=
  ⟨fun _ ↦ s, by simp [hs, Set.iUnion_const]⟩

lemma memSigma.union (hs : memSigma p s) (ht : memSigma p t) :
    memSigma p (s ∪ t) := by
  obtain ⟨A, hA, rfl⟩ := hs
  obtain ⟨B, hB, rfl⟩ := ht
  sorry

/-- The set is a countable intersection of sets that satisfy the property. -/
def memDelta (p : Set 𝓧 → Prop) : Set 𝓧 → Prop :=
  fun s ↦ ∃ A : ℕ → Set 𝓧, (∀ n, p (A n)) ∧ s = ⋂ n, A n

lemma memDelta_of_prop (hs : p s) : memDelta p s :=
  ⟨fun _ ↦ s, by simp [hs, Set.iInter_const]⟩

lemma memDelta.iInter {s : ℕ → Set 𝓧} (hs : ∀ n, memDelta p (s n)) :
    memDelta p (⋂ n, s n) := by
  sorry

lemma memDelta.inter (hs : memDelta p s) (ht : memDelta p t) :
    memDelta p (s ∩ t) := by
  sorry

/-- The set is a countable intersection of countable unions of sets that can be written as a
product of two sets, each satisfying a property. -/
def memProdSigmaDelta (p : Set 𝓧 → Prop) (q : Set 𝓚 → Prop) : Set (𝓧 × 𝓚) → Prop :=
  memDelta (memSigma (memProd p q))

/-- The set is a finite intersection of sets that satisfy the property. -/
def memFiniteInter (p : Set 𝓧 → Prop) : Set 𝓧 → Prop :=
  fun s ↦ ∃ (t : Finset ℕ) (A : ℕ → Set 𝓧), (∀ n ∈ t, p (A n)) ∧ s = ⋂ n ∈ t, A n

lemma memFiniteInter_of_prop (hs : p s) : memFiniteInter p s :=
  ⟨{0}, fun _ ↦ s, by simp [hs]⟩

lemma memFiniteInter.inter (hs : memFiniteInter p s) (ht : memFiniteInter p t) :
    memFiniteInter p (s ∩ t) := by
  obtain ⟨S, A, hA, rfl⟩ := hs
  obtain ⟨T, B, hB, rfl⟩ := ht
  sorry

/-- The set is a finite union of sets that satisfy the property. -/
def memFiniteUnion (p : Set 𝓧 → Prop) : Set 𝓧 → Prop :=
  fun s ↦ ∃ (t : Finset ℕ) (A : ℕ → Set 𝓧), (∀ n ∈ t, p (A n)) ∧ s = ⋃ n ∈ t, A n

lemma memFiniteUnion_of_prop (hs : p s) : memFiniteUnion p s :=
  ⟨{0}, fun _ ↦ s, by simp [hs]⟩

lemma memFiniteUnion.union (hs : memFiniteUnion p s) (ht : memFiniteUnion p t) :
    memFiniteUnion p (s ∪ t) := by
  obtain ⟨S, A, hA, rfl⟩ := hs
  obtain ⟨T, B, hB, rfl⟩ := ht
  sorry

lemma memProdSigmaDelta_iff {s : Set (𝓧 × 𝓚)} :
    memProdSigmaDelta p q s ↔
      ∃ (A : ℕ → ℕ → Set 𝓧) (K : ℕ → ℕ → Set 𝓚)
        (_ : ∀ n m, p (A n m)) (_ : ∀ n m, q (K n m)),
        s = ⋂ n, ⋃ m, A n m ×ˢ K n m := by
  simp only [memProdSigmaDelta, memDelta, memSigma, memProd, exists_and_left, exists_prop]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · choose A hA hs using h
    choose B hB hB' using hA
    choose C hC hC' using hB
    choose D hD hD' using hC'
    refine ⟨C, D, hD, hC, ?_⟩
    rw [hs]
    simp_rw [hB', hD']
  · obtain ⟨A, K, hK, hA, rfl⟩ := h
    refine ⟨fun n ↦ ⋃ m, A n m ×ˢ K n m, fun n ↦ ⟨fun m ↦ A n m ×ˢ K n m, fun m ↦ ?_, rfl⟩, rfl⟩
    exact ⟨A n m, hA n m, ⟨K n m, hK n m, rfl⟩⟩

lemma memProdSigmaDelta_of_prop {s : Set 𝓧} {t : Set 𝓚} (hs : p s) (hq : q t) :
    memProdSigmaDelta p q (s ×ˢ t) := by
  rw [memProdSigmaDelta_iff]
  exact ⟨fun n m ↦ s, fun n m ↦ t, fun _ _ ↦ hs, fun _ _ ↦ hq, by
    simp [Set.iInter_const, Set.iUnion_const]⟩

lemma memProdSigmaDelta.mono {p' : Set 𝓧 → Prop} (hp : ∀ s, p s → p' s) {q' : Set 𝓚 → Prop}
    (hq : ∀ s, q s → q' s) {s : Set (𝓧 × 𝓚)} (hs : memProdSigmaDelta p q s) :
    memProdSigmaDelta p' q' s := by
  simp_rw [memProdSigmaDelta_iff] at hs ⊢
  obtain ⟨A, K, hA, hK, rfl⟩ := hs
  refine ⟨A, K, fun n m ↦ hp _ (hA n m), fun n m ↦ hq _ (hK n m), rfl⟩

lemma memDelta_iff_of_inter (hp : ∀ s t, p s → p t → p (s ∩ t)) {s : Set 𝓧} :
    memDelta p s ↔ ∃ A : ℕ → Set 𝓧, (∀ n, p (A n)) ∧ Antitone A ∧ s = ⋂ n, A n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · obtain ⟨A, hA, _, rfl⟩ := h
    exact ⟨A, hA, rfl⟩
  · choose A hA hs using h
    refine ⟨Set.dissipate A, fun n ↦ ?_, Set.antitone_dissipate, ?_⟩
    · induction n with
    | zero => simp [hA]
    | succ n hn =>
      rw [Set.dissipate_succ]
      exact hp _ _ hn (hA _)
    · rwa [Set.iInter_dissipate]

lemma memSigma_iff_of_union (hp : ∀ s t, p s → p t → p (s ∪ t)) {s : Set 𝓧} :
    memSigma p s ↔ ∃ A : ℕ → Set 𝓧, (∀ n, p (A n)) ∧ Monotone A ∧ s = ⋃ n, A n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · obtain ⟨A, hA, _, rfl⟩ := h
    exact ⟨A, hA, rfl⟩
  · choose A hA hs using h
    refine ⟨Set.accumulate A, fun n ↦ ?_, Set.monotone_accumulate, ?_⟩
    · induction n with
    | zero => simp [hA]
    | succ n hn =>
      rw [Set.accumulate_succ]
      exact hp _ _ hn (hA _)
    · rwa [Set.iUnion_accumulate]

lemma _root_.IsCompactSystem.memProd (hp : IsCompactSystem p) (hq : IsCompactSystem q) :
    IsCompactSystem (memProd p q) := by
  sorry

lemma _root_.IsCompactSystem.memFiniteInter (hp : IsCompactSystem p) :
    IsCompactSystem (memFiniteInter p) := by
  sorry

lemma _root_.IsCompactSystem.memFiniteUnion (hp : IsCompactSystem p) :
    IsCompactSystem (memFiniteUnion p) := by
  sorry

-- He (35.1) in the proof of 1.35
lemma fst_iInter_of_memFiniteUnion_memProd_of_antitone (hq : IsCompactSystem q)
    {B : ℕ → Set (𝓧 × 𝓚)} (hB_anti : Antitone B)
    (hB : ∀ n, memFiniteUnion (memProd p q) (B n)) :
    Prod.fst '' (⋂ n, B n) = ⋂ n, Prod.fst '' B n := by
  refine le_antisymm (Set.image_iInter_subset _ _) ?_
  intro x hx
  choose S DC hDC hB_eq' using hB
  choose D' C' hD' hC' hDC_eq' using hDC
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
    exact hDC_eq' n m hm
  have hB_eq n : B n = ⋃ m ∈ S n, D n m ×ˢ C n m := by
    rw [hB_eq']
    congr
    ext m : 1
    by_cases hm : m ∈ S n
    swap; · simp [hm]
    simp only [hm, Set.iUnion_true]
    exact hDC_eq n m hm
  suffices (({x} ×ˢ .univ) ∩ ⋂ n, B n).Nonempty by
    obtain ⟨u, ⟨hu_left, hu_right⟩⟩ := this
    simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true] at hu_left
    rw [← hu_left, Set.mem_image]
    exact ⟨u, hu_right, rfl⟩
  let C'' n := ⋃ (m) (hm : m ∈ S n) (hx : x ∈ D n m), C n m -- `C'' n` is `C_n` in the book
  have h_inter n : ({x} ×ˢ .univ) ∩ B n = {x} ×ˢ C'' n := by
    simp_rw [C'', hB_eq n, Set.inter_iUnion, Set.prod_iUnion]
    congr
    ext m : 1
    by_cases hm : m ∈ S n
    swap; · simp [hm]
    simp only [hm, Set.iUnion_true]
    by_cases hx : x ∈ D n m
    · simp only [hx, Set.iUnion_true]
      ext
      simp
      grind
    · simp only [hx, Set.iUnion_false]
      ext
      simp
      grind
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
  have hC''q n : memFiniteUnion q (C'' n) := by
    simp only [C'']
    sorry
  have hC''_nonempty n : (C'' n).Nonempty := by
    sorry
  -- use that `memFiniteUnion q` is a compact paving (Bichteler A.5.6 (ii))
  -- if the intersection is empty, there is a finite subintersection that is empty
  -- that subintersection is just `C'' n` for some `n` since `C''` is antitone,
  -- so `C'' n` is empty, contradiction
  sorry

end MeasureTheory
