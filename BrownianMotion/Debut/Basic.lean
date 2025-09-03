/-
Copyright (c) 2025 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli
-/

import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Process.HittingTime
import BrownianMotion.Debut.Approximation

/-!
This file contains the basic definitions and properties of the debut of a set.


## Implementation notes

Following the implementation of hitting times in `Mathlib.Probability.Process.HittingTime`, we
bound the debut time by an upper and lower bound to ensure that it is well-defined even when the
set is empty or unbounded.
This allows us to define the debut for an index space without a top element, such as `ℕ` or `ℝ`.
The standard definition is recovered in the case of complete lattices, taking the bounds to
be `⊥` and `⊤`.

-/

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

open scoped Classical in
/-- The debut of a set `E ⊆ T × Ω` is the random variable that gives the smallest `t` such that
`(t, ω) ∈ E` for a given `ω`. -/
noncomputable def Debut [Preorder ι] [InfSet ι] (E : Set (ι × Ω)) (n m : ι) : Ω → ι :=
  fun ω ↦ if ∃ t ∈ Set.Icc n m, (t, ω) ∈ E then
    sInf {t ∈ Set.Icc n m | (t, ω) ∈ E} else m

open scoped Classical in
lemma debut_def [Preorder ι] [InfSet ι] (E : Set (ι × Ω)) (n m : ι) :
    Debut E n m = fun ω ↦ if ∃ t ∈ Set.Icc n m, (t, ω) ∈ E then
      sInf {t ∈ Set.Icc n m | (t, ω) ∈ E} else m := rfl

/- TODO: prove that this def is equiv to the hitting time of an indicator function of E,
when it hits [1,∞] -/

namespace Debut

variable [ConditionallyCompleteLinearOrder ι] (n m : ι)

/-- The debut of the empty set is the constant function that returns `m`. -/
@[simp]
lemma empty : Debut (∅ : Set (ι × Ω)) n m = fun _ ↦ m := by
  unfold Debut
  simp

@[simp]
lemma univ : Debut (Set.univ : Set (ι × Ω)) n m = fun _ ↦ if n ≤ m then n else m := by
  unfold Debut
  split_ifs with h
  · ext ω
    rw [if_pos ⟨n, Set.left_mem_Icc.mpr h, Set.mem_univ _⟩]
    simpa only [Set.mem_univ, and_true] using csInf_Icc h
  · simp [h]

open scoped Classical in
@[simp]
lemma prod (I : Set ι) (A : Set Ω) :
    Debut (I ×ˢ A) n m = fun ω ↦ if Set.Icc n m ∩ I ≠ ∅ then
        if ω ∈ A then sInf (Set.Icc n m ∩ I) else m
      else m := by
  ext ω
  split_ifs with hI hω
  · simp only [Debut, Set.mem_Icc, Set.mem_prod, hω, and_true]
    rw [if_pos (by exact Set.nonempty_iff_ne_empty.mpr hI)]
    congr
  · simp [Debut, hω]
  · simp only [ne_eq, Decidable.not_not] at hI
    refine if_neg ?_
    simp only [Set.mem_Icc, Set.mem_prod, not_exists, not_and, and_imp]
    exact fun i hni him hiI _ ↦ Set.notMem_empty i (hI ▸ ⟨⟨hni, him⟩, hiI⟩)

open scoped Classical in
lemma prod_univ (I : Set ι) :
    Debut (I ×ˢ (.univ : Set Ω)) n m = fun _ ↦ if Set.Icc n m ∩ I ≠ ∅ then
      sInf (Set.Icc n m ∩ I) else m := by
  simp

lemma univ_prod (A : Set Ω) [DecidablePred (· ∈ A)] :
    Debut ((.univ : Set ι) ×ˢ A) n m = fun ω ↦ if n ≤ m then
        if ω ∈ A then n else m
      else m := by
  unfold Debut
  split_ifs with h
  · ext ω
    split_ifs with hi hω hω
    · simpa [hω] using csInf_Icc h
    · simp_all
    · simp only [Set.mem_Icc, Set.mem_prod, Set.mem_univ, hω, and_true, not_exists,
        not_and, not_le] at hi
      exact hi n (Preorder.le_refl n) |>.not_ge h |>.elim
    · simp_all
  · simp [h]

lemma anti : Antitone (Debut (Ω := Ω) · n m) := by
  intro E F h ω
  simp only [Debut]
  split_ifs with hF hE hE
  · exact csInf_le_csInf ⟨n, fun i hi ↦ hi.1.1⟩ hE (by aesop)
  · have ⟨t, ht⟩ := hF
    exact csInf_le_of_le ⟨n, fun i hi ↦ hi.1.1⟩ ht ht.1.2
  · have ⟨t, ht⟩ := hE
    exact (hF ⟨t, ⟨ht.1, h ht.2⟩⟩).elim
  · exact Preorder.le_refl m

section Inequalities

lemma le (E : Set (ι × Ω)) (ω : Ω) : Debut E n m ω ≤ m := by
  unfold Debut
  split_ifs with h
  · have ⟨t, ht, htE⟩ := h
    exact csInf_le_of_le (BddBelow.inter_of_left bddBelow_Icc) ⟨ht, htE⟩ ht.2
  · exact le_rfl

lemma ge (E : Set (ι × Ω)) {n m : ι} (ω : Ω) (hnm : n ≤ m) : n ≤ Debut E n m ω := by
  unfold Debut
  split_ifs with h
  · exact le_csInf h fun i hi ↦ hi.1.1
  · exact hnm

lemma ge_of_exists {E : Set (ι × Ω)} {n m : ι} {ω : Ω} (h : ∃ t ∈ Set.Icc n m, (t, ω) ∈ E) :
    n ≤ Debut E n m ω := by
  refine ge E ω ?_
  by_contra! hh
  simp [hh] at h

lemma of_le (E : Set (ι × Ω)) {n m : ι} (ω : Ω) (h : m ≤ n) : Debut E n m ω = m := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_antisymm (le ..) (ge _ _ h)
  · grind [Debut, not_le, Set.Icc_eq_empty, Set.mem_empty_iff_false]

lemma mem_Icc (E : Set (ι × Ω)) {n m : ι} (ω : Ω) (hnm : n ≤ m) : Debut E n m ω ∈ Set.Icc n m :=
  ⟨ge E ω hnm, le ..⟩

lemma mem_set [WellFoundedLT ι] {E : Set (ι × Ω)} {n m : ι} {ω : Ω}
    (h : ∃ t ∈ Set.Icc n m, (t, ω) ∈ E) :
    (Debut E n m ω, ω) ∈ E := by
  rw [Debut, if_pos h]
  exact (csInf_mem h).2

lemma mem_set_of_debut_lt [WellFoundedLT ι] {E : Set (ι × Ω)} {n m : ι} {ω : Ω}
    (h : Debut E n m ω < m) :
    (Debut E n m ω, ω) ∈ E := by
  refine mem_set ?_
  by_contra ht
  simp [Debut, if_neg ht] at h

lemma le_of_mem {E : Set (ι × Ω)} {n m i : ι} (hni : n ≤ i) (him : i ≤ m) {ω : Ω}
    (hiE : (i, ω) ∈ E) :
    Debut E n m ω ≤ i := by
  have h_exists : ∃ k ∈ Set.Icc n m, (k, ω) ∈ E := ⟨i, ⟨hni, him⟩, hiE⟩
  simp_rw [Debut, if_pos h_exists]
  exact csInf_le (BddBelow.inter_of_left bddBelow_Icc) (Set.mem_inter ⟨hni, him⟩ hiE)

lemma eq_debut_of_exists {E : Set (ι × Ω)} {n m₁ m₂ : ι} {ω : Ω}
    (hm : m₁ ≤ m₂) (h : ∃ t ∈ Set.Icc n m₁, (t, ω) ∈ E) :
    Debut E n m₁ ω = Debut E n m₂ ω := by
  simp only [Debut, if_pos h]
  have ⟨t, ht, htE⟩ := h
  rw [if_pos ⟨t, ⟨ht.1, ht.2.trans hm⟩, htE⟩]
  refine le_antisymm ?_ (csInf_le_csInf bddBelow_Icc.inter_of_left ⟨t, ht, htE⟩
      (Set.inter_subset_inter_left _ (Set.Icc_subset_Icc_right hm)))
  refine le_csInf ⟨t, Set.Icc_subset_Icc_right hm ht, htE⟩ fun i hi => ?_
  by_cases him : i ≤ m₁
  · exact csInf_le bddBelow_Icc.inter_of_left ⟨⟨hi.1.1, him⟩, hi.2⟩
  · exact ((csInf_le bddBelow_Icc.inter_of_left ⟨ht, htE⟩).trans (ht.2.trans le_rfl)).trans
        (le_of_lt (not_le.1 him))

lemma mono_right (E : Set (ι × Ω)) (n : ι) (ω : Ω) : Monotone (Debut E n · ω) := by
  refine fun m₁ m₂ hm ↦ ?_
  by_cases h : ∃ j ∈ Set.Icc n m₁, (j, ω) ∈ E
  · exact (eq_debut_of_exists hm h).le
  · simp_rw [Debut, if_neg h]
    split_ifs with h'
    · have ⟨t, ht, htE⟩ := h'
      refine le_csInf h' fun t ht ↦ ?_
      by_contra! htm
      exact h ⟨t, ⟨ht.1.1, htm.le⟩, ht.2⟩
    · exact hm

end Inequalities

-- TODO: this may be put in a separate file, maybe in the file where ProgMeasurable is?
/- TODO: can we find some condition equivalent to this definition that is easier to state, maybe
something that does not involde the indicator function and only uses E as a set? Maybe there is a
σ algebra over `ι × Ω` such that ProgMeasurableSet is equivalent to being measurable with respect
to that σ-algebra?
maybe something like (mι : MeasurableSpace ι) [BorelSpace ι]
`∀ t, MeasurableSet[mι.prod (f t)] (E ∩ Set.Iic t ×ˢ Ω)`? I'm not completely sure this is actually
equivalent, but if I stated the lemma `MeasureTheory.Approximation.of_mem_prod_borel` correctly
this should be enough to prove the theorem below.
before changing this definition it may be worth it to begin the proof of `Debut.isStoppingTime`
to identify exactly what is needed, maybe in the end we do not even need to define the concpet of
progressively measurable set, but we can just add the necessary hypothesis manually. -/

/-- A set `E : Set ι × Ω` is *Progressively measurable* with respect to a filtration `f` if the
indicator function of `E` is a progressively measurable process with respect to `f`. -/
def _root_.MeasureTheory.ProgMeasurableSet
    [MeasurableSpace ι] (E : Set (ι × Ω)) (f : Filtration ι mΩ) :=
  ProgMeasurable f (E.indicator fun _ ↦ 1).curry

/-- **Debùt Therorem**: The debut of a progressively measurable set `E` is a stopping time. -/
theorem isStoppingTime [MeasurableSpace ι]
    {E : Set (ι × Ω)} {f : Filtration ι mΩ} (hE : ProgMeasurableSet E f) :
    IsStoppingTime f (Debut E n m) := by
  /- see the proof in the blueprint, we will probably need some more hypotheses, for example the
  usual hypotheses on the filtration (in particular the right continuity of the filtration, find if
  it is defined anywhere in mathlib, or if we need to define it ourselves or just state it as
  a hypothesis) -/
  sorry

end Debut

section HittingTime

-- This may be placed in `Mathlib.Probability.Process.HittingTime` in Mathlib.
/- We may need to add some hypotheses, like the filtration being right continuous. After proving
the theorem consider if this completely subsumes `hitting_isStoppingTime`, in that case we can
remove the latter. Also, consider if the fact that `β` is a borel space is actually needed. -/
theorem hitting_isStoppingTime' [ConditionallyCompleteLinearOrder ι] [MeasurableSpace ι]
    {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {f : Filtration ι mΩ} {X : ι → Ω → β} (hX : ProgMeasurable f X)
    {s : Set β} {n m : ι} (hs : MeasurableSet s) :
    IsStoppingTime f (hitting X s n m) := by
  sorry

end HittingTime


end MeasureTheory
