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

We follow the implementation of hitting times in `Mathlib.Probability.Process.HittingTime`.
The debut has values in `WithTop ι`, ensuring that it is always well-defined.
-/

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

open scoped Classical in
/-- The debut of a set `E ⊆ T × Ω` after `n` is the random variable that gives the smallest
`t ≥ n` such that `(t, ω) ∈ E` for a given `ω`. -/
noncomputable def debut [Preorder ι] [InfSet ι] (E : Set (ι × Ω)) (n : ι) : Ω → WithTop ι :=
  hittingAfter (fun t ω ↦ (t, ω)) E n

open scoped Classical in
lemma debut_eq_ite [Preorder ι] [InfSet ι] (E : Set (ι × Ω)) (n : ι) :
    debut E n = fun ω ↦ if ∃ t ≥ n, (t, ω) ∈ E then
      ((sInf {t ≥ n | (t, ω) ∈ E} : ι) : WithTop ι) else ⊤ := rfl

lemma debut_eq_hittingAfter_indicator [Preorder ι] [InfSet ι] (E : Set (ι × Ω))
    [∀ t ω, Decidable ((t, ω) ∈ E)] (n : ι) :
    debut E n = hittingAfter (fun t ω ↦ if (t, ω) ∈ E then 1 else 0) {1} n := by
  ext ω
  simp only [debut, hittingAfter]
  split_ifs <;> grind

lemma hittingAfter_eq_debut [Preorder ι] [InfSet ι] {β : Type*} (u : ι → Ω → β)
    (s : Set β) (n : ι) :
    hittingAfter u s n = debut {p : ι × Ω | u p.1 p.2 ∈ s} n := rfl

section Debut

variable [ConditionallyCompleteLinearOrder ι] (n : ι)

@[simp]
lemma hittingAfter_empty {β : Type*} {u : ι → Ω → β} : hittingAfter u ∅ n = fun _ ↦ ⊤ := by
  ext
  simp [hittingAfter]

@[simp]
lemma hittingAfter_univ {β : Type*} {u : ι → Ω → β} :
    hittingAfter u .univ n = fun _ ↦ (n : WithTop ι) := by
  ext ω
  classical
  simp only [hittingAfter, Set.mem_univ, and_true]
  rw [if_pos ⟨n, le_refl n⟩]
  exact_mod_cast csInf_Ici

lemma hittingAfter_anti {β : Type*} (u : ι → Ω → β) : Antitone (hittingAfter u · n) := by
  intro E F hEF ω
  simp only [hittingAfter]
  split_ifs with hF hE hE
  · norm_cast
    gcongr
    exacts [⟨n, by simp only [mem_lowerBounds, Set.mem_setOf_eq, and_imp]; grind⟩, hE, hEF]
  · simp
  · have ⟨t, ht⟩ := hE
    exact absurd ⟨t, ht.1, hEF ht.2⟩ hF
  · simp

lemma hittingAfter_mono {β : Type*} (u : ι → Ω → β) (s : Set β) : Monotone (hittingAfter u s) := by
  intro n m hnm ω
  simp only [hittingAfter]
  split_ifs with h_n h_m h_m
  · norm_cast
    gcongr
    exacts [⟨n, by simp only [mem_lowerBounds, Set.mem_setOf_eq, and_imp]; grind⟩, h_m]
  · simp
  · have ⟨t, ht⟩ := h_m
    exact absurd ⟨t, hnm.trans ht.1, ht.2⟩ h_n
  · simp

lemma hittingAfter_apply_anti {β : Type*} (u : ι → Ω → β) (ω : Ω) :
    Antitone (hittingAfter u · n ω) := fun _ _ hst ↦ hittingAfter_anti n u hst ω

lemma hittingAfter_apply_mono {β : Type*} (u : ι → Ω → β) (s : Set β) (ω : Ω) :
    Monotone (hittingAfter u s · ω) := fun _ _ hnm ↦ hittingAfter_mono u s hnm ω

/-- The debut of the empty set is the constant function that returns `m`. -/
@[simp]
lemma debut_empty : debut (∅ : Set (ι × Ω)) n = fun _ ↦ ⊤ := hittingAfter_empty n

@[simp]
lemma debut_univ : debut (.univ : Set (ι × Ω)) n = fun _ ↦ (n : WithTop ι) := hittingAfter_univ n

open scoped Classical in
@[simp]
lemma debut_prod (I : Set ι) (A : Set Ω) :
    debut (I ×ˢ A) n = fun ω ↦ if .Ici n ∩ I ≠ ∅ then
        if ω ∈ A then ((sInf (.Ici n ∩ I) : ι) : WithTop ι) else ⊤
      else ⊤ := by
  ext ω
  split_ifs with hI hω
  · simp only [debut_eq_ite, Set.mem_prod, hω, and_true]
    convert if_pos (Set.nonempty_iff_ne_empty.mpr hI) using 1
  · simp [debut_eq_ite, hω]
  · simp only [ne_eq, Decidable.not_not] at hI
    refine if_neg ?_
    simp only [Set.mem_prod, not_exists, not_and]
    exact fun i hni hiI _ ↦ Set.notMem_empty i (hI ▸ ⟨hni, hiI⟩)

open scoped Classical in
lemma debut_prod_univ (I : Set ι) :
    debut (I ×ˢ (.univ : Set Ω)) n = fun _ ↦ if .Ici n ∩ I ≠ ∅ then
      ((sInf (.Ici n ∩ I) : ι) : WithTop ι) else ⊤ := by
  simp

lemma debut_univ_prod (A : Set Ω) [DecidablePred (· ∈ A)] :
    debut ((.univ : Set ι) ×ˢ A) n = fun ω ↦ if ω ∈ A then (n : WithTop ι) else ⊤ := by
  rw [debut_eq_ite]
  ext ω
  split_ifs with hi hω hω
  · simp only [Set.mem_prod, Set.mem_univ, hω, and_true, WithTop.coe_eq_coe]
    exact csInf_Ici
  · simp_all
  · simp only [Set.mem_prod, Set.mem_univ, hω, and_true, not_exists, not_le] at hi
    exact (lt_self_iff_false n).mp (hi n) |>.elim
  · simp_all

lemma debut_anti : Antitone (debut (Ω := Ω) · n) := hittingAfter_anti n _

section Inequalities

variable {E : Set (ι × Ω)} {n t : ι} {ω : Ω}

lemma notMem_of_lt_debut (ht : t < debut E n ω) (hnt : n ≤ t) : (t, ω) ∉ E :=
  notMem_of_lt_hittingAfter ht hnt

lemma debut_eq_top_iff : debut E n ω = ⊤ ↔ ∀ t ≥ n, (t, ω) ∉ E := hittingAfter_eq_top_iff

lemma le_debut (ω : Ω) : n ≤ debut E n ω := le_hittingAfter ω

lemma debut_mem_set [WellFoundedLT ι] (h : ∃ t ≥ n, (t, ω) ∈ E) :
    ((debut E n ω).untopA, ω) ∈ E := hittingAfter_mem_set h

lemma debut_mem_set_of_ne_top [WellFoundedLT ι] (h : debut E n ω ≠ ⊤) :
    ((debut E n ω).untopA, ω) ∈ E := hittingAfter_mem_set_of_ne_top h

lemma debut_le_of_mem (ht : n ≤ t) (h_mem : (t, ω) ∈ E) :
    debut E n ω ≤ t := hittingAfter_le_of_mem ht h_mem

lemma debut_le_iff [WellFoundedLT ι] : debut E n ω ≤ t ↔ ∃ j ∈ Set.Icc n t, (j, ω) ∈ E :=
  hittingAfter_le_iff

lemma debut_lt_iff [WellFoundedLT ι] : debut E n ω < t ↔ ∃ j ∈ Set.Ico n t, (j, ω) ∈ E :=
  hittingAfter_lt_iff

lemma debut_mono (E : Set (ι × Ω)) (ω : Ω) : Monotone (debut E · ω) := hittingAfter_apply_mono _ _ _

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
before changing this definition it may be worth it to begin the proof of `debut.isStoppingTime`
to identify exactly what is needed, maybe in the end we do not even need to define the concpet of
progressively measurable set, but we can just add the necessary hypothesis manually. -/

/-- A set `E : Set ι × Ω` is *Progressively measurable* with respect to a filtration `f` if the
indicator function of `E` is a progressively measurable process with respect to `f`. -/
def _root_.MeasureTheory.ProgMeasurableSet
    [MeasurableSpace ι] (E : Set (ι × Ω)) (f : Filtration ι mΩ) :=
  ProgMeasurable f (E.indicator fun _ ↦ 1).curry

/-- **Debùt Therorem**: The debut of a progressively measurable set `E` is a stopping time. -/
theorem debut_isStoppingTime [MeasurableSpace ι]
    {E : Set (ι × Ω)} {f : Filtration ι mΩ} (hE : ProgMeasurableSet E f) :
    IsStoppingTime f (debut E n) := by
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
    IsStoppingTime f (hittingAfter X s n) := by
  sorry

end HittingTime


end MeasureTheory
