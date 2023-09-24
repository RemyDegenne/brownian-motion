import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ENat.Lattice

variable {α : Type*}

/-- A set `C` is an `r`-cover of another set `A` if every point in `A` belongs to a ball with radius
`r` around a point of `C`. -/
def IsCover [Dist α] (C : Set α) (r : ℝ) (A : Set α) : Prop :=
  ∀ a ∈ A, ∃ c ∈ C, dist a c ≤ r

/-- A set `C` is a `r`-separated if all pairs of points `a,b` of `C` satisfy `r < dist a b`. -/
def IsSeparated [Dist α] (C : Set α) (r : ℝ) : Prop :=
  ∀ (a : α) (b : α) (_ : a ∈ C) (_ : b ∈ C), r < dist a b

@[simp]
lemma isSeparated_empty [Dist α] (r : ℝ) : IsSeparated (∅ : Set α) r := by
  intros a b ha _
  simp at ha

noncomputable
def externalCoveringNumber [Dist α] (r : ℝ) (A : Set α) : ENat :=
  ⨅ (C : Finset α) (_ : IsCover C r A), C.card

noncomputable
def internalCoveringNumber [Dist α] (r : ℝ) (A : Set α) : ENat :=
  ⨅ (C : Finset α) (_ : ↑C ⊆ A) (_ : IsCover C r A), C.card

noncomputable
def packingNumber [Dist α] (r : ℝ) (A : Set α) : ENat :=
  ⨆ (C : Finset α) (_ : ↑C ⊆ A) (_ : IsSeparated (C : Set α) r), C.card

section minimalCover

variable {r : ℝ} {A : Set α}

lemma exists_finset_card_eq_internalCoveringNumber [Dist α] (h : internalCoveringNumber r A < ⊤) :
    ∃ (C : Finset α), ↑C ⊆ A ∧ IsCover (C : Set α) r A ∧ C.card = internalCoveringNumber r A := by
  sorry

/-- An internal `r`-cover of `A` with minimal cardinal. -/
noncomputable
def minimalCover [Dist α] (r : ℝ) (A : Set α) : Finset α :=
  if h : internalCoveringNumber r A < ⊤
    then (exists_finset_card_eq_internalCoveringNumber h).choose else ∅

lemma minimalCover_subset [Dist α] : ↑(minimalCover r A) ⊆ A := by
  by_cases h : internalCoveringNumber r A < ⊤
  · simp only [minimalCover, h, dite_true]
    exact (exists_finset_card_eq_internalCoveringNumber h).choose_spec.1
  · simp only [minimalCover, h, dite_false, Finset.coe_empty, Set.empty_subset]

lemma isCover_minimalCover [Dist α] (h : internalCoveringNumber r A < ⊤) :
    IsCover (minimalCover r A : Set α) r A := by
  simp only [minimalCover, h, dite_true]
  exact (exists_finset_card_eq_internalCoveringNumber h).choose_spec.2.1

lemma card_minimalCover [Dist α] (h : internalCoveringNumber r A < ⊤) :
    (minimalCover r A).card = internalCoveringNumber r A := by
  simp only [minimalCover, h, dite_true]
  exact (exists_finset_card_eq_internalCoveringNumber h).choose_spec.2.2

end minimalCover

section maximalSeparatedSet

variable {r : ℝ} {A : Set α}

lemma exists_finset_card_eq_packingNumber [Dist α] (h : packingNumber r A < ⊤) :
    ∃ (C : Finset α), ↑C ⊆ A ∧ IsSeparated (C : Set α) r ∧ C.card = packingNumber r A := by
  sorry

/-- A maximal `r`-separated finite subset of `A`. -/
noncomputable
def maximalSeparatedSet [Dist α] (r : ℝ) (A : Set α) : Finset α :=
  if h : packingNumber r A < ⊤ then (exists_finset_card_eq_packingNumber h).choose else ∅

lemma maximalSeparatedSet_subset [Dist α] : ↑(maximalSeparatedSet r A) ⊆ A := by
  by_cases h : packingNumber r A < ⊤
  · simp only [maximalSeparatedSet, h, dite_true]
    exact (exists_finset_card_eq_packingNumber h).choose_spec.1
  · simp only [maximalSeparatedSet, h, dite_false, Finset.coe_empty, Set.empty_subset]

lemma isSeparated_maximalSeparatedSet [Dist α] :
    IsSeparated (maximalSeparatedSet r A : Set α) r := by
  by_cases h : packingNumber r A < ⊤
  · simp only [maximalSeparatedSet, h, dite_true]
    exact (exists_finset_card_eq_packingNumber h).choose_spec.2.1
  · simp only [maximalSeparatedSet, h, dite_false, Finset.coe_empty,isSeparated_empty]

lemma card_maximalSeparatedSet [Dist α] (h : packingNumber r A < ⊤) :
    (maximalSeparatedSet r A).card = packingNumber r A := by
  simp only [maximalSeparatedSet, h, dite_true]
  exact (exists_finset_card_eq_packingNumber h).choose_spec.2.2

lemma card_le_of_isSeparated [Dist α] {C : Finset α} (h_subset : ↑C ⊆ A)
    (h : IsSeparated (C : Set α) r) :
    C.card ≤ (maximalSeparatedSet r A).card := by
  sorry

lemma isCover_maximalSeparatedSet [PseudoMetricSpace α] (h : packingNumber r A < ⊤) (hr : 0 ≤ r) :
    IsCover (maximalSeparatedSet r A) r A := by
  intro x hxA
  by_contra h_dist
  push_neg at h_dist
  have hx_not_mem : x ∉ maximalSeparatedSet r A := by 
    intro hx_mem
    specialize h_dist x hx_mem
    simp only [dist_self, not_lt.mpr hr] at h_dist 
  classical
  let C := {x} ∪ maximalSeparatedSet r A
  have hC_subset : ↑C ⊆ A := by
    simp [hxA, maximalSeparatedSet_subset, Set.insert_subset]
  have hC_separated : IsSeparated (C : Set α) r := by
    sorry
  refine absurd (card_le_of_isSeparated hC_subset hC_separated) ?_
  simp only [Finset.disjoint_singleton_left, hx_not_mem, not_false_eq_true,
    Finset.card_disjoint_union, Finset.card_singleton, add_le_iff_nonpos_left]

end maximalSeparatedSet

section comparisons

theorem packingNumber_two_le_internalCoveringNumber [Dist α] (r : ℝ) (A : Set α) :
    packingNumber (2 * r) A ≤ internalCoveringNumber r A := by
  sorry

theorem internalCoveringNumber_le_packingNumber [PseudoMetricSpace α] (r : ℝ) (A : Set α)
    (hr : 0 ≤ r) :
    internalCoveringNumber r A ≤ packingNumber r A := by
  by_cases h_top : packingNumber r A < ⊤
  · rw [← card_maximalSeparatedSet h_top]
    refine (iInf_le _ (maximalSeparatedSet r A : Finset α)).trans (le_of_eq ?_)
    simp only [maximalSeparatedSet_subset, iInf_pos, isCover_maximalSeparatedSet h_top hr]
  · rw [not_lt_top_iff] at h_top
    simp [h_top]

theorem externalCoveringNumber_le_internalCoveringNumber [Dist α] (r : ℝ) (A : Set α) :
    externalCoveringNumber r A ≤ internalCoveringNumber r A := by
  simp only [externalCoveringNumber, internalCoveringNumber, le_iInf_iff]
  exact fun C _ hC_cover ↦ iInf₂_le C hC_cover

theorem internalCoveringNumber_two_le_externalCoveringNumber [Dist α] (r : ℝ) (A : Set α) :
    internalCoveringNumber (2 * r) A ≤ externalCoveringNumber r A := by
  sorry

end comparisons