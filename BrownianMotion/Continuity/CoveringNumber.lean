/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Init

/-!
# Covering and packing numbers

### References
- Vershynin, High-Dimensional Probability (section 4.2)
-/

open ENNReal Metric

variable {E : Type*}

section Definitions

variable [EDist E]

/-- A set `C` is an `r`-cover of another set `A` if every point in `A` belongs to a ball with radius
`r` around a point of `C`. -/
def IsCover (C : Set E) (ε : ℝ≥0∞) (A : Set E) : Prop :=
  ∀ a ∈ A, ∃ c ∈ C, edist a c ≤ ε

noncomputable
def externalCoveringNumber (r : ℝ≥0∞) (A : Set E) : ENat :=
  ⨅ (C : Finset E) (_ : IsCover C r A), C.card

noncomputable
def internalCoveringNumber (r : ℝ≥0∞) (A : Set E) : ENat :=
  ⨅ (C : Finset E) (_ : ↑C ⊆ A) (_ : IsCover C r A), C.card

noncomputable
def packingNumber [PseudoEMetricSpace E] (r : ℝ≥0∞) (A : Set E) : ENat :=
  ⨆ (C : Finset E) (_ : ↑C ⊆ A) (_ : IsSeparated r (C : Set E)), C.card

end Definitions

lemma EMetric.isCover_iff [PseudoEMetricSpace E] {C : Set E} {ε : ℝ≥0∞} {A : Set E} :
    IsCover C ε A ↔ A ⊆ ⋃ x ∈ C, EMetric.closedBall x ε := by
  simp [IsCover, Set.subset_def]

lemma isCover_empty_iff [EDist E] (ε : ℝ≥0∞) (A : Set E) :
    IsCover (∅ : Set E) ε A ↔ A = ∅ := by
  simp only [IsCover, Set.mem_empty_iff_false, false_and, exists_false, imp_false]
  exact ⟨fun h ↦ by ext x; simp [h x], fun h ↦ by simp [h]⟩

lemma isCover_empty [EDist E] (ε : ℝ≥0∞) :
    IsCover (∅ : Set E) ε ∅ := by
  simp [isCover_empty_iff]

lemma not_isCover_empty [EDist E] (ε : ℝ≥0∞) (A : Set E) (h_nonempty : A.Nonempty) :
    ¬ IsCover (∅ : Set E) ε A := by
  simpa [IsCover]

@[simp]
lemma internalCoveringNumber_empty [EDist E] (r : ℝ≥0∞) :
    internalCoveringNumber r (∅ : Set E) = 0 := by
  simp [internalCoveringNumber, isCover_empty]

@[simp]
lemma externalCoveringNumber_empty [EDist E] (r : ℝ≥0∞) :
    externalCoveringNumber r (∅ : Set E) = 0 := by
  simp [externalCoveringNumber, isCover_empty]

lemma isCover_singleton_of_diam_le [PseudoEMetricSpace E] {ε : ℝ≥0∞} {A : Set E} {a : E}
    (hA : EMetric.diam A ≤ ε) (ha : a ∈ A) :
    IsCover ({a} : Set E) ε A :=
  fun x hxA ↦ ⟨a, by simp, (EMetric.edist_le_diam_of_mem hxA ha).trans hA⟩

lemma isCover_singleton_finset_of_diam_le [PseudoEMetricSpace E] {ε : ℝ≥0∞} {A : Set E} {a : E}
    (hA : EMetric.diam A ≤ ε) (ha : a ∈ A) :
    IsCover ({a} : Finset E) ε A :=
  fun x hxA ↦ ⟨a, by simp, (EMetric.edist_le_diam_of_mem hxA ha).trans hA⟩

lemma cover_eq_of_lt_iInf_edist [PseudoEMetricSpace E] {C : Set E} {ε : ℝ≥0∞} {A : Set E}
    (hC : IsCover C ε A) (hC_subset : C ⊆ A)
    (hε : ε < ⨅ (s : A) (t : { t : A // s ≠ t }), edist s t) : C = A := by
  sorry

lemma internalCoveringNumber_eq_one_of_diam_le [PseudoEMetricSpace E] {r : ℝ≥0∞} {A : Set E}
    (h_nonempty : A.Nonempty) (hA : EMetric.diam A ≤ r) :
    internalCoveringNumber r A = 1 := by
  refine le_antisymm ?_ ?_
  · have ⟨a, ha⟩ := h_nonempty
    refine (iInf₂_le ({a} : Finset E) (by simp [ha])).trans <| (iInf_le _ ?_).trans (by simp)
    exact isCover_singleton_finset_of_diam_le hA ha
  · refine le_iInf₂ (α := ℕ∞) fun C hC ↦ ?_
    refine le_iInf (α := ℕ∞) fun hCoverC ↦ ?_
    by_contra! hcontra
    apply (ENat.lt_one_iff_eq_zero).mp at hcontra
    simp only [Nat.cast_eq_zero, Finset.card_eq_zero] at hcontra
    rw [hcontra, Finset.coe_empty] at hCoverC
    exact not_isCover_empty r _ h_nonempty hCoverC

lemma externalCoveringNumber_eq_one_of_diam_le [PseudoEMetricSpace E] {r : ℝ≥0∞} {A : Set E}
    (h_nonempty : A.Nonempty) (hA : EMetric.diam A ≤ r) :
    externalCoveringNumber r A = 1 := by
  refine le_antisymm ?_ ?_
  · have ⟨a, ha⟩ := h_nonempty
    refine (iInf_le _ ({a} : Finset E)).trans <| iInf_le _ ?_
    exact isCover_singleton_finset_of_diam_le hA ha
  · refine le_iInf₂ (α := ℕ∞) fun C hC ↦ ?_
    by_contra! hcontra
    apply (ENat.lt_one_iff_eq_zero).mp at hcontra
    simp only [Nat.cast_eq_zero, Finset.card_eq_zero] at hcontra
    rw [hcontra, Finset.coe_empty] at hC
    exact not_isCover_empty r _ h_nonempty hC

lemma internalCoveringNumber_le_one_of_diam_le [PseudoEMetricSpace E] {r : ℝ≥0∞} {A : Set E}
    (hA : EMetric.diam A ≤ r) :
    internalCoveringNumber r A ≤ 1 := by
  by_cases h_emptyA : A.Nonempty
  · exact le_of_eq (internalCoveringNumber_eq_one_of_diam_le h_emptyA hA)
  · push_neg at h_emptyA
    let C := (∅ : Finset E)
    have hCover : IsCover (↑C) r A := by
      intro a ha
      simp [h_emptyA] at ha
    calc
      _ ≤ _ := iInf₂_le (α := ℕ∞) C (by simp [C])
      _ ≤ C.card := iInf_le (α := ℕ∞) _ hCover
    simp [C]

lemma subset_iUnion_of_isCover [PseudoEMetricSpace E] {C : Set E} {ε : ℝ≥0∞} {A : Set E}
    (hC : IsCover C ε A) :
    A ⊆ ⋃ x ∈ C, EMetric.closedBall x ε := by
  intro a ha
  simp only [Set.mem_iUnion, EMetric.mem_closedBall, exists_prop]
  exact hC a ha

lemma TotallyBounded.exists_isCover [PseudoEMetricSpace E] {A : Set E}
    (hA : TotallyBounded A) (r : ℝ≥0∞) (hr : 0 < r) :
    ∃ C : Finset E, ↑C ⊆ A ∧ IsCover (C : Set E) r A := by
  rw [EMetric.totallyBounded_iff'] at hA
  obtain ⟨C, hCA, hC_finite, hC⟩ := hA r hr
  simp only [EMetric.isCover_iff, Finset.mem_coe]
  refine ⟨Set.Finite.toFinset hC_finite, by simpa, ?_⟩
  · simp only [Set.Finite.mem_toFinset]
    refine hC.trans fun x hx ↦ ?_
    simp only [Set.mem_iUnion, EMetric.mem_ball, exists_prop, EMetric.mem_closedBall] at hx ⊢
    obtain ⟨y, hyC, hy⟩ := hx
    exact ⟨y, hyC, hy.le⟩

lemma IsCover.Nonempty [PseudoEMetricSpace E] {C : Set E} {ε : ℝ≥0∞} {A : Set E}
    (hC : IsCover C ε A) (hA : A.Nonempty) : C.Nonempty := by
  obtain ⟨a, haA⟩ := hA
  obtain ⟨c, hcC, hc⟩ := hC a haA
  exact ⟨c, hcC⟩

section minimalCover

variable [PseudoEMetricSpace E] {r : ℝ≥0∞} {A : Set E}

lemma exists_finset_card_eq_internalCoveringNumber (h : TotallyBounded A) (r : ℝ≥0∞) :
    ∃ (C : Finset E), ↑C ⊆ A ∧ IsCover (C : Set E) r A ∧ C.card = internalCoveringNumber r A := by
  sorry

open Classical in
/-- An internal `r`-cover of `A` with minimal cardinal. -/
noncomputable
def minimalCover (r : ℝ≥0∞) (A : Set E) : Finset E :=
  if h : TotallyBounded A
    then (exists_finset_card_eq_internalCoveringNumber h r).choose else ∅

lemma minimalCover_subset : ↑(minimalCover r A) ⊆ A := by
  by_cases h : TotallyBounded A
  · simp only [minimalCover, h, dite_true]
    exact (exists_finset_card_eq_internalCoveringNumber h r).choose_spec.1
  · simp only [minimalCover, h, dite_false, Finset.coe_empty, Set.empty_subset]

lemma isCover_minimalCover (h : TotallyBounded A) :
    IsCover (minimalCover r A : Set E) r A := by
  simp only [minimalCover, h, dite_true]
  exact (exists_finset_card_eq_internalCoveringNumber h r).choose_spec.2.1

lemma card_minimalCover (h : TotallyBounded A) :
    (minimalCover r A).card = internalCoveringNumber r A := by
  simp only [minimalCover, h, dite_true]
  exact (exists_finset_card_eq_internalCoveringNumber h r).choose_spec.2.2

end minimalCover

section maximalSeparatedSet

variable {r : ℝ≥0∞} {A : Set E}

lemma exists_finset_card_eq_packingNumber [PseudoEMetricSpace E] (h : packingNumber r A < ⊤) :
    ∃ (C : Finset E), ↑C ⊆ A ∧ IsSeparated r (C : Set E) ∧ C.card = packingNumber r A := by
  sorry

/-- A maximal `r`-separated finite subset of `A`. -/
noncomputable
def maximalSeparatedSet [PseudoEMetricSpace E] (r : ℝ≥0∞) (A : Set E) : Finset E :=
  if h : packingNumber r A < ⊤ then (exists_finset_card_eq_packingNumber h).choose else ∅

lemma maximalSeparatedSet_subset [PseudoEMetricSpace E] : ↑(maximalSeparatedSet r A) ⊆ A := by
  by_cases h : packingNumber r A < ⊤
  · simp only [maximalSeparatedSet, h, dite_true]
    exact (exists_finset_card_eq_packingNumber h).choose_spec.1
  · simp only [maximalSeparatedSet, h, dite_false, Finset.coe_empty, Set.empty_subset]

lemma isSeparated_maximalSeparatedSet [PseudoEMetricSpace E] :
    IsSeparated r (maximalSeparatedSet r A : Set E) := by
  by_cases h : packingNumber r A < ⊤
  · simp only [maximalSeparatedSet, h, dite_true]
    exact (exists_finset_card_eq_packingNumber h).choose_spec.2.1
  · simp only [maximalSeparatedSet, h, dite_false, Finset.coe_empty, IsSeparated.empty]

lemma card_maximalSeparatedSet [PseudoEMetricSpace E] (h : packingNumber r A < ⊤) :
    (maximalSeparatedSet r A).card = packingNumber r A := by
  simp only [maximalSeparatedSet, h, dite_true]
  exact (exists_finset_card_eq_packingNumber h).choose_spec.2.2

lemma card_le_of_isSeparated [PseudoEMetricSpace E] {C : Finset E} (h_subset : ↑C ⊆ A)
    (h_sep : IsSeparated r (C : Set E)) (h : packingNumber r A < ⊤) :
    C.card ≤ (maximalSeparatedSet r A).card := by
  suffices (C.card : ENat) ≤ (maximalSeparatedSet r A).card by norm_cast at this
  rw [card_maximalSeparatedSet h]
  exact le_iSup_of_le C <| le_iSup_of_le h_subset <| le_iSup_of_le h_sep le_rfl

lemma isCover_maximalSeparatedSet [PseudoEMetricSpace E] (h : packingNumber r A < ⊤) :
    IsCover (maximalSeparatedSet r A) r A := by
  intro x hxA
  by_contra h_dist
  push_neg at h_dist
  have hx_not_mem : x ∉ maximalSeparatedSet r A := by
    intro hx_mem
    specialize h_dist x hx_mem
    simp at h_dist
  classical
  let C := {x} ∪ maximalSeparatedSet r A
  have hC_subset : ↑C ⊆ A := by
    simp [C, hxA, maximalSeparatedSet_subset, Set.insert_subset]
  have hC_separated : IsSeparated r (C : Set E) := by
    intro a ha b hb hab
    by_cases hax : a = x
    · subst hax
      have hb' : b ∈ maximalSeparatedSet r A := by simpa [C, hab.symm] using hb
      exact h_dist b hb'
    by_cases hbx : b = x
    · subst hbx
      have ha' : a ∈ maximalSeparatedSet r A := by simpa [C, hab] using ha
      have h := h_dist a ha'
      rwa [edist_comm] at h
    simp [hax, hbx, C] at ha hb
    exact isSeparated_maximalSeparatedSet ha hb hab
  refine absurd (card_le_of_isSeparated hC_subset hC_separated h) ?_
  simp only [Finset.disjoint_singleton_left, hx_not_mem, not_false_eq_true,
    Finset.card_union_of_disjoint, Finset.card_singleton, add_le_iff_nonpos_left,
    nonpos_iff_eq_zero, one_ne_zero, C]

end maximalSeparatedSet

section comparisons

theorem internalCoveringNumber_le_packingNumber [PseudoEMetricSpace E] (r : ℝ≥0∞) (A : Set E) :
    internalCoveringNumber r A ≤ packingNumber r A := by
  by_cases h_top : packingNumber r A < ⊤
  · rw [← card_maximalSeparatedSet h_top]
    refine (iInf_le _ (maximalSeparatedSet r A : Finset E)).trans (le_of_eq ?_)
    simp only [maximalSeparatedSet_subset, iInf_pos, isCover_maximalSeparatedSet h_top]
  · rw [not_lt_top_iff] at h_top
    simp [h_top]

theorem packingNumber_two_le_externalCoveringNumber [PseudoEMetricSpace E] {r : ℝ≥0∞} (A : Set E)
    (hr : r ≠ ∞) :
    packingNumber (2 * r) A ≤ externalCoveringNumber r A := by
  simp only [packingNumber, externalCoveringNumber, le_iInf_iff, iSup_le_iff, Nat.cast_le]
  intro C hC_cover D hD_subset hD_separated
  let f : D → C := fun x ↦
    ⟨(hC_cover x.1 (hD_subset x.2)).choose, (hC_cover x.1 (hD_subset x.2)).choose_spec.1⟩
  have hf' (x : D) : edist x.1 (f x) ≤ r := (hC_cover x.1 (hD_subset x.2)).choose_spec.2
  suffices Function.Injective f from Finset.card_le_card_of_injective this
  intro x y hfxy
  by_contra hxy
  specialize hD_separated x.2 y.2 ?_
  · rwa [Subtype.ext_iff] at hxy
  suffices 0 < edist (f x) (f y) by simp [hfxy] at this
  have hx_ne_top : edist x.1 (f x) ≠ ∞ := ne_top_of_le_ne_top hr (hf' x)
  have hy_ne_top : edist y.1 (f y) ≠ ∞ := ne_top_of_le_ne_top hr (hf' y)
  calc 0
  _ ≤ 2 * r - edist x.1 (f x) - edist y.1 (f y) := zero_le'
  _ < edist x y - edist x.1 (f x) - edist y.1 (f y) := by
    rw [lt_tsub_iff_left, lt_tsub_iff_left]
    refine lt_of_eq_of_lt ?_ hD_separated
    rw [add_comm (edist y.1 _), ENNReal.sub_add_eq_add_sub, ENNReal.add_sub_cancel_right, add_comm,
      ENNReal.sub_add_eq_add_sub, ENNReal.add_sub_cancel_right]
    · exact hx_ne_top
    · refine (hf' x).trans ?_
      rw [two_mul]
      exact le_self_add
    · exact hx_ne_top
    · exact hy_ne_top
    · refine ENNReal.le_sub_of_add_le_left hx_ne_top ?_
      rw [two_mul]
      gcongr
      · exact hf' x
      · exact hf' y
    · exact hy_ne_top
  _ ≤ (edist x.1 (f x) + edist (f x) (f y) + edist (f y : E) y.1)
      - edist x.1 (f x) - edist y.1 (f y) := by
    gcongr
    exact edist_triangle4 x.1 (f x) (f y) y.1
  _ = edist (f x) (f y) := by
    simp only [hfxy, edist_self, add_zero]
    rw [edist_comm (f y : E), add_comm, ENNReal.add_sub_cancel_right, tsub_self]
    rw [← hfxy]
    exact hx_ne_top

theorem externalCoveringNumber_le_internalCoveringNumber [EDist E] (r : ℝ≥0∞) (A : Set E) :
    externalCoveringNumber r A ≤ internalCoveringNumber r A := by
  simp only [externalCoveringNumber, internalCoveringNumber, le_iInf_iff]
  exact fun C _ hC_cover ↦ iInf₂_le C hC_cover

theorem internalCoveringNumber_two_le_externalCoveringNumber [PseudoEMetricSpace E]
    (r : ℝ≥0∞) (A : Set E) :
    internalCoveringNumber (2 * r) A ≤ externalCoveringNumber r A := by
  rcases Set.eq_empty_or_nonempty A with (h_empty | h_nonempty)
  · simp [h_empty]
  by_cases hr : r = ∞
  · subst hr
    rw [internalCoveringNumber_eq_one_of_diam_le h_nonempty (by simp),
      externalCoveringNumber_eq_one_of_diam_le h_nonempty (by simp)]
  refine (internalCoveringNumber_le_packingNumber _ A).trans ?_
  exact packingNumber_two_le_externalCoveringNumber A hr

end comparisons
