/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.ENNReal
import BrownianMotion.Auxiliary.MeasureTheory
import BrownianMotion.Auxiliary.Nat
import Mathlib.Algebra.Order.Ring.Star

/-!
# Covering and packing numbers

### References
- Vershynin, High-Dimensional Probability (section 4.2)
-/

open ENNReal Metric
open scoped NNReal

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

lemma internalCoveringNumber_le_of_isCover [EDist E] {C : Finset E} {r : ℝ≥0∞} {A : Set E}
    (C_sub : ↑C ⊆ A) (C_cov : IsCover C r A) :
    internalCoveringNumber r A ≤ C.card :=
  iInf_le_of_le C <| iInf_le_of_le C_sub <| iInf_le_of_le C_cov le_rfl

@[simp]
lemma IsCover.self [PseudoEMetricSpace E] (A : Set E) (r : ℝ≥0∞) : IsCover A r A :=
  fun a ha => ⟨a, ha, by simp⟩

lemma isCover_zero_iff [EMetricSpace E] (C A : Set E) : IsCover C 0 A ↔ A ⊆ C := by
  refine ⟨fun h a ha ↦ ?_, fun h a ha ↦ ⟨a, h ha, by simp⟩⟩
  obtain ⟨c, hc, h⟩ := h a ha
  simp_all

lemma Set.Finite.internalCoveringNumber_le_ncard [PseudoEMetricSpace E] (r : ℝ≥0∞) (A : Set E)
    (ha : A.Finite) : internalCoveringNumber r A ≤ A.ncard := by
  rw [internalCoveringNumber]
  exact sInf_le ⟨ha.toFinset, by simpa using (ncard_eq_toFinset_card _ _).symm⟩

@[simp]
lemma internalCoveringNumber_zero [EMetricSpace E] (A : Set E) :
    internalCoveringNumber 0 A = A.encard := by
  obtain hA | hA := A.finite_or_infinite
  · refine le_antisymm (hA.cast_ncard_eq ▸ hA.internalCoveringNumber_le_ncard _) ?_
    rw [internalCoveringNumber]
    refine le_iInf fun C ↦ le_iInf fun hC₁ ↦ le_iInf fun hC₂ ↦ ?_
    rw [isCover_zero_iff] at hC₂
    simp [subset_antisymm hC₂ hC₁]
  · rw [hA.encard_eq, internalCoveringNumber]
    refine iInf_eq_top.2 fun C ↦ iInf_eq_top.2 fun hC₁ ↦ iInf_neg fun hC₂ ↦ ?_
    rw [isCover_zero_iff] at hC₂
    exact (subset_antisymm hC₁ hC₂ ▸ C.finite_toSet).not_infinite hA

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

lemma Set.Nonempty.one_le_internalCoveringNumber [EDist E] {A : Set E} (hA : A.Nonempty)
    (r : ℝ≥0∞) : 1 ≤ internalCoveringNumber r A := by
  refine le_iInf fun C ↦ le_iInf fun hC₁ ↦ le_iInf fun hC₂ ↦ ?_
  simp only [Nat.one_le_cast, Finset.one_le_card]
  by_contra!
  rw [Finset.not_nonempty_iff_eq_empty] at this
  rw [this, Finset.coe_empty, isCover_empty_iff] at hC₂
  exact Set.nonempty_iff_ne_empty.1 hA hC₂

lemma Set.Nonempty.internalCoveringNumber_top [PseudoEMetricSpace E] {A : Set E} (hA : A.Nonempty) :
    internalCoveringNumber ⊤ A = 1 := by
  refine le_antisymm ?_ (hA.one_le_internalCoveringNumber _)
  obtain ⟨x, hx⟩ := hA
  exact iInf_le_of_le {x} <| iInf_le_of_le (by simpa) <|
    iInf_le_of_le (fun _ _ ↦ ⟨x, by simp⟩) (by simp)

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

@[simp]
lemma packingNumber_empty [PseudoEMetricSpace E] (r : ℝ≥0∞) :
    packingNumber r (∅ : Set E) = 0 := by simp [packingNumber]

@[simp]
lemma packingNumber_singleton [PseudoEMetricSpace E] (r : ℝ≥0∞) (x : E) :
    packingNumber r ({x} : Set E) = 1 := by
  refine le_antisymm ?_ <|
    le_iSup_of_le ({x} : Finset E) <| le_iSup_of_le (by simp) <| le_iSup_of_le (by simp) (by simp)
  rw [packingNumber]
  simp only [Set.subset_singleton_iff, Finset.mem_coe, iSup_le_iff, Nat.cast_le_one]
  exact fun C hC _ ↦ Finset.card_le_one.2 (fun a ha b hb ↦ by rw [hC a ha, hC b hb])

lemma isCover_singleton_of_diam_le [PseudoEMetricSpace E] {ε : ℝ≥0∞} {A : Set E} {a : E}
    (hA : EMetric.diam A ≤ ε) (ha : a ∈ A) :
    IsCover ({a} : Set E) ε A :=
  fun x hxA ↦ ⟨a, by simp, (EMetric.edist_le_diam_of_mem hxA ha).trans hA⟩

lemma isCover_singleton_finset_of_diam_le [PseudoEMetricSpace E] {ε : ℝ≥0∞} {A : Set E} {a : E}
    (hA : EMetric.diam A ≤ ε) (ha : a ∈ A) :
    IsCover ({a} : Finset E) ε A :=
  fun x hxA ↦ ⟨a, by simp, (EMetric.edist_le_diam_of_mem hxA ha).trans hA⟩

lemma IsCover.mono [EDist E] {C : Set E} {ε ε' : ℝ≥0∞} {A : Set E} (h : ε ≤ ε')
    (hC : IsCover C ε A) : IsCover C ε' A := by
  intro a ha
  obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := hC a ha
  exact ⟨c, hc₁, hc₂.trans h⟩

lemma IsCover.subset [EDist E] {C : Set E} {ε : ℝ≥0∞} {A B : Set E}
    (h : A ⊆ B) (hC : IsCover C ε B) :
    IsCover C ε A := fun a ha ↦ hC a (h ha)

lemma internalCoveringNumber_anti [EDist E] {r r' : ℝ≥0∞} {A : Set E} (h : r ≤ r') :
    internalCoveringNumber r' A ≤ internalCoveringNumber r A := by
  rw [internalCoveringNumber, internalCoveringNumber]
  gcongr
  exact iInf_const_mono (IsCover.mono h)

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

@[simp]
lemma internalCoveringNumber_singleton [PseudoEMetricSpace E] {x : E} {r : ℝ≥0∞} :
    internalCoveringNumber r ({x} : Set E) = 1 :=
  internalCoveringNumber_eq_one_of_diam_le (by simp) (by simp)

@[simp]
lemma externalCoveringNumber_singleton [PseudoEMetricSpace E] {x : E} {r : ℝ≥0∞} :
    externalCoveringNumber r ({x} : Set E) = 1 :=
  externalCoveringNumber_eq_one_of_diam_le (by simp) (by simp)

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

lemma exists_finset_card_eq_internalCoveringNumber (h : TotallyBounded A) (hr : 0 < r) :
    ∃ (C : Finset E), ↑C ⊆ A ∧ IsCover (C : Set E) r A ∧ C.card = internalCoveringNumber r A := by
  have : Nonempty { s : Finset E // ↑s ⊆ A ∧ IsCover (↑s) r A } := by
    obtain ⟨C, hC⟩ := h.exists_isCover r hr
    exact⟨⟨C, hC⟩⟩
  let h := ENat.exists_eq_iInf
    (fun C : {s : Finset E // ↑s ⊆ A ∧ IsCover s r A} ↦ (C : Finset E).card)
  obtain ⟨C, hC⟩ := h
  refine ⟨C, C.2.1, C.2.2, ?_⟩
  rw [hC]
  simp_rw [iInf_subtype, iInf_and]
  rfl

open Classical in
/-- An internal `r`-cover of `A` with minimal cardinal. -/
noncomputable
def minimalCover (r : ℝ≥0∞) (A : Set E) (hr : 0 < r) : Finset E :=
  if h : TotallyBounded A
    then (exists_finset_card_eq_internalCoveringNumber h hr).choose else ∅

lemma minimalCover_subset (hr : 0 < r) : ↑(minimalCover r A hr) ⊆ A := by
  by_cases h : TotallyBounded A
  · simp only [minimalCover, h, dite_true]
    exact (exists_finset_card_eq_internalCoveringNumber h hr).choose_spec.1
  · simp only [minimalCover, h, dite_false, Finset.coe_empty, Set.empty_subset]

lemma isCover_minimalCover (h : TotallyBounded A) (hr : 0 < r) :
    IsCover (minimalCover r A hr : Set E) r A := by
  simp only [minimalCover, h, dite_true]
  exact (exists_finset_card_eq_internalCoveringNumber h hr).choose_spec.2.1

lemma card_minimalCover (h : TotallyBounded A) (hr : 0 < r) :
    (minimalCover r A hr).card = internalCoveringNumber r A := by
  simp only [minimalCover, h, dite_true]
  exact (exists_finset_card_eq_internalCoveringNumber h hr).choose_spec.2.2

end minimalCover

section maximalSeparatedSet

variable {r : ℝ≥0∞} {A : Set E}

lemma exists_finset_card_eq_packingNumber [PseudoEMetricSpace E] (h : packingNumber r A < ⊤) :
    ∃ (C : Finset E), ↑C ⊆ A ∧ IsSeparated r (C : Set E) ∧ C.card = packingNumber r A := by
  rcases Set.eq_empty_or_nonempty A with hA | hA
  · simp [hA, packingNumber]
  have : Nonempty { s : Finset E // ↑s ⊆ A ∧ IsSeparated r (↑s : Set E) } := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨⟨{a}, by simp [ha], by simp⟩⟩
  let h_exists := ENat.exists_eq_iSup_of_lt_top
    (f := fun C : { s : Finset E // ↑s ⊆ A ∧ IsSeparated r (↑s : Set E) } ↦ (C : Finset E).card)
  simp_rw [packingNumber] at h ⊢
  simp_rw [iSup_subtype, iSup_and] at h_exists
  specialize h_exists h
  obtain ⟨C, hC⟩ := h_exists
  refine ⟨C, C.2.1, C.2.2, ?_⟩
  rw [hC]

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
    simp only [Finset.coe_union, Finset.coe_singleton, Set.singleton_union, Set.mem_insert_iff, hax,
      Finset.mem_coe, false_or, hbx, C] at ha hb
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

lemma externalCoveringNumber_mono_set [EDist E] {r : ℝ≥0∞} {A B : Set E} (h : A ⊆ B) :
    externalCoveringNumber r A ≤ externalCoveringNumber r B := by
  simp only [externalCoveringNumber, le_iInf_iff]
  exact fun C hC ↦ iInf_le_of_le C <| iInf_le_of_le (hC.subset h) le_rfl

lemma internalCoveringNumber_subset_le [PseudoEMetricSpace E] {r : ℝ≥0∞} (hr : r ≠ ∞)
    {A B : Set E} (h : A ⊆ B) :
    internalCoveringNumber r A ≤ internalCoveringNumber (r / 2) B := by
  calc internalCoveringNumber r A
  _ ≤ packingNumber r A := internalCoveringNumber_le_packingNumber r A
  _ = packingNumber (2 * (r / 2)) A := by rw [ENNReal.mul_div_cancel (by simp) (by simp)]
  _ ≤ externalCoveringNumber (r / 2) A :=
    packingNumber_two_le_externalCoveringNumber A (by finiteness)
  _ ≤ externalCoveringNumber (r / 2) B := externalCoveringNumber_mono_set h
  _ ≤ internalCoveringNumber (r / 2) B :=
    externalCoveringNumber_le_internalCoveringNumber (r / 2) B

lemma internalCoveringNumber_le_encard [PseudoEMetricSpace E] (r : ℝ≥0∞) {A : Set E} :
    internalCoveringNumber r A ≤ A.encard := by
  by_cases h_top : A.encard = ⊤
  · simp [h_top]
  rw [internalCoveringNumber]
  refine iInf_le_of_le (Set.encard_ne_top_iff.mp h_top).toFinset <| iInf_le_of_le (by simp) <|
    iInf_le_of_le (fun a _ ↦ ⟨a, by simpa⟩) ?_
  rw [← (Set.encard_ne_top_iff.mp h_top).encard_eq_coe_toFinset_card]

end comparisons

lemma Isometry.isCover_image_iff {F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {f : E → F} (hf : Isometry f) {r : ℝ≥0∞} {A : Set E} (C : Set E) :
    IsCover (f '' C) r (f '' A) ↔ IsCover C r A := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨c, hc_mem, hc⟩ := h (f x) (Set.mem_image_of_mem _ hx)
    obtain ⟨c', hc', rfl⟩ := hc_mem
    refine ⟨c', hc', le_of_eq_of_le (hf.edist_eq _ _).symm hc⟩
  · obtain ⟨y, hy_mem, rfl⟩ := hx
    obtain ⟨c, hc_mem, hc⟩ := h y hy_mem
    refine ⟨f c, Set.mem_image_of_mem _ hc_mem, ?_⟩
    rwa [hf.edist_eq]

lemma Isometry.internalCoveringNumber_image'
    {F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {f : E → F} (hf : Isometry f) {r : ℝ≥0∞} {A : Set E} (hf_inj : Set.InjOn f A) :
    internalCoveringNumber r (f '' A) = internalCoveringNumber r A := by
  unfold internalCoveringNumber
  classical
  refine le_antisymm ?_ ?_
  · simp only [le_iInf_iff]
    intro C hC_subset hC_cover
    refine (iInf_le _ (C.image f)).trans ?_
    simp only [Finset.coe_image, Set.image_subset_iff]
    have : ↑C ⊆ f ⁻¹' (f '' A) := hC_subset.trans (Set.subset_preimage_image f A)
    refine (iInf_le _ this).trans ?_
    rw [hf.isCover_image_iff]
    refine (iInf_le _ hC_cover).trans ?_
    exact mod_cast Finset.card_image_le
  · simp only [le_iInf_iff]
    intro C hC_subset hC_cover
    obtain ⟨C', hC'_subset, rfl⟩ : ∃ (C' : Finset E), ↑C' ⊆ A ∧ C = C'.image f := by
      have (x : C) : ∃ y ∈ A, f y = x := by
        have hx : (x : F) ∈ f '' A := hC_subset x.2
        simpa only [Set.mem_image] using hx
      choose g hg_mem hg using this
      refine ⟨Finset.univ.image (fun x ↦ g x), ?_, ?_⟩
      · simp only [Finset.univ_eq_attach, Finset.coe_image, Finset.coe_attach, Set.image_univ]
        rwa [Set.range_subset_iff]
      · ext x
        simp only [Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach, true_and,
          Subtype.exists]
        refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
        · exact ⟨g ⟨x, h⟩, ⟨x, h, rfl⟩, hg _⟩
        · obtain ⟨x, hx, rfl⟩ := h
          obtain ⟨y, hy, rfl⟩ := hx
          rwa [hg]
    refine (iInf_le _ C').trans <| (iInf_le _ hC'_subset).trans ?_
    simp only [Finset.coe_image, hf.isCover_image_iff] at hC_cover
    refine (iInf_le _ hC_cover).trans ?_
    rw [Finset.card_image_iff.mpr (hf_inj.mono hC'_subset)]

lemma Isometry.internalCoveringNumber_image
    {F : Type*} [EMetricSpace E] [PseudoEMetricSpace F]
    {f : E → F} (hf : Isometry f) {r : ℝ≥0∞} {A : Set E} :
    internalCoveringNumber r (f '' A) = internalCoveringNumber r A :=
  hf.internalCoveringNumber_image' hf.injective.injOn

theorem internalCoveringNumber_Icc_zero_one_le_one_div {ε : ℝ≥0∞} (hε : ε ≤ 1) :
    internalCoveringNumber ε (Set.Icc (0 : ℝ) 1) ≤ 1 / ε := by
  obtain rfl | ε_pos := eq_zero_or_pos ε
  · simp
  -- Inequalities to be used in the proof
  have ε_ne_top : ε ≠ ∞ := hε.trans_lt (by norm_num) |>.ne
  have ε_toReal_pos : 0 < ε.toReal := toReal_pos ε_pos.ne' ε_ne_top
  have ε_toReal_le_one : ε.toReal ≤ 1 := toReal_le_of_le_ofReal (by norm_num) (by simpa)
  -- the biggest integer such that `1 / (k + 1) < ε ≤ 1 / k`.
  let k := ⌊1 / ε.toReal⌋₊
  have one_le_k : 1 ≤ k := (Nat.one_le_floor_iff _).2 (one_le_one_div ε_toReal_pos ε_toReal_le_one)
  have k_le : ↑k ≤ 1 / ε := by
    rw [← ofReal_toReal ε_ne_top, ← ofReal_one_div ε_toReal_pos,
      ENNReal.natCast_le_ofReal (by omega)]
    exact Nat.floor_le (by positivity)
  have hk1 : ε ≤ 1 / k := le_one_div_iff.1 k_le
  have hk2 : 1 / (k + 1) ≤ ε.toReal := by
    rw [one_div_le (by positivity) ε_toReal_pos]
    simp_rw [k]
    exact Nat.lt_floor_add_one _ |>.le
  have edist_le {x y : ℝ} {z : ℝ≥0∞} (h : |x - y| ≤ z.toReal) : edist x y ≤ z := by
    rw [edist_dist, Real.dist_eq]
    exact ofReal_le_of_le_toReal h
  -- We prove the result by constructing the cover of `[0, 1]` made by
  -- `1 / (k + 1), 2 / (k + 1), ..., k / (k + 1)`.
  let C : Finset ℝ := Finset.image (fun i : ℕ ↦ (i : ℝ) / (k + 1)) (Finset.Icc 1 k)
  have mem_C {x : ℝ} i (h1 : 1 ≤ i) (h2 : i ≤ k) (h3 : x = i / (k + 1)) : x ∈ C := by
    simp only [Finset.mem_image, Finset.mem_Icc, C]
    exact ⟨i, ⟨h1, h2⟩, h3.symm⟩
  -- It is indeed a cover.
  have : IsCover C ε (Set.Icc (0 : ℝ) 1) := by
    intro x ⟨hx1, hx2⟩
    -- There are 3 cases. If `x` is less than `1 / (k + 1)` then we can take `1 / (k + 1)`.
    -- Otherwise we can pick `i` the biggest integer such that `i / (k + 1) ≤ x`, but this
    -- does not work for `x = 1` because it gives `1`, which is not in the covering.
    -- We start with `x = 1`.
    obtain rfl | h1 := eq_or_lt_of_le hx2
    · refine ⟨k / (k + 1), mem_C k one_le_k le_rfl rfl, edist_le ?_⟩
      field_simp
      rwa [add_sub_cancel_left, abs_of_nonneg (by positivity)]
    -- Now the case `x < 1 / (k + 1)`
    obtain h2 | h2 := lt_or_ge x (1 / (k + 1) : ℝ)
    · refine ⟨1 / (k + 1), mem_C 1 le_rfl one_le_k (by simp), edist_le ?_⟩
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    -- Finally the general case
    refine ⟨⌊x * (k + 1)⌋₊ / (k + 1), mem_C ⌊x * (k + 1)⌋₊ ?_ ?_ rfl, edist_le ?_⟩
    · rwa [Nat.one_le_floor_iff, ← div_le_iff₀ (by positivity)]
    · rw [← Nat.lt_succ, Nat.floor_lt (by positivity)]
      calc
      x * (k + 1) < 1 * (k + 1) := (mul_lt_mul_iff_left₀ (by positivity)).2 h1
      _ = k.succ := by simp
    rw [abs_of_nonneg]
    · calc
      x - ⌊x * (k + 1)⌋₊ / (k + 1) = (x * (k + 1) - ⌊x * (k + 1)⌋₊) / (k + 1) := by field_simp
      _ ≤ 1 / (k + 1) := by
        rw [div_le_div_iff_of_pos_right (by positivity)]
        exact Nat.self_sub_floor_lt_one _ |>.le
      _ ≤ ε.toReal := hk2
    calc
    0 ≤ (x * (k + 1) - ⌊x * (k + 1)⌋₊) / (k + 1) :=
      div_nonneg (Nat.zero_le_self_sub_floor (by positivity)) (by positivity)
    _ = x - ⌊x * (k + 1)⌋₊ / (k + 1) := by field_simp
  -- It has the right cardinality.
  have card_C : C.card = k := by
    rw [← Nat.add_sub_cancel_right k 1, ← Nat.card_Icc]
    exact Finset.card_image_iff.2 <|
      div_left_injective₀ (by positivity)|>.comp CharZero.cast_injective |>.injOn
  -- It is a subset of `[0, 1]`.
  have C_sub : (C : Set ℝ) ⊆ Set.Icc 0 1 := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_Icc, Set.mem_image, Set.mem_Icc, C] at hx
    obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := hx
    exact ⟨by positivity, div_le_one (by positivity) |>.2 (by norm_cast; omega)⟩
  calc
  (internalCoveringNumber ε (Set.Icc (0 : ℝ) 1) : ℝ≥0∞) ≤ C.card := by
    norm_cast
    exact internalCoveringNumber_le_of_isCover C_sub this
  _ = k := by simp_all
  _ ≤ 1 / ε := k_le

section Volume

open MeasureTheory

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {A : Set E} {C : Finset E} {ε : ℝ≥0∞}

lemma volume_le_of_isCover (hC : IsCover C ε A) :
    volume A ≤ C.card * volume (EMetric.closedBall (0 : E) ε) := by
  have : A ⊆ ⋃ x ∈ C, EMetric.closedBall x ε := by rwa [EMetric.isCover_iff] at hC
  calc volume A
  _ ≤ volume (⋃ x ∈ C, EMetric.closedBall x ε) := measure_mono this
  _ ≤ ∑ x ∈ C, volume (EMetric.closedBall x ε) := measure_biUnion_finset_le _ _
  _ = C.card * volume (EMetric.closedBall (0 : E) ε) := by
    simp_rw [fun x ↦ Measure.IsAddLeftInvariant.measure_closedBall_const' volume x (0 : E) ε,
      Finset.sum_const, nsmul_eq_mul]

lemma volume_le_externalCoveringNumber_mul (A : Set E) {ε : ℝ≥0∞} (hε : 0 < ε) :
    volume A ≤ externalCoveringNumber ε A * volume (EMetric.closedBall (0 : E) ε) := by
  rw [externalCoveringNumber]
  let X := {C : Finset E | IsCover (C : Set E) ε A}
  change _ ≤ (⨅ C ∈ X, (C.card : ℕ∞)).toENNReal * _
  rw [← iInf_subtype'']
  obtain _ | _ := isEmpty_or_nonempty X
  · simp [ENat.iInf_eq_top_of_isEmpty, ENat.toENNReal_top,
      EMetric.measure_closedBall_pos _ _ hε.ne' |>.ne']
  obtain ⟨C, hC⟩ := ENat.exists_eq_iInf (fun C : X ↦ (C : Finset E).card)
  grw [← hC, volume_le_of_isCover C.2]
  norm_cast

open scoped Pointwise in
lemma le_volume_of_isSeparated (hC : IsSeparated ε (C : Set E)) (h_subset : ↑C ⊆ A) :
    C.card * volume (EMetric.closedBall (0 : E) (ε / 2))
      ≤ volume (A + EMetric.closedBall (0 : E) (ε / 2)) := by
  calc
  C.card * volume (EMetric.closedBall (0 : E) (ε / 2)) =
      ∑ x ∈ C, volume (EMetric.closedBall x (ε / 2)) := by
    simp_rw [fun x ↦ Measure.IsAddLeftInvariant.measure_closedBall_const' volume x (0 : E),
      Finset.sum_const, nsmul_eq_mul]
  _ = volume (⋃ x ∈ C, EMetric.closedBall x (ε / 2)) :=
    (measure_biUnion_finset hC.disjoint_closedBall
      fun _ _ ↦ EMetric.isClosed_closedBall.measurableSet).symm
  _ ≤ volume (A + EMetric.closedBall (0 : E) (ε / 2)) := by
    refine measure_mono fun x hx ↦ ?_
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨y, hy, hx⟩ := hx
    refine ⟨y, h_subset hy, x - y, ?_, by simp⟩
    rwa [EMetric.mem_closedBall, edist_zero_right, ← edist_eq_enorm_sub]

open scoped Pointwise in
lemma volume_eq_top_of_packingNumber (A : Set E) {ε : ℝ≥0∞} (hε : 0 < ε)
    (h : packingNumber ε A = ⊤) : volume (A + EMetric.closedBall (0 : E) (ε / 2)) = ∞ := by
  set X := {C : Finset E | (C : Set E) ⊆ A ∧ IsSeparated ε (C : Set E)}
  rw [packingNumber] at h
  have : ⨆ C : Finset E, ⨆ (_ : (C : Set E) ⊆ A), ⨆ (_ : IsSeparated ε (C : Set E)),
      C.card * volume (EMetric.closedBall (0 : E) (ε / 2)) = ⊤ := by
    simp_rw [← ENNReal.iSup_mul, ← ENat.toENNReal_coe, ← ENat.toENNReal_iSup, h]
    rw [ENat.toENNReal_top, top_mul]
    exact EMetric.measure_closedBall_pos volume _
        (ENNReal.div_ne_zero.2 ⟨hε.ne', by norm_num⟩) |>.ne'
  rw [eq_top_iff, ← this]
  exact iSup_le fun C ↦ iSup₂_le fun hC₁ hC₂ ↦ le_volume_of_isSeparated hC₂ hC₁

open scoped Pointwise in
lemma packingNumber_mul_le_volume (A : Set E) (ε : ℝ≥0∞) :
    packingNumber ε A * volume (EMetric.closedBall (0 : E) (ε / 2))
      ≤ volume (A + EMetric.closedBall (0 : E) (ε / 2)) := by
  obtain rfl | hε := eq_zero_or_pos ε
  · obtain _ | _ := subsingleton_or_nontrivial E
    · obtain rfl | hA := Set.eq_empty_or_nonempty A
      · simp
      rw [hA.eq_zero]
      simp
    · simp
  obtain h | h := eq_top_or_lt_top (packingNumber ε A)
  · simp [volume_eq_top_of_packingNumber A hε h]
  rw [← card_maximalSeparatedSet h]
  norm_cast
  exact le_volume_of_isSeparated isSeparated_maximalSeparatedSet maximalSeparatedSet_subset

lemma volume_div_le_internalCoveringNumber (A : Set E) {ε : ℝ≥0∞} (hε : 0 < ε) :
    volume A / volume (EMetric.closedBall (0 : E) ε) ≤ internalCoveringNumber ε A := by
  obtain rfl | hε' := eq_top_or_lt_top ε
  · obtain _ | _ := subsingleton_or_nontrivial E
    · grw [volume_le_externalCoveringNumber_mul A hε, ENNReal.mul_div_cancel_right,
        externalCoveringNumber_le_internalCoveringNumber ⊤ A]
      all_goals simp
    simp
  grw [volume_le_externalCoveringNumber_mul A hε, ENNReal.mul_div_cancel_right,
    externalCoveringNumber_le_internalCoveringNumber ε A]
  · exact EMetric.measure_closedBall_pos volume _ hε.ne' |>.ne'
  · lift ε to ℝ≥0 using hε'.ne
    rw [Metric.emetric_closedBall_nnreal]
    exact ProperSpace.isCompact_closedBall _ _ |>.measure_ne_top

open scoped Pointwise in
lemma internalCoveringNumber_le_volume_div (A : Set E) {ε : ℝ≥0∞} (hε₁ : 0 < ε) (hε₂ : ε < ∞) :
    internalCoveringNumber ε A
      ≤ volume (A + EMetric.closedBall (0 : E) (ε / 2))
        / volume (EMetric.closedBall (0 : E) (ε / 2)) := by
  grw [internalCoveringNumber_le_packingNumber, ENNReal.le_div_iff_mul_le,
    packingNumber_mul_le_volume]
  · exact Or.inl <| EMetric.measure_closedBall_pos volume _
      (ENNReal.div_ne_zero.2 ⟨hε₁.ne', by norm_num⟩) |>.ne'
  · lift ε to ℝ≥0 using hε₂.ne
    rw [show (ε : ℝ≥0∞) / 2 = ↑(ε / 2) by simp, Metric.emetric_closedBall_nnreal]
    exact Or.inl <| ProperSpace.isCompact_closedBall _ _ |>.measure_ne_top

lemma internalCoveringNumber_closedBall_ge (ε : ℝ≥0∞) (x : E) {r : ℝ≥0∞} (hr : 0 < r) :
    (r / ε) ^ (Module.finrank ℝ E) ≤ internalCoveringNumber ε (EMetric.closedBall x r) := by
  obtain _ | _ := subsingleton_or_nontrivial E
  · simp only [Module.finrank_zero_of_subsingleton, pow_zero]
    norm_cast
    exact EMetric.nonempty_closedBall.one_le_internalCoveringNumber _
  obtain rfl | hε := eq_zero_or_pos ε
  · simp only [internalCoveringNumber_zero]
    rw [Set.encard_eq_top]
    · simp
    · exact infinite_of_mem_nhds x (EMetric.closedBall_mem_nhds x hr)
  refine le_of_eq_of_le ?_
    (volume_div_le_internalCoveringNumber (EMetric.closedBall x r) hε)
  rw [InnerProductSpace.volume_closedBall_div']

lemma internalCoveringNumber_closedBall_one_ge (ε : ℝ≥0∞) (x : E) :
    ε⁻¹ ^ (Module.finrank ℝ E) ≤ internalCoveringNumber ε (EMetric.closedBall x 1) :=
  le_of_eq_of_le (by simp) (internalCoveringNumber_closedBall_ge _ _ (by norm_num))

lemma internalCoveringNumber_closedBall_le (ε : ℝ≥0∞) (x : E) (r : ℝ≥0∞) :
    internalCoveringNumber ε (EMetric.closedBall x r)
      ≤ (2 * r / ε + 1) ^ (Module.finrank ℝ E) := by
  obtain _ | _ := subsingleton_or_nontrivial E
  · simp only [Module.finrank_zero_of_subsingleton, pow_zero]
    norm_cast
    grw [internalCoveringNumber_le_encard, Set.encard_le_one_iff]
    exact fun a b _ _ ↦ Subsingleton.allEq a b
  obtain rfl | hε := eq_top_or_lt_top ε
  · simp [EMetric.nonempty_closedBall.internalCoveringNumber_top]
  obtain rfl | hr := eq_zero_or_pos r
  · simp
  lift ε to ℝ≥0 using hε.ne
  obtain rfl | hε' := eq_zero_or_pos ε
  · simp [div_zero, hr.ne']
  grw [internalCoveringNumber_le_volume_div (EMetric.closedBall x r),
    EMetric.closedBall_add_closedBall, InnerProductSpace.volume_closedBall_div',
    ← ENNReal.div_mul, ENNReal.add_div, ← mul_one_div (ε / 2 : ℝ≥0∞), ← ENNReal.mul_div_mul_comm,
    mul_comm (ε : ℝ≥0∞) 1, ENNReal.mul_div_mul_right, add_mul, ENNReal.div_mul_cancel,
    ENNReal.mul_comm_div, mul_comm (2 : ℝ≥0∞), mul_div_assoc]
  all_goals simp_all [hε'.ne']

lemma internalCoveringNumber_closedBall_one_le (ε : ℝ≥0∞) (x : E) :
    internalCoveringNumber ε (EMetric.closedBall x 1)
      ≤ (2 / ε + 1) ^ (Module.finrank ℝ E) :=
  (internalCoveringNumber_closedBall_le _ _ _).trans_eq (by simp)

lemma internalCoveringNumber_closedBall_le_three_mul [Nontrivial E]
    {ε : ℝ≥0∞} {x : E} {r : ℝ≥0∞} (hr_zero : r ≠ 0) (hr_top : r ≠ ∞) (hε : ε ≤ r) :
    internalCoveringNumber ε (EMetric.closedBall x r)
      ≤ (3 * r / ε) ^ (Module.finrank ℝ E) := by
  by_cases hε_zero : ε = 0
  · simp only [hε_zero, internalCoveringNumber_zero]
    rw [ENNReal.div_zero, ENNReal.top_pow]
    · exact le_top
    · exact Module.finrank_ne_zero
    · simp [hr_zero]
  refine (internalCoveringNumber_closedBall_le _ _ _).trans ?_
  let d := Module.finrank ℝ E
  calc (2 * r / ε + 1) ^ d
  _ ≤ (2 * r / ε + r / ε) ^ d := by
    gcongr
    rwa [ENNReal.le_div_iff_mul_le (.inl hε_zero) (.inr hr_top), one_mul]
  _ = (3 * r / ε) ^ d := by
    congr
    rw [← two_add_one_eq_three, add_mul, one_mul, ENNReal.add_div]

end Volume
