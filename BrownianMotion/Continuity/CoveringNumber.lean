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

open ENNReal

variable {E : Type*}

section Definitions

variable [EDist E]

/-- A set `C` is an `r`-cover of another set `A` if every point in `A` belongs to a ball with radius
`r` around a point of `C`. -/
def IsCover (C : Set E) (ε : ℝ≥0∞) (A : Set E) : Prop :=
  ∀ a ∈ A, ∃ c ∈ C, edist a c ≤ ε

/-- A set `C` is a `r`-separated if all pairs of points `a,b` of `C` satisfy `r < dist a b`. -/
def IsSeparated (C : Set E) (r : ℝ≥0∞) : Prop :=
  ∀ (a : E) (b : E) (_ : a ∈ C) (_ : b ∈ C), r < edist a b

noncomputable
def externalCoveringNumber (r : ℝ≥0∞) (A : Set E) : ENat :=
  ⨅ (C : Finset E) (_ : IsCover C r A), C.card

noncomputable
def internalCoveringNumber (r : ℝ≥0∞) (A : Set E) : ENat :=
  ⨅ (C : Finset E) (_ : ↑C ⊆ A) (_ : IsCover C r A), C.card

noncomputable
def packingNumber (r : ℝ≥0∞) (A : Set E) : ENat :=
  ⨆ (C : Finset E) (_ : ↑C ⊆ A) (_ : IsSeparated (C : Set E) r), C.card

end Definitions

lemma EMetric.isCover_iff [PseudoEMetricSpace E] {C : Set E} {ε : ℝ≥0∞} {A : Set E} :
    IsCover C ε A ↔ A ⊆ ⋃ x ∈ C, EMetric.closedBall x ε := by
  simp [IsCover, Set.subset_def]

lemma isCover_singleton_of_diam_le [PseudoEMetricSpace E] {ε : ℝ≥0∞} {A : Set E} {a : E}
    (hA : EMetric.diam A ≤ ε) (ha : a ∈ A) :
    IsCover ({a} : Set E) ε A := by
  intro x hxA
  simp only [Set.mem_singleton_iff, exists_eq_left]
  refine le_trans ?_ hA
  exact EMetric.edist_le_diam_of_mem hxA ha

lemma internalCoveringNumber_eq_one_of_diam_le [PseudoEMetricSpace E] {r : ℝ≥0∞} {A : Set E}
    (h_nonempty : A.Nonempty) (hA : EMetric.diam A ≤ r) :
    internalCoveringNumber r A = 1 := by
  sorry

lemma internalCoveringNumber_le_one_of_diam_le [PseudoEMetricSpace E] {r : ℝ≥0∞} {A : Set E}
    (hA : EMetric.diam A ≤ r) :
    internalCoveringNumber r A ≤ 1 := by
  sorry

@[simp]
lemma isSeparated_empty [EDist E] (r : ℝ≥0∞) : IsSeparated (∅ : Set E) r := by
  intros a b ha _
  simp at ha

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

lemma exists_finset_card_eq_packingNumber [EDist E] (h : packingNumber r A < ⊤) :
    ∃ (C : Finset E), ↑C ⊆ A ∧ IsSeparated (C : Set E) r ∧ C.card = packingNumber r A := by
  sorry

/-- A maximal `r`-separated finite subset of `A`. -/
noncomputable
def maximalSeparatedSet [EDist E] (r : ℝ≥0∞) (A : Set E) : Finset E :=
  if h : packingNumber r A < ⊤ then (exists_finset_card_eq_packingNumber h).choose else ∅

lemma maximalSeparatedSet_subset [EDist E] : ↑(maximalSeparatedSet r A) ⊆ A := by
  by_cases h : packingNumber r A < ⊤
  · simp only [maximalSeparatedSet, h, dite_true]
    exact (exists_finset_card_eq_packingNumber h).choose_spec.1
  · simp only [maximalSeparatedSet, h, dite_false, Finset.coe_empty, Set.empty_subset]

lemma isSeparated_maximalSeparatedSet [EDist E] :
    IsSeparated (maximalSeparatedSet r A : Set E) r := by
  by_cases h : packingNumber r A < ⊤
  · simp only [maximalSeparatedSet, h, dite_true]
    exact (exists_finset_card_eq_packingNumber h).choose_spec.2.1
  · simp only [maximalSeparatedSet, h, dite_false, Finset.coe_empty,isSeparated_empty]

lemma card_maximalSeparatedSet [EDist E] (h : packingNumber r A < ⊤) :
    (maximalSeparatedSet r A).card = packingNumber r A := by
  simp only [maximalSeparatedSet, h, dite_true]
  exact (exists_finset_card_eq_packingNumber h).choose_spec.2.2

lemma card_le_of_isSeparated [EDist E] {C : Finset E} (h_subset : ↑C ⊆ A)
    (h : IsSeparated (C : Set E) r) :
    C.card ≤ (maximalSeparatedSet r A).card := by
  sorry

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
  have hC_separated : IsSeparated (C : Set E) r := by
    sorry
  refine absurd (card_le_of_isSeparated hC_subset hC_separated) ?_
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

theorem packingNumber_two_le_externalCoveringNumber [EDist E] (r : ℝ≥0∞) (A : Set E) :
    packingNumber (2 * r) A ≤ externalCoveringNumber r A := by
  simp only [packingNumber, externalCoveringNumber, le_iInf_iff, iSup_le_iff, Nat.cast_le]
  intro C hC_cover D hD_subset hD_separated
  sorry

theorem externalCoveringNumber_le_internalCoveringNumber [EDist E] (r : ℝ≥0∞) (A : Set E) :
    externalCoveringNumber r A ≤ internalCoveringNumber r A := by
  simp only [externalCoveringNumber, internalCoveringNumber, le_iInf_iff]
  exact fun C _ hC_cover ↦ iInf₂_le C hC_cover

theorem internalCoveringNumber_two_le_externalCoveringNumber [PseudoEMetricSpace E]
    (r : ℝ≥0∞) (A : Set E) :
    internalCoveringNumber (2 * r) A ≤ externalCoveringNumber r A := by
  refine (internalCoveringNumber_le_packingNumber _ A).trans ?_
  exact packingNumber_two_le_externalCoveringNumber r A

theorem test (ε : ℝ≥0∞) (hε : ε ≤ 1) : internalCoveringNumber ε (Set.Icc (0 : ℝ) 1) ≤ 1 / ε := by
  obtain rfl | h := eq_zero_or_pos ε
  · simp
  let k := ⌊1 / ε.toReal⌋₊
  have one_le_k : 1 ≤ k := by
    rw [Nat.one_le_floor_iff]
    apply one_le_one_div
    · exact toReal_pos h.ne' (hε.trans_lt (by norm_num) |>.ne)
    · refine toReal_le_of_le_ofReal (by norm_num) (by simpa)
  have k_le : ↑k ≤ 1 / ε := calc
    (k : ℝ≥0∞) ≤ ENNReal.ofReal (1 / ε.toReal) := by
      rw [ENNReal.natCast_le_ofReal (by linarith)]
      exact Nat.floor_le (by positivity)
    _ = 1 / ε := by
      rw [ENNReal.ofReal_div_of_pos]
      · simp only [ofReal_one, one_div, inv_inj, ofReal_toReal_eq_iff]
        exact hε.trans_lt (by norm_num) |>.ne
      refine toReal_pos h.ne' (hε.trans_lt (by norm_num) |>.ne)
  have hk1 : ε ≤ 1 / k := by
    refine (ENNReal.le_div_iff_mul_le (by simp) (by simp)).mpr ?_
    rw [mul_comm]
    refine (ENNReal.le_div_iff_mul_le (by simp) (by simp)).mp k_le
  have hk2 : 1 / (k + 1) ≤ ε.toReal := by
    rw [one_div_le]
    simp_rw [k]
    exact Nat.lt_floor_add_one (1 / ε.toReal) |>.le
    positivity
    exact toReal_pos h.ne' (hε.trans_lt (by norm_num) |>.ne)
  let C : Finset ℝ := Finset.image (fun i : ℕ ↦ (i : ℝ) / (k + 1)) (Finset.Icc 1 k)
  have : IsCover C ε (Set.Icc (0 : ℝ) 1) := by
    intro x ⟨hx1, hx2⟩
    obtain rfl | h1 := eq_or_lt_of_le hx2
    · refine ⟨k / (k + 1), ?_, ?_⟩
      · simp only [Finset.coe_image, Finset.coe_Icc, Set.mem_image, Set.mem_Icc,
        mul_eq_mul_right_iff, Nat.cast_inj, inv_eq_zero, C]
        exact ⟨k, ⟨one_le_k, le_rfl⟩, rfl⟩
      rw [edist_dist, Real.dist_eq]
      apply ofReal_le_of_le_toReal
      field_simp
      rw [abs_of_nonneg (by positivity)]
      exact hk2
    obtain h2 | h2 := le_or_gt (1 / (k + 1) : ℝ) x
    · refine ⟨⌊x * (k + 1)⌋₊ / (k + 1), ?_, ?_⟩
      · simp only [Finset.coe_image, Finset.coe_Icc, Set.mem_image, Set.mem_Icc, C]
        refine ⟨⌊x * (k + 1)⌋₊, ⟨?_, ?_⟩, rfl⟩
        · rwa [Nat.one_le_floor_iff, ← div_le_iff₀]
          norm_cast
          simp
        rw [← Nat.lt_succ, Nat.floor_lt (by positivity)]
        calc
        x * (k + 1) < 1 * (k + 1) := (_root_.mul_lt_mul_right (by positivity)).2 h1
        _ = k.succ := by simp
      rw [edist_dist, Real.dist_eq, abs_of_nonneg]
      · apply ofReal_le_of_le_toReal
        calc
        x - ⌊x * (k + 1)⌋₊ / (k + 1) = (x * (k + 1) - ⌊x * (k + 1)⌋₊) / (k + 1) := by field_simp
        _ ≤ 1 / (k + 1) := by
          rw [div_le_div_iff_of_pos_right (by positivity), sub_le_iff_le_add, add_comm 1]
          exact Nat.lt_floor_add_one _ |>.le
        _ ≤ ε.toReal := hk2
      calc
      0 ≤ (x * (k + 1) - ⌊x * (k + 1)⌋₊) / (k + 1) := by
        apply div_nonneg
        · simp only [sub_nonneg]
          exact Nat.floor_le (by positivity)
        positivity
      _ = x - ⌊x * (k + 1)⌋₊ / (k + 1) := by
        rw [sub_div, mul_div_cancel_right₀]
        positivity
    · refine ⟨1 / (k + 1), ?_, ?_⟩
      · simp only [Finset.coe_image, Finset.coe_Icc, Set.mem_image, Set.mem_Icc, C]
        exact ⟨1, ⟨le_rfl, one_le_k⟩, by simp⟩
      rw [edist_dist, Real.dist_eq]
      apply ofReal_le_of_le_toReal
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
  have card_C : C.card = k := by
    rw [← Nat.add_sub_cancel_right k 1, ← Nat.card_Icc]
    apply Finset.card_image_iff.2
    apply Function.Injective.injOn
    change Function.Injective ((fun x : ℝ ↦ x / (k + 1)) ∘ ((↑) : ℕ → ℝ))
    apply Function.Injective.comp
    · intro x y hxy
      field_simp at hxy
      exact hxy
    · exact CharZero.cast_injective
  have C_sub : (C : Set ℝ) ⊆ Set.Icc 0 1 := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_Icc, Set.mem_image, Set.mem_Icc, C] at hx
    obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := hx
    rw [Set.mem_Icc]
    constructor
    · positivity
    · rw [div_le_one]
      norm_cast
      omega
      positivity
  calc
  (internalCoveringNumber ε (Set.Icc (0 : ℝ) 1) : ℝ≥0∞) ≤ C.card := by
    norm_cast
    rw [internalCoveringNumber]
    refine iInf₂_le_of_le C C_sub fun a ha ↦ ⟨C.card, ?_, ?_⟩
    · exact iInf_pos this
    simp_all
  _ = k := by simp_all
  _ ≤ 1 / ε := k_le

end comparisons
