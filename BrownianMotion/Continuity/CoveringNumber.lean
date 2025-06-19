/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Algebra
import BrownianMotion.Auxiliary.ENNReal
import BrownianMotion.Auxiliary.Nat
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

lemma internalCoveringNumber_le_of_isCover [EDist E] {C : Finset E} {r : ℝ≥0∞} {A : Set E}
    (C_sub : ↑C ⊆ A) (C_cov : IsCover C r A) :
    internalCoveringNumber r A ≤ C.card :=
  iInf_le_of_le C <| iInf_le_of_le C_sub <| iInf_le_of_le C_cov le_rfl

lemma EMetric.isCover_iff [PseudoEMetricSpace E] {C : Set E} {ε : ℝ≥0∞} {A : Set E} :
    IsCover C ε A ↔ A ⊆ ⋃ x ∈ C, EMetric.closedBall x ε := by
  simp [IsCover, Set.subset_def]

lemma not_isCover_empty [EDist E] (ε : ℝ≥0∞) (A : Set E) (h_nonempty : A.Nonempty) :
    ¬ IsCover (∅ : Set E) ε A := by
  simpa [IsCover]

lemma isCover_singleton_of_diam_le [PseudoEMetricSpace E] {ε : ℝ≥0∞} {A : Set E} {a : E}
    (hA : EMetric.diam A ≤ ε) (ha : a ∈ A) :
    IsCover ({a} : Set E) ε A := by
  intro x hxA
  simp only [Set.mem_singleton_iff, exists_eq_left]
  refine le_trans ?_ hA
  exact EMetric.edist_le_diam_of_mem hxA ha

lemma cover_eq_of_lt_iInf_edist [PseudoEMetricSpace E] {C : Set E} {ε : ℝ≥0∞} {A : Set E}
    (hC : IsCover C ε A) (hC_subset : C ⊆ A)
    (hε : ε < ⨅ (s : A) (t : { t : A // s ≠ t }), edist s t) : C = A := by
  sorry

lemma internalCoveringNumber_eq_one_of_diam_le [PseudoEMetricSpace E] {r : ℝ≥0∞} {A : Set E}
    (h_nonempty : A.Nonempty) (hA : EMetric.diam A ≤ r) :
    internalCoveringNumber r A = 1 := by
  refine le_antisymm ?_ ?_
  · have ⟨a, ha⟩ := h_nonempty
    let C := ({a} : Finset E)
    have hC : ↑C ⊆ A := by simp [C, ha]
    calc
      _ ≤ _ := iInf₂_le (α := ℕ∞) C hC
      _ ≤ C.card := by
        refine iInf_le (α := ℕ∞) _ fun b hb ↦ ⟨a, by simp [C], hA.trans' ?_⟩
        simp only [EMetric.diam, C]
        trans ⨆ y ∈ A, edist b y
        · exact le_iSup₂ (α := ENNReal) a ha
        · exact le_iSup₂ (α := ENNReal) b hb
      _ ≤ _ := by simp [C]
  · refine le_iInf₂ (α := ℕ∞) fun C hC ↦ ?_
    refine le_iInf (α := ℕ∞) fun hCoverC ↦ ?_
    by_contra! hcontra
    apply (ENat.lt_one_iff_eq_zero).mp at hcontra
    simp only [Nat.cast_eq_zero, Finset.card_eq_zero] at hcontra
    rw [hcontra, Finset.coe_empty] at hCoverC
    exact not_isCover_empty r _ h_nonempty hCoverC

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
      rwa [abs_of_nonneg (by positivity)]
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
      x * (k + 1) < 1 * (k + 1) := (_root_.mul_lt_mul_right (by positivity)).2 h1
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

end comparisons
