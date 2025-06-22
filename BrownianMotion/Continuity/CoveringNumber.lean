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

lemma internalCoveringNumber_le_of_isCover [EDist E] {C : Finset E} {r : ℝ≥0∞} {A : Set E}
    (C_sub : ↑C ⊆ A) (C_cov : IsCover C r A) :
    internalCoveringNumber r A ≤ C.card :=
  iInf_le_of_le C <| iInf_le_of_le C_sub <| iInf_le_of_le C_cov le_rfl

@[simp]
lemma IsCover.self [PseudoEMetricSpace E] (A : Set E) (r : ℝ≥0∞) : IsCover A r A :=
  fun a ha => ⟨a, ha, by simp⟩

lemma Set.Finite.internalCoveringNumber_le_ncard [PseudoEMetricSpace E] (r : ℝ≥0∞) (A : Set E)
    (ha : A.Finite) : internalCoveringNumber r A ≤ A.ncard := by
  rw [internalCoveringNumber]
  exact sInf_le ⟨ha.toFinset, by simpa using (ncard_eq_toFinset_card _ _).symm⟩

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

lemma IsCover.mono [EDist E] {C : Set E} {ε ε' : ℝ≥0∞} {A : Set E} (h : ε ≤ ε')
    (hC : IsCover C ε A) : IsCover C ε' A := by
  intro a ha
  obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := hC a ha
  exact ⟨c, hc₁, hc₂.trans h⟩

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

section Volume

open MeasureTheory

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {A : Set E} {C : Finset E} {ε : ℝ≥0∞}

lemma volume_le_of_isCover (hC : IsCover C ε A) :
    volume A ≤ C.card * volume (EMetric.closedBall (0 : E) ε) := by
  sorry

lemma volume_le_externalCoveringNumber_mul (A : Set E) (ε : ℝ≥0∞) :
    volume A ≤ externalCoveringNumber ε A * volume (EMetric.closedBall (0 : E) ε) := by
  sorry

open scoped Pointwise in
lemma le_volume_of_isSeparated (hC : IsSeparated ε (C : Set E)) (h_subset : ↑C ⊆ A) :
    C.card * volume (EMetric.ball (0 : E) (ε/2)) ≤ volume (A + EMetric.ball (0 : E) (ε/2)) := by
  sorry

open scoped Pointwise in
lemma packingNumber_mul_le_volume (A : Set E) (ε : ℝ≥0∞) :
    packingNumber ε A * volume (EMetric.ball (0 : E) (ε/2))
      ≤ volume (A + EMetric.ball (0 : E) (ε/2)) := by
  sorry

lemma volume_div_le_internalCoveringNumber (A : Set E) (ε : ℝ≥0∞) :
    volume A / volume (EMetric.closedBall (0 : E) ε) ≤ internalCoveringNumber ε A := by
  sorry

open scoped Pointwise in
lemma internalCoveringNumber_le_volume_div (A : Set E) (ε : ℝ≥0∞) :
    internalCoveringNumber ε A
      ≤ volume (A + EMetric.ball (0 : E) (ε/2)) / volume (EMetric.closedBall (0 : E) (ε/2)) := by
  sorry

lemma internalCoveringNumber_closedBall_ge (ε : ℝ≥0∞) :
    ε⁻¹ ^ (Module.finrank ℝ E) ≤ internalCoveringNumber ε (EMetric.closedBall (0 : E) 1) := by
  sorry

lemma internalCoveringNumber_closedBall_le (ε : ℝ≥0∞) :
    internalCoveringNumber ε (EMetric.closedBall (0 : E) 1)
      ≤ (2 / ε + 1) ^ (Module.finrank ℝ E) := by
  sorry

end Volume
