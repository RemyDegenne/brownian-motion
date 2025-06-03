/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Init

/-!
# TODO

-/

open MeasureTheory
open scoped ENNReal NNReal Finset

variable {T : Type*} [PseudoEMetricSpace T] {a c : ℝ≥0∞} {n : ℕ} {V : Finset T} {t : T}

lemma exists_radius_le (t : T) (V : Finset T) (ha : 1 < a) (c : ℝ≥0∞) :
    ∃ r : ℕ, 1 ≤ r ∧ #(V.filter fun x ↦ edist t x ≤ r * c) ≤ a ^ r := by
  obtain ⟨r, hr1, hr⟩ : ∃ r : ℕ, 1 ≤ r ∧ #V ≤ a ^ r := by
    sorry
  exact ⟨r, hr1, le_trans (mod_cast Finset.card_filter_le V _) hr⟩

open Classical in
noncomputable
def logSizeRadius (t : T) (V : Finset T) (a c : ℝ≥0∞) : ℕ :=
  if h : 1 < a then Nat.find (exists_radius_le t V h c) else 0

lemma one_le_logSizeRadius (ha : 1 < a) : 1 ≤ logSizeRadius t V a c := by
  rw [logSizeRadius, dif_pos ha]
  exact (Nat.find_spec (exists_radius_le t V ha c)).1

lemma card_le_logSizeRadius_le (ha : 1 < a) :
    #(V.filter fun x ↦ edist t x ≤ logSizeRadius t V a c * c) ≤ a ^ (logSizeRadius t V a c) := by
  rw [logSizeRadius, dif_pos ha]
  exact (Nat.find_spec (exists_radius_le t V ha c)).2

lemma card_le_logSizeRadius_ge (ha : 1 < a) (ht : t ∈ V) :
    a ^ (logSizeRadius t V a c - 1)
      ≤ #(V.filter fun x ↦ edist t x ≤ (logSizeRadius t V a c - 1) * c) := by
  by_cases h_one : logSizeRadius t V a c = 1
  · simp only [h_one, tsub_self, pow_zero, Nat.cast_one, zero_mul, nonpos_iff_eq_zero,
      Nat.one_le_cast, Finset.one_le_card]
    refine ⟨t, ?_⟩
    simp [ht]
  rw [logSizeRadius, dif_pos ha] at h_one ⊢
  have : Nat.find (exists_radius_le t V ha c) - 1 < Nat.find (exists_radius_le t V ha c) := by
    simp
  have h := Nat.find_min (exists_radius_le t V ha c) this
  simp only [ENNReal.natCast_sub, Nat.cast_one, not_and, not_le] at h
  refine (h ?_).le
  omega

open Classical in
noncomputable
def logSizeBallSeq (J : Finset T) (hJ : J.Nonempty) (a c : ℝ≥0∞) : ℕ → Finset T × T × ℕ :=
  Nat.rec ((J, hJ.choose, logSizeRadius hJ.choose J a c))
    (fun _ (V, t, r) ↦
      let V' := V.filter (fun x ↦ (r - 1) * c < edist t x)
      let t' := if hV' : V'.Nonempty then hV'.choose else hJ.choose
      (V', t', logSizeRadius t' V' a c))

variable {J : Finset T}

lemma logSizeRadius_logSizeBallSeq_le (hJ : J.Nonempty) (hJ_card : #J ≤ a ^ n) (i : ℕ) :
    (logSizeBallSeq J hJ a c i).2.2 ≤ n := by
  sorry

lemma logSizeBallSeq_subset (hJ : J.Nonempty) (i : ℕ) :
    (logSizeBallSeq J hJ a c (i + 1)).1 ⊆ (logSizeBallSeq J hJ a c i).1 := by
  sorry

lemma mem_logSizeBallSeq (hJ : J.Nonempty) (i : ℕ) (h : (logSizeBallSeq J hJ a c i).1.Nonempty) :
    (logSizeBallSeq J hJ a c i).2.1 ∈ (logSizeBallSeq J hJ a c i).1 := by
  sorry

lemma notMem_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : ℕ)
    (h : (logSizeBallSeq J hJ a c i).1.Nonempty) :
    (logSizeBallSeq J hJ a c i).2.1 ∉ (logSizeBallSeq J hJ a c (i + 1)).1 := by
  sorry

lemma card_logSizeBallSeq_add_one_lt (hJ : J.Nonempty) (i : ℕ)
    (h : (logSizeBallSeq J hJ a c i).1.Nonempty) :
    #(logSizeBallSeq J hJ a c (i + 1)).1 < #(logSizeBallSeq J hJ a c 1).1 := by
  sorry

lemma card_logSizeBallSeq_le (hJ : J.Nonempty) (i : ℕ) :
    #(logSizeBallSeq J hJ a c i).1 ≤ #J - i := by
  sorry

lemma card_logSizeBall_card_eq_zero (hJ : J.Nonempty) :
    #(logSizeBallSeq J hJ a c #J).1 = 0 := by
  sorry

open Classical in
noncomputable
def pairSetSeq (J : Finset T) (a c : ℝ≥0∞) (n : ℕ) : Finset (T × T) :=
  if hJ : J.Nonempty then
    let S := logSizeBallSeq J hJ a c
    Finset.product {(S n).2.1} ((S n).1.filter fun x ↦ edist (S n).2.1 x ≤ (S n).2.2 * c)
  else ∅

open Classical in
noncomputable
def pairSet (J : Finset T) (a c : ℝ≥0∞) : Finset (T × T) :=
  Finset.biUnion (Finset.range #J) (pairSetSeq J a c)

lemma card_pairSet_le (hJ_card : #J ≤ a ^ n) (ha : 1 < a) :
    #(pairSet J a c) ≤ a * #J := by
  sorry

lemma edist_le_of_mem_pairSet (hJ_card : #J ≤ a ^ n) (ha : 1 < a) (hc : c ≠ 0)
    {s t : T} (h : (s, t) ∈ pairSet J a c) :
    edist s t ≤ n * c := by
  sorry

theorem pair_reduction (J : Finset T) (hJ : #J ≤ a ^ n) (ha : 1 < a) (hc : c ≠ 0)
    (E : Type*) [EDist E] :
    ∃ K : Finset (T × T), K ⊆ J.product J
      ∧ #K ≤ a * #J
      ∧ (∀ s t, (s, t) ∈ K → edist s t ≤ n * c)
      ∧ (∀ f : T → E,
        ⨆ (s) (t) (hs : s ∈ J) (ht : t ∈ J) (h : edist s t ≤ c), edist (f s) (f t)
        ≤ 2 * ⨆ p ∈ K, edist (f p.1) (f p.2)) := by
  refine ⟨pairSet J a c, ?_, ?_, ?_, ?_⟩
  · sorry
  · exact card_pairSet_le hJ ha
  · exact fun _ _ ↦ edist_le_of_mem_pairSet hJ ha hc
  · sorry
