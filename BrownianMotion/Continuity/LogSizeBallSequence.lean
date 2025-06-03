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

structure logSizeBallStruct (T : Type*) where
  finset : Finset T
  point : T
  radius : ℕ

noncomputable
def logSizeBallStruct.smallBall (struct : logSizeBallStruct T) (c : ℝ≥0∞) :
    Finset T :=
  struct.finset.filter fun x ↦ edist struct.point x ≤ (struct.radius - 1) * c

noncomputable
def logSizeBallStruct.ball (struct : logSizeBallStruct T) (c : ℝ≥0∞) :
    Finset T :=
  struct.finset.filter fun x ↦ edist struct.point x ≤ struct.radius * c

open Classical in
noncomputable
def logSizeBallSeq (J : Finset T) (hJ : J.Nonempty) (a c : ℝ≥0∞) : ℕ → logSizeBallStruct T :=
  Nat.rec ({finset := J, point := hJ.choose, radius := logSizeRadius hJ.choose J a c})
    (fun _ struct ↦
      let V' := struct.finset \ struct.smallBall c
      let t' := if hV' : V'.Nonempty then hV'.choose else struct.point
      { finset := V',
        point := t',
        radius := logSizeRadius t' V' a c })

variable {J : Finset T}

lemma finset_logSizeBallSeq_zero (hJ : J.Nonempty) :
    (logSizeBallSeq J hJ a c 0).finset = J := rfl

lemma point_logSizeBallSeq_zero (hJ : J.Nonempty) :
    (logSizeBallSeq J hJ a c 0).point = hJ.choose := rfl

lemma radius_logSizeBallSeq_zero (hJ : J.Nonempty) :
    (logSizeBallSeq J hJ a c 0).radius = logSizeRadius hJ.choose J a c := rfl

open Classical in
lemma finset_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : ℕ) :
    (logSizeBallSeq J hJ a c (i + 1)).finset =
      (logSizeBallSeq J hJ a c i).finset \ (logSizeBallSeq J hJ a c i).smallBall c := rfl

open Classical in
lemma point_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : ℕ) :
    (logSizeBallSeq J hJ a c (i + 1)).point
      = if hV' : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty then hV'.choose
        else (logSizeBallSeq J hJ a c i).point := rfl

lemma radius_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : ℕ) :
    (logSizeBallSeq J hJ a c (i + 1)).radius
      = logSizeRadius (logSizeBallSeq J hJ a c (i + 1)).point
          (logSizeBallSeq J hJ a c (i + 1)).finset a c := rfl

lemma radius_logSizeBallSeq_le (hJ : J.Nonempty) (hJ_card : #J ≤ a ^ n) (i : ℕ) :
    (logSizeBallSeq J hJ a c i).radius ≤ n := by
  sorry

lemma finset_logSizeBallSeq_add_one_subset (hJ : J.Nonempty) (i : ℕ) :
    (logSizeBallSeq J hJ a c (i + 1)).finset ⊆ (logSizeBallSeq J hJ a c i).finset := by
  sorry

lemma point_mem_finset_logSizeBallSeq (hJ : J.Nonempty) (i : ℕ)
    (h : (logSizeBallSeq J hJ a c i).finset.Nonempty) :
    (logSizeBallSeq J hJ a c i).point ∈ (logSizeBallSeq J hJ a c i).finset := by
  sorry

lemma point_notMem_finset_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : ℕ)
    (h : (logSizeBallSeq J hJ a c i).1.Nonempty) :
    (logSizeBallSeq J hJ a c i).point ∉ (logSizeBallSeq J hJ a c (i + 1)).finset := by
  sorry

lemma card_finset_logSizeBallSeq_add_one_lt (hJ : J.Nonempty) (i : ℕ)
    (h : (logSizeBallSeq J hJ a c i).finset.Nonempty) :
    #(logSizeBallSeq J hJ a c (i + 1)).finset < #(logSizeBallSeq J hJ a c i).finset := by
  sorry

lemma card_finset_logSizeBallSeq_le (hJ : J.Nonempty) (i : ℕ) :
    #(logSizeBallSeq J hJ a c i).finset ≤ #J - i := by
  sorry

lemma card_finset_logSizeBallSeq_card_eq_zero (hJ : J.Nonempty) :
    #(logSizeBallSeq J hJ a c #J).finset = 0 := by
  sorry

lemma disjoint_smallBall_logSizeBallSeq (hJ : J.Nonempty) (i j : ℕ) (hij : i ≠ j) :
    Disjoint
      ((logSizeBallSeq J hJ a c i).smallBall c) ((logSizeBallSeq J hJ a c j).smallBall c) := by
  sorry

open Classical in
noncomputable
def pairSetSeq (J : Finset T) (a c : ℝ≥0∞) (n : ℕ) : Finset (T × T) :=
  if hJ : J.Nonempty then
    Finset.product {(logSizeBallSeq J hJ a c n).point} ((logSizeBallSeq J hJ a c n).ball c)
  else ∅

open Classical in
noncomputable
def pairSet (J : Finset T) (a c : ℝ≥0∞) : Finset (T × T) :=
  Finset.biUnion (Finset.range #J) (pairSetSeq J a c)

lemma pairSet_subset : pairSet J a c ⊆ J.product J := by
  sorry

lemma card_pairSet_le (hJ_card : #J ≤ a ^ n) (ha : 1 < a) :
    #(pairSet J a c) ≤ a * #J := by
  sorry

lemma edist_le_of_mem_pairSet (hJ_card : #J ≤ a ^ n) (ha : 1 < a) (hc : c ≠ 0)
    {s t : T} (h : (s, t) ∈ pairSet J a c) :
    edist s t ≤ n * c := by
  sorry

lemma iSup_edist_pairSet {E : Type*} [PseudoEMetricSpace E] (f : T → E) :
    ⨆ (s) (t) (hs : s ∈ J) (ht : t ∈ J) (h : edist s t ≤ c), edist (f s) (f t)
        ≤ 2 * ⨆ p ∈ pairSet J a c, edist (f p.1) (f p.2) := by
  sorry

theorem pair_reduction (J : Finset T) (hJ : #J ≤ a ^ n) (ha : 1 < a) (hc : c ≠ 0)
    (E : Type*) [PseudoEMetricSpace E] :
    ∃ K : Finset (T × T), K ⊆ J.product J
      ∧ #K ≤ a * #J
      ∧ (∀ s t, (s, t) ∈ K → edist s t ≤ n * c)
      ∧ (∀ f : T → E,
        ⨆ (s) (t) (_hs : s ∈ J) (_ht : t ∈ J) (_h : edist s t ≤ c), edist (f s) (f t)
        ≤ 2 * ⨆ p ∈ K, edist (f p.1) (f p.2)) := by
  refine ⟨pairSet J a c, ?_, ?_, ?_, ?_⟩
  · exact pairSet_subset
  · exact card_pairSet_le hJ ha
  · exact fun _ _ ↦ edist_le_of_mem_pairSet hJ ha hc
  · exact iSup_edist_pairSet
