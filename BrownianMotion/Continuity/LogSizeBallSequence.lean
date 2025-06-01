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

variable {T : Type*} [PseudoEMetricSpace T] {a b c : ℝ≥0∞} {n : ℕ}

open Classical in
noncomputable
def logSizeRadius (t : T) (V : Finset T) (a b c : ℝ≥0∞) : ℕ :=
  if h : ∃ r : ℕ, #(V.filter fun x ↦ edist t x ≤ r * c) ≤  b * a ^ r
  then Nat.find h
  else 0

open Classical in
noncomputable
def logSizeBallSeq (J : Finset T) (hJ : J.Nonempty) (a b c : ℝ≥0∞) : ℕ → Finset T × T × ℕ :=
  Nat.rec ((J, hJ.choose, logSizeRadius hJ.choose J a b c))
    (fun _ (V, t, r) ↦
      let V' := V.filter (fun x ↦ (r - 1) * c < edist t x)
      let t' := if hV' : V'.Nonempty then hV'.choose else hJ.choose
      (V', t', logSizeRadius t' V' a b c))

open Classical in
noncomputable
def pairSetSeq (J : Finset T) (a b c : ℝ≥0∞) (n : ℕ) : Finset (T × T) :=
  if hJ : J.Nonempty then
    let S := logSizeBallSeq J hJ a b c
    Finset.product {(S n).2.1} ((S n).1.filter fun x ↦ edist (S n).2.1 x ≤ (S n).2.2 * c)
  else ∅

open Classical in
noncomputable
def pairSet (J : Finset T) (a b c : ℝ≥0∞) : Finset (T × T) :=
    Finset.biUnion (Finset.range #J) (pairSetSeq J a b c)

theorem pair_reduction (J : Finset T) (hJ : #J ≤ b * a ^ n) (ha : 1 < a) (E : Type*) [EDist E] :
    ∃ K : Finset (T × T), K ⊆ J.product J
      ∧ #K ≤ a * #J
      ∧ (∀ s t, (s, t) ∈ K → edist s t ≤ n * c)
      ∧ (∀ f : T → E,
        ⨆ (s) (t) (hs : s ∈ J) (ht : t ∈ J) (h : edist s t ≤ c), edist (f s) (f t)
        ≤ 2 * ⨆ p ∈ K, edist (f p.1) (f p.2)) := by
  refine ⟨pairSet J a b c, ?_, ?_, ?_⟩
  · sorry
  · sorry
  · sorry
