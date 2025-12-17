/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Wojciech Czernous
-/
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Probability.Process.HittingTime
import Init.Data.Function

/-!
# Hitting times when enlarging the time index set

## Main results

* `hittingBtwn_monotone_in_index_set`: a discrete hitting time of an adapted process
  may not become earlier after restricting the time index set.
-/

variable {Ω β ι κ : Type*} {m : MeasurableSpace Ω}
  [ConditionallyCompleteLinearOrder ι] [ConditionallyCompleteLinearOrder κ]

open ProbabilityTheory MeasureTheory
open scoped Classical in

set_option diagnostics true in
/- Given the injection map f : ι ↪ κ, we show that the hitting time of the process
  u : ι → Ω → β is not earlier (up to f) than the hitting time of the process v : κ → Ω → β,
  where u is the restriction of v, given by f. -/

example (s : Set ι) (hempty : s = ∅) : s.Finite := by
  exact hempty.symm ▸ Set.finite_empty

private lemma CCLO.sInf_image_le_of_sInf_attained
  (f : ι → κ) (s : Set ι) (hatt : sInf s ∈ s)
  (hbfs : BddBelow (f '' s))
    : sInf (f '' s) ≤ f (sInf s) := by
  simpa using
    ConditionallyCompleteLattice.csInf_le (f '' s) _ hbfs (Set.mem_image_of_mem _ hatt)

private lemma CCLO.sInf_sup_image_le_of_sInf_attained
  (f : ι → κ) (s : Set ι) (hatt : sInf s ∈ s)
  (t : Set κ)
  (hbt : BddBelow t)
  (hfssubt : f '' s ⊆ t) : sInf (t) ≤ f (sInf s) := by
  simpa using
    ConditionallyCompleteLattice.csInf_le t _ hbt (hfssubt (Set.mem_image_of_mem _ hatt))


lemma hittingBtwn_not_earlier_when_restricting_index_set
  (f : ι → κ) (hmono : Monotone f)
  (hfinι : ∀ n m : ι, (Set.Icc n m).Finite) -- finite intervals in ι
  (u : ι → Ω → β) (v : κ → Ω → β) (hv : ∀ i : ι, v (f i) = u i) -- u is a restriction of v to f(ι)
  (s : Set β) (n m : ι) : ∀ ω : Ω, hittingBtwn v s (f n) (f m) ω ≤ f (hittingBtwn u s n m ω) := by
    intro ω
    let A := ∃ j ∈ Set.Icc n m, u j ω ∈ s
    let B := ∃ j ∈ Set.Icc (f n) (f m), v j ω ∈ s
    have hfIcc : ∀ ⦃i⦄, i ∈ Set.Icc n m → f i ∈ Set.Icc (f n) (f m) :=
      fun _ ⟨h₁, h₂⟩ => ⟨hmono h₁, hmono h₂⟩
    have hAB : A → B := by
      rintro ⟨j, hj, hj_in_s⟩
      exact ⟨f j, ⟨hmono hj.1, hmono hj.2⟩, by simpa [hv j] using hj_in_s⟩
    let s' := Set.Icc n m ∩ { i | u i ω ∈ s }
    let t' := Set.Icc (f n) (f m) ∩ { i | v i ω ∈ s }
    have s'finite : s'.Finite := Set.Finite.inter_of_left (hfinι n m) {i | u i ω ∈ s}
    have hbt : BddBelow t' := BddBelow.inter_of_left bddBelow_Icc
    by_cases hA : A
    · have hB : B := hAB hA
      -- both sides take the “exists” branch
      simp only [hittingBtwn, A, B, hA, hB]; simp only [if_true]
      have s'hatt : sInf s' ∈ s' := Set.Nonempty.csInf_mem hA s'finite
      have hfs'subt' : f '' s' ⊆ t' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨hfIcc hx.1, by simpa [hv x] using hx.2⟩
      have : sInf t' ≤ f (sInf s') :=
        CCLO.sInf_sup_image_le_of_sInf_attained f s' s'hatt t' hbt hfs'subt'
      exact this
    · by_cases hB : B
      · -- LHS “exists”, RHS “empty”
        simp only [hittingBtwn, A, B, hA, hB]; simp only [if_true, if_false]
        rcases hB with ⟨j, hjIcc, hj_in_s⟩
        have : sInf t' ≤ j := ConditionallyCompleteLattice.csInf_le t' _ hbt ⟨hjIcc, hj_in_s⟩
        exact this.trans hjIcc.2
      · -- both “empty”
        simp only [hittingBtwn, A, B, hA, hB]; rfl
