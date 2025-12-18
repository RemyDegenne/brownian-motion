/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Wojciech Czernous
-/
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Upcrossing
import Init.Data.Function

/-!
# Hitting times when enlarging the time index set

## Main results

* `hittingBtwn_monotone_in_index_set`: a discrete hitting time of an adapted process
  may not become earlier after restricting the time index set.
-/

variable {Ω β ι κ : Type*} {m : MeasurableSpace Ω}
  [ConditionallyCompleteLinearOrderBot ι] [ConditionallyCompleteLinearOrderBot κ]

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

lemma hittingBtwn_antimono_index_set
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

lemma hittingBtwn_mono_left (u : ι → Ω → β)
    (s : Set β) (n₁ n₂ m : ι) (h : n₁ ≤ n₂) (ω : Ω)
  : hittingBtwn u s n₁ m ω ≤ hittingBtwn u s n₂ m ω := by
  set A₁ : Prop := ∃ j ∈ Set.Icc n₁ m, u j ω ∈ s with hA₁
  set A₂ : Prop := ∃ j ∈ Set.Icc n₂ m, u j ω ∈ s with hA₂
  rw [hittingBtwn, hittingBtwn, ← hA₁, ← hA₂]
  set s₁ : Set ι := Set.Icc n₁ m ∩ { i | u i ω ∈ s } with hs₁
  set s₂ : Set ι := Set.Icc n₂ m ∩ { i | u i ω ∈ s } with hs₂
  have h12 : Set.Icc n₂ m ⊆ Set.Icc n₁ m := fun x hx => ⟨h.trans hx.1, hx.2⟩
  have h2sub1 : s₂ ⊆ s₁ := fun x hx => ⟨h12 hx.1, hx.2⟩
  by_cases hA₂ : A₂
  · have hA₁ : A₁ := by
      rcases hA₂ with ⟨j, hjIcc, hj_in_s⟩
      exact ⟨j, h12 hjIcc, hj_in_s⟩
    simp only [hA₁, hA₂]; simp only [if_true]
    have : sInf s₁ ≤ sInf s₂ :=
      csInf_le_csInf (BddBelow.inter_of_left bddBelow_Icc) hA₂ h2sub1
    exact this
  · by_cases hA₁ : A₁
    · -- LHS “exists”, RHS “empty”
      simp only [hA₁, hA₂]; simp only [if_true, if_false]
      rcases hA₁ with ⟨j, hjIcc, hj_in_s⟩
      have : sInf s₁ ≤ j := ConditionallyCompleteLattice.csInf_le
        s₁ _ (BddBelow.inter_of_left bddBelow_Icc) ⟨hjIcc, hj_in_s⟩
      exact this.trans hjIcc.2
    · -- both “empty”
      simp only [hA₁, hA₂]; rfl

lemma lowerCrossingTimeAux_antimono_index_set
  (f : ι → κ) (hmono : Monotone f)
  (hfinι : ∀ n m : ι, (Set.Icc n m).Finite) -- finite intervals in ι
  (u : ι → Ω → ℝ) (v : κ → Ω → ℝ) (hv : ∀ i : ι, v (f i) = u i) -- u is a restriction of v to f(ι)
  (a : ℝ) (c N : ι)
  : ∀ ω : Ω, lowerCrossingTimeAux a v (f c) (f N) ω ≤ f (lowerCrossingTimeAux a u c N ω) :=
    hittingBtwn_antimono_index_set f hmono hfinι u v hv (Set.Iic a) c N

lemma lowerCrossingTimeAux_mono_left (u : ι → Ω → ℝ)
  (a : ℝ) (c₁ c₂ N : ι) (h : c₁ ≤ c₂) (ω : Ω)
  : lowerCrossingTimeAux a u c₁ N ω ≤ lowerCrossingTimeAux a u c₂ N ω :=
    hittingBtwn_mono_left u (Set.Iic a) c₁ c₂ N h ω


#check lintegral_iSup' /-- Monotone convergence theorem, version with `AEMeasurable` functions. -/

lemma upperCrossingTime_antimono_index_set
  (f : ι → κ) (hmono : Monotone f)
  (hfinι : ∀ n m : ι, (Set.Icc n m).Finite) -- finite intervals in ι
  (u : ι → Ω → ℝ) (v : κ → Ω → ℝ) (hv : ∀ i : ι, v (f i) = u i) -- u is a restriction of v to f(ι)
  (a b : ℝ) (N : ι) (n : ℕ)
  : ∀ ω : Ω, upperCrossingTime a b v (f N) n ω ≤ f (upperCrossingTime a b u N n ω) := by
    intro ω
    induction n
    case zero =>
      simp only [upperCrossingTime]
      have : ⊥ ≤ f (⊥ : ι) := bot_le
      exact this
    case succ n ih =>
      simp only [upperCrossingTime]
      set c : ι := upperCrossingTime a b u N n ω with hc
