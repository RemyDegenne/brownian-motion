/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Martingale.Centering

/-!
# Lemmas about the Doob decomposition

-/

@[expose] public section

open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : ℕ → Ω → E} {𝓕 : Filtration ℕ mΩ}

@[simp]
lemma martingalePart_zero : martingalePart X 𝓕 μ 0 = X 0 := by
  simp [martingalePart]

lemma predictablePart_add_one (n : ℕ) :
    predictablePart X 𝓕 μ (n + 1) =
      predictablePart X 𝓕 μ n + μ[X (n + 1) - X n | 𝓕 n] := by
  simp [predictablePart, Finset.sum_range_add]

lemma predictablePart_smul (c : ℝ) (n : ℕ) :
    predictablePart (c • X) 𝓕 μ n =ᵐ[μ] c • predictablePart X 𝓕 μ n := by
  simp only [predictablePart, Finset.smul_sum]
  refine eventuallyEq_sum fun i hi => ?_
  simp [← smul_sub, condExp_smul]

lemma martingalePart_smul (c : ℝ) (n : ℕ) :
    martingalePart (c • X) 𝓕 μ n =ᵐ[μ] c • martingalePart X 𝓕 μ n := by
  filter_upwards [predictablePart_smul (X := X) c n] with ω hω
  simpa [martingalePart, smul_sub]

lemma predictablePart_add {Y : ℕ → Ω → E} (hXint : ∀ n, Integrable (X n) μ)
    (hYint : ∀ n, Integrable (Y n) μ) (n : ℕ) :
    predictablePart (X + Y) 𝓕 μ n =ᵐ[μ] predictablePart X 𝓕 μ n + predictablePart Y 𝓕 μ n := by
  simp only [predictablePart, ← Finset.sum_add_distrib]
  refine eventuallyEq_sum fun i hi => ?_
  calc
  _ =ᵐ[μ] μ[(X (i + 1) - X i) + (Y (i + 1) - Y i) | 𝓕 i] := by simp; abel_nf; rfl
  _ =ᵐ[μ] _ := by apply condExp_add ((hXint (i + 1)).sub (hXint i)) ((hYint (i + 1)).sub (hYint i))

lemma martingalePart_add {Y : ℕ → Ω → E} (hXint : ∀ n, Integrable (X n) μ)
    (hYint : ∀ n, Integrable (Y n) μ) (n : ℕ) :
    martingalePart (X + Y) 𝓕 μ n =ᵐ[μ] martingalePart X 𝓕 μ n + martingalePart Y 𝓕 μ n := by
  filter_upwards [predictablePart_add (𝓕 := 𝓕) hXint hYint n] with ω hω
  simp_all [martingalePart]
  abel

lemma Martingale.predictablePart_eq_zero (hX : Martingale X 𝓕 μ) (n : ℕ) :
    predictablePart X 𝓕 μ n =ᵐ[μ] 0 := by
  rw [predictablePart, ← Finset.sum_const_zero (s := Finset.range n)]
  refine eventuallyEq_sum fun i hi => ?_
  calc
  _ =ᵐ[μ] μ[X (i + 1) | 𝓕 i] - μ[X i | 𝓕 i] := by
    simp [condExp_sub (hX.integrable (i + 1)) (hX.integrable i) (𝓕 i)]
  _ =ᵐ[μ] X i - X i := (hX.condExp_ae_eq (Nat.le_succ i)).sub (hX.condExp_ae_eq le_rfl)
  _ =ᵐ[μ] 0 := by simp

lemma Martingale.martingalePart_eq (hX : Martingale X 𝓕 μ) (n : ℕ) :
    martingalePart X 𝓕 μ n =ᵐ[μ] X n := by
  filter_upwards [hX.predictablePart_eq_zero n] with ω hω
  simp [martingalePart, hω]

variable [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

lemma isPredictable_predictablePart : IsPredictable 𝓕 (predictablePart X 𝓕 μ) :=
  isPredictable_of_measurable_add_one (by simp [measurable_const'])
    fun n ↦ (stronglyAdapted_predictablePart n).measurable

lemma IsPredictable.predictablePart_eq [SigmaFiniteFiltration μ 𝓕] (hX : IsPredictable 𝓕 X)
    (hXint : ∀ n, Integrable (X n) μ) (n : ℕ) :
    predictablePart X 𝓕 μ n =ᵐ[μ] X n - X 0 := by
  simp only [predictablePart, ← Finset.sum_range_sub]
  exact eventuallyEq_sum fun i hi => (condExp_of_stronglyMeasurable (𝓕.le i)
    ((hX.measurable_add_one i).stronglyMeasurable.sub (hX.adapted i))
    ((hXint (i + 1)).sub (hXint i))).eventuallyEq

lemma IsPredictable.martingalePart_eq [SigmaFiniteFiltration μ 𝓕] (hX : IsPredictable 𝓕 X)
    (hXint : ∀ n, Integrable (X n) μ) (n : ℕ) :
    martingalePart X 𝓕 μ n =ᵐ[μ] X 0 := by
  filter_upwards [hX.predictablePart_eq (μ := μ) hXint n] with ω hω
  simp [martingalePart, hω, sub_eq_add_neg]

-- todo: feel free to replace `Preorder E` by something stonger if needed
lemma Submartingale.monotone_predictablePart {X : ℕ → Ω → ℝ} (hX : Submartingale X 𝓕 μ) :
    ∀ᵐ ω ∂μ, Monotone (predictablePart X 𝓕 μ · ω) := by
  have := ae_all_iff.2 <| fun n : ℕ ↦ hX.condExp_sub_nonneg n.le_succ
  filter_upwards [this] with ω h
  simp only [Pi.zero_apply, Nat.succ_eq_add_one, ← ge_iff_le] at h
  refine monotone_nat_of_le_succ fun n ↦ (?_ : _ ≥ _)
  grw [predictablePart_add_one, Pi.add_apply, h n, add_zero]

lemma Submartingale.nonneg_predictablePart {X : ℕ → Ω → ℝ} (hX : Submartingale X 𝓕 μ) :
    ∀ᵐ ω ∂μ, ∀ n, 0 ≤ predictablePart X 𝓕 μ n ω := by
  filter_upwards [hX.monotone_predictablePart] with ω hω n
  simpa [predictablePart_zero] using hω (Nat.zero_le n)

end MeasureTheory
