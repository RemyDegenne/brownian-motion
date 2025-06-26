/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.MeasureTheory
import BrownianMotion.Gaussian.MultivariateGaussian
import BrownianMotion.Init

/-!
# Pre-Brownian motion as a projective limit

-/

open MeasureTheory NormedSpace Set
open scoped ENNReal NNReal

namespace L2

variable {ι : Type*} [Fintype ι]
variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/- In an `L2` space, the matrix of intersections of pairs of sets is positive semi-definite. -/
theorem posSemidef_interMatrix {μ : Measure α} {v : ι → (Set α)}
    (hv₁ : ∀ j, MeasurableSet (v j)) (hv₂ : ∀ j, μ (v j) ≠ ∞ := by finiteness) :
    Matrix.PosSemidef (Matrix.of fun i j : ι ↦ μ.real (v i ∩ v j)) := by
  -- simp only [hv₁, ne_eq, hv₂, not_false_eq_true,
      -- ← inner_indicatorConstLp_one_indicatorConstLp_one']
  -- exact gram_posSemidef
  sorry -- include once Mathlib PR #25883 is available

end L2

namespace ProbabilityTheory

variable {ι : Type*} {d : ℕ}

def brownianCovMatrix (I : Finset ℝ≥0) : Matrix I I ℝ := Matrix.of fun s t ↦ min s.1 t.1

lemma brownianCovMatrix_apply {I : Finset ℝ≥0} (s t : I) :
    brownianCovMatrix I s t = min s.1 t.1 := rfl

variable [Fintype ι]

lemma posSemidef_brownianCovMatrix (I : Finset ℝ≥0) :
    (brownianCovMatrix I).PosSemidef := by
  have h : brownianCovMatrix I =
      fun s t ↦ volume.real ((Icc 0 s.1.toReal) ∩ (Icc 0 t.1.toReal)) := by
    simp [Icc_inter_Icc, max_self, Real.volume_real_Icc, sub_zero, le_inf_iff,
      NNReal.zero_le_coe, and_self, sup_of_le_left]
    rfl
  exact h ▸ L2.posSemidef_interMatrix (fun j ↦ measurableSet_Icc)
    (fun j ↦ isCompact_Icc.measure_ne_top)

variable [DecidableEq ι]

noncomputable
def gaussianProjectiveFamily (I : Finset ℝ≥0) :
    Measure (EuclideanSpace ℝ I) :=
  multivariateGaussian 0 (brownianCovMatrix I) (posSemidef_brownianCovMatrix I)

instance isGaussian_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    IsGaussian (gaussianProjectiveFamily I) := by
  unfold gaussianProjectiveFamily
  infer_instance

lemma integral_id_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    ∫ x, x ∂(gaussianProjectiveFamily I) = 0 :=
  integral_id_multivariateGaussian

lemma isProjectiveMeasureFamily_gaussianProjectiveFamily :
    IsProjectiveMeasureFamily (α := fun _ ↦ ℝ) gaussianProjectiveFamily := by
  sorry

noncomputable
def gaussianLimit : Measure (ℝ≥0 → ℝ) :=
  projectiveLimit gaussianProjectiveFamily isProjectiveMeasureFamily_gaussianProjectiveFamily

lemma isProjectiveLimit_gaussianLimit :
    IsProjectiveLimit gaussianLimit gaussianProjectiveFamily :=
  isProjectiveLimit_projectiveLimit isProjectiveMeasureFamily_gaussianProjectiveFamily

end ProbabilityTheory
