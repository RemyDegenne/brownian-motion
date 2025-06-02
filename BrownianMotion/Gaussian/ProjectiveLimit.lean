/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Gaussian.MultivariateGaussian
import BrownianMotion.Init

/-!
# Pre-Brownian motion as a projective limit

-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] {d : ℕ}

def brownianCovMatrix (I : ι → ℝ≥0) : Matrix ι ι ℝ := Matrix.of fun i j ↦ min (I i) (I j)

lemma posSemidef_brownianCovMatrix (I : ι → ℝ≥0) :
    (brownianCovMatrix I).PosSemidef := by
  sorry -- done in Mathlib PR #24575

noncomputable
def gaussianProjectiveFamilyAux (I : Fin d → ℝ≥0) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  multivariateGaussian 0 (brownianCovMatrix I) (posSemidef_brownianCovMatrix I)

instance isGaussian_gaussianProjectiveFamilyAux (I : Fin d → ℝ≥0) :
    IsGaussian (gaussianProjectiveFamilyAux I) := by
  unfold gaussianProjectiveFamilyAux
  infer_instance

noncomputable
def gaussianProjectiveFamily (I : Finset ℝ≥0) : Measure ((i : I) → ℝ) :=
  (gaussianProjectiveFamilyAux (fun i ↦ (I.equivFin).symm i)).map
    ((MeasurableEquiv.refl ℝ).arrowCongr' I.equivFin.symm)

instance isGaussian_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    IsGaussian (gaussianProjectiveFamily I) := by
  unfold gaussianProjectiveFamily
  sorry

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
