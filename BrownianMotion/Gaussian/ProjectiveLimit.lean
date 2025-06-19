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

open MeasureTheory NormedSpace
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

noncomputable
def dualEuclideanSpaceFromDualSubtype (I : Finset ℝ≥0) (L : ({ x // x ∈ I } → ℝ) →L[ℝ] ℝ) :
    Dual ℝ (EuclideanSpace ℝ (Fin I.card)) :=
  LinearMap.toContinuousLinearMap
    { toFun := L ∘ ((MeasurableEquiv.refl ℝ).arrowCongr' I.equivFin.symm)
      map_add' x y := by
        have : (x + y) ∘ I.equivFin = x ∘ I.equivFin + y ∘ I.equivFin := by ext; simp
        simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr,
          MeasurableEquiv.refl, this]
      map_smul' c x := by
        have : (c • x) ∘ I.equivFin = c • (x ∘ I.equivFin) := by ext; simp
        simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr,
          MeasurableEquiv.refl, this] }

lemma coe_dualEuclideanSpaceFromDualSubtype (I : Finset ℝ≥0) (L : ({ x // x ∈ I } → ℝ) →L[ℝ] ℝ) :
    (dualEuclideanSpaceFromDualSubtype I L : EuclideanSpace ℝ (Fin I.card) → ℝ)
     = L ∘ ((MeasurableEquiv.refl ℝ).arrowCongr' I.equivFin.symm) := rfl

instance isGaussian_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    IsGaussian (gaussianProjectiveFamily I) where
  map_eq_gaussianReal L := by
    unfold gaussianProjectiveFamily
    rw [Measure.map_map (by fun_prop) (by fun_prop), variance_map (by fun_prop) (by fun_prop),
      integral_map (by fun_prop) (by fun_prop), ← coe_dualEuclideanSpaceFromDualSubtype,
      IsGaussian.map_eq_gaussianReal (dualEuclideanSpaceFromDualSubtype I L)]
    congr

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
