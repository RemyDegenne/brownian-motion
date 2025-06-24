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

variable {ι : Type*} [Fintype ι] {d : ℕ}

def brownianCovMatrix (I : ι → ℝ≥0) : Matrix ι ι ℝ := Matrix.of fun i j ↦ min (I i) (I j)

lemma posSemidef_brownianCovMatrix (I : ι → ℝ≥0) :
    (brownianCovMatrix I).PosSemidef := by
  let v : ι → (Set ℝ) := fun i ↦ Set.Icc 0 (I i)
  have h : brownianCovMatrix I =
    fun i j ↦ (volume.real ((Icc 0 (I i).toReal) ∩ (Icc 0 (I j)))) := by
    simp only [Icc_inter_Icc, max_self, Real.volume_real_Icc, sub_zero, le_inf_iff,
      NNReal.zero_le_coe, and_self, sup_of_le_left]
    rfl
  apply h ▸ L2.posSemidef_interMatrix (fun j ↦ measurableSet_Icc)
    (fun j ↦ IsCompact.measure_ne_top isCompact_Icc)

variable [DecidableEq ι]

noncomputable
def gaussianProjectiveFamilyAux (I : ι → ℝ≥0) :
    Measure (EuclideanSpace ℝ ι) :=
  multivariateGaussian 0 (brownianCovMatrix I) (posSemidef_brownianCovMatrix I)

instance isGaussian_gaussianProjectiveFamilyAux (I : ι → ℝ≥0) :
    IsGaussian (gaussianProjectiveFamilyAux I) := by
  unfold gaussianProjectiveFamilyAux
  infer_instance

lemma integral_id_gaussianProjectiveFamilyAux (I : ι → ℝ≥0) :
    ∫ x, x ∂(gaussianProjectiveFamilyAux I) = 0 :=
  integral_id_multivariateGaussian

noncomputable
def finToSubtype (I : Finset ℝ≥0) : EuclideanSpace ℝ (Fin I.card) ≃L[ℝ] (I → ℝ) :=
  (EuclideanSpace.equiv (Fin I.card) ℝ).trans
  { toEquiv := Equiv.arrowCongr' I.equivFin.symm (Equiv.refl ℝ)
    map_add' x y := by
      have : (x + y) ∘ I.equivFin = x ∘ I.equivFin + y ∘ I.equivFin := by ext; simp
      simp [Equiv.arrowCongr', Equiv.arrowCongr, this]
    map_smul' c x := by
      have : (c • x) ∘ I.equivFin = c • (x ∘ I.equivFin) := by ext; simp
      simp [Equiv.arrowCongr', Equiv.arrowCongr, this] }

@[simp]
lemma finToSubtype_apply (I : Finset ℝ≥0) (x : Fin I.card → ℝ) :
    finToSubtype I x = fun i ↦ x (I.equivFin i) := rfl

@[simp]
lemma finToSubtype_apply' (I : Finset ℝ≥0) (x : Fin I.card → ℝ) (i : I) :
    finToSubtype I x i = x (I.equivFin i) := rfl

noncomputable
def gaussianProjectiveFamily (I : Finset ℝ≥0) : Measure (EuclideanSpace ℝ I) :=
  (gaussianProjectiveFamilyAux ((↑) : I → ℝ≥0))

instance isGaussian_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    IsGaussian (gaussianProjectiveFamily I) where
  map_eq_gaussianReal L := by
    unfold gaussianProjectiveFamily gaussianProjectiveFamilyAux
    rw [IsGaussian.map_eq_gaussianReal]

lemma integral_id_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    ∫ x, x ∂(gaussianProjectiveFamily I) = 0 := by
  rw [gaussianProjectiveFamily, gaussianProjectiveFamilyAux, integral_id_multivariateGaussian]


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
