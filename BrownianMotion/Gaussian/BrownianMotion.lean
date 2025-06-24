/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Gaussian.GaussianProcess
import BrownianMotion.Gaussian.ProjectiveLimit
import BrownianMotion.Continuity.KolmogorovChentsov

/-!
# Brownian motion

-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

def preBrownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω ↦ ω t

lemma measurable_preBrownian (t : ℝ≥0) : Measurable (preBrownian t) := by
  unfold preBrownian
  fun_prop

lemma isGaussianProcess_preBrownian : IsGaussianProcess preBrownian gaussianLimit := by
  intro I
  simp only [preBrownian, Measure.map_id']
  rw [isProjectiveLimit_gaussianLimit]
  exact isGaussian_gaussianProjectiveFamily I

lemma tkt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    Var[X - Y; P] = Var[X; P] - 2 * cov[X, Y; P] + Var[Y; P] := by
  rw [← covariance_same, covariance_sub_left, covariance_sub_right, covariance_sub_right,
    covariance_same, covariance_same, covariance_comm]
  · ring
  any_goals assumption
  · exact hY.aestronglyMeasurable.aemeasurable
  · exact hX.aestronglyMeasurable.aemeasurable
  · exact hX.sub hY
  · exact hX.aestronglyMeasurable.aemeasurable.sub hY.aestronglyMeasurable.aemeasurable

open scoped RealInnerProductSpace

lemma test (s t : ℝ≥0) : s + t - 2 * min s t = max (s - t) (t - s) := by
  suffices h : ∀ (s t : ℝ≥0), s ≤ t → s + t - 2 * min s t = max (s - t) (t - s) by
    obtain hst | hts := le_total s t
    · exact h s t hst
    · convert h t s hts using 1
      · rw [add_comm, min_comm]
      · rw [max_comm]
  intro s t hst
  rw [min_eq_left hst, max_eq_right, two_mul, add_tsub_add_eq_tsub_left]
  grw [hst]

lemma map_sub_preBrownian (s t : ℝ≥0) :
    gaussianLimit.map (preBrownian s - preBrownian t) = gaussianReal 0 (max (s - t) (t - s)) := by
  let L : EuclideanSpace ℝ ({s, t} : Finset ℝ≥0) →L[ℝ] ℝ :=
    { toFun x := x ⟨s, by simp⟩ - x ⟨t, by simp⟩
      map_add' x y := by simp only [PiLp.add_apply]; abel
      map_smul' m x := by simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
      cont := by fun_prop }
  have : preBrownian s - preBrownian t =
      L ∘ ({s, t} : Finset ℝ≥0).restrict := by ext; simp [L, preBrownian]
  rw [this, ← AEMeasurable.map_map_of_aemeasurable, isProjectiveLimit_gaussianLimit,
    IsGaussian.map_eq_gaussianReal, L.integral_comp_id_comm, integral_id_gaussianProjectiveFamily,
    map_zero]
  · congr
    rw [gaussianProjectiveFamily, gaussianProjectiveFamilyAux]
    · simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, L]
      rw [← Pi.sub_def, tkt]
      · have this (x : EuclideanSpace ℝ ({s, t} : Finset ℝ≥0)) :
            x ⟨s, by simp⟩ = ⟪EuclideanSpace.basisFun ({s, t} : Finset ℝ≥0) ℝ ⟨s, by simp⟩, x⟫ := by
          simp
        simp_rw [this]
        rw [← covInnerBilin_self, covInnerBilin_multivariateGaussian,
          ← OrthonormalBasis.coe_toBasis, ContinuousBilinForm.ofMatrix_basis]
        · simp_rw [brownianCovMatrix, Matrix.of_apply]
          have this (x : EuclideanSpace ℝ ({s, t} : Finset ℝ≥0)) :
              x ⟨t, by simp⟩ =
                ⟪EuclideanSpace.basisFun ({s, t} : Finset ℝ≥0) ℝ ⟨t, by simp⟩, x⟫ := by
            simp
          simp_rw [this]
          rw [← covInnerBilin_self, covInnerBilin_multivariateGaussian,
            ← OrthonormalBasis.coe_toBasis, ContinuousBilinForm.ofMatrix_basis]
          · simp_rw [Matrix.of_apply]
            rw [← covInnerBilin_apply_eq, covInnerBilin_multivariateGaussian,
              ContinuousBilinForm.ofMatrix_basis]
            · simp_rw [Matrix.of_apply, min_self]
              norm_cast
              rw [sub_add_eq_add_sub, ← NNReal.coe_add, ← NNReal.coe_sub, Real.toNNReal_coe, test]
              rw [two_mul]
              nth_grw 1 [min_le_left, min_le_right]
          exact IsGaussian.memLp_two_id _
        exact IsGaussian.memLp_two_id _
      · have : (fun (x : EuclideanSpace ℝ ({s, t} : Finset ℝ≥0)) ↦ x ⟨s, by simp⟩) =
            ContinuousBilinForm.inner _
              (EuclideanSpace.basisFun ({s, t} : Finset ℝ≥0) ℝ ⟨s, by simp⟩) := by
          ext; simp
        rw [this]
        exact ContinuousLinearMap.comp_memLp' _ <| IsGaussian.memLp_two_id _
      · have : (fun (x : EuclideanSpace ℝ ({s, t} : Finset ℝ≥0)) ↦ x ⟨t, by simp⟩) =
            ContinuousBilinForm.inner _
              (EuclideanSpace.basisFun ({s, t} : Finset ℝ≥0) ℝ ⟨t, by simp⟩) := by
          ext; simp
        rw [this]
        exact ContinuousLinearMap.comp_memLp' _ <| IsGaussian.memLp_two_id _
  · exact IsGaussian.integrable_id _
  · fun_prop
  · fun_prop

lemma isKolmogorovProcess_preBrownian (n : ℕ) :
    IsKolmogorovProcess preBrownian gaussianLimit (2 * n) n (Nat.doubleFactorial (2 * n - 1)) := by
  sorry

noncomputable
def brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  (exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ isKolmogorovProcess_preBrownian (n + 2)) (fun n ↦ by positivity)
    (fun n ↦ by simp; norm_cast; omega)).choose

lemma brownian_eq_preBrownian (t : ℝ≥0) :
    brownian t =ᵐ[gaussianLimit] preBrownian t :=
  (exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ isKolmogorovProcess_preBrownian (n + 2)) (fun n ↦ by positivity)
    (fun n ↦ by simp; norm_cast; omega)).choose_spec.1 t

lemma isHolderWith_brownian {β : ℝ≥0} (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) (ω : ℝ≥0 → ℝ) :
    ∃ C : ℝ≥0, HolderWith C β (brownian · ω) := by
  refine (exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ isKolmogorovProcess_preBrownian (n + 2)) (fun n ↦ by positivity)
    (fun n ↦ by simp; norm_cast; omega)).choose_spec.2 β hβ_pos ?_ ω
  have hβ_lt' : (β : ℝ) < 2⁻¹ := by
    sorry
  refine hβ_lt'.trans_eq ?_
  sorry

lemma aemeasurable_brownian_apply (t : ℝ≥0) : AEMeasurable (brownian t) gaussianLimit :=
  ⟨preBrownian t, measurable_preBrownian t, brownian_eq_preBrownian t⟩

lemma aemeasurable_brownian : AEMeasurable (fun ω t ↦ brownian t ω) gaussianLimit := by
  sorry

lemma continuous_brownian (ω : ℝ≥0 → ℝ) :
    Continuous (brownian · ω) := by
  sorry

lemma isGaussianProcess_brownian : IsGaussianProcess brownian gaussianLimit :=
  isGaussianProcess_preBrownian.modification fun t ↦ (brownian_eq_preBrownian t).symm

section Measure

-- Subtype measurable space. The measurable space on `ℝ≥0 → ℝ` is the product of Borel σ-algebras
-- #synth MeasurableSpace {f : ℝ≥0 → ℝ // Continuous f}

noncomputable
def wienerMeasureAux : Measure {f : ℝ≥0 → ℝ // Continuous f} :=
  gaussianLimit.map (fun ω ↦ (⟨fun t ↦ brownian t ω, continuous_brownian ω⟩))

-- Compact-open topology
-- #synth TopologicalSpace C(ℝ≥0, ℝ)

section ContinuousMap.MeasurableSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

instance : MeasurableSpace C(X, Y) := borel _
instance : BorelSpace C(X, Y) where
  measurable_eq := rfl

lemma ContinuousMap.borel_eq_iSup_comap_eval [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y] :
    borel C(X, Y) = ⨆ a : X, (borel Y).comap fun b ↦ b a := by
  -- https://math.stackexchange.com/questions/4789531/when-does-the-borel-sigma-algebra-of-compact-convergence-coincide-with-the-pr
  apply le_antisymm
  swap
  · refine iSup_le fun x ↦ ?_
    rw [← measurable_iff_comap_le]
    simp_rw [← BorelSpace.measurable_eq]
    refine Continuous.measurable ?_
    fun_prop
  sorry

lemma ContinuousMap.measurableSpace_eq_iSup_comap_eval
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y] :
    (inferInstance : MeasurableSpace C(X, Y))
      = ⨆ a : X, (inferInstance : MeasurableSpace Y).comap fun b ↦ b a := by
  simp_rw [BorelSpace.measurable_eq, borel_eq_iSup_comap_eval]

lemma ContinuousMap.measurable_iff_eval {α : Type*} [MeasurableSpace α]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (g : α → C(X, Y)) :
    Measurable g ↔ ∀ (x : X), Measurable fun (a : α) ↦ g a x := by
  simp_rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, measurable_iff_comap_le,
    MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp, Function.comp_def]

end ContinuousMap.MeasurableSpace

def MeasurableEquiv.continuousMap : {f : ℝ≥0 → ℝ // Continuous f} ≃ᵐ C(ℝ≥0, ℝ) where
  toFun := fun f ↦ ContinuousMap.mk f.1 f.2
  invFun := fun f ↦ ⟨f, f.continuous⟩
  left_inv f := rfl
  right_inv f := rfl
  measurable_toFun := by
    simp only [Equiv.coe_fn_mk]
    rw [ContinuousMap.measurable_iff_eval]
    intro x
    simp only [ContinuousMap.coe_mk]
    revert x
    rw [← measurable_pi_iff]
    exact measurable_subtype_coe
  measurable_invFun := by
    simp only [Equiv.coe_fn_symm_mk]
    refine Measurable.subtype_mk ?_
    rw [measurable_pi_iff]
    exact fun _ ↦ Continuous.measurable (by fun_prop)


noncomputable
def wienerMeasure : Measure C(ℝ≥0, ℝ) := wienerMeasureAux.map MeasurableEquiv.continuousMap

end Measure

end ProbabilityTheory
