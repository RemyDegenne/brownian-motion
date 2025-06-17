/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib
import BrownianMotion.Auxiliary.MeasureTheory
import BrownianMotion.Gaussian.Fernique


/-!
# Multivariate Gaussian distributions
-/

open MeasureTheory ProbabilityTheory Filter Matrix NormedSpace
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  {d : ℕ}

variable (E) in
/-- Standard Gaussian distribution on `E`. -/
noncomputable
def stdGaussian : Measure E :=
  (Measure.pi (fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 1)).map
    (fun x ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i)

variable [BorelSpace E]

instance isProbabilityMeasure_stdGaussian : IsProbabilityMeasure (stdGaussian E) :=
    isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

-- TODO: generalize to `f` taking values in a Banach space
lemma integrable_eval_pi {ι 𝕜 : Type*} [Fintype ι] [NormedCommRing 𝕜] {X : ι → Type*} {i : ι}
    {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}
    [∀ i, IsFiniteMeasure (μ i)] {f : X i → 𝕜} (hf : Integrable f (μ i)) :
    Integrable (fun x ↦ f (x i)) (Measure.pi μ) := by
  classical
  let g : Π i, X i → 𝕜 := fun j ↦ if h : j = i then h ▸ f else 1
  have : (fun x ↦ ∏ j, g j (x j)) = fun (x : Π i, X i) ↦ f (x i) := by
    ext x
    rw [show f (x i) = g i (x i) by simp [g]]
    exact Finset.prod_eq_single_of_mem i (by simp) (fun j _ hj ↦ by simp [g, hj])
  rw [← this]
  refine Integrable.fintype_prod_dep fun j ↦ ?_
  by_cases h : j = i
  · cases h; simpa [g]
  · simpa [g, h] using integrable_const 1

-- TODO: generalize to `f` taking values in a Banach space
lemma integral_eval_pi {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜] {X : ι → Type*} {i : ι}
    {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}
    [∀ i, IsProbabilityMeasure (μ i)] {f : X i → 𝕜} :
    ∫ (x : Π i, X i), f (x i) ∂Measure.pi μ = ∫ x, f x ∂μ i := by
  classical
  let g : Π i, X i → 𝕜 := fun j ↦ if h : j = i then h ▸ f else 1
  have : (fun x ↦ ∏ j, g j (x j)) = fun (x : Π i, X i) ↦ f (x i) := by
    ext x
    rw [show f (x i) = g i (x i) by simp [g]]
    exact Finset.prod_eq_single_of_mem i (by simp) (fun j _ hj ↦ by simp [g, hj])
  rw [← this, integral_fintype_prod_eq_prod, show ∫ x, f x ∂μ i = ∫ x, g i x ∂μ i by simp [g]]
  exact Finset.prod_eq_single_of_mem i (by simp) (fun j _ hj ↦ by simp [g, hj])

lemma integral_id_stdGaussian : ∫ x, x ∂(stdGaussian E) = 0 := by
  rw [stdGaussian, integral_map _ (by fun_prop)]
  swap; · exact (Finset.measurable_sum _ (by fun_prop)).aemeasurable -- todo: add fun_prop tag
  rw [integral_finset_sum]
  swap
  · refine fun i _ ↦ Integrable.smul_const ?_ _
    convert integrable_eval_pi (i := i) (f := id) ?_
    · infer_instance
    · rw [← memLp_one_iff_integrable]
      exact memLp_id_gaussianReal 1
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have : (∫ (a : Fin (Module.finrank ℝ E) → ℝ), a i ∂Measure.pi fun x ↦ gaussianReal 0 1)
      = ∫ x, x ∂gaussianReal 0 1 := by
    convert integral_eval_pi (i := i)
    · rfl
    · infer_instance
  simp [integral_smul_const, this]

lemma isCentered_stdGaussian : ∀ L : Dual ℝ E, (stdGaussian E)[L] = 0 := by
  intro L
  rw [L.integral_comp_id_comm, integral_id_stdGaussian, map_zero]
  rw [stdGaussian, integrable_map_measure]
  · rw [Function.id_comp]
    exact integrable_finset_sum _ fun i _ ↦ Integrable.smul_const
      (integrable_eval_pi (f := id) (IsGaussian.integrable_id _)) _
  · exact aestronglyMeasurable_id
  · exact Measurable.aemeasurable (by fun_prop)

lemma variance_pi {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)] {X : Π i, Ω i → ℝ}
    (h : ∀ i, MemLp (X i) 2 (μ i)) :
    Var[∑ i, fun ω ↦ X i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i] := by
  rw [IndepFun.variance_sum]
  · congr with i
    change Var[(X i) ∘ (fun ω ↦ ω i); Measure.pi μ] = _
    rw [← variance_map, (measurePreserving_eval i).map_eq]
    · rw [(measurePreserving_eval i).map_eq]
      exact (h i).aestronglyMeasurable.aemeasurable
    · exact Measurable.aemeasurable (by fun_prop)
  · exact fun i _ ↦ (h i).comp_measurePreserving (measurePreserving_eval i)
  · exact fun i _ j _ hij ↦
      (iIndepFun_pi₀ fun i ↦ (h i).aestronglyMeasurable.aemeasurable).indepFun hij

lemma variance_dual_stdGaussian (L : Dual ℝ E) :
    Var[L; stdGaussian E] = ∑ i, L (stdOrthonormalBasis ℝ E i) ^ 2 := by
  rw [stdGaussian, variance_map]
  · have : L ∘ (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i) =
        ∑ i, (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ L (stdOrthonormalBasis ℝ E i) * x i) := by
      ext x; simp [mul_comm]
    rw [this, variance_pi]
    · change ∑ i, Var[fun x ↦ _ * (id x); gaussianReal 0 1] = _
      simp_rw [variance_mul, variance_id_gaussianReal]
      simp
    · exact fun i ↦ ((isGaussian_gaussianReal 0 1).memLp_two_id _).const_mul _
  · exact L.continuous.aemeasurable
  · exact Measurable.aemeasurable (by fun_prop)

instance isGaussian_stdGaussian : IsGaussian (stdGaussian E) := by
  refine isGaussian_of_charFunDual_eq fun L ↦ ?_
  rw [integral_complex_ofReal, isCentered_stdGaussian L]
  simp only [Complex.ofReal_zero, zero_mul, zero_sub]
  -- todo: need a lemma `charFunDual_map_sum_pi`
  sorry

noncomputable
def multivariateGaussian (μ : EuclideanSpace ℝ (Fin d)) (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosSemidef) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) hS.sqrt x)

variable {μ : EuclideanSpace ℝ (Fin d)} {S : Matrix (Fin d) (Fin d) ℝ} {hS : S.PosSemidef}

instance isGaussian_multivariateGaussian : IsGaussian (multivariateGaussian μ S hS) := by
  sorry

end ProbabilityTheory
