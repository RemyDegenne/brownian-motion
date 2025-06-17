/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib
import BrownianMotion.Auxiliary.MeasureTheory
import BrownianMotion.Gaussian.Fernique
import BrownianMotion.Gaussian.Gaussian


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

theorem _root_.OrthonormalBasis.sum_sq_inner_right {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i : ι, ⟪b i, x⟫ ^ 2 = ‖x‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner]
  simp

theorem _root_.OrthonormalBasis.sum_sq_inner_left {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i : ι, ⟪x, b i⟫ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [← b.sum_sq_inner_right, real_inner_comm]

lemma charFun_stdGaussian (t : E) : charFun (stdGaussian E) t = Complex.exp (- ‖t‖ ^ 2 / 2) := by
  rw [charFun_apply, stdGaussian, integral_map]
  · simp_rw [sum_inner, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum,
      integral_fintype_prod_eq_prod
        (f := fun i x ↦ Complex.exp (⟪x • stdOrthonormalBasis ℝ E i, t⟫ * Complex.I)),
      inner_smul_left, mul_comm _ (⟪_, _⟫), Complex.ofReal_mul, conj_trivial,
      ← charFun_apply_real, charFun_gaussianReal]
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one, one_mul,
      zero_sub]
    simp_rw [← Complex.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, ← Complex.ofReal_pow,
      ← Complex.ofReal_sum, ← (stdOrthonormalBasis ℝ E).sum_sq_inner_right, neg_div]
  · exact Measurable.aemeasurable (by fun_prop)
  · exact Measurable.aestronglyMeasurable (by fun_prop)

instance isGaussian_stdGaussian : IsGaussian (stdGaussian E) := by
  refine isGaussian_iff_gaussian_charFun.2 ?_
  use 0, ContinuousBilinForm.inner E, ContinuousBilinForm.isPosSemidef_inner
  simp [charFun_stdGaussian, real_inner_self_eq_norm_sq, neg_div]

lemma covInnerBilin_stdGaussian_eq :
    covInnerBilin (stdGaussian E) = ContinuousBilinForm.inner E := by
  refine gaussian_charFun_congr 0 _ ContinuousBilinForm.isPosSemidef_inner (fun t ↦ ?_) |>.2.symm
  simp [charFun_stdGaussian, real_inner_self_eq_norm_sq, neg_div]

lemma covMatrix_stdGaussian_eq : covMatrix (stdGaussian E) = 1 := by
  rw [covMatrix, covInnerBilin_stdGaussian_eq, ContinuousBilinForm.inner_toMatrix_eq_one]

noncomputable
def multivariateGaussian (μ : EuclideanSpace ℝ (Fin d)) (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosSemidef) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) hS.sqrt x)

variable {μ : EuclideanSpace ℝ (Fin d)} {S : Matrix (Fin d) (Fin d) ℝ} {hS : S.PosSemidef}

instance isGaussian_multivariateGaussian : IsGaussian (multivariateGaussian μ S hS) := by
  sorry

end ProbabilityTheory
