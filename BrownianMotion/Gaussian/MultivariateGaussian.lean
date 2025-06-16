/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib


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

instance isProbabilityMeasure_stdGaussian : IsProbabilityMeasure (stdGaussian E) where
  measure_univ := by
    rw [stdGaussian, Measure.map_apply (by fun_prop) .univ]
    simp

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
  rw [stdGaussian, integral_map _ (by fun_prop)]
  swap; · exact (Finset.measurable_sum _ (by fun_prop)).aemeasurable -- todo: add fun_prop tag
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [integral_finset_sum]
  swap
  · intro i _
    refine Integrable.mul_const ?_ _
    convert integrable_eval_pi (i := i) (f := id) ?_
    · infer_instance
    · rw [← memLp_one_iff_integrable]
      exact memLp_id_gaussianReal 1
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [integral_mul_const]
  have : (∫ (a : Fin (Module.finrank ℝ E) → ℝ), a i ∂Measure.pi fun x ↦ gaussianReal 0 1)
      = ∫ x, x ∂gaussianReal 0 1 := by
    convert integral_eval_pi (i := i)
    · rfl
    · infer_instance
  simp [this]

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)] {X : Π i, Ω i → ℝ}

lemma measurePreserving_eval (i : ι) :
    MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) := by
  refine ⟨measurable_pi_apply i, ?_⟩
  ext s hs
  classical
  rw [Measure.map_apply (measurable_pi_apply i) hs, ← Set.univ_pi_update_univ, Measure.pi_pi]
  have : μ i s = (μ i) (Function.update (fun j ↦ Set.univ) i s i) := by simp
  rw [this]
  exact Finset.prod_eq_single_of_mem i (by simp) (fun j _ hj ↦ by simp [hj])

lemma lol {ι : Type*} [Fintype ι] {Ω 𝒳 : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {m𝒳 : ∀ i, MeasurableSpace (𝒳 i)}
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)] {X : Π i, Ω i → 𝒳 i}
    (mX : ∀ i, Measurable (X i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ) := by
  apply @iIndepFun_iff_map_fun_eq_pi_map (Π i, Ω i) ι _ (Measure.pi μ) _ 𝒳 _
    (fun i x ↦ X i (x i)) _ ?_ |>.2
  · symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply]
    · have : (fun (ω : Π i, Ω i) i ↦ X i (ω i)) ⁻¹' (Set.univ.pi s) =
          Set.univ.pi (fun i ↦ (X i) ⁻¹' (s i)) := by
        ext x
        simp
      rw [this, Measure.pi_pi]
      congr with i
      rw [Measure.map_apply]
      · change _ = (Measure.pi μ) (((X i) ∘ (fun x ↦ x i)) ⁻¹' s i)
        rw [Set.preimage_comp, ← Measure.map_apply (measurable_pi_apply i),
          (measurePreserving_eval i).map_eq]
        · exact mX i (hs i)
      · fun_prop
      · exact hs i
    · fun_prop
    · exact MeasurableSet.univ_pi hs
  · exact fun i ↦ Measurable.aemeasurable (by fun_prop)

lemma lol' {ι : Type*} [Fintype ι] {Ω 𝒳 : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {m𝒳 : ∀ i, MeasurableSpace (𝒳 i)}
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)] {X : Π i, Ω i → 𝒳 i}
    (mX : ∀ i, AEMeasurable (X i) (μ i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ) := by
  have : iIndepFun (fun i ω ↦ (mX i).mk (X i) (ω i)) (Measure.pi μ) :=
    lol (fun i ↦ (mX i).measurable_mk)
  apply this.congr
  intro i
  change ((mX i).mk (X i)) ∘ Function.eval i =ᶠ[_] (X i) ∘ Function.eval i
  apply ae_eq_comp
  · exact (measurable_pi_apply i).aemeasurable
  · rw [(measurePreserving_eval i).map_eq]
    exact EventuallyEq.symm (AEMeasurable.ae_eq_mk (mX i))

lemma variance_pi {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)] {X : (i : ι) → Ω i → ℝ}
    (h : ∀ i, MemLp (X i) 2 (μ i)) :
    Var[∑ i, fun ω ↦ X i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i] := by
  classical
  rw [IndepFun.variance_sum]
  · congr with i
    rw [variance_eq_integral, integral_eval_pi,
      @integral_eval_pi ι _ _ _ Ω i _ μ _ (fun x : Ω i ↦ (X i x - ∫ y, X i y ∂μ i) ^ 2),
      variance_eq_integral]
    · exact (h i).aestronglyMeasurable.aemeasurable
    · exact (h i).aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving
        (measurePreserving_eval i).quasiMeasurePreserving
  · intro i hi
    exact (h i).comp_measurePreserving (measurePreserving_eval i)
  · rintro i - j - hij
    refine @iIndepFun.indepFun (Π i, Ω i) ι _ (Measure.pi μ) (fun _ ↦ ℝ) _ (fun i x ↦ X i (x i)) ?_
      i j hij
    exact lol' fun i ↦ (h i).aestronglyMeasurable.aemeasurable

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
    · intro i
      apply MemLp.const_mul
      exact (isGaussian_gaussianReal 0 1).memLp_ _


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
