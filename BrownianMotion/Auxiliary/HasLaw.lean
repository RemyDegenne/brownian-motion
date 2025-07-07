import Mathlib.Probability.Distributions.Gaussian.Basic

open MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section HasLaw

variable {𝓧} {m𝓧 : MeasurableSpace 𝓧} (X : Ω → 𝓧) (P : Measure Ω) (μ : Measure 𝓧)

/-- The predicate `HasLaw X P μ` registers the fact that the random variable `X` has law `μ` under
the measure `P`, in other words that `P.map X = μ`. We also require `X` to be `AEMeasurable`,
to allow for nice interactions with operations on the codomain of `X`. See for instance
`HasLaw.comp`, `IndepFun.hasLaw_mul` and `IndepFun.hasLaw_add`. -/
structure HasLaw : Prop where
  protected aemeasurable : AEMeasurable X P := by fun_prop
  protected map_eq : P.map X = μ

variable {X P μ}

lemma HasLaw.congr {Y : Ω → 𝓧} (hX : HasLaw X P μ) (hY : Y =ᵐ[P] X) : HasLaw Y P μ where
  aemeasurable := hX.aemeasurable.congr hY.symm
  map_eq := by rw [Measure.map_congr hY, hX.map_eq]

lemma MeasurePreserving.hasLaw (h : MeasurePreserving X P μ) : HasLaw X P μ where
  aemeasurable := h.measurable.aemeasurable
  map_eq := h.map_eq

lemma HasLaw.measurePreserving (h₁ : HasLaw X P μ) (h₂ : Measurable X) :
    MeasurePreserving X P μ where
  measurable := h₂
  map_eq := h₁.map_eq

lemma HasLaw.comp {𝒴 : Type*} {m𝒴 : MeasurableSpace 𝒴} {ν : Measure 𝒴} {Y : 𝓧 → 𝒴}
    (hY : HasLaw Y μ ν) (hX : HasLaw X P μ) : HasLaw (Y ∘ X) P ν where
  aemeasurable := (hX.map_eq ▸ hY.aemeasurable).comp_aemeasurable hX.aemeasurable
  map_eq := by
    rw [← AEMeasurable.map_map_of_aemeasurable _ hX.aemeasurable, hX.map_eq, hY.map_eq]
    rw [hX.map_eq]; exact hY.aemeasurable

lemma HasLaw.fun_comp {𝒴 : Type*} {m𝒴 : MeasurableSpace 𝒴} {ν : Measure 𝒴} {Y : 𝓧 → 𝒴}
    (hY : HasLaw Y μ ν) (hX : HasLaw X P μ) : HasLaw (fun ω ↦ Y (X ω)) P ν :=
  hY.comp hX

@[to_additive]
lemma IndepFun.hasLaw_mul [IsFiniteMeasure P] {M : Type*} [Monoid M] {mM : MeasurableSpace M}
    [MeasurableMul₂ M] {μ ν : Measure M} {X Y : Ω → M} (hX : HasLaw X P μ) (hY : HasLaw Y P ν)
    (hXY : IndepFun X Y P) :
    HasLaw (X * Y) P (μ ∗ₘ ν) where
  aemeasurable := hX.aemeasurable.mul hY.aemeasurable
  map_eq := by
    rw [hXY.map_mul_eq_map_mconv_map₀ hX.aemeasurable hY.aemeasurable, hX.map_eq, hY.map_eq]

@[to_additive]
lemma IndepFun.hasLaw_fun_mul [IsFiniteMeasure P] {M : Type*} [Monoid M] {mM : MeasurableSpace M}
    [MeasurableMul₂ M] {μ ν : Measure M} {X Y : Ω → M} (hX : HasLaw X P μ) (hY : HasLaw Y P ν)
    (hXY : IndepFun X Y P) :
    HasLaw (fun ω ↦ X ω * Y ω) P (μ ∗ₘ ν) := hXY.hasLaw_mul hX hY

lemma HasLaw.integral_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Ω → 𝓧} (hX : HasLaw X P μ) {f : 𝓧 → E} (hf : AEStronglyMeasurable f μ) :
    P[f ∘ X] = ∫ x, f x ∂μ := by
  rw [← hX.map_eq, integral_map hX.aemeasurable]
  · rfl
  · rwa [hX.map_eq]

lemma HasLaw.lintegral_comp {X : Ω → 𝓧} (hX : HasLaw X P μ) {f : 𝓧 → ℝ≥0∞}
    (hf : AEMeasurable f μ) : ∫⁻ ω, f (X ω) ∂P = ∫⁻ x, f x ∂μ := by
  rw [← hX.map_eq, lintegral_map' _ hX.aemeasurable]
  rwa [hX.map_eq]

lemma HasLaw.integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Measure E}
    {X : Ω → E} (hX : HasLaw X P μ) : P[X] = ∫ x, x ∂μ := by
  rw [← Function.id_comp X, hX.integral_comp aestronglyMeasurable_id]
  simp

lemma HasLaw.variance_eq {μ : Measure ℝ} {X : Ω → ℝ} (hX : HasLaw X P μ) :
    Var[X; P] = Var[id; μ] := by
  rw [← hX.map_eq, variance_map aemeasurable_id hX.aemeasurable, Function.id_comp]

end HasLaw

section HasGaussianLaw

variable {E : Type*} (X : Ω → E) (P : Measure Ω)

section Basic

variable [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [mE : MeasurableSpace E]

/-- The predicate `HasGaussianLaw X P` means that under the measure `P`,
`X` has a Gaussian distribution -/
class HasGaussianLaw :
    Prop where
  protected isGaussian_map : IsGaussian (P.map X)

attribute [instance] HasGaussianLaw.isGaussian_map

variable {X P}

instance IsGaussian.hasGaussianLaw [IsGaussian (P.map X)] :
    HasGaussianLaw X P where
  isGaussian_map := inferInstance

instance IsGaussian.hasGaussianLaw_fun [IsGaussian (P.map X)] :
    HasGaussianLaw (fun ω ↦ X ω) P where
  isGaussian_map := inferInstance

variable {mE} in
instance IsGaussian.hasGaussianLaw_id {μ : Measure E} [IsGaussian μ] :
    HasGaussianLaw id μ where
  isGaussian_map := by rwa [Measure.map_id]

@[fun_prop, measurability]
lemma HasGaussianLaw.aemeasurable [hX : HasGaussianLaw X P] : AEMeasurable X P := by
  by_contra! h
  have := hX.isGaussian_map
  rw [Measure.map_of_not_aemeasurable h] at this
  exact this.toIsProbabilityMeasure.ne_zero _ rfl

lemma HasGaussianLaw.isProbabilityMeasure [HasGaussianLaw X P] : IsProbabilityMeasure P where
  measure_univ := by
    rw [← Set.preimage_univ (f := X), ← Measure.map_apply_of_aemeasurable (by fun_prop) .univ,
      measure_univ]

variable {mE} in
lemma HasLaw.hasGaussianLaw {μ : Measure E} (hX : HasLaw X P μ) [IsGaussian μ] :
    HasGaussianLaw X P where
  isGaussian_map := by rwa [hX.map_eq]

end Basic

section NormedSpace

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) {X P}

instance HasGaussianLaw.map [HasGaussianLaw X P] : HasGaussianLaw (L ∘ X) P where
  isGaussian_map := by
    rw [← AEMeasurable.map_map_of_aemeasurable]
    · infer_instance
    all_goals fun_prop

instance HasGaussianLaw.map_fun [hX : HasGaussianLaw X P] : HasGaussianLaw (fun ω ↦ L (X ω)) P :=
  hX.map L

variable (L : E ≃L[ℝ] F)

instance HasGaussianLaw.map_equiv [HasGaussianLaw X P] : HasGaussianLaw (L ∘ X) P where
  isGaussian_map := by
    rw [← AEMeasurable.map_map_of_aemeasurable]
    · infer_instance
    all_goals fun_prop

instance HasGaussianLaw.map_equiv_fun [hX : HasGaussianLaw X P] :
    HasGaussianLaw (fun ω ↦ L (X ω)) P := hX.map_equiv L

instance IsGaussian.eval {ι Ω : Type*} {E : ι → Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}
    [h : IsGaussian (P.map (fun ω ↦ (X · ω)))] (i : ι) :
    IsGaussian (P.map (X i)) := by
  have : X i = (ContinuousLinearMap.proj (R := ℝ) (φ := E) i) ∘ (fun ω ↦ (X · ω)) := by ext; simp
  rw [this, ← AEMeasurable.map_map_of_aemeasurable]
  · infer_instance
  · fun_prop
  by_contra!
  rw [Measure.map_of_not_aemeasurable] at h
  · exact h.toIsProbabilityMeasure.ne_zero _ rfl
  · exact this

instance HasGaussianLaw.eval {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)]
    {X : (i : ι) → Ω → E i} [HasGaussianLaw (fun ω ↦ (X · ω)) P] (i : ι) :
    HasGaussianLaw (X i) P := inferInstance

instance HasGaussianLaw.fun_eval {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {X : (i : ι) → Ω → E i} [HasGaussianLaw (fun ω ↦ (X · ω)) P] (i : ι) :
    HasGaussianLaw (fun ω ↦ X i ω) P := inferInstance

end NormedSpace

end HasGaussianLaw

end ProbabilityTheory
