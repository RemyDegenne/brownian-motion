import BrownianMotion.Auxiliary.MeasureTheory
import Mathlib.Probability.Distributions.Gaussian.Basic

open MeasureTheory ENNReal WithLp

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section HasLaw

variable {𝓧} {m𝓧 : MeasurableSpace 𝓧} (X : Ω → 𝓧) (μ : Measure 𝓧)
  (P : Measure Ω := by volume_tac)

/-- The predicate `HasLaw X μ P` registers the fact that the random variable `X` has law `μ` under
the measure `P`, in other words that `P.map X = μ`. We also require `X` to be `AEMeasurable`,
to allow for nice interactions with operations on the codomain of `X`. See for instance
`HasLaw.comp`, `IndepFun.hasLaw_mul` and `IndepFun.hasLaw_add`. -/
structure HasLaw : Prop where
  protected isProbabilityMeasure : IsProbabilityMeasure μ := by infer_instance
  protected map_eq : P.map X = μ

variable {X μ} {P : Measure Ω}

lemma HasLaw.aemeasurable (h : HasLaw X μ P) : AEMeasurable X P :=
  haveI := h.isProbabilityMeasure
  aemeasurable_of_map_neZero (h.map_eq ▸ inferInstance)

lemma HasLaw.isProbabilityMeasure₂ (h : HasLaw X μ P) : IsProbabilityMeasure P where
  measure_univ := by
    have := h.isProbabilityMeasure
    rw [← Set.preimage_univ (f := X), ← Measure.map_apply_of_aemeasurable h.aemeasurable .univ,
      h.map_eq, measure_univ]

lemma hasLaw_map [IsProbabilityMeasure P] (hX : AEMeasurable X P) : HasLaw X (P.map X) P where
  isProbabilityMeasure := isProbabilityMeasure_map hX
  map_eq := rfl

lemma HasLaw.congr {Y : Ω → 𝓧} (hX : HasLaw X μ P) (hY : Y =ᵐ[P] X) : HasLaw Y μ P where
  map_eq := by rw [Measure.map_congr hY, hX.map_eq]

lemma _root_.MeasureTheory.MeasurePreserving.hasLaw (h : MeasurePreserving X P μ) :
    HasLaw X μ P where
  aemeasurable := h.measurable.aemeasurable
  map_eq := h.map_eq

lemma HasLaw.measurePreserving (h₁ : HasLaw X μ P) (h₂ : Measurable X) :
    MeasurePreserving X P μ where
  measurable := h₂
  map_eq := h₁.map_eq

lemma HasLaw.comp {𝒴 : Type*} {m𝒴 : MeasurableSpace 𝒴} {ν : Measure 𝒴} {Y : 𝓧 → 𝒴}
    (hY : HasLaw Y ν μ) (hX : HasLaw X μ P) : HasLaw (Y ∘ X) ν P where
  aemeasurable := (hX.map_eq ▸ hY.aemeasurable).comp_aemeasurable hX.aemeasurable
  map_eq := by
    rw [← AEMeasurable.map_map_of_aemeasurable _ hX.aemeasurable, hX.map_eq, hY.map_eq]
    rw [hX.map_eq]; exact hY.aemeasurable

lemma HasLaw.fun_comp {𝒴 : Type*} {m𝒴 : MeasurableSpace 𝒴} {ν : Measure 𝒴} {Y : 𝓧 → 𝒴}
    (hY : HasLaw Y ν μ) (hX : HasLaw X μ P) : HasLaw (fun ω ↦ Y (X ω)) ν P :=
  hY.comp hX

@[to_additive]
lemma IndepFun.hasLaw_mul [IsFiniteMeasure P] {M : Type*} [Monoid M] {mM : MeasurableSpace M}
    [MeasurableMul₂ M] {μ ν : Measure M} {X Y : Ω → M} (hX : HasLaw X μ P) (hY : HasLaw Y ν P)
    (hXY : IndepFun X Y P) :
    HasLaw (X * Y) (μ ∗ₘ ν) P where
  aemeasurable := hX.aemeasurable.mul hY.aemeasurable
  map_eq := by
    rw [hXY.map_mul_eq_map_mconv_map₀ hX.aemeasurable hY.aemeasurable, hX.map_eq, hY.map_eq]

@[to_additive]
lemma IndepFun.hasLaw_fun_mul [IsFiniteMeasure P] {M : Type*} [Monoid M] {mM : MeasurableSpace M}
    [MeasurableMul₂ M] {μ ν : Measure M} {X Y : Ω → M} (hX : HasLaw X μ P) (hY : HasLaw Y ν P)
    (hXY : IndepFun X Y P) :
    HasLaw (fun ω ↦ X ω * Y ω) (μ ∗ₘ ν) P := hXY.hasLaw_mul hX hY

lemma HasLaw.integral_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Ω → 𝓧} (hX : HasLaw X μ P) {f : 𝓧 → E} (hf : AEStronglyMeasurable f μ) :
    P[f ∘ X] = ∫ x, f x ∂μ := by
  rw [← hX.map_eq, integral_map hX.aemeasurable]
  · rfl
  · rwa [hX.map_eq]

lemma HasLaw.lintegral_comp {X : Ω → 𝓧} (hX : HasLaw X μ P) {f : 𝓧 → ℝ≥0∞}
    (hf : AEMeasurable f μ) : ∫⁻ ω, f (X ω) ∂P = ∫⁻ x, f x ∂μ := by
  rw [← hX.map_eq, lintegral_map' _ hX.aemeasurable]
  rwa [hX.map_eq]

lemma HasLaw.covariance_fun_comp {X : Ω → 𝓧} (hX : HasLaw X μ P) {f g : 𝓧 → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    cov[fun ω ↦ f (X ω), fun ω ↦ g (X ω); P] = cov[fun x ↦ f x, fun x ↦ g x; μ] := by
  rw [← hX.map_eq, covariance_map]
  · rfl
  · rw [hX.map_eq]
    exact hf.aestronglyMeasurable
  · rw [hX.map_eq]
    exact hg.aestronglyMeasurable
  · exact hX.aemeasurable

lemma HasLaw.integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Measure E}
    {X : Ω → E} (hX : HasLaw X μ P) : P[X] = ∫ x, x ∂μ := by
  rw [← Function.id_comp X, hX.integral_comp aestronglyMeasurable_id]
  simp

lemma HasLaw.variance_eq {μ : Measure ℝ} {X : Ω → ℝ} (hX : HasLaw X μ P) :
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
lemma HasLaw.hasGaussianLaw {μ : Measure E} (hX : HasLaw X μ P) [IsGaussian μ] :
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

instance HasGaussianLaw.eval {ι Ω : Type*} {E : ι → Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}
    [h : HasGaussianLaw (fun ω ↦ (X · ω)) P] (i : ι) :
    HasGaussianLaw (X i) P := by
  have : X i = (ContinuousLinearMap.proj (R := ℝ) (φ := E) i) ∘ (fun ω ↦ (X · ω)) := by ext; simp
  rw [this]
  infer_instance

instance HasGaussianLaw.toLp_comp (p : ℝ≥0∞) [Fact (1 ≤ p)] {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {X : (i : ι) → Ω → E i} [HasGaussianLaw (fun ω ↦ (X · ω)) P] :
    HasGaussianLaw (fun ω ↦ toLp p (X · ω)) P := by
  rw [← PiLp.continuousLinearEquiv_symm_apply p ℝ]
  infer_instance

instance HasGaussianLaw.toLp_comp' (p : ℝ≥0∞) [Fact (1 ≤ p)] {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    {X : Ω → E} {Y : Ω → F} [HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] :
    HasGaussianLaw (fun ω ↦ toLp p (X ω, Y ω)) P := by
  conv => enter [1, ω]; change (WithLp.prodContinuousLinearEquiv p ℝ E F).symm _
  infer_instance

lemma HasGaussianLaw.fst {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    {X : Ω → E} {Y : Ω → F} [HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] :
    HasGaussianLaw X P := by
  have : X = (ContinuousLinearMap.fst ℝ E F) ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  infer_instance

lemma HasGaussianLaw.snd {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    {X : Ω → E} {Y : Ω → F} [HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] :
    HasGaussianLaw Y P := by
  have : Y = (ContinuousLinearMap.snd ℝ E F) ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  infer_instance

instance IsGaussian.map_eval {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] {mE : ∀ i, MeasurableSpace (E i)}
    [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {μ : Measure (Π i, E i)} [IsGaussian μ] (i : ι) : HasGaussianLaw (fun x ↦ x i) μ := by
  refine HasGaussianLaw.eval (Ω := Π j, E j) (X := fun i x ↦ x i) (h := ?_) i
  exact IsGaussian.hasGaussianLaw_id

instance IsGaussian.map_eval_piLp (p : ℝ≥0∞) [Fact (1 ≤ p)] {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] {mE : ∀ i, MeasurableSpace (E i)}
    [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {μ : Measure (PiLp p E)} [IsGaussian μ] (i : ι) : HasGaussianLaw (fun x ↦ x i) μ :=
  IsGaussian.map_eval i

instance HasGaussianLaw.sub {ι Ω E : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {X : ι → Ω → E}
    [h : HasGaussianLaw (fun ω ↦ (X · ω)) P] (i j : ι) :
    HasGaussianLaw (X i - X j) P := by
  have : X i - X j = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ E) i -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ E) j) ∘ (fun ω ↦ (X · ω)) := by ext; simp
  rw [this]
  infer_instance

instance IsGaussian.map_eval_sub_eval {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure (ι → E)} [IsGaussian μ] (i j : ι) :
    HasGaussianLaw (fun x ↦ x i - x j) μ := by
  refine HasGaussianLaw.sub (Ω := ι → E) (X := fun i x ↦ x i) (h := ?_) i j
  exact IsGaussian.hasGaussianLaw_id

instance IsGaussian.map_eval_sub_eval_piLp (p : ℝ≥0∞) [Fact (1 ≤ p)] {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {μ : Measure (PiLp p (fun _ ↦ E))} [IsGaussian μ] (i j : ι) :
    HasGaussianLaw (fun x ↦ x i - x j) μ :=
  IsGaussian.map_eval_sub_eval i j

end NormedSpace

end HasGaussianLaw

end ProbabilityTheory
