import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.HasLaw

open MeasureTheory ENNReal WithLp

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section HasLaw

variable {𝓧} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧} {μ : Measure 𝓧} {P : Measure Ω}

lemma hasLaw_map (hX : AEMeasurable X P) : HasLaw X (P.map X) P where
  aemeasurable := hX
  map_eq := rfl

section dirac

lemma HasLaw.aeeq_of_dirac' {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} [MeasurableSingletonClass 𝓧]
    {x : 𝓧} {X : Ω → 𝓧}
    (hX : HasLaw X (.dirac x) P) : X =ᵐ[P] (fun _ ↦ x) := by
  apply ae_of_ae_map (p := fun y ↦ y = x) hX.aemeasurable
  rw [hX.map_eq, ae_dirac_iff]
  simp

lemma HasLaw.aeeq_of_dirac {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} [MeasurableSingletonClass 𝓧]
    {x : 𝓧} {X : Ω → 𝓧}
    (hX : HasLaw X (.dirac x) P) : ∀ᵐ ω ∂P, X ω = x := hX.aeeq_of_dirac'

lemma HasLaw.aeeq_const_of_gaussianReal {X : Ω → ℝ} {μ : ℝ} (hX : HasLaw X (gaussianReal μ 0) P) :
    ∀ᵐ ω ∂P, X ω = μ := by
  rw [gaussianReal_zero_var] at hX
  exact hX.aeeq_of_dirac

end dirac

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [IsProbabilityMeasure P] {X Y : Ω → E}

lemma IndepFun.charFunDual_map_add_eq_mul [NormedSpace ℝ E]
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : IndepFun X Y P) :
    charFunDual (P.map (X + Y)) = charFunDual (P.map X) * charFunDual (P.map Y) := by
  ext L
  rw [(hXY.hasLaw_add (hasLaw_map mX) (hasLaw_map mY)).map_eq, charFunDual_conv, Pi.mul_apply]

lemma IndepFun.charFun_map_add_eq_mul [InnerProductSpace ℝ E]
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : IndepFun X Y P) :
    charFun (P.map (X + Y)) = charFun (P.map X) * charFun (P.map Y) := by
  ext t
  rw [(hXY.hasLaw_add (hasLaw_map mX) (hasLaw_map mY)).map_eq, charFun_conv, Pi.mul_apply]

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

lemma HasGaussianLaw.congr {Y : Ω → E} [HasGaussianLaw X P] (h : ∀ᵐ ω ∂P, X ω = Y ω) :
    HasGaussianLaw Y P where
  isGaussian_map := by
    rw [← Measure.map_congr h]
    infer_instance

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

section SpecificMaps

section Prod

variable [SecondCountableTopologyEither E F] {Y : Ω → F}

instance HasGaussianLaw.toLp_comp_prodMk (p : ℝ≥0∞) [Fact (1 ≤ p)]
    [HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] :
    HasGaussianLaw (fun ω ↦ toLp p (X ω, Y ω)) P := by
  conv => enter [1, ω]; change (WithLp.prodContinuousLinearEquiv p ℝ E F).symm _
  infer_instance

lemma HasGaussianLaw.fst [HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] :
    HasGaussianLaw X P := by
  have : X = (ContinuousLinearMap.fst ℝ E F) ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  infer_instance

lemma HasGaussianLaw.snd [HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] :
    HasGaussianLaw Y P := by
  have : Y = (ContinuousLinearMap.snd ℝ E F) ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  infer_instance

end Prod

section Pi

variable [SecondCountableTopology E] {ι : Type*} [Fintype ι] {X : ι → Ω → E}

section Nondependent

instance HasGaussianLaw.sub [h : HasGaussianLaw (fun ω ↦ (X · ω)) P] (i j : ι) :
    HasGaussianLaw (X i - X j) P := by
  have : X i - X j = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ E) i -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ E) j) ∘ (fun ω ↦ (X · ω)) := by ext; simp
  rw [this]
  infer_instance

instance IsGaussian.hasGaussianLaw_sub_eval {μ : Measure (ι → E)} [IsGaussian μ] (i j : ι) :
    HasGaussianLaw (fun x ↦ x i - x j) μ :=
  HasGaussianLaw.sub (h := IsGaussian.hasGaussianLaw_id) i j

instance IsGaussian.hasGaussianLaw_sub_eval_piLp (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {μ : Measure (PiLp p (fun _ ↦ E))} [IsGaussian μ] (i j : ι) :
    HasGaussianLaw (fun x ↦ x i - x j) μ :=
  IsGaussian.hasGaussianLaw_sub_eval i j

end Nondependent

variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}

instance HasGaussianLaw.eval [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}
    [h : HasGaussianLaw (fun ω ↦ (X · ω)) P] (i : ι) :
    HasGaussianLaw (X i) P := by
  have : X i = (ContinuousLinearMap.proj (R := ℝ) (φ := E) i) ∘ (fun ω ↦ (X · ω)) := by ext; simp
  rw [this]
  infer_instance

instance HasGaussianLaw.toLp_comp_pi (p : ℝ≥0∞) [Fact (1 ≤ p)]
    [HasGaussianLaw (fun ω ↦ (X · ω)) P] :
    HasGaussianLaw (fun ω ↦ toLp p (X · ω)) P := by
  rw [← PiLp.continuousLinearEquiv_symm_apply p ℝ]
  infer_instance

instance IsGaussian.hasGaussianLaw_eval {μ : Measure (Π i, E i)} [IsGaussian μ] (i : ι) :
    HasGaussianLaw (fun x ↦ x i) μ :=
  HasGaussianLaw.eval (h := IsGaussian.hasGaussianLaw_id) i

instance IsGaussian.hasGaussianLaw_eval_piLp (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {μ : Measure (PiLp p E)} [IsGaussian μ] (i : ι) : HasGaussianLaw (fun x ↦ x i) μ :=
  IsGaussian.hasGaussianLaw_eval i

end Pi

end SpecificMaps

end NormedSpace

end HasGaussianLaw

end ProbabilityTheory
