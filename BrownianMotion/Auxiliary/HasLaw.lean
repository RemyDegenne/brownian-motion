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
    HasGaussianLaw (X i) P where
  isGaussian_map := by
    have : X i = (ContinuousLinearMap.proj (R := ℝ) (φ := E) i) ∘ (fun ω ↦ (X · ω)) := by ext; simp
    rw [this, ← AEMeasurable.map_map_of_aemeasurable]
    · infer_instance
    · fun_prop
    · exact h.aemeasurable

instance HasGaussianLaw.toLp_comp (p : ℝ≥0∞) [Fact (1 ≤ p)] {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {X : (i : ι) → Ω → E i} [HasGaussianLaw (fun ω ↦ (X · ω)) P] :
    HasGaussianLaw (fun ω ↦ toLp p (X · ω)) P := by
  rw [← PiLp.continuousLinearEquiv_symm_apply p ℝ]
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
    HasGaussianLaw (X i - X j) P where
  isGaussian_map := by
    have : X i - X j = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ E) i -
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ E) j) ∘ (fun ω ↦ (X · ω)) := by ext; simp
    rw [this, ← AEMeasurable.map_map_of_aemeasurable]
    · infer_instance
    · fun_prop
    · exact h.aemeasurable

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
