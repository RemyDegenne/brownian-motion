import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

open MeasureTheory ENNReal WithLp

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section HasLaw

variable {𝓧} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧} {μ : Measure 𝓧} {P : Measure Ω}

lemma hasLaw_map (hX : AEMeasurable X P) : HasLaw X (P.map X) P where
  aemeasurable := hX
  map_eq := rfl

section dirac

lemma HasLaw.ae_eq_of_dirac' {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} [MeasurableSingletonClass 𝓧]
    {x : 𝓧} {X : Ω → 𝓧}
    (hX : HasLaw X (.dirac x) P) : X =ᵐ[P] (fun _ ↦ x) := by
  apply ae_of_ae_map (p := fun y ↦ y = x) hX.aemeasurable
  rw [hX.map_eq, ae_dirac_iff]
  simp

lemma HasLaw.ae_eq_of_dirac {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} [MeasurableSingletonClass 𝓧]
    {x : 𝓧} {X : Ω → 𝓧}
    (hX : HasLaw X (.dirac x) P) : ∀ᵐ ω ∂P, X ω = x := hX.ae_eq_of_dirac'

lemma HasLaw.ae_eq_const_of_gaussianReal {X : Ω → ℝ} {μ : ℝ} (hX : HasLaw X (gaussianReal μ 0) P) :
    ∀ᵐ ω ∂P, X ω = μ := by
  rw [gaussianReal_zero_var] at hX
  exact hX.ae_eq_of_dirac

end dirac

end HasLaw

end ProbabilityTheory
