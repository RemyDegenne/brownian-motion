import BrownianMotion.Gaussian.BrownianMotion

/-!
# Verso file for the Brownian motion process

This file is used to generate the Verso manual page about Brownian motion.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology
noncomputable section

abbrev Ω := ℝ≥0 → ℝ

variable {I : Finset ℝ≥0} {s t : ℝ≥0} {ω : Ω}

/- Projective family and limit -/

-- ANCHOR: Measures
example (I : Finset ℝ≥0) :
  brownianCovMatrix I = Matrix.of fun s t ↦ min s.1 t.1 := rfl

example (I : Finset ℝ≥0) :
    gaussianProjectiveFamily I =
      (multivariateGaussian 0 (brownianCovMatrix I)).map
      (MeasurableEquiv.toLp 2 (I → ℝ)).symm :=
  rfl

example : (gaussianLimit : Measure Ω) =
  projectiveLimit gaussianProjectiveFamily
    isProjectiveMeasureFamily_gaussianProjectiveFamily := rfl
-- ANCHOR_END: Measures

instance : MeasureSpace Ω := ⟨gaussianLimit⟩

/- Brownian and its law. -/

-- ANCHOR: Brownian
def B : ℝ≥0 → Ω → ℝ := brownian

example (t : ℝ≥0) : HasLaw (B t) (gaussianReal 0 t) :=
  hasLaw_brownian_eval

example (s t : ℝ≥0) : cov[B s, B t] = min s t :=
  covariance_brownian s t

example (s t : ℝ≥0) :
    HasLaw (B s - B t) (gaussianReal 0 (max (s - t) (t - s))) :=
  hasLaw_brownian_sub

example (I : Finset ℝ≥0) :
    HasLaw (fun ω ↦ I.restrict (B · ω)) (gaussianProjectiveFamily I) :=
  hasLaw_restrict_brownian
-- ANCHOR_END: Brownian

/- Continuity. -/

-- ANCHOR: Continuity
example (ω : Ω) (t β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) :
    ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (B · ω) U :=
  memHolder_brownian ω t β hβ_pos hβ_lt

example (ω : Ω) : Continuous (B · ω) := continuous_brownian ω
-- ANCHOR_END: Continuity

/- Conclution: IsBrownian. In particular, IsGaussianProcess. -/

--ANCHOR: IsBrownian
example : IsBrownian B := IsBrownian_brownian

example : IsGaussianProcess B := isGaussianProcess_brownian

example : HasLaw (fun ω ↦ (B · ω)) gaussianLimit := hasLaw_brownian
-- ANCHOR_END: IsBrownian

/- Independent increments. -/

-- ANCHOR: HasIndepIncrements
example : HasIndepIncrements B := hasIndepIncrements_brownian

example (X : ℝ≥0 → Ω → ℝ) (hX : AEMeasurable (fun ω ↦ (X · ω)))
    (law : ∀ t, HasLaw (X t) (gaussianReal 0 t)) (incr : HasIndepIncrements X) :
    HasLaw (fun ω ↦ (X · ω)) gaussianLimit :=
  (incr.isPreBrownian_of_hasLaw law).hasLaw_gaussianLimit hX
-- ANCHOR_END: HasIndepIncrements

/- Other. -/

example {n : ℕ} (hn : 0 < n) :
    IsKolmogorovProcess B gaussianLimit (2 * n) n (Nat.doubleFactorial (2 * n - 1)) :=
  isKolmogorovProcess_brownian hn

-- ANCHOR: Transformations
variable {X : ℝ≥0 → Ω → ℝ}

example [IsBrownian X] {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownian (fun t ω ↦ (X (c * t) ω) / √c) :=
  IsBrownian.smul hc

example [IsBrownian X] (t₀ : ℝ≥0) :
    IsBrownian (fun t ω ↦ X (t₀ + t) ω - X t₀ ω) :=
  IsBrownian.shift t₀

example [IsBrownian X] :
    IsBrownian (fun t ω ↦ t * (X (1 / t) ω)) :=
  IsBrownian.inv

example [IsBrownian X] :
    ∀ᵐ ω, Filter.Tendsto (X · ω) (𝓝 0) (𝓝 0) :=
  IsBrownian.tendsto_nhds_zero
-- ANCHOR_END: Transformations

end
