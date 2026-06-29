import Manual.Pages.Processes
import Manual.Pages.Extension
import Manual.Pages.Gaussian
import Manual.Pages.Continuity
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

set_option verso.exampleProject "../"

set_option verso.exampleModule "BrownianMotion.Verso.Brownian"

#doc (Manual) "Formalization of Brownian motion" =>
%%%
authors := ["Rémy Degenne, David Ledvinka, Etienne Marion, Peter Pfaffelhuber"]
shortTitle := "Formalization of Brownian motion"
%%%

*The Brownian motion project*

This is a collaborative formalization project, in which we formalized the following results:
- Kolmogorov extension theorem
- Gaussian measures and their properties
- Kolmogorov-Chentsov continuity theorem
- Putting everything together: construction of a Brownian motion on the nonnegative reals.

Besides the main authors, contributions were made by Markus Himmel, Jonas Bayer, Lorenzo Luccioli, Alessio Rondelli and Jérémy Scanvic, with technical support from Pietro Monticone.

*Main result: construction of a Brownian motion*

A stochastic process `ℝ≥0 → Ω → ℝ` is called *Brownian* if its finite-dimensional law for points $`t_1, ..., t_n` is a multivariate Gaussian with mean zero and covariance matrix given by $`min(t_i, t_j)`, and if it has almost-sure continuous paths.

We formalize the finite dimensional laws and the law of Brownian motion by constructing a projective family of finite-dimensional Gaussian measures with the correct covariance structure, and then taking its projective limit.

For a finite set `(I : Finset ℝ≥0)`, we define the covariance matrix {anchorTerm Measures}`brownianCovMatrix I` with entries `min s t` for `(s t : I)`.
Then, we define a family of multivaliate Gaussian measures, with mean zero and that covariance matrix.
Finally, we take the projective limit of this family, `gaussianLimit`.

```anchor Measures
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
```

The main result of the Brownian motion project is the construction of a process with that law and continuous paths.
Let's build one now, and first check that it has the right laws.
We write `Ω` for the probability space `ℝ≥0 → ℝ` endowed with the probability measure `gaussianLimit`.

```anchor Brownian
def B : ℝ≥0 → Ω → ℝ := brownian

example (t : ℝ≥0) : HasLaw (B t) (gaussianReal 0 t) :=
  hasLaw_brownian_eval

example (s t : ℝ≥0) : cov[B s, B t] = min s t :=
  covariance_brownian s t

example (s t : ℝ≥0) :
    HasLaw (B s - B t) (gaussianReal 0 (nndist s t)) :=
  hasLaw_brownian_sub

example (I : Finset ℝ≥0) :
    HasLaw (fun ω ↦ I.restrict (B · ω)) (gaussianProjectiveFamily I) :=
  hasLaw_restrict_brownian
```

The stochastic process {anchorTerm Brownian}`B` is such that {anchorTerm Brownian}`B t` has law {anchorTerm Brownian}`gaussianReal 0 t` for every `t : ℝ≥0`, with covariance structure given by {anchorTerm Brownian}`cov[B s, B t] = min s t`.
We also derived the law of its increments, and importantly to check that it has the right law, we checked that its finite-dimensional distributions match the projective family we constructed before.

Finally, we can check that {anchorTerm Brownian}`B` has continuous paths.
It even satisfies a stronger regularity property: local Hölder continuity.

```anchor Continuity
example (ω : Ω) (t β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) :
    ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (B · ω) U :=
  memHolder_brownian ω t β hβ_pos hβ_lt

example (ω : Ω) : Continuous (B · ω) := continuous_brownian ω
```

*Other properties of Brownian motion*

First, we check that {anchorTerm Brownian}`B` has independent increments, and we prove that any process with the same one-dimensional marginals and independent increments has the same law as {anchorTerm Brownian}`B` (but it might not be continuous).

```anchor HasIndepIncrements
example : HasIndepIncrements B := hasIndepIncrements_brownian

example (X : ℝ≥0 → Ω → ℝ) (hX : AEMeasurable (fun ω ↦ (X · ω)))
    (law : ∀ t, HasLaw (X t) (gaussianReal 0 t)) (incr : HasIndepIncrements X) :
    HasLaw (fun ω ↦ (X · ω)) gaussianLimit :=
  (incr.isPreBrownianReal_of_hasLaw law).hasLaw_gaussianLimit hX
```

Finally, we prove some classical transformations of Brownian motion: scaling, time shift, inversion.
Note that we use the structure {anchorTerm Transformations}`IsBrownianReal` to state that a process is a Brownian motion (it has the right law and has almost surely continuous paths).

```anchor Transformations
variable {X : ℝ≥0 → Ω → ℝ}

example (hX : IsBrownianReal X) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownianReal (fun t ω ↦ (√↑c)⁻¹ * X (c * t) ω) :=
  hX.smul hc

example (hX : IsBrownianReal X) (t₀ : ℝ≥0) :
    IsBrownianReal (fun t ω ↦ X (t₀ + t) ω - X t₀ ω) :=
  hX.shift t₀

example (hX : IsBrownianReal X) :
    IsBrownianReal (fun t ω ↦ t * (X (1 / t) ω)) :=
  hX.inv

example (hX : IsBrownianReal X) :
    ∀ᵐ ω, Filter.Tendsto (X · ω) (𝓝 0) (𝓝 0) :=
  hX.tendsto_nhds_zero
```
