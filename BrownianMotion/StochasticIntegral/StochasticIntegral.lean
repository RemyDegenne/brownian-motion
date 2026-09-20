/-
Copyright (c) 2025 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Filtration
public import BrownianMotion.Auxiliary.Indistinguishable

/-!
# Characterization of the stochastic integral.

This file contains an axiomatic characterization of the stochastic integral
against a process `Y : ι → Ω → ℝ`. The integral is defined as a map from `ι → Ω → ℝ`
to `Ω → ℝ`, meaning that we are evaluating the integral at some fixed, terminal time.

We ask for the following properties, which we expect
any good stochastic integral `I` to have:
* The integral agrees with the Riemann-Stieltjes integral for elementary processes.
* Linearity for the integral and its domain.
* The integral and its domain respect indistinguishability.
* Dominated convergence: if a process `X` is integrable, then any pointwise limit of a
  sequence of integrable processes which is dominated by `X` should again be integrable.

The properties above are encoded in the predicate `IsRiemannStieltjesExtension`.
However, this predicate does not ensure that the integral is canonical or unique.
To get a true stochastic integral `I`, we additionally impose the following.
* Any extension of the Riemann-Stieltjes integral must agree with `I` on
  the intersection of their domains.

This additional condition is encoded in `IsStochasticIntegral` which extends
`IsRiemannStieltjesExtension`.

Note that none of the definitions impose that the domain `S` should be maximal.
As a consequence, it is possible to define stochastic integrals with different domains.
However, any two such integrals will necessarily agree (almost surely) on the intersection
of their domains.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
variable {ι : Type*} [LinearOrder ι] [OrderBot ι]
variable (Y : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ)

/-- A domain is a subset of stochastic processes. -/
abbrev Domain := Set (ι → Ω → ℝ)
/-- An `SIntegral` maps processes to random variables. -/
abbrev SIntegral := (X : ι → Ω → ℝ) → Ω → ℝ

/-- An SIntegral `I` with domain `S` is an extension of the Riemann-Stieltjes integral
if it agrees with Riemann-Stieltjes on elementary processes and respects linearity,
indistinguishability, and dominated convergence. -/
structure IsRiemannStieltjesExtension (I : SIntegral) (S : Domain) : Prop where
  /-- The stochastic integral is measurable. -/
  measurable X (h : X ∈ S) : AEStronglyMeasurable (I X) P
  /-- Elementary functions are in the domain and the value of the integral is the
  expected one. -/
  elementary_ioc i j (h : i ≤ j) (X : @SimpleFunc Ω (𝓕 i) ℝ) :
    (fun k ω ↦ if (k ∈ Set.Ioc i j) then X ω else 0) ∈ S ∧
    I (fun k ω ↦ if (k ∈ Set.Ioc i j) then X ω else 0) =ᵐ[P] X * (Y j - Y i)
  elementary_iic i (X : @SimpleFunc Ω (𝓕 ⊥) ℝ) :
    (fun j ω ↦ if (j ∈ Set.Iic i) then X ω else 0) ∈ S ∧
    I (fun j ω ↦ if (j ∈ Set.Iic i) then X ω else 0) =ᵐ[P] X * (Y i - Y ⊥)
  /-- The integral and the domain respect addition. -/
  integral_add X₁ X₂ (h₁ : X₁ ∈ S) (h₂ : X₂ ∈ S) :
    X₁ + X₂ ∈ S ∧ I (X₁ + X₂) =ᵐ[P] I X₁ + I X₂
  /-- The integral and the domain respect scalar multiplication. -/
  integral_smul X (α : ℝ) (h : X ∈ S) :
    α • X ∈ S ∧ I (α • X) =ᵐ[P] α • I X
  /-- The integral and its domain respect indistinguishability. -/
  integral_indistinguishable X₁ X₂ (h₁ : X₁ ∈ S) (h₂ : X₁ ≡ᵐ[P] X₂) :
    X₂ ∈ S ∧ I X₁ =ᵐ[P] I X₂
  /-- The domain is closed under dominated convergence, and in this case the integral
  commutes with the limit. -/
  integral_dct (X : ℕ → ι → Ω → ℝ) X_dom X_lim (h₁ : ∀ n, X n ∈ S) (h₂ : X_dom ∈ S)
      (h_dom : ∀ n i ω, |X n i ω| ≤ |X_dom i ω|)
      (h_lim : ∀ i ω, Tendsto (X · i ω) atTop (𝓝 (X_lim i ω))) :
    X_lim ∈ S ∧ TendstoInMeasure P (fun n ↦ I (X n)) atTop (I X_lim)

/-- An SIntegral `I` with domain `S` is a *stochastic integral* if it is an extension of the
Riemann-Stieltjes integral and it agrees with any other extension on the intersection
of their domains. -/
structure IsStochasticIntegral I S extends IsRiemannStieltjesExtension P Y 𝓕 I S where
  consistent I' S' (h : IsRiemannStieltjesExtension P Y 𝓕 I' S') X (hX : X ∈ S ∩ S') :
    I X =ᵐ[P] I' X

end ProbabilityTheory

end
