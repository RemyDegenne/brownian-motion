/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Gaussian.BrownianMotion
public import BrownianMotion.StochasticIntegral.QuadraticVariation

/-! # Quadratic variation of Brownian motion

-/

@[expose] public section

open MeasureTheory Filter Filtration
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- The linear order instance on `ℝ≥0` used locally for the quadratic-variation construction. -/
noncomputable local instance qvLinearOrderNNReal : LinearOrder ℝ≥0 :=
  let inst := (inferInstance : ConditionallyCompleteLinearOrderBot ℝ≥0)
  inst.toConditionallyCompleteLinearOrder.toLinearOrder

/-- Continuous paths are càdlàg. -/
lemma continuous_isCadlag {ι E : Type*} [TopologicalSpace ι] [Preorder ι] [TopologicalSpace E]
    {f : ι → E} (hf : Continuous f) : IsCadlag f where
  right_continuous _ := hf.continuousAt.continuousWithinAt
  left_limit a := ⟨f a, hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩

/-- The natural filtration of the canonical Brownian motion. -/
noncomputable abbrev brownianNaturalFiltration :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) :=
  natural brownian fun t ↦ (measurable_brownian t).stronglyMeasurable

/-- The Brownian natural filtration admits dyadic approximations of stopping times. -/
noncomputable instance brownianNaturalFiltrationApproximable :
    Approximable brownianNaturalFiltration gaussianLimit :=
  ⟨fun τ hτ ↦ ⟨nnrealApproxSeq τ, nnrealApproxSeq_isStoppingTime brownianNaturalFiltration hτ,
    nnrealApproxSeq_countable τ, nnrealApproxSeq_antitone τ,
    nnrealApproxSeq_le τ, ae_of_all _ <| nnrealApproxSeq_tendsto τ⟩⟩

/-- The canonical Brownian motion has càdlàg paths. -/
lemma isCadlag_brownian (ω : ℝ≥0 → ℝ) : IsCadlag (brownian · ω) :=
  continuous_isCadlag (continuous_brownian ω)

/-- The canonical Brownian motion is a martingale with respect to its natural filtration. -/
lemma martingale_brownian :
    Martingale brownian brownianNaturalFiltration gaussianLimit := by
  haveI : IsFilteredPreBrownian brownian brownianNaturalFiltration gaussianLimit :=
    isBrownianReal_brownian.toIsPreBrownianReal.isFilteredPreBrownian measurable_brownian
  exact IsPreBrownianReal.isMartingale brownian brownianNaturalFiltration gaussianLimit

/-- The fixed-time `L²` norm of Brownian motion is the square root of time. -/
lemma eLpNorm_brownian_eq (t : ℝ≥0) :
    eLpNorm (brownian t) 2 gaussianLimit = ENNReal.ofReal (Real.sqrt (t : ℝ)) := by
  have hmem : MemLp (brownian t) 2 gaussianLimit :=
    (isGaussianProcess_brownian.hasGaussianLaw_eval t).memLp_two
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have hsquare : ∫ ω, brownian t ω ^ 2 ∂gaussianLimit = (t : ℝ) := by
    have hlaw : HasLaw (brownian t) (gaussianReal 0 t) gaussianLimit := hasLaw_brownian_eval
    have hmean : gaussianLimit[brownian t] = 0 := by
      calc
        gaussianLimit[brownian t] = ∫ x, x ∂gaussianReal 0 t := hlaw.integral_eq
        _ = 0 := by simp
    have hvar : Var[brownian t; gaussianLimit] = (t : ℝ) := by
      rw [hlaw.variance_eq, variance_id_gaussianReal]
    rw [variance_eq_integral hlaw.aemeasurable, hmean] at hvar
    simpa using hvar
  have hnorm :
      ∫ ω, ‖brownian t ω‖ ^ (2 : ℝ≥0∞).toReal ∂gaussianLimit = (t : ℝ) := by
    simpa [Real.norm_eq_abs, sq_abs, pow_two] using hsquare
  rw [hnorm]
  norm_num
  rw [Real.sqrt_eq_rpow]

/-- Brownian motion stopped at a positive deterministic horizon is square-integrable. -/
lemma isSquareIntegrable_stopped_brownian_const (T : ℝ≥0) (hT : 0 < T) :
    IsSquareIntegrable
      (stoppedProcess brownian (fun _ : ℝ≥0 → ℝ ↦ (T : WithTop ℝ≥0)))
      brownianNaturalFiltration gaussianLimit := by
  refine ⟨?_, ?_, ?_⟩
  · convert martingale_brownian.stoppedProcess_indicator
      (fun ω ↦ (isCadlag_brownian ω).right_continuous)
      (isStoppingTime_const' brownianNaturalFiltration (T : WithTop ℝ≥0)) using 1
    ext i ω
    have hpos : (⊥ : WithTop ℝ≥0) < (T : WithTop ℝ≥0) := by
      simpa using (WithTop.coe_lt_coe.mpr hT :
        ((0 : ℝ≥0) : WithTop ℝ≥0) < (T : WithTop ℝ≥0))
    have hmem :
        ω ∈ {ω : ℝ≥0 → ℝ | (⊥ : WithTop ℝ≥0) < (T : WithTop ℝ≥0)} := hpos
    simp only [stoppedProcess]
    rw [Set.indicator_of_mem hmem]
  · convert isStable_isCadlag brownian isCadlag_brownian
      (fun _ : ℝ≥0 → ℝ ↦ (T : WithTop ℝ≥0))
      (isStoppingTime_const' brownianNaturalFiltration (T : WithTop ℝ≥0)) using 1
    ext i ω
    have hpos : (⊥ : WithTop ℝ≥0) < (T : WithTop ℝ≥0) := by
      simpa using (WithTop.coe_lt_coe.mpr hT :
        ((0 : ℝ≥0) : WithTop ℝ≥0) < (T : WithTop ℝ≥0))
    have hmem :
        ω ∈ {ω : ℝ≥0 → ℝ | (⊥ : WithTop ℝ≥0) < (T : WithTop ℝ≥0)} := hpos
    simp only [stoppedProcess]
    rw [Set.indicator_of_mem hmem]
  · have hstopped :
        stoppedProcess brownian (fun _ : ℝ≥0 → ℝ ↦ (T : WithTop ℝ≥0)) =
          fun i ↦ brownian (min i T) := by
      ext i ω
      simp only [stoppedProcess]
      rw [← WithTop.coe_min i T, WithTop.untopA_coe]
    rw [hstopped]
    refine lt_of_le_of_lt ?_
      (show ENNReal.ofReal (Real.sqrt (T : ℝ)) < ∞ from ENNReal.ofReal_lt_top)
    refine iSup_le fun i ↦ ?_
    rw [eLpNorm_brownian_eq]
    exact ENNReal.ofReal_le_ofReal
      (Real.sqrt_le_sqrt (by exact_mod_cast (min_le_right i T)))

/-- The canonical Brownian motion is locally square-integrable.

The localizing sequence is given by deterministic positive horizons. -/
lemma locally_isSquareIntegrable_brownian :
    IsLocallySquareIntegrable brownian brownianNaturalFiltration gaussianLimit := by
  let τ : ℕ → (ℝ≥0 → ℝ) → WithTop ℝ≥0 :=
    fun n _ ↦ (((n + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)
  refine ⟨τ, ?_, fun n ↦ ?_⟩
  · exact {
      isStoppingTime := fun n ↦
        isStoppingTime_const' brownianNaturalFiltration
          ((((n + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0))
      mono := by
        filter_upwards with ω
        intro n m hnm
        exact WithTop.coe_le_coe.mpr (by exact_mod_cast Nat.add_le_add_right hnm 1)
      tendsto_top := by
        filter_upwards with ω
        refine nhds_top_basis.tendsto_right_iff.2 fun i hi ↦ ?_
        lift i to ℝ≥0 using (lt_top_iff_ne_top.mp hi) with a
        obtain ⟨N, hN⟩ := exists_nat_gt a
        filter_upwards [Ici_mem_atTop N] with n hn
        exact WithTop.coe_lt_coe.mpr
          (lt_of_lt_of_le hN (by exact_mod_cast (Nat.le_add_right_of_le hn))) }
  · let T : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0)
    have hT : 0 < T := by positivity
    convert isSquareIntegrable_stopped_brownian_const T hT using 1
    ext i ω
    have hpos : (⊥ : WithTop ℝ≥0) < (T : WithTop ℝ≥0) := by
      simpa using (WithTop.coe_lt_coe.mpr hT :
        ((0 : ℝ≥0) : WithTop ℝ≥0) < (T : WithTop ℝ≥0))
    have hmem : ω ∈ {ω : ℝ≥0 → ℝ |
        (⊥ : WithTop ℝ≥0) < (T : WithTop ℝ≥0)} := hpos
    simp only [τ, T, stoppedProcess]
    rw [Set.indicator_of_mem hmem]

/-- The quadratic variation process attached to the canonical Brownian motion. -/
noncomputable abbrev brownianQuadraticVariation : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  quadraticVariation locally_isSquareIntegrable_brownian isCadlag_brownian

/-- At each deterministic time, the Brownian quadratic variation is almost surely `t`. -/
theorem quadraticVariation_brownian (t : ℝ≥0) :
    brownianQuadraticVariation t =ᵐ[gaussianLimit] fun _ => (t : ℝ) := by
  -- This needs the normalized uniqueness statement for the local Doob-Meyer predictable part.
  sorry

end ProbabilityTheory
