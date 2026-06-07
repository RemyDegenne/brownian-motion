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

/-- The natural filtration of the canonical Brownian motion. -/
noncomputable abbrev brownianNaturalFiltration :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) :=
  natural brownian fun t ↦ (measurable_brownian t).stronglyMeasurable

section QuadraticVariationOrder

noncomputable local instance qvLinearOrderNNReal : LinearOrder ℝ≥0 :=
  let inst := (inferInstance : ConditionallyCompleteLinearOrderBot ℝ≥0)
  inst.toConditionallyCompleteLinearOrder.toLinearOrder

/-- The Brownian natural filtration admits dyadic approximations of stopping times. -/
noncomputable instance brownianNaturalFiltration_approximable :
    Approximable brownianNaturalFiltration gaussianLimit :=
  ⟨fun τ hτ ↦ ⟨nnrealApproxSeq τ, nnrealApproxSeq_isStoppingTime brownianNaturalFiltration hτ,
    nnrealApproxSeq_countable τ, nnrealApproxSeq_antitone τ,
    nnrealApproxSeq_le τ, ae_of_all _ <| nnrealApproxSeq_tendsto τ⟩⟩

end QuadraticVariationOrder

/-- The canonical Brownian motion has càdlàg paths. -/
lemma isCadlag_brownian (ω : ℝ≥0 → ℝ) : IsCadlag (brownian · ω) :=
  Continuous.isCadlag (continuous_brownian ω)

/-- The canonical Brownian motion is a martingale with respect to its natural filtration. -/
lemma martingale_brownian :
    Martingale brownian brownianNaturalFiltration gaussianLimit := by
  haveI : IsFilteredPreBrownian brownian brownianNaturalFiltration gaussianLimit :=
    IsPreBrownian.isFilteredPreBrownian (X := brownian) (P := gaussianLimit) measurable_brownian
  exact IsPreBrownian.isMartingale brownian brownianNaturalFiltration gaussianLimit

/-- The canonical Brownian square minus time process is a martingale. -/
lemma martingale_brownian_sq_sub_time :
    Martingale (fun t omega => brownian t omega ^ 2 - (t : ℝ))
      brownianNaturalFiltration gaussianLimit := by
  refine ⟨?_, ?_⟩
  · intro t
    have ht : StronglyMeasurable[brownianNaturalFiltration t] (brownian t) :=
      martingale_brownian.stronglyAdapted t
    simpa [pow_two] using (ht.mul ht).sub stronglyMeasurable_const
  · intro s t hst
    haveI : IsFilteredPreBrownian brownian brownianNaturalFiltration gaussianLimit :=
      IsPreBrownian.isFilteredPreBrownian (X := brownian) (P := gaussianLimit) measurable_brownian
    have hM := fun u ↦
      ((IsFilteredPreBrownian.stronglyAdapted (X := brownian)
        (𝓕 := brownianNaturalFiltration) (P := gaussianLimit) u).mono
          (brownianNaturalFiltration.le u)).measurable
    have hBs_sm : StronglyMeasurable[brownianNaturalFiltration s] (brownian s) :=
      martingale_brownian.stronglyAdapted s
    have hBs_L2 : MemLp (brownian s) 2 gaussianLimit :=
      (isGaussianProcess_brownian.hasGaussianLaw_eval s).memLp_two
    have hDelta_L2 : MemLp (brownian t - brownian s) 2 gaussianLimit :=
      (isGaussianProcess_brownian.hasGaussianLaw_fun_sub (s := t) (t := s)).memLp_two
    have hDeltaLaw : HasLaw (brownian t - brownian s) (gaussianReal 0 (t - s))
      gaussianLimit := by
      have hvar : max (t - s) (s - t) = t - s := by
        rw [tsub_eq_zero_of_le hst]
        exact max_eq_left (by positivity)
      simpa [hvar] using (hasLaw_brownian_sub (s := t) (t := s))
    have hDeltaMean : gaussianLimit[brownian t - brownian s] = 0 := by
      calc
        gaussianLimit[brownian t - brownian s]
            = ∫ x, x ∂gaussianReal 0 (t - s) := hDeltaLaw.integral_eq
        _ = 0 := by simp
    have hDeltaSqIntegral :
        ∫ ω, (brownian t - brownian s) ω ^ 2 ∂gaussianLimit =
          ((t - s : ℝ≥0) : ℝ) := by
      have hvar_delta :
          Var[brownian t - brownian s; gaussianLimit] = ((t - s : ℝ≥0) : ℝ) := by
        rw [hDeltaLaw.variance_eq, variance_id_gaussianReal]
      rw [variance_eq_integral hDeltaLaw.aemeasurable, hDeltaMean] at hvar_delta
      simpa using hvar_delta
    have hDeltaNoCond :
        gaussianLimit[brownian t - brownian s | brownianNaturalFiltration s]
          =ᵐ[gaussianLimit] fun _ => gaussianLimit[brownian t - brownian s] := by
      refine condExp_indep_eq ?_ (brownianNaturalFiltration.le s) ?_
        (IsFilteredPreBrownian.indep (X := brownian) (𝓕 := brownianNaturalFiltration)
          (P := gaussianLimit) s t hst)
      · exact Measurable.comap_le (Measurable.sub (hM t) (hM s))
      · exact (comap_measurable (brownian t - brownian s)).stronglyMeasurable
    have hDeltaCondZero :
        gaussianLimit[brownian t - brownian s | brownianNaturalFiltration s]
          =ᵐ[gaussianLimit] fun _ => 0 :=
      hDeltaNoCond.trans (ae_of_all _ fun _ => hDeltaMean)
    have hProdInt :
        Integrable (fun ω => brownian s ω * (brownian t ω - brownian s ω))
          gaussianLimit := by
      rw [← memLp_one_iff_integrable]
      exact hDelta_L2.mul' hBs_L2
    have hDeltaInt : Integrable (brownian t - brownian s) gaussianLimit :=
      (isGaussianProcess_brownian.hasGaussianLaw_fun_sub (s := t) (t := s)).integrable
    have hProdCondZero :
        gaussianLimit[fun ω => brownian s ω * (brownian t ω - brownian s ω) |
            brownianNaturalFiltration s] =ᵐ[gaussianLimit] fun _ => 0 := by
      have hpull := condExp_mul_of_stronglyMeasurable_left hBs_sm hProdInt
        hDeltaInt
      have hpull' :
          gaussianLimit[fun ω => brownian s ω * (brownian t ω - brownian s ω) |
              brownianNaturalFiltration s]
            =ᵐ[gaussianLimit]
              brownian s * gaussianLimit[fun ω => brownian t ω - brownian s ω |
                brownianNaturalFiltration s] := by
        simpa [Pi.mul_apply] using hpull
      filter_upwards [hpull', hDeltaCondZero] with ω hpullω hzeroω
      have hzeroω' :
          (gaussianLimit[fun ω => brownian t ω - brownian s ω |
            brownianNaturalFiltration s]) ω = 0 := by
        simpa [Pi.sub_apply] using hzeroω
      rw [hpullω]
      simp [Pi.mul_apply, hzeroω']
    have hTwoProdInt :
        Integrable (fun ω => (2 : ℝ) * (brownian s ω * (brownian t ω - brownian s ω)))
          gaussianLimit := by
      simpa [Pi.smul_apply, smul_eq_mul] using hProdInt.const_mul (2 : ℝ)
    have hTwoProdCondZero :
        gaussianLimit[fun ω => (2 : ℝ) * (brownian s ω * (brownian t ω - brownian s ω)) |
            brownianNaturalFiltration s] =ᵐ[gaussianLimit] fun _ => 0 := by
      have hsmul := condExp_smul (μ := gaussianLimit) (c := (2 : ℝ))
        (f := fun ω => brownian s ω * (brownian t ω - brownian s ω))
        (m := brownianNaturalFiltration s)
      have hsmul' :
          gaussianLimit[fun ω => (2 : ℝ) *
              (brownian s ω * (brownian t ω - brownian s ω)) |
              brownianNaturalFiltration s]
            =ᵐ[gaussianLimit]
              (2 : ℝ) • gaussianLimit[fun ω => brownian s ω *
                (brownian t ω - brownian s ω) | brownianNaturalFiltration s] := by
        simpa [Pi.smul_apply, smul_eq_mul] using hsmul
      filter_upwards [hsmul', hProdCondZero] with ω hsmulω hzeroω
      rw [hsmulω]
      simp [Pi.smul_apply, hzeroω]
    have hCenterInt :
        Integrable (fun ω => (brownian t ω - brownian s ω) ^ 2 - (t - s : ℝ≥0))
          gaussianLimit :=
      hDelta_L2.integrable_sq.sub (integrable_const ((t - s : ℝ≥0) : ℝ))
    have hCenterIndep : Indep
        (MeasurableSpace.comap
          (fun ω => (brownian t ω - brownian s ω) ^ 2 - (t - s : ℝ≥0)) inferInstance)
        (brownianNaturalFiltration s) gaussianLimit := by
      refine indep_of_indep_of_le_left
        (IsFilteredPreBrownian.indep (X := brownian) (𝓕 := brownianNaturalFiltration)
          (P := gaussianLimit) s t hst) ?_
      have hcomp :
          (fun ω => (brownian t ω - brownian s ω) ^ 2 - (t - s : ℝ≥0)) =
            (fun x : ℝ => x ^ 2 - (t - s : ℝ≥0)) ∘ (brownian t - brownian s) := rfl
      rw [hcomp, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (Measurable.comap_le (by fun_prop))
    have hCenterNoCond :
        gaussianLimit[fun ω => (brownian t ω - brownian s ω) ^ 2 - (t - s : ℝ≥0) |
            brownianNaturalFiltration s]
          =ᵐ[gaussianLimit]
            fun _ => ∫ ω, (brownian t ω - brownian s ω) ^ 2 - (t - s : ℝ≥0)
              ∂gaussianLimit := by
      refine condExp_indep_eq ?_ (brownianNaturalFiltration.le s) ?_ hCenterIndep
      · exact Measurable.comap_le
          (((Measurable.sub (hM t) (hM s)).pow_const 2).sub measurable_const)
      · exact (comap_measurable
          (fun ω => (brownian t ω - brownian s ω) ^ 2 - (t - s : ℝ≥0))).stronglyMeasurable
    have hCenterIntegralZero :
        ∫ ω, (brownian t ω - brownian s ω) ^ 2 - (t - s : ℝ≥0) ∂gaussianLimit = 0 := by
      change ∫ ω, (brownian t - brownian s) ω ^ 2 - ((t - s : ℝ≥0) : ℝ)
        ∂gaussianLimit = 0
      rw [integral_sub hDelta_L2.integrable_sq
        (integrable_const ((t - s : ℝ≥0) : ℝ)), hDeltaSqIntegral, integral_const]
      simp [smul_eq_mul]
    have hCenterCondZero :
        gaussianLimit[fun ω => (brownian t ω - brownian s ω) ^ 2 - (t - s : ℝ≥0) |
            brownianNaturalFiltration s] =ᵐ[gaussianLimit] fun _ => 0 :=
      hCenterNoCond.trans (ae_of_all _ fun _ => hCenterIntegralZero)
    let twoProd : (ℝ≥0 → ℝ) → ℝ :=
      fun ω => (2 : ℝ) * (brownian s ω * (brownian t ω - brownian s ω))
    let center : (ℝ≥0 → ℝ) → ℝ :=
      fun ω => (brownian t ω - brownian s ω) ^ 2 - (t - s : ℝ≥0)
    let rest : (ℝ≥0 → ℝ) → ℝ := fun ω => twoProd ω + center ω
    let past : (ℝ≥0 → ℝ) → ℝ := fun ω => brownian s ω ^ 2 - (s : ℝ)
    have hTwoProdInt' : Integrable twoProd gaussianLimit := by
      dsimp only [twoProd]
      exact hTwoProdInt
    have hCenterInt' : Integrable center gaussianLimit := by
      dsimp only [center]
      exact hCenterInt
    have hTwoProdCondZero' :
        gaussianLimit[twoProd | brownianNaturalFiltration s]
          =ᵐ[gaussianLimit] fun _ => 0 := by
      dsimp only [twoProd]
      exact hTwoProdCondZero
    have hCenterCondZero' :
        gaussianLimit[center | brownianNaturalFiltration s]
          =ᵐ[gaussianLimit] fun _ => 0 := by
      dsimp only [center]
      exact hCenterCondZero
    have hRestInt : Integrable rest gaussianLimit := by
      dsimp only [rest]
      exact hTwoProdInt'.add hCenterInt'
    have hRestCondZero : gaussianLimit[rest | brownianNaturalFiltration s]
        =ᵐ[gaussianLimit] fun _ => 0 := by
      dsimp only [rest]
      calc
        gaussianLimit[fun ω => twoProd ω + center ω | brownianNaturalFiltration s]
            =ᵐ[gaussianLimit]
              gaussianLimit[twoProd | brownianNaturalFiltration s] +
              gaussianLimit[center | brownianNaturalFiltration s] :=
          condExp_add hTwoProdInt' hCenterInt' _
        _ =ᵐ[gaussianLimit] fun _ => 0 := by
          filter_upwards [hTwoProdCondZero', hCenterCondZero'] with ω htwo hcenter
          rw [Pi.add_apply, htwo, hcenter]
          simp
    have hPastInt : Integrable past gaussianLimit := by
      dsimp only [past]
      exact hBs_L2.integrable_sq.sub (integrable_const (s : ℝ))
    have hPastSm : StronglyMeasurable[brownianNaturalFiltration s] past := by
      dsimp only [past]
      simpa only [pow_two] using (hBs_sm.mul hBs_sm).sub stronglyMeasurable_const
    have hExpand :
        (fun omega => brownian t omega ^ 2 - (t : ℝ)) = fun omega => past omega + rest omega := by
      funext omega
      dsimp only [past, rest, twoProd, center]
      have htime : (t : ℝ) = (s : ℝ) + ((t - s : ℝ≥0) : ℝ) := by
        rw [← NNReal.coe_add, add_tsub_cancel_of_le hst]
      rw [htime]
      ring
    calc
      gaussianLimit[fun omega => brownian t omega ^ 2 - (t : ℝ) | brownianNaturalFiltration s]
          = gaussianLimit[fun omega => past omega + rest omega | brownianNaturalFiltration s] := by
        rw [hExpand]
      _ =ᵐ[gaussianLimit]
          gaussianLimit[past | brownianNaturalFiltration s] +
            gaussianLimit[rest | brownianNaturalFiltration s] :=
        condExp_add hPastInt hRestInt _
      _ =ᵐ[gaussianLimit] past + (fun _ => 0) :=
        by
          rw [condExp_of_stronglyMeasurable (brownianNaturalFiltration.le s) hPastSm hPastInt]
          filter_upwards [hRestCondZero] with omega hrest
          rw [Pi.add_apply, hrest]
          simp
      _ =ᵐ[gaussianLimit] (fun omega => brownian s omega ^ 2 - (s : ℝ)) := by
        filter_upwards with omega
        dsimp only [past]
        simp

/-- The deterministic time process `A_t = t`, used as the predictable Brownian quadratic
variation candidate. -/
noncomputable abbrev brownianDeterministicTime :
    ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  fun t _ => (t : ℝ)

/-- Brownian square minus deterministic time has càdlàg paths. -/
lemma isCadlag_brownian_sq_sub_time (ω : ℝ≥0 → ℝ) :
    IsCadlag (fun t : ℝ≥0 => brownian t ω ^ 2 - (t : ℝ)) := by
  have hsq : IsCadlag (fun t : ℝ≥0 => brownian t ω ^ 2) := by
    have hpow : Continuous fun x : ℝ => x ^ 2 := by fun_prop
    simpa [Function.comp_def] using (isCadlag_brownian ω).continuous_comp hpow
  have htime : IsCadlag (fun t : ℝ≥0 => (t : ℝ)) :=
    Continuous.isCadlag NNReal.continuous_coe
  have hneg : IsCadlag (fun t : ℝ≥0 => (-1 : ℝ) • (t : ℝ)) :=
    htime.const_smul (-1)
  have hadd : IsCadlag
      ((fun t : ℝ≥0 => brownian t ω ^ 2) +
        fun t : ℝ≥0 => (-1 : ℝ) • (t : ℝ)) :=
    hsq.add hneg
  simpa [sub_eq_add_neg, Pi.add_apply, smul_eq_mul] using hadd

/-- The deterministic time process is strongly adapted to the Brownian natural filtration. -/
lemma stronglyAdapted_brownianDeterministicTime :
    StronglyAdapted brownianNaturalFiltration brownianDeterministicTime := by
  intro t
  exact stronglyMeasurable_const

/-- The deterministic time process is strongly predictable. -/
lemma isStronglyPredictable_brownianDeterministicTime :
    IsStronglyPredictable brownianNaturalFiltration brownianDeterministicTime := by
  refine stronglyAdapted_brownianDeterministicTime.isStronglyPredictable_of_leftContinuous ?_
  intro ω a
  change ContinuousWithinAt (fun t : ℝ≥0 => (t : ℝ)) (Set.Iio a) a
  exact (NNReal.continuous_coe.continuousAt (x := a)).continuousWithinAt

/-- The deterministic time process is strongly progressive. -/
lemma isStronglyProgressive_brownianDeterministicTime :
    IsStronglyProgressive brownianNaturalFiltration brownianDeterministicTime := by
  refine stronglyAdapted_brownianDeterministicTime.isStronglyProgressive_of_rightContinuous ?_
  intro ω a
  change ContinuousWithinAt (fun t : ℝ≥0 => (t : ℝ)) (Set.Ioi a) a
  exact (NNReal.continuous_coe.continuousAt (x := a)).continuousWithinAt

/-- The deterministic time process has càdlàg paths. -/
lemma isCadlag_brownianDeterministicTime (ω : ℝ≥0 → ℝ) :
    IsCadlag (brownianDeterministicTime · ω) := by
  simpa [brownianDeterministicTime] using
    (Continuous.isCadlag (NNReal.continuous_coe : Continuous fun t : ℝ≥0 => (t : ℝ)))

/-- The deterministic time process is pathwise monotone. -/
lemma monotone_brownianDeterministicTime (ω : ℝ≥0 → ℝ) :
    Monotone (brownianDeterministicTime · ω) := by
  intro s t hst
  exact_mod_cast hst

/-- The deterministic time process starts from zero. -/
lemma brownianDeterministicTime_bot_eq_zero (ω : ℝ≥0 → ℝ) :
    brownianDeterministicTime ⊥ ω = 0 := by
  simp [brownianDeterministicTime]

section DeterministicTimeUsualConditions

variable [brownianNaturalFiltration.IsComplete gaussianLimit]
variable [brownianNaturalFiltration.IsRightContinuous]

/-- The deterministic time process has integrable running supremum on every deterministic
time interval. -/
lemma hasIntegrableSup_brownianDeterministicTime :
    HasIntegrableSup brownianDeterministicTime gaussianLimit := by
  have hsup_meas : HasStronglyMeasurableSupProcess brownianDeterministicTime :=
    MeasureTheory.IsStronglyProgressive.hasStronglyMeasurableSupProcess
      (𝓕 := brownianNaturalFiltration) gaussianLimit
      isStronglyProgressive_brownianDeterministicTime
  refine ⟨hsup_meas, fun t => ?_⟩
  refine Integrable.of_mem_Icc_enorm (a := 0) (b := ‖(t : ℝ)‖ₑ) ?_ enorm_ne_top
    (hsup_meas.comp_measurable (measurable_const.prodMk measurable_id)).aemeasurable ?_
  · simp
  · filter_upwards with ω
    have hle : (⨆ s ≤ t, ‖brownianDeterministicTime s ω‖ₑ) ≤ ‖(t : ℝ)‖ₑ := by
      refine iSup₂_le fun s hs => ?_
      simp only [brownianDeterministicTime]
      rw [Real.enorm_of_nonneg (NNReal.coe_nonneg s),
        Real.enorm_of_nonneg (NNReal.coe_nonneg t)]
      exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hs)
    exact ⟨bot_le, hle⟩

/-- The deterministic time process has locally integrable running supremum. -/
lemma hasLocallyIntegrableSup_brownianDeterministicTime :
    HasLocallyIntegrableSup brownianDeterministicTime brownianNaturalFiltration gaussianLimit := by
  simpa [HasLocallyIntegrableSup] using
    (Locally.of_prop (𝓕 := brownianNaturalFiltration) (P := gaussianLimit)
      (p := fun X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ => HasIntegrableSup X gaussianLimit)
      hasIntegrableSup_brownianDeterministicTime)

end DeterministicTimeUsualConditions

/-- The canonical Brownian motion is a local martingale with respect to its natural filtration. -/
lemma isLocalMartingale_brownian :
    IsLocalMartingale brownian brownianNaturalFiltration gaussianLimit :=
  Martingale.IsLocalMartingale martingale_brownian isCadlag_brownian

section UsualConditions

variable [brownianNaturalFiltration.IsComplete gaussianLimit]
variable [brownianNaturalFiltration.IsRightContinuous]

/-- The quadratic variation process attached to the canonical Brownian motion. -/
noncomputable abbrev brownianQuadraticVariation : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  letI : Approximable brownianNaturalFiltration gaussianLimit :=
    brownianNaturalFiltration_approximable
  quadraticVariation isLocalMartingale_brownian isCadlag_brownian

/-- At each deterministic time, the Brownian quadratic variation is almost surely `t`. -/
theorem quadraticVariation_brownian (t : ℝ≥0) :
    brownianQuadraticVariation t =ᵐ[gaussianLimit] fun _ => (t : ℝ) := by
  letI : Approximable brownianNaturalFiltration gaussianLimit :=
    brownianNaturalFiltration_approximable
  let X2 : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun s ω => ‖brownian s ω‖ ^ 2
  have hX2_cadlag : ∀ ω, IsCadlag (X2 · ω) := by
    intro ω
    simpa [X2, Function.comp_def] using
      ((isCadlag_brownian ω).continuous_comp (continuous_norm.pow 2))
  have hX_sub : IsLocalSubmartingale X2 brownianNaturalFiltration gaussianLimit := by
    simpa [X2] using
      (isLocalMartingale_brownian.isLocalSubmartingale_sq_norm isCadlag_brownian)
  let M : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun s ω => brownian s ω ^ 2 - (s : ℝ)
  have hM : IsLocalMartingale M brownianNaturalFiltration gaussianLimit := by
    simpa [M] using
      (Martingale.IsLocalMartingale martingale_brownian_sq_sub_time
        isCadlag_brownian_sq_sub_time)
  have hM_cadlag : ∀ ω, IsCadlag (M · ω) := by
    intro ω
    simpa [M, Function.comp_def] using isCadlag_brownian_sq_sub_time ω
  have hX_decomp : X2 = M + brownianDeterministicTime := by
    ext s ω
    simp only [X2, M, Pi.add_apply, brownianDeterministicTime]
    rw [Real.norm_eq_abs, sq_abs]
    ring
  have hcompare :
      hX_sub.predictablePart X2 hX2_cadlag t =ᵐ[gaussianLimit]
        brownianDeterministicTime t :=
    hX_sub.predictablePart_eq_of_normalized_decomposition hX2_cadlag hX_decomp hM
      hM_cadlag isStronglyPredictable_brownianDeterministicTime
      isStronglyProgressive_brownianDeterministicTime isCadlag_brownianDeterministicTime
      hasLocallyIntegrableSup_brownianDeterministicTime monotone_brownianDeterministicTime
      brownianDeterministicTime_bot_eq_zero t
  simpa [brownianQuadraticVariation, quadraticVariation, X2,
    brownianDeterministicTime] using hcompare

end UsualConditions

end ProbabilityTheory
