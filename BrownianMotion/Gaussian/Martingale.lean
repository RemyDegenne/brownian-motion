/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import BrownianMotion.Gaussian.BrownianMotion

/-!
# Martingale properties of Brownian motion

For a filtered pre-Brownian motion `X`, the following are martingales w.r.t. the filtration `𝓕`:

* `X` itself (already provided as `IsPreBrownian.isMartingale` in `Gaussian/BrownianMotion.lean`)
* `t ↦ (X t)² − t`
* `t ↦ exp(α X_t − α² t / 2)` (Wald exponential), for any `α : ℝ`

## Main results

* `IsFilteredPreBrownian.squareSubTime_isMartingale`
* `IsFilteredPreBrownian.waldExponential_isMartingale`
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- For `s ≤ t : ℝ≥0`, the NNReal-valued increment-variance `max (t-s) (s-t)`
coerces to `(t : ℝ) - (s : ℝ)` (since truncated `s - t = 0` when `s ≤ t`). -/
private lemma NNReal.max_sub_eq_of_le {s t : ℝ≥0} (hst : s ≤ t) :
    ((max (t - s) (s - t) : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) := by
  have hst_zero : s - t = (0 : ℝ≥0) := tsub_eq_zero_of_le hst
  rw [hst_zero, max_eq_left (zero_le _)]
  exact NNReal.coe_sub hst

/-- MGF specialization: for `α : ℝ` and `v : ℝ≥0`,
`∫ x, exp(α x) ∂(gaussianReal 0 v) = exp(α² v / 2)`. -/
private lemma integral_exp_mul_gaussianReal_zero (α : ℝ) (v : ℝ≥0) :
    ∫ x, Real.exp (α * x) ∂(gaussianReal 0 v) = Real.exp (α ^ 2 * (v : ℝ) / 2) := by
  have h := congr_fun (mgf_id_gaussianReal (μ := 0) (v := v)) α
  show mgf id (gaussianReal 0 v) α = _
  rw [h]
  ring_nf

/-- Second moment of a centered real Gaussian: `∫ x, x² ∂(gaussianReal 0 v) = v`. -/
private lemma integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have h_var : variance id (gaussianReal 0 v) = (v : ℝ) := variance_id_gaussianReal
  have h_mean : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  rw [variance_of_integral_eq_zero aemeasurable_id h_mean] at h_var
  exact h_var

namespace IsFilteredPreBrownian

variable [hX : IsFilteredPreBrownian X 𝓕 P] [IsFiniteMeasure P]

/-- For a filtered pre-Brownian motion `X`, the process `t ↦ (X t)² − t` is a martingale
w.r.t. `𝓕`.

Decomposition: `(X_t)² = (X_s)² + 2 X_s (X_t − X_s) + (X_t − X_s)²`. The first summand is
`𝓕_s`-measurable; the cross term has zero conditional expectation by pull-out + independence;
the squared increment has conditional expectation `t − s` (its variance). -/
theorem squareSubTime_isMartingale :
    Martingale (fun t ω ↦ (X t ω) ^ 2 - (t : ℝ)) 𝓕 P := by
  refine ⟨fun u ↦ ?_, fun s t hst ↦ ?_⟩
  -- Adaptedness of `(X u)² − u`.
  · have hB : StronglyMeasurable[𝓕 u] (X u) := hX.stronglyAdapted u
    have hsq : StronglyMeasurable[𝓕 u] (fun ω ↦ (X u ω) ^ 2) := by
      simpa [pow_two] using hB.mul hB
    exact hsq.sub stronglyMeasurable_const
  -- Conditional-expectation step.
  have h_int_s : Integrable (X s) P := hX.integrable_eval s
  have h_int_t : Integrable (X t) P := hX.integrable_eval t
  have h_int_diff : Integrable (fun ω ↦ X t ω - X s ω) P := h_int_t.sub h_int_s
  have h_meas_t : Measurable (X t) := ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (X s) := ((hX.stronglyAdapted s).mono (𝓕.le s)).measurable
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω) := h_meas_t.sub h_meas_s
  have h_eq_diff : (fun ω ↦ X t ω - X s ω) = (X t - X s : Ω → ℝ) := by funext; rfl
  -- HasLaws from `IsPreBrownian`.
  have hL_diff : HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    hX.hasLaw_sub t s
  have hL_s : HasLaw (X s) (gaussianReal 0 s) P := hX.hasLaw_eval s
  -- L² membership transferred via HasLaw + `memLp_id_gaussianReal`.
  have h_Bs_memLp : MemLp (X s) 2 P := by
    have h_id : MemLp (id : ℝ → ℝ) 2 (Measure.map (X s) P) := by
      rw [hL_s.map_eq]; exact memLp_id_gaussianReal 2
    exact h_id.comp_of_map h_meas_s.aemeasurable
  have h_diff_memLp : MemLp (fun ω ↦ X t ω - X s ω) 2 P := by
    rw [h_eq_diff]
    have h_id : MemLp (id : ℝ → ℝ) 2 (Measure.map (X t - X s) P) := by
      rw [hL_diff.map_eq]; exact memLp_id_gaussianReal 2
    refine h_id.comp_of_map ?_
    rw [← h_eq_diff]
    exact h_meas_diff.aemeasurable
  -- Integrabilities.
  have h_int_Bs_sq : Integrable (fun ω ↦ (X s ω) ^ 2) P := h_Bs_memLp.integrable_sq
  have h_int_diff_sq : Integrable (fun ω ↦ (X t ω - X s ω) ^ 2) P := h_diff_memLp.integrable_sq
  have h_int_cross : Integrable (fun ω ↦ X s ω * (X t ω - X s ω)) P := by
    have := h_Bs_memLp.integrable_mul h_diff_memLp
    simpa using this
  -- Mean of increment is 0.
  have h_int_diff_zero : ∫ ω, (X t ω - X s ω) ∂P = 0 := by
    rw [h_eq_diff, hL_diff.integral_eq, integral_id_gaussianReal]
  -- Variance of increment integral: ∫ (X_t − X_s)² ∂P = t − s.
  have h_int_diff_sq_zero : ∫ ω, (X t ω - X s ω) ^ 2 ∂P = (t : ℝ) - (s : ℝ) := by
    have h_change : ∫ ω, (X t ω - X s ω) ^ 2 ∂P
        = ∫ x, x ^ 2 ∂(gaussianReal 0 (max (t - s) (s - t))) := by
      have := hL_diff.integral_comp (f := fun x : ℝ ↦ x ^ 2)
        (by fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ x ^ 2)
          (gaussianReal 0 (max (t - s) (s - t))))
      simpa [Function.comp] using this
    rw [h_change, integral_sq_gaussianReal]
    exact NNReal.max_sub_eq_of_le hst
  -- `𝓕_s`-measurability of `X_s` and `(X_s)²`.
  have h_smeas_s : StronglyMeasurable[𝓕 s] (X s) := hX.stronglyAdapted s
  have h_smeas_s_sq : StronglyMeasurable[𝓕 s] (fun ω ↦ (X s ω) ^ 2) := by
    simpa [pow_two] using h_smeas_s.mul h_smeas_s
  -- `E[(X_s)² | 𝓕_s] = (X_s)²`.
  have h_condBs_sq :
      P[fun ω ↦ (X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)] = fun ω ↦ (X s ω) ^ 2 :=
    condExp_of_stronglyMeasurable (𝓕.le s) h_smeas_s_sq h_int_Bs_sq
  -- Independence machinery: align the user's `fun ω ↦ X t ω - X s ω` form with the
  -- pi-arithmetic `(X t - X s)` form Degenne uses in `IsFilteredPreBrownian.indep`.
  have h_indep : Indep (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)) (𝓕 s) P := by
    have := hX.indep s t hst
    convert this using 2
  have h_diff_meas_comap :
      Measurable[MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)]
        (fun ω ↦ X t ω - X s ω) :=
    fun s' hs' ↦ ⟨s', hs', rfl⟩
  have h_diff_smeas_comap :
      StronglyMeasurable[MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)]
        (fun ω ↦ X t ω - X s ω) :=
    h_diff_meas_comap.stronglyMeasurable
  have h_le_comap :
      MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ) ≤ mΩ := by
    rintro s' ⟨t', ht', rfl⟩
    exact h_meas_diff ht'
  -- `E[X_t − X_s | 𝓕_s] =ᵐ 0`.
  have h_condDiff :
      P[fun ω ↦ X t ω - X s ω | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    have := condExp_indep_eq h_le_comap (𝓕.le s) h_diff_smeas_comap h_indep
    rw [h_int_diff_zero] at this
    exact this
  -- `E[(X_t − X_s)² | 𝓕_s] =ᵐ (t − s)`.
  have h_diff_sq_meas_comap :
      Measurable[MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)]
        (fun ω ↦ (X t ω - X s ω) ^ 2) :=
    fun s' hs' ↦ ⟨(fun x : ℝ ↦ x ^ 2) ⁻¹' s',
      (continuous_id.pow 2).measurable hs', rfl⟩
  have h_diff_sq_smeas_comap :
      StronglyMeasurable[MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)]
        (fun ω ↦ (X t ω - X s ω) ^ 2) :=
    h_diff_sq_meas_comap.stronglyMeasurable
  have h_condDiffSq :
      P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] fun _ ↦ ((t : ℝ) - (s : ℝ)) := by
    have := condExp_indep_eq h_le_comap (𝓕.le s) h_diff_sq_smeas_comap h_indep
    rw [h_int_diff_sq_zero] at this
    exact this
  -- Pull-out for the cross term.
  have h_cross_eq :
      (fun ω ↦ X s ω * (X t ω - X s ω)) = (X s) * (fun ω ↦ X t ω - X s ω) := by funext ω; rfl
  have h_pullout :
      P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] (X s) * (P[fun ω ↦ X t ω - X s ω | (𝓕 s : MeasurableSpace Ω)]) := by
    rw [h_cross_eq]
    exact condExp_mul_of_stronglyMeasurable_left h_smeas_s
      (by simpa [h_cross_eq] using h_int_cross) h_int_diff
  have h_cond_cross :
      P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    refine h_pullout.trans ?_
    filter_upwards [h_condDiff] with ω hω
    change (X s) ω * (P[fun ω ↦ X t ω - X s ω | (𝓕 s : MeasurableSpace Ω)]) ω = (0 : ℝ)
    rw [hω]; simp
  -- Decomposition of the integrand.
  have h_decomp_ae :
      (fun ω ↦ (X t ω) ^ 2 - (t : ℝ)) =ᵐ[P] fun ω ↦
        ((X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))) +
          ((X t ω - X s ω) ^ 2 - (t : ℝ)) :=
    Filter.Eventually.of_forall fun ω ↦ by ring
  -- `condExp` respects ae-equality.
  have step1 :
      P[fun ω ↦ (X t ω) ^ 2 - (t : ℝ) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] P[fun ω ↦
          ((X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))) +
            ((X t ω - X s ω) ^ 2 - (t : ℝ)) | (𝓕 s : MeasurableSpace Ω)] :=
    condExp_congr_ae h_decomp_ae
  -- Outer linearity.
  have h_int_inner_left :
      Integrable (fun ω ↦ (X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))) P :=
    h_int_Bs_sq.add (h_int_cross.const_mul 2)
  have h_int_inner_right :
      Integrable (fun ω ↦ (X t ω - X s ω) ^ 2 - (t : ℝ)) P :=
    h_int_diff_sq.sub (integrable_const _)
  have step2 :
      P[fun ω ↦
          ((X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))) +
            ((X t ω - X s ω) ^ 2 - (t : ℝ)) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (P[fun ω ↦ (X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))
              | (𝓕 s : MeasurableSpace Ω)]) +
            (P[fun ω ↦ (X t ω - X s ω) ^ 2 - (t : ℝ) | (𝓕 s : MeasurableSpace Ω)]) :=
    condExp_add h_int_inner_left h_int_inner_right _
  -- Inner linearity. Use `(2 : ℝ) •` so `condExp_smul` applies.
  have h_eq_smul : (fun ω ↦ 2 * (X s ω * (X t ω - X s ω)))
                 = (2 : ℝ) • (fun ω ↦ X s ω * (X t ω - X s ω)) := by
    funext ω; simp [Pi.smul_apply, smul_eq_mul]
  have h_int_2cross : Integrable (fun ω ↦ 2 * (X s ω * (X t ω - X s ω))) P :=
    h_int_cross.const_mul 2
  have step3a :
      P[fun ω ↦ (X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))
          | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (P[fun ω ↦ (X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)]) +
            (P[fun ω ↦ 2 * (X s ω * (X t ω - X s ω)) | (𝓕 s : MeasurableSpace Ω)]) :=
    condExp_add h_int_Bs_sq h_int_2cross _
  have step3b :
      P[fun ω ↦ 2 * (X s ω * (X t ω - X s ω)) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] (2 : ℝ) • P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)] := by
    rw [h_eq_smul]; exact condExp_smul (2 : ℝ) _ _
  rw [h_condBs_sq] at step3a
  have step3 :
      P[fun ω ↦ (X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))
          | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (fun ω ↦ (X s ω) ^ 2) +
            (2 : ℝ) • (P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)]) := by
    filter_upwards [step3a, step3b] with ω h3a h3b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h3a h3b ⊢
    linarith
  -- Inner sub on the right.
  have step4 :
      P[fun ω ↦ (X t ω - X s ω) ^ 2 - (t : ℝ) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)]) -
            (fun _ ↦ (t : ℝ)) := by
    have h_const_int : Integrable (fun _ : Ω ↦ (t : ℝ)) P := integrable_const _
    have step4a :
        P[fun ω ↦ (X t ω - X s ω) ^ 2 - (t : ℝ) | (𝓕 s : MeasurableSpace Ω)]
          =ᵐ[P]
            (P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)]) -
              P[fun _ : Ω ↦ (t : ℝ) | (𝓕 s : MeasurableSpace Ω)] :=
      condExp_sub h_int_diff_sq h_const_int _
    have step4b :
        P[fun _ : Ω ↦ (t : ℝ) | (𝓕 s : MeasurableSpace Ω)] = fun _ ↦ (t : ℝ) :=
      condExp_const (𝓕.le s) (t : ℝ)
    filter_upwards [step4a] with ω h4a
    rw [h4a, step4b]
  -- Combine via `linear_combination`.
  filter_upwards [step1, step2, step3, step4, h_cond_cross, h_condDiffSq]
    with ω hs1 hs2 hs3 hs4 hcross hdiffsq
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hs2 hs3 hs4
  linear_combination hs1 + hs2 + hs3 + hs4 + 2 * hcross + hdiffsq

/-- **Wald exponential martingale.** For a filtered pre-Brownian motion `X` and `α : ℝ`,
the process `t ↦ exp(α X_t − α² t / 2)` is a martingale w.r.t. `𝓕`.

Decomposition: `α X_t − α²t/2 = (α X_s − α²s/2) + (α (X_t − X_s) − α²(t−s)/2)`. Setting
`M_s := exp(α X_s − α²s/2)` (which is `𝓕_s`-measurable) and
`D_{st} := exp(α (X_t − X_s) − α²(t−s)/2)` (which is independent of `𝓕_s`),
pointwise `M_t = M_s · D_{st}` and `E[D_{st}] = 1` (Gaussian MGF at `α`). Pull-out yields
`E[M_t | 𝓕_s] = M_s · E[D_{st} | 𝓕_s] = M_s`. -/
theorem waldExponential_isMartingale (α : ℝ) :
    Martingale (fun t ω ↦ Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2)) 𝓕 P := by
  refine ⟨fun u ↦ ?_, fun s t hst ↦ ?_⟩
  -- Adaptedness.
  · have hB : StronglyMeasurable[𝓕 u] (X u) := hX.stronglyAdapted u
    have hinner : StronglyMeasurable[𝓕 u]
        (fun ω ↦ α * X u ω - α ^ 2 * (u : ℝ) / 2) :=
      (hB.const_mul α).sub stronglyMeasurable_const
    exact Real.continuous_exp.comp_stronglyMeasurable hinner
  -- Conditional-expectation step.
  have h_meas_t : Measurable (X t) := ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (X s) := ((hX.stronglyAdapted s).mono (𝓕.le s)).measurable
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω) := h_meas_t.sub h_meas_s
  have h_eq_diff : (fun ω ↦ X t ω - X s ω) = (X t - X s : Ω → ℝ) := by funext; rfl
  have hL_diff : HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    hX.hasLaw_sub t s
  -- Integrability of `exp(α (X_t − X_s))`.
  have h_int_exp_diff : Integrable (fun ω ↦ Real.exp (α * (X t ω - X s ω))) P := by
    rw [show (fun ω ↦ Real.exp (α * (X t ω - X s ω)))
          = (fun x ↦ Real.exp (α * x)) ∘ (X t - X s) from by funext ω; rfl]
    refine Integrable.comp_aemeasurable ?_ h_meas_diff.aemeasurable
    rw [hL_diff.map_eq]
    exact integrable_exp_mul_gaussianReal α
  -- Mean of `exp(α (X_t − X_s))` (Gaussian MGF at `α`).
  have h_int_exp_diff_eq :
      ∫ ω, Real.exp (α * (X t ω - X s ω)) ∂P
        = Real.exp (α ^ 2 * ((max (t - s) (s - t) : ℝ≥0) : ℝ) / 2) := by
    have hf : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (α * x))
                (gaussianReal 0 (max (t - s) (s - t))) := by fun_prop
    have h := hL_diff.integral_comp hf
    have h_lhs : ((fun x ↦ Real.exp (α * x)) ∘ (X t - X s))
               = (fun ω ↦ Real.exp (α * (X t ω - X s ω))) := by funext ω; rfl
    rw [h_lhs, integral_exp_mul_gaussianReal_zero] at h
    exact h
  -- Define `M_s` (𝓕_s-measurable factor) and the increment exponential `D_{st}`.
  set Ms : Ω → ℝ := fun ω ↦ Real.exp (α * X s ω - α ^ 2 * (s : ℝ) / 2) with hMs_def
  set Dst : Ω → ℝ := fun ω ↦
    Real.exp (α * (X t ω - X s ω) - α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) with hDst_def
  have hMs_meas : StronglyMeasurable[𝓕 s] Ms := by
    have hB_s : StronglyMeasurable[𝓕 s] (X s) := hX.stronglyAdapted s
    have hinner_s : StronglyMeasurable[𝓕 s] (fun ω ↦ α * X s ω - α ^ 2 * (s : ℝ) / 2) :=
      (hB_s.const_mul α).sub stronglyMeasurable_const
    exact Real.continuous_exp.comp_stronglyMeasurable hinner_s
  -- Pointwise: `exp(α X_t − α²t/2) = M_s · D_{st}`.
  have h_decomp : ∀ ω, Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2) = Ms ω * Dst ω := by
    intro ω
    change _ = Real.exp _ * Real.exp _
    rw [← Real.exp_add]
    congr 1
    ring
  -- Integrability of `D_{st}`.
  have h_int_Dst : Integrable Dst P := by
    have h_eq : Dst = (fun ω ↦ Real.exp (-(α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2))
                                 * Real.exp (α * (X t ω - X s ω))) := by
      funext ω
      change Real.exp _ = _ * Real.exp _
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h_eq]
    exact h_int_exp_diff.const_mul _
  -- Mean of `D_{st}` is 1.
  have h_int_Dst_eq_one : ∫ ω, Dst ω ∂P = 1 := by
    have h_eq : Dst = (fun ω ↦ Real.exp (-(α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2))
                                 * Real.exp (α * (X t ω - X s ω))) := by
      funext ω
      change Real.exp _ = _ * Real.exp _
      rw [← Real.exp_add]; congr 1; ring
    rw [h_eq, integral_const_mul, h_int_exp_diff_eq, NNReal.max_sub_eq_of_le hst,
        ← Real.exp_add]
    rw [show -(α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) + α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2 = 0
        from by ring, Real.exp_zero]
  -- Independence: `D_{st}` is a function of `(X_t − X_s)`, which is independent of `𝓕_s`.
  have h_indep : Indep (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)) (𝓕 s) P := by
    have := hX.indep s t hst
    convert this using 2
  have h_le_comap :
      MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ) ≤ mΩ := by
    rintro s' ⟨t', ht', rfl⟩; exact h_meas_diff ht'
  have h_Dst_meas_comap :
      Measurable[MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)] Dst := by
    have h_phi : Continuous fun x : ℝ ↦
        Real.exp (α * x - α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) :=
      Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub continuous_const)
    intro s' hs'
    exact ⟨_, h_phi.measurable hs', rfl⟩
  have h_Dst_smeas_comap :
      StronglyMeasurable[MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)] Dst :=
    h_Dst_meas_comap.stronglyMeasurable
  have h_condDst : P[Dst | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (1 : ℝ) := by
    have := condExp_indep_eq h_le_comap (𝓕.le s) h_Dst_smeas_comap h_indep
    rw [h_int_Dst_eq_one] at this
    exact this
  -- Pull-out: `E[M_s · D_{st} | 𝓕_s] =ᵐ M_s · E[D_{st} | 𝓕_s] =ᵐ M_s · 1 = M_s`.
  have h_int_Ms : Integrable Ms P := by
    have h_eq : Ms = (fun ω ↦ Real.exp (-(α ^ 2 * (s : ℝ) / 2))
                                * Real.exp (α * X s ω)) := by
      funext ω
      change Real.exp _ = _ * Real.exp _
      rw [← Real.exp_add]; congr 1; ring
    rw [h_eq]
    refine Integrable.const_mul ?_ _
    have hL_s : HasLaw (X s) (gaussianReal 0 s) P := hX.hasLaw_eval s
    rw [show (fun ω ↦ Real.exp (α * X s ω))
          = (fun x ↦ Real.exp (α * x)) ∘ (X s) from by funext ω; rfl]
    refine Integrable.comp_aemeasurable ?_ h_meas_s.aemeasurable
    rw [hL_s.map_eq]
    exact integrable_exp_mul_gaussianReal α
  have h_int_MsDst : Integrable (fun ω ↦ Ms ω * Dst ω) P := by
    have h_decomp_fun : (fun ω ↦ Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2))
                      = (fun ω ↦ Ms ω * Dst ω) := funext h_decomp
    rw [← h_decomp_fun]
    have h_eq : (fun ω ↦ Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2))
              = (fun ω ↦ Real.exp (-(α ^ 2 * (t : ℝ) / 2)) * Real.exp (α * X t ω)) := by
      funext ω
      change Real.exp _ = _ * Real.exp _
      rw [← Real.exp_add]; congr 1; ring
    rw [h_eq]
    refine Integrable.const_mul ?_ _
    have hL_t : HasLaw (X t) (gaussianReal 0 t) P := hX.hasLaw_eval t
    rw [show (fun ω ↦ Real.exp (α * X t ω))
          = (fun x ↦ Real.exp (α * x)) ∘ (X t) from by funext ω; rfl]
    refine Integrable.comp_aemeasurable ?_ h_meas_t.aemeasurable
    rw [hL_t.map_eq]
    exact integrable_exp_mul_gaussianReal α
  have h_pullout :
      P[fun ω ↦ Ms ω * Dst ω | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] Ms * (P[Dst | (𝓕 s : MeasurableSpace Ω)]) := by
    have h_eq : (fun ω ↦ Ms ω * Dst ω) = Ms * Dst := by funext ω; rfl
    rw [h_eq]
    exact condExp_mul_of_stronglyMeasurable_left hMs_meas
      (by rw [← h_eq]; exact h_int_MsDst) h_int_Dst
  have h_decomp_ae :
      (fun u ↦ Real.exp (α * X t u - α ^ 2 * (t : ℝ) / 2)) =ᵐ[P] fun ω ↦ Ms ω * Dst ω :=
    Filter.Eventually.of_forall h_decomp
  refine (condExp_congr_ae h_decomp_ae).trans ?_
  refine h_pullout.trans ?_
  filter_upwards [h_condDst] with ω hω
  change (Ms * P[Dst | (𝓕 s : MeasurableSpace Ω)]) ω = Ms ω
  simp [Pi.mul_apply, hω]

end IsFilteredPreBrownian

end ProbabilityTheory
