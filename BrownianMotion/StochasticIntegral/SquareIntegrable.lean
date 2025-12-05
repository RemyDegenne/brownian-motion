/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Martingale
import BrownianMotion.StochasticIntegral.ApproxSeq
import BrownianMotion.StochasticIntegral.Locally
import BrownianMotion.Auxiliary.Adapted
import BrownianMotion.StochasticIntegral.OptionalSampling
import Mathlib.Probability.Process.HittingTime

/-! # Square integrable martingales

-/

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

/-- A square integrable martingale is a martingale with cadlag paths and uniformly bounded
second moments. -/
structure IsSquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop where
  martingale : Martingale X 𝓕 P
  cadlag : ∀ ω, IsCadlag (X · ω)
  bounded : ⨆ i, eLpNorm (X i) 2 P < ∞

lemma IsSquareIntegrable.integrable_sq (hX : IsSquareIntegrable X 𝓕 P) (i : ι) :
    Integrable (fun ω ↦ ‖X i ω‖ ^ 2) P := by
  constructor
  · have hX_meas := (hX.martingale.adapted i).mono (𝓕.le i)
    fun_prop
  · have hX_bound : eLpNorm (X i) 2 P < ∞ := by
      calc eLpNorm (X i) 2 P
      _ ≤ ⨆ j, eLpNorm (X j) 2 P := le_iSup (fun j ↦ eLpNorm (X j) 2 P) i
      _ < ∞ := hX.bounded
    simpa [HasFiniteIntegral, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top] using hX_bound

lemma IsSquareIntegrable.add (hX : IsSquareIntegrable X 𝓕 P)
    (hY : IsSquareIntegrable Y 𝓕 P) :
    IsSquareIntegrable (fun i ω ↦ X i ω + Y i ω) 𝓕 P := by
  refine ⟨hX.martingale.add hY.martingale, fun ω ↦ ?_, ?_⟩
  · sorry
  · have hX_bound : ⨆ i, eLpNorm (X i) 2 P < ∞ := hX.bounded
    have hY_bound : ⨆ i, eLpNorm (Y i) 2 P < ∞ := hY.bounded
    calc ⨆ i, eLpNorm (fun ω ↦ X i ω + Y i ω) 2 P
        ≤ ⨆ i, (eLpNorm (X i) 2 P + eLpNorm (Y i) 2 P) := by
          refine iSup_mono fun i ↦ ?_
          exact eLpNorm_add_le ((hX.martingale.adapted i).mono (𝓕.le i)).aestronglyMeasurable
            ((hY.martingale.adapted i).mono (𝓕.le i)).aestronglyMeasurable (by simp)
      _ ≤ (⨆ i, eLpNorm (X i) 2 P) + ⨆ i, eLpNorm (Y i) 2 P := by
          sorry
      _ < ∞ := ENNReal.add_lt_top.mpr ⟨hX_bound, hY_bound⟩

lemma IsSquareIntegrable.submartingale_sq_norm (hX : IsSquareIntegrable X 𝓕 P) :
    Submartingale (fun i ω ↦ ‖X i ω‖ ^ 2) 𝓕 P := by
  sorry
open Filter

lemma IsSquareIntegrable.eLpNorm_mono [IsFiniteMeasure P] (hX : IsSquareIntegrable X 𝓕 P)
    {i j : ι} (hij : i ≤ j) : eLpNorm (X i) 2 P ≤ eLpNorm (X j) 2 P := by
  have hX2 := IsSquareIntegrable.submartingale_sq_norm hX
  rw [← ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)]
  rw [(by rfl : ((2 : ℝ) = ((2 : NNReal): ℝ))) ]
  change eLpNorm (X i) (2 : NNReal) P ^ ((2 : NNReal) : ℝ) ≤
      eLpNorm (X j) (2 : NNReal) P ^ ((2 : NNReal) : ℝ)
  rw [eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero]
  rw [eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero]
  have h_int : ∀ k, Integrable ((‖X · ·‖ ^ 2) k) P := hX2.2.2
  have h_meas := fun k ↦ (h_int k).1
  have lintegral_sq_eq_ofReal_integral : ∀ k,
      ∫⁻ a, ‖X k a‖ₑ ^ (2 : ℝ) ∂P = ENNReal.ofReal (∫ a, (‖X · ·‖ ^ 2) k a ∂P) := by
    intro k
    have h_eq : ∀ᵐ a ∂P, ‖X k a‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ((‖X · ·‖ ^ 2) k a) := by
      filter_upwards with a
      simp
    rw [lintegral_congr_ae h_eq]
    rw [integral_eq_lintegral_of_nonneg_ae _ (h_int k).aestronglyMeasurable]
    · rw [ENNReal.ofReal_toReal]
      refine (lintegral_ofReal_ne_top_iff_integrable (h_meas k) ?_).mpr (h_int k)
      filter_upwards with x
      simp
    filter_upwards
    simp
  norm_cast
  rw [lintegral_sq_eq_ofReal_integral i, lintegral_sq_eq_ofReal_integral j]
  apply ENNReal.ofReal_le_ofReal
  have h_submart : (‖X · ·‖ ^ 2) i ≤ᵐ[P] P[(‖X · ·‖ ^ 2) j | 𝓕 i] := hX2.2.1 i j hij
  calc ∫ ω, (‖X · ·‖ ^ 2) i ω ∂P
    _ ≤ ∫ ω, (P[(‖X · ·‖ ^ 2) j | 𝓕 i]) ω ∂P := by
        apply integral_mono_ae (h_int i) (integrable_condExp) h_submart
    _ = ∫ ω, (‖X · ·‖ ^ 2) j ω ∂P := integral_condExp _

end ProbabilityTheory
