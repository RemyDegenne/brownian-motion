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
  refine ⟨hX.martingale.add hY.martingale, fun ω ↦ ⟨fun i => ?_, fun i => ?_⟩, ?_⟩
  · exact ContinuousWithinAt.add ((hX.2 ω).1 i) ((hY.2 ω).1 i)
  · obtain ⟨r, hr⟩ := (hX.2 ω).2 i
    obtain ⟨s, hs⟩ := (hY.2 ω).2 i
    exact ⟨r + s, Tendsto.add hr hs⟩
  · have hX_bound : ⨆ i, eLpNorm (X i) 2 P < ∞ := hX.bounded
    have hY_bound : ⨆ i, eLpNorm (Y i) 2 P < ∞ := hY.bounded
    calc ⨆ i, eLpNorm (fun ω ↦ X i ω + Y i ω) 2 P
        ≤ ⨆ i, (eLpNorm (X i) 2 P + eLpNorm (Y i) 2 P) := by
          refine iSup_mono fun i ↦ ?_
          exact eLpNorm_add_le ((hX.martingale.adapted i).mono (𝓕.le i)).aestronglyMeasurable
            ((hY.martingale.adapted i).mono (𝓕.le i)).aestronglyMeasurable (by simp)
      _ ≤ (⨆ i, eLpNorm (X i) 2 P) + ⨆ i, eLpNorm (Y i) 2 P := by
          refine iSup_le fun i => ?_
          gcongr
          · exact le_iSup (fun i => eLpNorm (X i) 2 P) i
          · exact le_iSup (fun i => eLpNorm (Y i) 2 P) i
      _ < ∞ := ENNReal.add_lt_top.mpr ⟨hX_bound, hY_bound⟩

variable [SigmaFinite P]

lemma IsSquareIntegrable.submartingale_sq_norm (hX : IsSquareIntegrable X 𝓕 P) :
    Submartingale (fun i ω ↦ ‖X i ω‖ ^ 2) 𝓕 P := by
  refine hX.1.submartingale_convex_comp (φ := fun x => ‖x‖ ^ 2) ?_ (by fun_prop) fun i => ?_
  · have s : (fun x : E => ‖x‖)'' (Set.univ : Set E) ⊆ Set.Ici 0 := by intro; aesop
    have ic : Convex ℝ  ((fun x : E => ‖x‖)'' (Set.univ : Set E)) := by
      by_cases Nontrivial E
      · simp [convex_Ici]
      · refine Set.Subsingleton.convex (Set.Subsingleton.image ?_ fun x => ‖x‖)
        simp_all [not_nontrivial_iff_subsingleton]
    simpa using ((convexOn_rpow (p := 2) (by linarith)).subset s ic).comp convexOn_univ_norm
      ((Real.monotoneOn_rpow_Ici_of_exponent_nonneg (r := 2) (by linarith)).mono s)
  · refine MemLp.integrable_norm_pow ⟨?_, ?_⟩ (by linarith)
    · exact hX.1.1.stronglyMeasurable.aestronglyMeasurable
    · exact lt_of_le_of_lt (le_iSup (fun i => eLpNorm (X i) 2 P) i) hX.3

variable [SigmaFiniteFiltration P 𝓕]

lemma IsSquareIntegrable.eLpNorm_mono (hX : IsSquareIntegrable X 𝓕 P) {i j : ι} (hij : i ≤ j) :
    eLpNorm (X i) 2 P ≤ eLpNorm (X j) 2 P := by
  have : ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ ∫ ω, ‖X j ω‖ ^ 2 ∂P := by
    simpa using hXsub.setIntegral_le hij MeasurableSet.univ
  calc
  _ = (∫⁻ ω, ‖X i ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂P) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    simp [eLpNorm_eq_lintegral_rpow_enorm]
  _ = (ENNReal.ofReal (∫ ω, ‖X i ω‖ ^ 2 ∂P)) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    congr
    simpa using (ofReal_integral_norm_eq_lintegral_enorm (hX.integrable_sq i)).symm
  _ ≤ (ENNReal.ofReal (∫ ω, ‖X j ω‖ ^ 2 ∂P)) ^ (1 / (2 : ℝ≥0∞).toReal) := by gcongr
  _ = (∫⁻ ω, ‖X j ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂P) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    congr
    simpa using (ofReal_integral_norm_eq_lintegral_enorm (hX.integrable_sq j))
  _ = eLpNorm (X j) 2 P := by
    simp [eLpNorm_eq_lintegral_rpow_enorm]

end ProbabilityTheory
