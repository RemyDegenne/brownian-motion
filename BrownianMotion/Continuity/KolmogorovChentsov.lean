/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Continuity.HasBoundedInternalCoveringNumber
import BrownianMotion.Continuity.IsKolmogorovProcess

/-!
# Kolmogorov-Chentsov theorem

-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {T Ω E : Type*} [EMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  {X : T → Ω → E}
  {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0}
  {P : Measure Ω}

lemma lintegral_div_edist_le_sum_integral_edist_le (hT : EMetric.diam (Set.univ : Set T) < ∞)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hβ_pos : 0 < β) (hp_pos : 0 < p) {J : Set T} (hJ : Countable J) :
    ∫⁻ ω, ⨆ (s : J) (t : J), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ ∑' (k : ℕ), 2 ^ (k * β * p)
          * ∫⁻ ω, ⨆ (s : J) (t : J)
            (_he : edist s t ≤ 2 * 2⁻¹ ^ k * (EMetric.diam (.univ : Set T) + 1)),
            edist (X s ω) (X t ω) ^p ∂P := by
  let η k := 2⁻¹ ^ k * (EMetric.diam (Set.univ : Set T) + 1)
  have hη_ge (k : ℕ) : 2⁻¹ ^ (k : ℝ) ≤ η k := by simp [η, mul_add]
  have hη_succ (k : ℕ) : η (k + 1) = 2⁻¹ * η k := by simp [η, pow_add, mul_assoc, mul_comm]
  have hη_lim : Filter.Tendsto η Filter.atTop (nhds 0) := by
    unfold η
    rw [← zero_mul (EMetric.diam (Set.univ : Set T) + 1)]
    apply ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
    simp [← lt_top_iff_ne_top, hT]
  conv in 2 ^ _ * _ => rw [← lintegral_const_mul' _ _ (by simp)]
  rw [← lintegral_tsum (by fun_prop)]
  refine lintegral_mono (fun ω ↦ ?_)
  rw [iSup_le_iff]; rintro ⟨s, hs⟩
  rw [iSup_le_iff]; intro ⟨t, ht⟩
  wlog hst : s ≠ t
  · simp [not_ne_iff.mp hst, edist_self, ge_iff_le, ENNReal.zero_rpow_of_pos (by positivity)]
  obtain ⟨k, lb, ub⟩ : ∃ k, (η k ≤ edist s t) ∧ (edist s t ≤ 2 * η k) := by
    have hη_dist : ∃ k, η k ≤ edist s t :=
      (Filter.Eventually.exists (Filter.Tendsto.eventually_le_const (edist_pos.mpr hst) hη_lim))
    refine ⟨Nat.find hη_dist, Nat.find_spec hη_dist, ?_⟩
    match hk : Nat.find hη_dist with
    | 0 =>
        apply le_trans (EMetric.edist_le_diam_of_mem (Set.mem_univ _) (Set.mem_univ _))
        simp [η]
        exact le_mul_of_one_le_of_le (by norm_num) (le_add_right (le_refl _))
    | k + 1 =>
        rw [hη_succ k, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        refine le_of_not_ge (Nat.find_min hη_dist ?_)
        simp [hk]
  refine le_trans ?_ (Summable.le_tsum (ENNReal.summable) k (fun _ _ ↦ zero_le _))
  rw [ENNReal.div_eq_inv_mul]
  refine mul_le_mul ?_ ?_ (zero_le _) (zero_le _)
  · rw [ENNReal.inv_le_iff_inv_le, ← ENNReal.inv_rpow, mul_assoc, ENNReal.rpow_mul,
      ENNReal.rpow_le_rpow_iff (by positivity)]
    exact le_trans (hη_ge k) lb
  apply le_trans
  · apply le_iSup (fun (_ :edist s t ≤ 2 * 2⁻¹ ^ k * (EMetric.diam (.univ : Set T) + 1))
      ↦ edist (X s ω) (X t ω) ^ p)
    rwa [mul_assoc]
  apply le_iSup_of_le (i := ⟨s, hs⟩)
  apply le_iSup_of_le (i := ⟨t, ht⟩)
  exact le_refl _

noncomputable
-- the `max 0 ...` in the blueprint is performed by `ENNReal.ofReal` here
def constL (T : Type*) [PseudoEMetricSpace T] (c : ℝ≥0∞) (d p q β : ℝ) : ℝ≥0∞ :=
  4 ^ (p + 2 * q + 1) * c * (EMetric.diam (.univ : Set T) + 1) ^ (q - d)
  * ∑' k, 2 ^ (k * β * p + (-k + 1) * (q - d))
      * (4 ^ d * (ENNReal.ofReal (Real.logb 2 c.toReal + (k + 1) * d)) ^ q
        + Cp d p q)

lemma constL_lt_top (hc : c ≠ ∞) (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    constL T c d p q β < ∞ := by
  sorry

theorem finite_kolmogorov_chentsov (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    (T' : Set T) (hT' : T'.Finite) :
    ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^p / edist s t ^ (β * p) ∂P
      ≤ M * constL T c d p q β := by
  sorry

theorem countable_kolmogorov_chentsov (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    (T' : Set T) (hT' : T'.Countable) :
    ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ M * constL T c d p q β := by
  sorry

lemma exists_modification_holder_aux (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    ∃ Y : T → Ω → E, (∀ t, Y t =ᵐ[P] X t) ∧ ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  sorry

lemma exists_modification_holder (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p),
        ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  sorry

end ProbabilityTheory
