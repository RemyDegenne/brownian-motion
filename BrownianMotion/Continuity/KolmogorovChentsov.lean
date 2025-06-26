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

section aux

theorem lintegral_eq_zero_of_zero_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} : f =ᵐ[μ] 0 →  ∫⁻ a, f a ∂μ = 0 :=
  fun h ↦ (lintegral_congr_ae h).trans lintegral_zero

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}

section PseudoEMetricSpace

variable [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]

lemma lintegral_div_edist_le_sum_integral_edist_le (hT : EMetric.diam (Set.univ : Set T) < ∞)
    (hX : IsKolmogorovProcess X P p q M)
    (hβ : 0 < β) (hp : 0 < p) (hq : 0 < q) {J : Set T} [hJ : Countable J] :
    ∫⁻ ω, ⨆ (s : J) (t : J), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ ∑' (k : ℕ), 2 ^ (k * β * p)
          * ∫⁻ ω, ⨆ (s : J)
              (t : {t : J // edist s t ≤ 2 * 2⁻¹ ^ k * (EMetric.diam (.univ : Set T) + 1)}),
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
  rw [← lintegral_tsum (by fun_prop (disch := exact hX))]
  have h_ae : ∀ᵐ (ω : Ω) ∂P, ∀ (s t : J), edist s t = 0 → edist (X s ω) (X t ω) = 0 := by
    rw [eventually_countable_forall]; intro s
    rw [eventually_countable_forall]; intro t
    by_cases h_dist : edist s t = 0
    · apply Filter.Eventually.mp (IsKolmogorovProcess.edist_eq_zero hX hp hq h_dist)
      filter_upwards with _ h _ using h
    filter_upwards with _ using by simp [h_dist]
  refine lintegral_mono_ae (Filter.Eventually.mp h_ae ?_)
  filter_upwards with ω h
  rw [iSup_le_iff]; rintro ⟨s, hs⟩
  rw [iSup_le_iff]; intro ⟨t, ht⟩
  wlog hst : 0 < edist s t
  · simp [(h ⟨s, hs⟩ ⟨t, ht⟩) <| nonpos_iff_eq_zero.mp (le_of_not_gt hst),
      ENNReal.zero_rpow_of_pos (by positivity)]
  obtain ⟨k, lb, ub⟩ : ∃ k, (η k ≤ edist s t) ∧ (edist s t ≤ 2 * η k) := by
    have hη_dist : ∃ k, η k ≤ edist s t :=
      (Filter.Eventually.exists (Filter.Tendsto.eventually_le_const hst hη_lim))
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
  apply le_iSup_of_le (i := ⟨s, hs⟩)
  exact le_iSup_of_le (i := ⟨⟨t, ht⟩, by rwa [mul_assoc]⟩) (le_refl _)

noncomputable
-- the `max 0 ...` in the blueprint is performed by `ENNReal.ofReal` here
def constL (T : Type*) [PseudoEMetricSpace T] (c : ℝ≥0∞) (d p q β : ℝ) : ℝ≥0∞ :=
  2 ^ (2 * p + 5 * q + 1) * c * (EMetric.diam (.univ : Set T) + 1) ^ (q - d)
  * ∑' (k : ℕ), 2 ^ (k * (β * p - (q - d)))
      * (4 ^ d * (ENNReal.ofReal (Real.logb 2 c.toReal + (k + 2) * d)) ^ q
        + Cp d p q)

lemma constL_lt_top (hc : c ≠ ∞) (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    constL T c d p q β < ∞ := by
  sorry

theorem finite_kolmogorov_chentsov
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) (T' : Set T) [hT' : Finite T'] :
    ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ M * constL T c d p q β := by
  have h_diam : EMetric.diam .univ < ∞ := hT.diam_lt_top hd_pos
  have hq_pos : 0 < q := lt_trans hd_pos hdq_lt
  simp [constL, ← ENNReal.tsum_mul_left]
  by_cases h_ae : ∀ᵐ (ω : Ω) ∂P, ∀ (s t : T'), edist (X s ω) (X t ω) = 0
  · convert zero_le'
    apply lintegral_eq_zero_of_zero_ae
    filter_upwards [h_ae] with ω h
    rw [Pi.zero_apply]
    rw [ENNReal.iSup_eq_zero]; rintro ⟨s, hs⟩
    rw [ENNReal.iSup_eq_zero]; rintro ⟨t, ht⟩
    simp [h ⟨s, hs⟩ ⟨t, ht⟩, hp_pos]
  have hM : (M : ℝ≥0∞) ≠ 0 := by
    contrapose! h_ae
    rw [Filter.eventually_all]; intro s
    rw [Filter.eventually_all]; intro t
    rw_mod_cast [h_ae] at hX
    exact hX.edist_eq_zero_of_M_eq_zero hp_pos
  have h_diam_zero : 0 < EMetric.diam (.univ : Set T) := by
    contrapose! h_ae
    rw [Filter.eventually_all]; intro s
    rw [Filter.eventually_all]; intro t
    apply hX.edist_eq_zero hp_pos hq_pos
    rw [← le_zero_iff]
    exact le_trans (EMetric.edist_le_diam_of_mem (Set.mem_univ _) (Set.mem_univ _)) h_ae
  have h_diam_real : 0 < (EMetric.diam (.univ : Set T)).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨h_diam_zero, h_diam⟩
  apply le_trans (lintegral_div_edist_le_sum_integral_edist_le h_diam hX hβ_pos hp_pos hq_pos)
  apply ENNReal.tsum_le_tsum
  intro k
  wlog hc : c ≠ ∞
  · simp [not_ne_iff.mp hc]
    repeat rw [ENNReal.top_mul]
    · rw [ENNReal.mul_top hM]
      exact le_top
    · have : 0 < (k + 2) * d := by positivity
      simp [this]
    · simp [le_of_lt hdq_lt]
  apply le_trans
  · apply mul_le_mul_left'
    refine finite_set_bound_of_edist_le (c := 2 ^ d * c) ?_ hT' hX ?_ hd_pos hp_pos hdq_lt ?_
    · exact hT.subset (Set.subset_univ _) hd_pos.le
    · finiteness
    · simp
  rw [ENNReal.mul_rpow_of_ne_top (by finiteness) (by finiteness), ← mul_assoc,
    ← mul_assoc _ (2 ^ ((k : ℝ) * _)), ← mul_assoc (M : ℝ≥0∞)]
  refine mul_le_mul' (le_of_eq ?_) ?_
  · calc 2 ^ (k * β * p) * (2 ^ (2 * p + 4 * q + 1) * M * (2 ^ d * c)
        * ((2 * 2⁻¹ ^ k) ^ (q - d) * (EMetric.diam Set.univ + 1) ^ (q - d)))
    _ = 2 ^ (k * β * p) * (2 ^ (2 * p + 4 * q + 1) * M * (2 ^ d * c)
        * ((2 ^ (q - d) * 2 ^ (- k * (q - d)))
        * (EMetric.diam (Set.univ : Set T) + 1) ^ (q - d))) := by
      congr
      rw [ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by bound), ENNReal.rpow_neg,
        ← ENNReal.inv_pow, ENNReal.rpow_natCast]
    _ = M * (2 ^ (2 * p + 4 * q + 1) * (2 ^ (q - d) * 2 ^ d)) * c
        * (EMetric.diam (Set.univ : Set T) + 1) ^ (q - d)
        * (2 ^ (k * β * p) * 2 ^ (- k * (q - d))) := by ring
    _ = M * 2 ^ (2 * p + 5 * q + 1) * c * (EMetric.diam Set.univ + 1) ^ (q - d)
        * 2 ^ (↑k * (↑β * p - (q - d))) := by
      congr
      · rw [← ENNReal.rpow_add _ _ (by simp) (by simp), ← ENNReal.rpow_add _ _ (by simp) (by simp)]
        ring_nf
      · rw [← ENNReal.rpow_add _ _ (by simp) (by simp)]
        ring_nf
    _ = _ := by ring
  by_cases hc_zero : c.toReal = 0
  · simp [hc_zero]; gcongr; exact zero_le _
  gcongr with k
  simp only [← ENNReal.rpow_natCast, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, mul_inv_rev]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  repeat rw [Real.mul_rpow (by positivity) (by positivity)]
  repeat rw [Real.logb_mul (by positivity) (by positivity)]
  grw [inv_lt_one_of_one_lt₀ (by simp [h_diam_real])]
  · apply le_of_eq
    rw [(by norm_num : (4 : ℝ) = 2 ^ (2 : ℝ)), ← Real.inv_rpow (by positivity), inv_inv,
      ← Real.rpow_neg_one]
    repeat rw [← Real.rpow_mul (by positivity)]
    repeat rw [Real.logb_rpow (by norm_num) (by norm_num)]
    simp
    ring
  · norm_num

theorem countable_kolmogorov_chentsov (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    (T' : Set T) (hT' : T'.Countable) :
    ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ M * constL T c d p q β := by
  sorry

end PseudoEMetricSpace

section EMetricSpace

variable [EMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology T]

lemma exists_modification_holder_aux (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    ∃ Y : T → Ω → E, (∀ t, Y t =ᵐ[P] X t) ∧ ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  have : Countable T' := hT'_countable
  have h_ae : ∀ᵐ ω ∂P, (⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p))
      < ∞ := by
    refine ae_lt_top' ?_ ((countable_kolmogorov_chentsov hT hX hd_pos hp_pos hdq_lt
      hβ_pos hβ_lt T' hT'_countable).trans_lt ?_).ne
    · refine AEMeasurable.iSup (fun s ↦ AEMeasurable.iSup (fun t ↦ ?_))
      exact AEMeasurable.div (hX.aemeasurable_edist.pow_const _) (by fun_prop)
    · exact ENNReal.mul_lt_top (by simp) (constL_lt_top hc hd_pos hp_pos hdq_lt hβ_pos hβ_lt)
  sorry

lemma exists_modification_holder (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p),
        ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  sorry

lemma exists_modification_holder' {C : ℕ → Set T} {c : ℕ → ℝ≥0∞}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : IsKolmogorovProcess X P p q M) (hp_pos : 0 < p) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p),
        ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  sorry

lemma exists_modification_holder_iSup {C : ℕ → Set T} {c : ℕ → ℝ≥0∞} {p q : ℕ → ℝ} {M : ℕ → ℝ≥0}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : ∀ n, IsKolmogorovProcess X P (p n) (q n) (M n))
    (hp_pos : ∀ n, 0 < p n) (hdq_lt : ∀ n, d < q n) :
    ∃ Y : T → Ω → E, (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < ⨆ n, (q n - d) / (p n)),
        ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  sorry

end EMetricSpace

end ProbabilityTheory
