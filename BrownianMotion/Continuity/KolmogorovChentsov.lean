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

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  {X : T → Ω → E}
  {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0}
  {P : Measure Ω}

lemma lintegral_div_edist_le_sum_integral_edist_le (hT : EMetric.diam (Set.univ : Set T) < ∞)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    {J : Set T} (hJ : J.Finite) :
    ∫⁻ ω, ⨆ (s) (t) (hs : s ∈ J) (ht : t ∈ J), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ ∑' k, 2 ^ (k * β * p)
          * ∫⁻ ω, ⨆ (s) (t) (hs : s ∈ J) (ht : t ∈ J)
            (_he : edist s t ≤ 2 * 2⁻¹ ^ k * (EMetric.diam (.univ : Set T) + 1)),
            edist (X s ω) (X t ω) ^p ∂P := by
  let η k := 2⁻¹ ^ k * (EMetric.diam (Set.univ : Set T) + 1)
  have hη_ge k : 2⁻¹ ^ k ≤ η k := by
    sorry
  sorry

noncomputable
-- the `max 0 ...` in the blueprint is performed by `ENNReal.ofReal` here
def constL (T : Type*) [PseudoEMetricSpace T] (c : ℝ≥0∞) (d p q β : ℝ) : ℝ≥0∞ :=
  4 ^ (p + 2 * q + 1) * c * (EMetric.diam (.univ : Set T) + 1) ^ (q - d)
  * ∑' (k: ℕ), 2 ^ (k * β * p + (-k + 1) * (q - d))
      * (4 ^ d * (ENNReal.ofReal (Real.logb 2 c.toReal + (k + 1) * d)) ^ q
        + Cp d p q)

lemma constL_lt_top (hT : EMetric.diam (Set.univ : Set T) ≠ ∞) (hc : 0 < c ∧ c < ⊤) (hd_pos : 0 < d)
    (hp_pos : 0 < p) (hdq_lt : d < q) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    constL T c d p q β < ∞ := by
  -- 1. L is finite as long as the sum in it is finite.
  unfold constL
  have hc' := hc.2
  repeat (any_goals first | apply ENNReal.mul_lt_top | apply ENNReal.rpow_lt_top_of_nonneg)
  all_goals norm_num
  any_goals assumption
  any_goals linarith
  clear! T
  -- 2. The sum is finite as long as its summand is a O(1 / k^2).
  unfold Cp
  -- Let f k be the k-th summand.
  let' f : ℕ → ℝ≥0∞ := _
  change ∑' (k : ℕ), f k < ∞
  rw [tsum_congr (g := fun k => ↑ (ENNReal.toNNReal (f k)))]
  rotate_left
  · intro k
    symm
    apply ENNReal.coe_toNNReal
    subst f
    rw [←lt_top_iff_ne_top]
    apply ENNReal.mul_lt_top
    · rw [lt_top_iff_ne_top]
      apply ENNReal.rpow_ne_top_of_ne_zero
      all_goals norm_num
    simp_all
    split_ands
    · apply ENNReal.mul_lt_top
      · rw [lt_top_iff_ne_top]
        apply ENNReal.rpow_ne_top_of_ne_zero
        all_goals norm_num
      apply ENNReal.rpow_lt_top_of_nonneg
      · linarith
      simp_all
    · apply ENNReal.rpow_pos
      · field_simp
        apply ENNReal.one_lt_rpow
        · norm_num
        simp_all
      simp_all
    apply ENNReal.one_lt_rpow
    · norm_num
    simp_all
  rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable, ←NNReal.summable_coe]
  apply summable_of_isBigO_nat (g := fun k => (k ^ 2)⁻¹)
  · rw [Real.summable_nat_pow_inv]
    norm_num
  -- 3. The summand is a O(1 / k^2).
  calc (fun a ↦ (f a).toNNReal.toReal)
      =O[Filter.atTop] fun (k: ℕ) ↦ ((k: ℝ) ^ 2)⁻¹ := by sorry

theorem finite_kolmogorov_chentsov (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    (T' : Set T) (hT' : T'.Finite) :
    ∫⁻ ω, ⨆ (s) (t) (hs : s ∈ T') (ht : t ∈ T'), edist (X s ω) (X t ω) ^p / edist s t ^ (β * p) ∂P
      ≤ M * constL T c d p q β := by
  sorry

theorem countable_kolmogorov_chentsov (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    (T' : Set T) (hT' : T'.Countable) :
    ∫⁻ ω, ⨆ (s) (t) (hs : s ∈ T') (ht : t ∈ T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
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
