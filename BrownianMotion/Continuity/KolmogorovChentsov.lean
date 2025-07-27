/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Topology
import BrownianMotion.Continuity.IsKolmogorovProcess
import BrownianMotion.Gaussian.StochasticProcesses
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Kolmogorov-Chentsov theorem

-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

theorem measurable_limUnder {ι X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → X → E} [hE : Nonempty E] (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x ↦ limUnder l (f · x)) := by
  obtain rfl | hl := eq_or_neBot l
  · simp [limUnder, Filter.map_bot]
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable
  let e := Classical.choice hE
  let conv := {x | ∃ c, Tendsto (f · x) l (𝓝 c)}
  have mconv : MeasurableSet conv := measurableSet_exists_tendsto hf
  have : (fun x ↦ _root_.limUnder l (f · x)) = ((↑) : conv → X).extend
      (fun x ↦ _root_.limUnder l (f · x)) (fun _ ↦ e) := by
    ext x
    by_cases hx : x ∈ conv
    · rw [Function.extend_val_apply hx]
    · rw [Function.extend_val_apply' hx, limUnder_of_not_tendsto hx]
  rw [this]
  refine (MeasurableEmbedding.subtype_coe mconv).measurable_extend
    (measurable_of_tendsto_metrizable' l
      (fun i ↦ (hf i).comp measurable_subtype_coe)
      (tendsto_pi_nhds.2 fun ⟨x, ⟨c, hc⟩⟩ ↦ ?_)) measurable_const
  rwa [hc.limUnder_eq]

theorem Asymptotics.IsEquivalent.add_const_of_norm_tendsto_atTop {α β : Type*}
    [NormedField β] [LinearOrder β] [IsStrictOrderedRing β] {u v : α → β} {l : Filter α} {c : β}
    (huv : u ~[l] v) (hv : Tendsto (norm ∘ v) l atTop) :
    (u · + c) ~[l] v := by
  apply Asymptotics.IsEquivalent.add_isLittleO huv
  rw [Asymptotics.isLittleO_const_left]
  exact Or.inr hv

theorem Asymptotics.IsEquivalent.const_add_of_norm_tendsto_atTop {α β : Type*}
    [NormedField β] [LinearOrder β] [IsStrictOrderedRing β] {u v : α → β} {l : Filter α} {c : β}
    (huv : u ~[l] v) (hv : Tendsto (norm ∘ v) l atTop) :
    (c + u ·) ~[l] v := by
  conv => enter [2, _]; rw [add_comm]
  exact Asymptotics.IsEquivalent.add_const_of_norm_tendsto_atTop huv hv

theorem Asymptotics.IsEquivalent.add_add_of_nonneg {α : Type*}
    {t u v w : α → ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) {l : Filter α}
    (htu : t ~[l] u) (hvw : v ~[l] w) : t + v ~[l] u + w := by
  simp only [IsEquivalent, add_sub_add_comm]
  change (fun x ↦ (t - u) x + (v - w) x) =o[l] (fun x ↦ u x + w x)
  conv => enter [3, x]; rw [← (abs_eq_self).mpr (hu x), ← (abs_eq_self).mpr (hw x)]
  simpa only [← Real.norm_eq_abs] using Asymptotics.IsLittleO.add_add htu hvw

protected theorem Asymptotics.IsEquivalent.rpow_of_nonneg {α : Type*}
    {t u : α → ℝ} (hu : 0 ≤ u) {l : Filter α} (h : t ~[l] u) {r : ℝ} :
    t ^ r ~[l] u ^ r := by
  obtain ⟨φ, hφ, htφu⟩ := IsEquivalent.exists_eq_mul h
  rw [isEquivalent_iff_exists_eq_mul]
  have hφr : Tendsto ((fun x ↦ x ^ r) ∘ φ) l (𝓝 1) := by
    rw [← Real.one_rpow r]
    refine Tendsto.comp ?_ hφ
    exact ContinuousAt.tendsto (Real.continuousAt_rpow_const _ _ (by left; norm_num))
  use (· ^ r) ∘ φ, hφr
  conv => enter [3]; change fun x ↦ φ x ^ r * u x ^ r
  filter_upwards [Filter.Tendsto.eventually_const_lt (zero_lt_one) hφ, htφu] with x hφ_pos htu'
  simp [← Real.mul_rpow (le_of_lt hφ_pos) (hu x), htu']

theorem Set.iUnion_le_nat : ⋃ n : ℕ, {i | i ≤ n} = Set.univ :=
 subset_antisymm (Set.subset_univ _)
  (fun i _ ↦ Set.mem_iUnion_of_mem i (Set.mem_setOf.mpr (le_refl _)))

-- modelled after `CompactExhaustion`
structure FiniteExhaustion {α : Type*} (s : Set α) where
  toFun : ℕ → Set α
  Finite' : ∀ n, Finite (toFun n)
  subset_succ' : ∀ n, toFun n ⊆ toFun (n + 1)
  iUnion_eq' : ⋃ n, toFun n = s

namespace FiniteExhaustion

instance {α : Type*} {s : Set α} : FunLike (FiniteExhaustion s) ℕ (Set α) where
  coe := toFun
  coe_injective' | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

instance  {α : Type*} {s : Set α} : RelHomClass (FiniteExhaustion s) LE.le HasSubset.Subset where
  map_rel K _ _ h := monotone_nat_of_le_succ (fun n ↦ K.subset_succ' n) h

instance {α : Type*} {s : Set α} {K : FiniteExhaustion s} {n : ℕ} : Finite (K n) :=
  K.Finite' n

variable {α : Type*} {s : Set α} (K : FiniteExhaustion s)

@[simp]
theorem toFun_eq_coe : K.toFun = K := rfl

protected theorem Finite (n : ℕ) : (K n).Finite := K.Finite' n

theorem subset_succ (n : ℕ) : K n ⊆ K (n + 1) := K.subset_succ' n

protected theorem subset {m n : ℕ} (h : m ≤ n) : K m ⊆ K n :=
  OrderHomClass.mono K h

theorem iUnion_eq : ⋃ n, K n = s :=
  K.iUnion_eq'

noncomputable def choice {α : Type*} (s : Set α) [Countable s] : FiniteExhaustion s := by
    apply Classical.choice
    by_cases h : Nonempty s
    · obtain ⟨f, hf⟩ := exists_surjective_nat s
      have : s → α := Subtype.val
      refine ⟨fun n ↦ (Subtype.val ∘ f) '' {i | i ≤ n}, ?_, ?_, ?_⟩
      · exact fun n ↦ Set.Finite.image _ (Set.finite_le_nat n)
      · intro n
        simp only [Function.comp_apply]
        apply Set.image_subset
        intro _ h
        simp [le_trans h (Nat.le_succ _)]
      · simp [← Set.image_image, ← Set.image_iUnion, Set.iUnion_le_nat, Set.range_eq_univ.mpr hf]
    · refine ⟨fun _ ↦ ∅, by simp [Set.Finite.to_subtype], fun n ↦ by simp, ?_⟩
      simp [Set.not_nonempty_iff_eq_empty'.mp h]

section prod

variable {β : Type*} {t : Set β} (K' : FiniteExhaustion t)

protected def prod :
    FiniteExhaustion (s ×ˢ t) :=
  { toFun := fun n ↦ K n ×ˢ K' n
    Finite' := fun n ↦ Set.Finite.prod (K.Finite n) (K'.Finite n)
    subset_succ' := fun n ↦ Set.prod_mono (K.subset_succ n) (K'.subset_succ n)
    iUnion_eq' := by
      apply subset_antisymm
      · rw [Set.iUnion_subset_iff]
        refine fun i ↦ Set.prod_mono ?_ ?_
        · simp [← K.iUnion_eq, Set.subset_iUnion]
        · simp [← K'.iUnion_eq, Set.subset_iUnion]
      rintro ⟨a, b⟩ h
      simp only [← K.iUnion_eq, ← K'.iUnion_eq, Set.mem_prod, Set.mem_iUnion] at h
      obtain ⟨⟨i,hi⟩, ⟨j, hj⟩⟩ := h
      simp only [Set.mem_iUnion, Set.mem_prod]
      exact ⟨max i j, K.subset (le_max_left _ _) hi, K'.subset (le_max_right _ _ ) hj⟩ }


protected theorem prod_apply (n : ℕ) : (K.prod K') n = K n ×ˢ K' n := by rfl

end prod

end FiniteExhaustion

lemma measure_add_ge_le_add_measure_ge {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω}
    {f g : Ω → ℝ≥0∞} {x u : ℝ≥0∞} (hu : u ≤ x) :
    P {ω | x ≤ f ω + g ω} ≤ P {ω | u ≤ f ω} + P {ω | x - u ≤ g ω} := by
  calc P {ω | x ≤ f ω + g ω}
  _ = P {ω | u + (x - u) ≤ f ω + g ω} := by
    congr with ω
    congr!
    exact (add_tsub_cancel_of_le hu).symm
  _ ≤ P ({ω | u ≤ f ω} ∪ {ω | (x - u) ≤ g ω}) := by
    refine measure_mono fun ω ↦ ?_
    simp only [Set.mem_setOf_eq, Set.mem_union]
    contrapose!
    rintro ⟨h₁, h₂⟩
    gcongr
  _ ≤ P {ω | u ≤ f ω} + P {ω | x - u ≤ g ω} := measure_union_le _ _

lemma measure_add_ge_le_add_measure_ge_half {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω}
    {f g : Ω → ℝ≥0∞} {x : ℝ≥0∞} :
    P {ω | x ≤ f ω + g ω} ≤ P {ω | x / 2 ≤ f ω} + P {ω | x / 2 ≤ g ω} := by
  by_cases hx : x = ∞
  · simp only [hx, top_le_iff, ENNReal.add_eq_top]
    rw [ENNReal.top_div_of_ne_top (by finiteness)]
    simp only [top_le_iff]
    exact measure_union_le {ω | f ω = ∞} {ω | g ω = ∞}
  convert measure_add_ge_le_add_measure_ge ENNReal.half_le_self using 2
  rw [ENNReal.sub_half hx]

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]

lemma lintegral_div_edist_le_sum_integral_edist_le (hT : EMetric.diam (Set.univ : Set T) < ∞)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hβ : 0 < β) {J : Set T} [Countable J] :
    ∫⁻ ω, ⨆ (s : J) (t : J), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ ∑' (k : ℕ), 2 ^ (k * β * p)
          * ∫⁻ ω, ⨆ (s : J)
              (t : {t : J // edist s t ≤ 2 * 2⁻¹ ^ k * (EMetric.diam (.univ : Set T) + 1)}),
                edist (X s ω) (X t ω) ^p ∂P := by
  let η k := 2⁻¹ ^ k * (EMetric.diam (Set.univ : Set T) + 1)
  have hp_pos := hX.p_pos
  have hq_pos := hX.q_pos
  have hη_ge (k : ℕ) : 2⁻¹ ^ (k : ℝ) ≤ η k := by simp [η, mul_add]
  have hη_succ (k : ℕ) : η (k + 1) = 2⁻¹ * η k := by simp [η, pow_add, mul_assoc, mul_comm]
  have hη_lim : Filter.Tendsto η Filter.atTop (nhds 0) := by
    unfold η
    rw [← zero_mul (EMetric.diam (Set.univ : Set T) + 1)]
    apply ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
    simp [← lt_top_iff_ne_top, hT]
  conv in 2 ^ _ * _ => rw [← lintegral_const_mul' _ _ (by simp)]
  rw [← lintegral_tsum fun i ↦ ?_]
  swap
  · have h_ae s t := hX.aemeasurable_edist (s := s) (t := t)
    fun_prop
  have h_ae : ∀ᵐ (ω : Ω) ∂P, ∀ (s t : J), edist s t = 0 → edist (X s ω) (X t ω) = 0 := by
    rw [eventually_countable_forall]; intro s
    rw [eventually_countable_forall]; intro t
    by_cases h_dist : edist s t = 0
    · apply Filter.Eventually.mp (IsAEKolmogorovProcess.edist_eq_zero hX h_dist)
      filter_upwards with _ h _ using h
    filter_upwards with _ using by simp [h_dist]
  refine lintegral_mono_ae (Filter.Eventually.mp h_ae ?_)
  filter_upwards with ω h
  rw [iSup_le_iff]; rintro ⟨s, hs⟩
  rw [iSup_le_iff]; intro ⟨t, ht⟩
  wlog hst : 0 < edist s t
  · simp [(h ⟨s, hs⟩ ⟨t, ht⟩) <| nonpos_iff_eq_zero.mp (le_of_not_gt hst),
      ENNReal.zero_rpow_of_pos hX.p_pos]
  obtain ⟨k, lb, ub⟩ : ∃ k, (η k ≤ edist s t) ∧ (edist s t ≤ 2 * η k) := by
    have hη_dist : ∃ k, η k ≤ edist s t :=
      (Filter.Eventually.exists (Filter.Tendsto.eventually_le_const hst hη_lim))
    refine ⟨Nat.find hη_dist, Nat.find_spec hη_dist, ?_⟩
    match hk : Nat.find hη_dist with
    | 0 =>
        apply le_trans (EMetric.edist_le_diam_of_mem (Set.mem_univ _) (Set.mem_univ _))
        simp only [pow_zero, one_mul, η]
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
      * (4 ^ d * (ENNReal.ofReal (Real.logb 2 c.toReal + (k + 2) * d)) ^ q + Cp d p q)

lemma constL_lt_top (hT : EMetric.diam (Set.univ : Set T) < ∞)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q) (hβ_lt : β < (q - d) / p) :
    constL T c d p q β < ∞ := by
  have hq_pos : 0 < q := lt_trans hd_pos hdq_lt
  have hC : Cp d p q ≠ ⊤ := by
    unfold Cp
    apply max_ne_top <;> apply ENNReal.div_ne_top (by norm_num)
    · apply ne_of_gt
      refine ENNReal.rpow_pos ?_ (by finiteness)
      exact tsub_pos_of_lt (ENNReal.one_lt_rpow (by norm_num) (by bound))
    · exact ne_of_gt <| tsub_pos_of_lt (ENNReal.one_lt_rpow (by norm_num) (by bound))
  have hC_pos : 0 < Cp d p q := by
    unfold Cp
    apply lt_max_of_lt_right (ENNReal.div_pos (by norm_num) (by finiteness))
  apply ENNReal.mul_lt_top (by finiteness)
  conv =>
    enter [1, 1, _]
    rw [← (ENNReal.ofReal_toReal_eq_iff (a := _ * _)).mpr (by finiteness),
      ENNReal.ofReal_eq_coe_nnreal (by positivity)]
  rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
  apply summable_of_ratio_test_tendsto_lt_one (l := 2 ^ (β * p - (q - d)))
  · apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    simp [← lt_div_iff₀, hp_pos, hβ_lt]
  · filter_upwards with k
    apply ne_of_gt
    simp only [ENNReal.toReal_mul, NNReal.coe_mk]
    apply mul_pos <;> refine ENNReal.toReal_pos_iff.mpr ⟨?_, by finiteness⟩
    · exact ENNReal.rpow_pos (by norm_num) (by norm_num)
    · positivity
  simp only [Nat.cast_add, Nat.cast_one, ENNReal.toReal_mul, NNReal.coe_mk, norm_mul,
    Real.norm_eq_abs, ENNReal.abs_toReal, ← div_mul_div_comm, add_mul (b := (1 : ℝ)), one_mul]
  conv => enter [1, _, 2, 1]; rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  conv => enter [1, _, 2, 2]; rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [← ENNReal.toReal_rpow, ENNReal.toReal_ofNat, Nat.ofNat_pos, Real.rpow_add,
    ENNReal.toReal_mul]
  conv => enter [1, _, 1]; rw [mul_div_cancel_left₀ _ (by positivity)]
  conv => enter [3, 1]; rw [← mul_one (_ ^ _)]
  apply Tendsto.const_mul
  conv => enter [1]; change (fun n ↦ _) / (fun n ↦ _)
  rw [← Asymptotics.isEquivalent_iff_tendsto_one]; swap
  · filter_upwards with _
    apply ne_of_gt
    refine lt_of_le_of_lt ?_ <| (add_lt_add_left (ENNReal.toReal_pos (by positivity) hC)) _
    positivity
  refine Asymptotics.IsEquivalent.add_add_of_nonneg
    (by intro _; positivity) (by intro _; positivity) ?_ .refl
  apply Asymptotics.IsEquivalent.mul .refl
  apply Asymptotics.IsEquivalent.rpow_of_nonneg (by intro _; positivity)
  have h (k : ℕ) : ∀ᶠ (n : ℕ) in atTop, 0 ≤ Real.logb 2 c.toReal + (n + k + 2) * d := by
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (- Real.logb 2 c.toReal / d)
    rw [eventually_atTop]
    use n₀
    intro n hn
    grw [hn, add_mul, add_mul, ← le_of_lt ((div_lt_iff₀ hd_pos).mp hn₀), add_assoc, ← add_assoc]
    simp
    positivity
  apply Asymptotics.IsEquivalent.congr_right; swap
  · filter_upwards [h 0] with n h_nonneg
    rw [← add_zero (n : ℝ), ← Nat.cast_zero, ENNReal.toReal_ofReal h_nonneg]
  apply Asymptotics.IsEquivalent.congr_left; swap
  · filter_upwards [h 1] with n h_nonneg
    rw [← Nat.cast_one, ENNReal.toReal_ofReal h_nonneg]
  apply Asymptotics.IsEquivalent.const_add_of_norm_tendsto_atTop; swap
  · apply Tendsto.comp tendsto_norm_atTop_atTop
    apply tendsto_atTop_add_const_left
    rw [tendsto_mul_const_atTop_of_pos hd_pos]
    repeat apply tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_iff.mpr tendsto_id
  refine (Asymptotics.IsEquivalent.const_add_of_norm_tendsto_atTop ?_ ?_).symm; swap
  · apply Tendsto.comp tendsto_norm_atTop_atTop
    rw [tendsto_mul_const_atTop_of_pos hd_pos]
    repeat apply tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_iff.mpr tendsto_id
  refine Asymptotics.IsEquivalent.mul ?_ .refl
  simp only [add_assoc]
  apply Asymptotics.IsEquivalent.add_const_of_norm_tendsto_atTop; swap
  · apply Tendsto.comp tendsto_norm_atTop_atTop
    apply tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_iff.mpr tendsto_id
  refine (Asymptotics.IsEquivalent.add_const_of_norm_tendsto_atTop .refl ?_).symm
  exact Tendsto.comp tendsto_norm_atTop_atTop (tendsto_natCast_atTop_iff.mpr tendsto_id)

theorem finite_kolmogorov_chentsov
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (T' : Set T) [hT' : Finite T'] :
    ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ M * constL T c d p q β := by
  have h_diam : EMetric.diam .univ < ∞ := hT.diam_lt_top hd_pos
  have hq_pos : 0 < q := lt_trans hd_pos hdq_lt
  simp [constL, ← ENNReal.tsum_mul_left]
  by_cases h_ae : ∀ᵐ (ω : Ω) ∂P, ∀ (s t : T'), edist (X s ω) (X t ω) = 0
  · convert zero_le'
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [h_ae] with ω h
    rw [Pi.zero_apply]
    rw [ENNReal.iSup_eq_zero]; rintro ⟨s, hs⟩
    rw [ENNReal.iSup_eq_zero]; rintro ⟨t, ht⟩
    simp [h ⟨s, hs⟩ ⟨t, ht⟩, hX.p_pos]
  have hM : (M : ℝ≥0∞) ≠ 0 := by
    contrapose! h_ae
    rw [Filter.eventually_all]; intro s
    rw [Filter.eventually_all]; intro t
    rw_mod_cast [h_ae] at hX
    exact hX.edist_eq_zero_of_const_eq_zero _ _
  have h_diam_zero : 0 < EMetric.diam (.univ : Set T) := by
    contrapose! h_ae
    rw [Filter.eventually_all]; intro s
    rw [Filter.eventually_all]; intro t
    apply hX.edist_eq_zero
    rw [← le_zero_iff]
    exact le_trans (EMetric.edist_le_diam_of_mem (Set.mem_univ _) (Set.mem_univ _)) h_ae
  have h_diam_real : 0 < (EMetric.diam (.univ : Set T)).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨h_diam_zero, h_diam⟩
  apply le_trans
    (lintegral_div_edist_le_sum_integral_edist_le h_diam hX hβ_pos)
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
    refine finite_set_bound_of_edist_le (c := 2 ^ d * c) ?_ hT' hX ?_ hd_pos hdq_lt ?_
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
    (hX : IsAEKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hdq_lt : d < q) (hβ_pos : 0 < β)
    (T' : Set T) [Countable T'] :
    ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ M * constL T c d p q β := by
  let K := (FiniteExhaustion.choice T')
  simp only [iSup_subtype, Subtype.edist_mk_mk, ← biSup_prod', ← (K.prod K).iUnion_eq,
    Set.mem_iUnion, iSup_exists, K.prod_apply, iSup_comm (ι' := ℕ)]
  simp only [biSup_prod]
  simp only [← iSup_subtype'']
  rw [MeasureTheory.lintegral_iSup', iSup_le_iff]
  · exact fun n ↦ finite_kolmogorov_chentsov hT hX hd_pos hdq_lt hβ_pos (K n)
  · intro n
    have h_ae s t := hX.aemeasurable_edist (s := s) (t := t)
    fun_prop
  · filter_upwards with ω
    intro _ _ h
    simp only [iSup_subtype, ← biSup_prod']
    exact iSup_le_iSup_of_subset (Set.prod_mono (K.subset h) (K.subset h))

end PseudoEMetricSpace

section EMetricSpace

variable [PseudoMetricSpace T] [EMetricSpace E] [MeasurableSpace E] [BorelSpace E]

lemma IsKolmogorovProcess.ae_iSup_rpow_edist_div_lt_top
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    {T' : Set T} (hT' : T'.Countable) :
    ∀ᵐ ω ∂P, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) < ∞ := by
  have : Countable T' := hT'
  have h_diam : EMetric.diam .univ < ∞ := hT.diam_lt_top hd_pos
  refine ae_lt_top' ?_ ((countable_kolmogorov_chentsov hT hX.IsAEKolmogorovProcess hd_pos
    hdq_lt hβ_pos T').trans_lt ?_).ne
  · refine AEMeasurable.iSup (fun s ↦ AEMeasurable.iSup (fun t ↦ ?_))
    exact AEMeasurable.div (hX.measurable_edist.aemeasurable.pow_const _) (by fun_prop)
  · exact ENNReal.mul_lt_top (by simp) (constL_lt_top h_diam hc hd_pos hX.p_pos hdq_lt hβ_lt)

omit [MeasurableSpace E] [BorelSpace E] in
def holderSet (X : T → Ω → E) (T' : Set T) (p β : ℝ) : Set Ω :=
  {ω | ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) < ∞
      ∧ ∀ (s t : T'), edist s t = 0 → edist (X s ω) (X t ω) = 0}

omit [MeasurableSpace E] [BorelSpace E] in
lemma IsKolmogorovProcess.measurableSet_holderSet
    (hX : IsKolmogorovProcess X P p q M) {T' : Set T} (hT' : T'.Countable) :
    MeasurableSet (holderSet X T' p β) := by
  have : Countable T' := hT'
  let C ω := ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
  refine MeasurableSet.inter ?_ ?_
  · change MeasurableSet {ω | C ω < ∞}
    refine measurableSet_lt ?_ (by fun_prop)
    refine Measurable.iSup (fun s ↦ Measurable.iSup (fun t ↦ ?_))
    exact Measurable.div (hX.measurable_edist.pow_const _) (by fun_prop)
  · have : {ω | ∀ (s t : T'), edist s t = 0 → edist (X s ω) (X t ω) = 0}
        = ⋂ (s : T') (t : T'), ({ω | edist (X s ω) (X t ω) = 0} ∪ {ω | edist s t ≠ 0}) := by
      ext; simp [imp_iff_or_not]
    change MeasurableSet {ω | ∀ (s t : T'), edist s t = 0 → edist (X s ω) (X t ω) = 0}
    rw [this]
    refine MeasurableSet.iInter (fun s ↦ MeasurableSet.iInter (fun t ↦ ?_))
    refine MeasurableSet.union ?_ ?_
    · exact MeasurableSet.preimage (measurableSet_singleton 0) hX.measurable_edist
    · exact (MeasurableSet.preimage (measurableSet_singleton 0) (by fun_prop)).compl

omit [MeasurableSpace E] [BorelSpace E] in
lemma holderWith_of_mem_holderSet (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hβ_pos : 0 < β)
    {T' : Set T} {ω : Ω} (hω : ω ∈ holderSet X T' p β) :
    letI C ω := ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
    HolderWith (C ω ^ p⁻¹).toNNReal β fun (t : T') ↦ X t ω := by
  intro s t
  have h_edist_lt_top : edist s t < ∞ := by
    calc edist s t ≤ EMetric.diam (Set.univ : Set T) :=
      EMetric.edist_le_diam_of_mem (Set.mem_univ s) (Set.mem_univ t)
    _ < ∞ := hT.diam_lt_top hd_pos
  have h_dist_top : edist s t ^ (β : ℝ) ≠ ∞
  · simp only [ne_eq, ENNReal.rpow_eq_top_iff, NNReal.coe_pos, not_or, not_and, not_lt,
      NNReal.zero_le_coe, implies_true, nonpos_iff_eq_zero, true_and]
    exact fun h_eq_top ↦ absurd h_eq_top h_edist_lt_top.ne
  by_cases h_dist_zero : edist s t = 0
  · simpa [h_dist_zero, hβ_pos] using hω.2 s t h_dist_zero
  rw [← ENNReal.div_le_iff (by simp [h_dist_zero]) h_dist_top]
  rw [ENNReal.coe_toNNReal]
  swap; · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hω.1.ne
  rw [ENNReal.le_rpow_inv_iff hp_pos, ENNReal.div_rpow_of_nonneg _ _ hp_pos.le,
    ← ENNReal.rpow_mul]
  exact le_iSup₂ s t (f := fun (s t : T') ↦ edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p))

omit [MeasurableSpace E] [BorelSpace E] in
lemma uniformContinuous_of_mem_holderSet
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hβ_pos : 0 < β)
    {T' : Set T} {ω : Ω} (hω : ω ∈ holderSet X T' p β) :
    UniformContinuous fun (t : T') ↦ X t ω :=
      (holderWith_of_mem_holderSet hT hd_pos hp_pos hβ_pos hω).uniformContinuous hβ_pos

omit [MeasurableSpace E] [BorelSpace E] in
lemma continuous_of_mem_holderSet (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hβ_pos : 0 < β)
    {T' : Set T} {ω : Ω} (hω : ω ∈ holderSet X T' p β) :
    Continuous fun (t : T') ↦ X t ω :=
  (holderWith_of_mem_holderSet hT hd_pos hp_pos hβ_pos hω).continuous hβ_pos

omit [MeasurableSpace E] [BorelSpace E] in
lemma IsKolmogorovProcess.tendstoInMeasure_of_mem_holderSet
    (hX : IsKolmogorovProcess X P p q M)
    (hq_pos : 0 < q) {T' : Set T} {u : ℕ → T'} {t : T}
    (hu : Tendsto (fun n ↦ (u n : T)) atTop (𝓝 t)) :
    TendstoInMeasure P (fun n ↦ X (u n)) atTop (X t) := by
  intro ε hε
  -- todo: change tendstoInMeasure_of_ne_top to work in a PseudoEMetricSpace, or change the def
  suffices h_of_ne_top :
      ∀ ε, 0 < ε → ε ≠ ∞ → Tendsto (fun n ↦ P {ω | ε ≤ edist (X (u n) ω) (X t ω)}) atTop (𝓝 0) by
    by_cases hε_top : ε = ∞
    swap; · exact h_of_ne_top _ hε hε_top
    have h1 : Tendsto (fun n ↦ P {ω | 1 ≤ edist (X (u n) ω) (X t ω)}) atTop (𝓝 0) :=
      h_of_ne_top 1 (by simp) (by simp)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ ↦ zero_le') ?_
    intro n
    simp only [hε_top]
    gcongr
    simp
  intro ε hε hε_top
  have h_tendsto : Tendsto (fun n ↦ ∫⁻ ω, edist (X (u n) ω) (X t ω) ^ p ∂P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le')
      (fun n ↦ hX.kolmogorovCondition (u n) t)
    have : Tendsto (fun n ↦ edist (u n).1 t) atTop (𝓝 0) := by
      rwa [← tendsto_iff_edist_tendsto_0]
    rw [← mul_zero (M : ℝ≥0∞)]
    refine ENNReal.Tendsto.const_mul ?_ (by simp)
    change Tendsto ((fun x : ℝ≥0∞ ↦ x ^ q) ∘ (fun n ↦ edist (u n).1 t)) atTop (𝓝 0)
    refine Tendsto.comp ?_ this
    convert ENNReal.continuous_rpow_const.tendsto 0
    simp [hq_pos]
  suffices Tendsto (fun n ↦ P {ω | ε ^ p ≤ edist (X (u n) ω) (X t ω) ^ p}) atTop (𝓝 0) by
    convert this using 3 with n
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [ENNReal.rpow_le_rpow_iff hX.p_pos]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le') ?_
    (h := fun n ↦ (ε ^ p)⁻¹ * ∫⁻ ω, edist (X (u n) ω) (X t ω) ^ p ∂P)
  · rw [← mul_zero (ε ^ p)⁻¹]
    exact ENNReal.Tendsto.const_mul h_tendsto (by simp [hε_top, hε.ne'])
  · refine fun n ↦ (meas_ge_le_lintegral_div ?_ ?_ ?_).trans_eq ?_
    · exact (hX.measurable_edist.pow_const _).aemeasurable
    · simp [hε.ne', hX.p_pos.le]
    · simp [hε.ne', hε_top]
    · rw [ENNReal.div_eq_inv_mul]

-- TODO: I (Rémy) gave up on separability of `E`. The measurability checks are driving me crazy.
variable [Nonempty E] [SecondCountableTopology T] [CompleteSpace E] [SecondCountableTopology E]
  [IsFiniteMeasure P]

-- TODO: in this lemma we use the notion of convergence in measure, but since we use `edist` and not
-- `dist`, we can't use the existing definition `TendstoInMeasure`.
lemma exists_modification_holder_aux' (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  -- Let `T'` be a countable dense subset of `T`
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  have : Countable T' := hT'_countable
  have h_ae_zero : ∀ᵐ ω ∂P, ∀ (s t : T'), edist s t = 0 → edist (X s ω) (X t ω) = 0 := by
    simp_rw [ae_all_iff]
    exact fun s t hst ↦ hX.IsAEKolmogorovProcess.edist_eq_zero hst
  -- For each `ω`, `C ω < ∞` is a bound on `edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)`
  let C ω := ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
  have hC_lt_top : ∀ᵐ ω ∂P, C ω < ∞ :=
    hX.ae_iSup_rpow_edist_div_lt_top hT hc hd_pos hdq_lt hβ_pos hβ_lt hT'_countable
  -- Let `A` be the event that `C ω < ∞` and `X s ω = X t ω` for `edist s t = 0`.
  -- This is an event of probability 1.
  let A := holderSet X T' p β
  have hA : MeasurableSet A := hX.measurableSet_holderSet hT'_countable
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := by
    filter_upwards [hC_lt_top, h_ae_zero] with ω hω₁ hω₂ using ⟨hω₁, hω₂⟩
  have hPA {s : Set Ω} (hs : MeasurableSet s) : P (s ∩ A) = P s := by
    rw [Set.inter_comm, Measure.measure_inter_eq_of_ae hA_ae]
  -- We build a modification `Y` of `X`, by using `Dense.extend` on `X · ω` if `ω ∈ A` and by taking
  -- an arbitrary constant value if `ω ∉ A`.
  let x₀ : E := Nonempty.some inferInstance
  classical
  let Y (t : T) (ω : Ω) : E := if ω ∈ A then hT'_dense.extend (fun t ↦ X t ω) t else x₀
  have hY t : Measurable (Y t) := by
    refine Measurable.ite hA ?_ (by fun_prop)
    -- todo: extract lemma `measurable_extend`
    exact measurable_limUnder (f := fun (t : T') ω ↦ X t ω) fun t ↦ hX.measurable t
  have hY_eq {ω : Ω} (hω : ω ∈ A) (t : T') : Y t ω = X t ω := by
    simp only [hω, ↓reduceIte, Y]
    exact hT'_dense.extend_eq (continuous_of_mem_holderSet hT hd_pos hX.p_pos hβ_pos hω) t
  have hY_unif ω : UniformContinuous (fun t ↦ Y t ω) := by
    by_cases hω : ω ∈ A
    · simp only [hω, ↓reduceIte, Y]
      refine hT'_dense.uniformContinuous_extend ?_
      exact uniformContinuous_of_mem_holderSet hT hd_pos hX.p_pos hβ_pos hω
    · simp only [hω, ↓reduceIte, Y]
      exact uniformContinuous_const
  have hY_cont ω : Continuous (fun t ↦ Y t ω) := (hY_unif ω).continuous
  refine ⟨Y, hY, fun t ↦ ?_, fun ω ↦ ?_⟩
  · suffices ∀ᵐ ω ∂P, edist (Y t ω) (X t ω) ≤ 0 by
      filter_upwards [this] with ω h using by simpa using h
    obtain ⟨u, hu⟩ : ∃ u : ℕ → T', Tendsto (fun n ↦ (u n : T)) atTop (𝓝 t) := by
      have ht_mem_closure : t ∈ closure T' := by simp [hT'_dense.closure_eq]
      rw [mem_closure_iff_seq_limit] at ht_mem_closure
      obtain ⟨u, hu⟩ := ht_mem_closure
      exact ⟨fun n ↦ ⟨u n, hu.1 n⟩, hu.2⟩
    have h_le n {ω} (hω : ω ∈ A) : edist (Y t ω) (X t ω)
        ≤ edist (Y t ω) (Y (u n) ω) + edist (X (u n) ω) (X t ω) := by
      refine (edist_triangle4 (Y t ω) (Y (u n) ω) (X (u n) ω) (X t ω)).trans_eq ?_
      simp [hY_eq hω (u n)]
    -- `X (u n)` converges in measure to `X t`
    have h_tendsto_X : TendstoInMeasure P (fun n ↦ X (u n)) atTop (X t) :=
      hX.tendstoInMeasure_of_mem_holderSet (hd_pos.trans hdq_lt) hu
    -- `Y (u n)` converges in measure to `Y t`
    have h_tendsto_Y : TendstoInMeasure P (fun n ↦ Y (u n)) atTop (Y t) := by
      have h_ae ω : Tendsto (fun n ↦ Y (u n) ω) atTop (𝓝 (Y t ω)) :=
        ((hY_cont ω).tendsto t).comp hu
      refine tendstoInMeasure_of_tendsto_ae_of_stronglyMeasurable ?_ ?_ ?_
      · exact fun n ↦ (hY (u n)).stronglyMeasurable
      · exact (hY t).stronglyMeasurable
      · exact ae_of_all _ h_ae
    refine (ae_le_const_iff_forall_gt_measure_zero _ _).mpr fun ε hε ↦ ?_
    suffices Tendsto (fun n : ℕ ↦ P {ω | ε ≤ edist (Y t ω) (X t ω)}) atTop (𝓝 0) by
      simpa using this
    have hP_le n : P {ω | ε ≤ edist (Y t ω) (X t ω)}
        ≤ P {ω | ε/2 ≤ edist (Y (u n) ω) (Y t ω)} + P {ω | ε/2 ≤ edist (X (u n) ω) (X t ω)} := by
      calc P {ω | ε ≤ edist (Y t ω) (X t ω)}
      _ = P ({ω | ε ≤ edist (Y t ω) (X t ω)} ∩ A) := by
        rw [hPA]
        exact measurableSet_le (by fun_prop) (Measurable.edist (hY t) (hX.measurable t))
      _ ≤ P ({ω | ε ≤ edist (Y (u n) ω) (Y t ω) + edist (X (u n) ω) (X t ω)} ∩ A) := by
        refine measure_mono fun ω ↦ ?_
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_imp]
        refine fun hε_le hω ↦ ⟨(hε_le.trans (h_le n hω)).trans_eq ?_, hω⟩
        rw [edist_comm]
      _ = P {ω | ε ≤ edist (Y (u n) ω) (Y t ω) + edist (X (u n) ω) (X t ω)} := by
        rw [hPA]
        refine measurableSet_le (by fun_prop) ?_
        exact ((hY (u n)).edist (hY t)).add ((hX.measurable (u n)).edist (hX.measurable t))
      _ ≤ P {ω | ε / 2 ≤ edist (Y (u n) ω) (Y t ω)}
          + P {ω | ε / 2 ≤ edist (X (u n) ω) (X t ω)} := measure_add_ge_le_add_measure_ge_half
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le') hP_le
    rw [← add_zero (0 : ℝ≥0∞)]
    exact Tendsto.add (h_tendsto_Y (ε / 2) (ENNReal.half_pos hε.ne'))
      (h_tendsto_X (ε / 2) (ENNReal.half_pos hε.ne'))
  · by_cases hω : ω ∈ A
    swap; · simp only [hω, ↓reduceIte, Y]; exact ⟨0, by simp [HolderWith]⟩
    simp only [hω, ↓reduceIte, Y, A]
    refine ⟨(C ω ^ p⁻¹).toNNReal, ?_⟩
    exact hT'_dense.holderWith_extend (holderWith_of_mem_holderSet hT hd_pos hX.p_pos hβ_pos hω)
      hβ_pos

lemma exists_modification_holder_aux (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω, MemHolder β (Y · ω) := by
  obtain ⟨Y, hY_meas, hY_eq, hY_holder⟩ :=
    exists_modification_holder_aux' hT hX.IsKolmogorovProcess_mk hc hd_pos hdq_lt
      hβ_pos hβ_lt
  refine ⟨Y, hY_meas, fun t ↦ ?_, hY_holder⟩
  filter_upwards [hX.ae_eq_mk t, hY_eq t] with ω hω1 hω2 using hω2.trans hω1.symm

omit [MeasurableSpace E] [BorelSpace E] [Nonempty E] [SecondCountableTopology E]
  [CompleteSpace E] in
lemma StronglyMeasurable.measurableSet_eq_of_continuous {f g : T → Ω → E}
    (hf : ∀ ω, Continuous (f · ω)) (hg : ∀ ω, Continuous (g · ω))
    (hf_meas : ∀ t, StronglyMeasurable (f t)) (hg_meas : ∀ t, StronglyMeasurable (g t)) :
    MeasurableSet  {ω | ∀ t, f t ω = g t ω} := by
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  have : {ω | ∀ (t : T), f t ω = g t ω} = {ω | ∀ (t : T'), f t ω = g t ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Subtype.forall]
    refine ⟨fun h t _ ↦ h t, fun h ↦ ?_⟩
    rw [← funext_iff]
    exact Continuous.ext_on hT'_dense (hf ω) (hg ω) h
  rw [this]
  have : {ω | ∀ (t : T'), f t ω = g t ω} = ⋂ (t : T'), {ω | f t ω = g t ω} := by
    ext; simp
  rw [this]
  have : Countable T' := hT'_countable
  refine MeasurableSet.iInter (fun t ↦ ?_)
  exact StronglyMeasurable.measurableSet_eq_fun (hf_meas t) (hg_meas t)

lemma exists_modification_holder (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ (β : ℝ≥0) (_ : 0 < β) (_ : β < (q - d) / p) ω, MemHolder β (Y · ω) := by
  have hp_pos : 0 < p := hX.p_pos
  have h_ratio_pos : 0 < (q - d) / p := by
    have : 0 < q - d := by bound
    positivity
  obtain ⟨β', hβ'_mono, hβ'_mem, hβ'_tendsto⟩ := exists_seq_strictMono_tendsto' h_ratio_pos
  let β : ℕ → ℝ≥0 := fun n ↦ ⟨β' n, (hβ'_mem n).1.le⟩
  have hβ_pos : ∀ n, 0 < β n := fun n ↦ mod_cast (hβ'_mem n).1
  have h_exists := fun n ↦ exists_modification_holder_aux hT hX hc hd_pos hdq_lt (β := β n)
    (hβ_pos n) (mod_cast (hβ'_mem n).2)
  choose Z hZ_meas hZ_ae_eq hZ_holder using h_exists
  have hZ_ae_eq' n : ∀ᵐ ω ∂P, ∀ t, Z n t ω = Z 0 t ω := by
    refine indistinduishable_of_modification (ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_) ?_
    · obtain ⟨C, hC⟩ := hZ_holder n ω
      exact hC.continuous (hβ_pos n)
    · obtain ⟨C, hC⟩ := hZ_holder 0 ω
      exact hC.continuous (hβ_pos 0)
    · intro t
      filter_upwards [hZ_ae_eq n t, hZ_ae_eq 0 t] with ω hω₁ hω₂ using hω₁.trans hω₂.symm
  rw [← ae_all_iff] at hZ_ae_eq'
  let A := {ω | ∀ n t, Z n t ω = Z 0 t ω}
  have hA : MeasurableSet A := by
    have : A = ⋂ n, {ω | ∀ t, Z n t ω = Z 0 t ω} := by ext; simp [A]
    rw [this]
    refine MeasurableSet.iInter (fun n ↦ ?_)
    refine StronglyMeasurable.measurableSet_eq_of_continuous (fun ω ↦ ?_) (fun ω ↦ ?_) ?_ ?_
    · obtain ⟨_, h⟩ := hZ_holder n ω
      exact h.continuous (hβ_pos n)
    · obtain ⟨_, h⟩ := hZ_holder 0 ω
      exact h.continuous (hβ_pos 0)
    · exact fun t ↦ (hZ_meas n t).stronglyMeasurable
    · exact fun t ↦ (hZ_meas 0 t).stronglyMeasurable
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := hZ_ae_eq'
  classical
  let Y (t : T) (ω : Ω) : E := if ω ∈ A then Z 0 t ω else Nonempty.some inferInstance
  refine ⟨Y, fun t ↦ Measurable.ite hA (hZ_meas 0 t) (by fun_prop), fun t ↦ ?_, ?_⟩
  · filter_upwards [hA_ae, hZ_ae_eq 0 t] with ω hω hω₂
    simpa only [hω, ↓reduceIte, Y] using hω₂
  · intro β₀ hβ₀_pos hβ₀_lt ω
    by_cases hω : ω ∈ A
    swap; · simp [hω, Y]
    simp only [hω, ↓reduceIte, Y]
    obtain ⟨n, hn⟩ : ∃ n, β₀ < β n := by
      obtain ⟨n, hn⟩ : ∃ n, β₀ < β' n := (Tendsto.eventually_const_lt hβ₀_lt hβ'_tendsto).exists
      exact ⟨n, mod_cast hn⟩
    suffices MemHolder (β n) fun x ↦ Z 0 x ω by
      have h_bounded : BoundedSpace T := by -- extract this lemma
        constructor
        rw [Metric.isBounded_iff_ediam_ne_top]
        exact (hT.diam_lt_top hd_pos).ne
      refine this.mono hn.le
    simp_rw [← hω n]
    exact hZ_holder n ω

lemma exists_modification_holder' {C : ℕ → Set T} {c : ℕ → ℝ≥0∞}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : IsAEKolmogorovProcess X P p q M) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t, ∃ U ∈ 𝓝 t, ∀ (β : ℝ≥0) (_ : 0 < β) (_ : β < (q - d) / p),
        ∃ C, HolderOnWith C β (Y · ω) U := by
  have hp_pos : 0 < p := hX.p_pos
  have h_div_pos : 0 < (q - d) / p := by
    have : 0 < q - d := by bound
    positivity
  let ⟨β₀', hβ₀_pos', hβ₀_lt'⟩ := exists_between h_div_pos
  let β₀ : ℝ≥0 := ⟨β₀', hβ₀_pos'.le⟩
  have hβ₀_pos : 0 < β₀ := mod_cast hβ₀_pos'
  have hβ₀_lt : β₀ < (q - d) / p := mod_cast hβ₀_lt'
  let Xn : (n : ℕ) → (C n) → Ω → E := fun n t ω ↦ X t ω
  have hXn n : IsAEKolmogorovProcess (Xn n) P p q M := by
    refine ⟨fun t ω ↦ hX.mk X t ω, ?_, fun t ↦ by filter_upwards [hX.ae_eq_mk t] with ω hω using hω⟩
    constructor
    · exact fun s t ↦ hX.IsKolmogorovProcess_mk.measurablePair s t
    · exact fun s t ↦ hX.IsKolmogorovProcess_mk.kolmogorovCondition s t
    · exact hp_pos
    · exact hX.q_pos
  have hC' n : HasBoundedInternalCoveringNumber (Set.univ : Set (C n)) (c n) d := by
    have h := hC.hasBoundedCoveringNumber n
    refine fun ε hε ↦ ?_
    specialize h ε (hε.trans_eq ?_)
    · unfold EMetric.diam
      simp [iSup_subtype]
    refine le_of_eq_of_le ?_ h
    simp only [ENat.toENNReal_inj]
    unfold internalCoveringNumber
    simp only [Set.subset_univ, iInf_pos]
    classical
    refine le_antisymm ?_ ?_
    · simp only [le_iInf_iff]
      intro A hA hA_cover
      refine (iInf₂_le (A.subtype (C n) : Finset (C n)) (fun x _ ↦ ?_)).trans ?_
      · have ⟨c, hc_mem, hc_edist⟩ := hA_cover x x.2
        exact ⟨⟨c, hA hc_mem⟩, by simpa using hc_mem, hc_edist⟩
      · simp only [Finset.card_subtype, Nat.cast_le]
        exact Finset.card_filter_le _ _
    · simp only [le_iInf_iff]
      intro A hA_cover
      refine (iInf₂_le (A.image (fun x : C n ↦ (x : T))) (by simp)).trans ?_
      refine (iInf_le _ ?_).trans ?_
      · intro x hx_mem
        obtain ⟨c, hc_mem, hc⟩ := hA_cover ⟨x, hx_mem⟩ (Set.mem_univ _)
        exact ⟨c, by simpa using hc_mem, hc⟩
      · exact mod_cast Finset.card_image_le
  choose Z hZ hZ_eq hZ_holder
    using fun n ↦ exists_modification_holder (hC' n) (hXn n) (hc n) hd_pos hdq_lt
  have hZ_ae_eq : ∀ᵐ ω ∂P,
      ∀ n t (ht : t ∈ C n), Z n ⟨t, ht⟩ ω = Z (n + 1) ⟨t, hC.mono _ _ (Nat.le_succ _) ht⟩ ω := by
    rw [ae_all_iff]
    intro n
    suffices ∀ᵐ ω ∂P, ∀ (t : C n), Z n ⟨t, t.2⟩ ω
        = Z (n + 1) ⟨t, hC.mono _ _ (Nat.le_succ _) t.2⟩ ω by
      filter_upwards [this] with ω hω t ht using hω ⟨t, ht⟩
    refine indistinduishable_of_modification (ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_) ?_
    · obtain ⟨_, h⟩ :=  hZ_holder n β₀ hβ₀_pos hβ₀_lt ω
      exact h.continuous hβ₀_pos
    · obtain ⟨_, h⟩ :=  hZ_holder (n + 1) β₀ hβ₀_pos hβ₀_lt ω
      have h_cont := h.continuous hβ₀_pos
      fun_prop
    · intro t
      filter_upwards [hZ_eq n t, hZ_eq (n + 1) ⟨t, hC.mono _ _ (Nat.le_succ _) t.2⟩] with ω hω₁ hω₂
      exact hω₁.trans hω₂.symm
  let A := {ω | ∀ n t (ht : t ∈ C n),
    Z n ⟨t, ht⟩ ω = Z (n + 1) ⟨t, hC.mono _ _ (Nat.le_succ _) ht⟩ ω}
  have hA_eq_le {ω} (hω : ω ∈ A) {n m} (hnm : n ≤ m) (t : C n) :
      Z n ⟨t, t.2⟩ ω = Z m ⟨t, hC.mono _ _ hnm t.2⟩ ω := by
    induction m with
    | zero => simp only [nonpos_iff_eq_zero] at hnm; subst hnm; simp
    | succ m hm =>
      by_cases hnm' : n ≤ m
      · exact (hm hnm').trans (hω m t (hC.mono _ _ hnm' t.2))
      · have : n = m + 1 := by omega
        subst this
        rfl
  have hA : MeasurableSet A := by
    have : A = ⋂ n, {ω | ∀ t : C n,
      Z n ⟨t, t.2⟩ ω = Z (n + 1) ⟨t, hC.mono _ _ (Nat.le_succ _) t.2⟩ ω} := by ext; simp [A]
    rw [this]
    refine MeasurableSet.iInter (fun n ↦ ?_)
    refine StronglyMeasurable.measurableSet_eq_of_continuous (fun ω ↦ ?_) (fun ω ↦ ?_) ?_ ?_
    · obtain ⟨_, h⟩ :=  hZ_holder n β₀ hβ₀_pos hβ₀_lt ω
      exact h.continuous hβ₀_pos
    · obtain ⟨_, h⟩ :=  hZ_holder (n + 1) β₀ hβ₀_pos hβ₀_lt ω
      have h_cont := h.continuous hβ₀_pos
      fun_prop
    · exact fun t ↦ (hZ n t).stronglyMeasurable
    · exact fun t ↦ (hZ _ ⟨t, hC.mono _ _ (Nat.le_succ _) t.2⟩).stronglyMeasurable
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := hZ_ae_eq
  classical
  have h_mem t : ∃ n, t ∈ C n := by
    have ht : t ∈ ⋃ n, C n := hC.subset_iUnion (by simp : t ∈ Set.univ)
    simpa using ht
  let nt t := Nat.find (h_mem t)
  have hnt t : t ∈ C (nt t) := Nat.find_spec (h_mem t)
  let Y (t : T) (ω : Ω) : E := if ω ∈ A then Z (nt t) ⟨t, hnt t⟩ ω else Nonempty.some inferInstance
  have hY_eq {ω} (hω : ω ∈ A) n (t : T) (ht : t ∈ C n) : Y t ω = Z n ⟨t, ht⟩ ω := by
    simp only [hω, ↓reduceIte, Y]
    exact hA_eq_le hω (Nat.find_le ht) ⟨t, hnt t⟩
  refine ⟨Y, fun t ↦ Measurable.ite hA (hZ _ _) (by fun_prop), fun t ↦ ?_, ?_⟩
  · specialize hZ (nt t) ⟨t, hnt t⟩
    filter_upwards [hA_ae, hZ_eq (nt t) ⟨t, hnt t⟩] with ω hω hω₂
    simp only [hω, ↓reduceIte, hω₂, Y, A, Xn]
  · intro ω t
    refine ⟨C (nt t), (hC.isOpen (nt t)).mem_nhds (hnt t), ?_⟩
    intro β₀ hβ₀_pos hβ₀_lt
    by_cases hω : ω ∈ A
    swap
    · simp [hω, Y, HolderOnWith]
    obtain ⟨C', hC'⟩ := hZ_holder (nt t) β₀ hβ₀_pos hβ₀_lt ω
    refine ⟨C', ?_⟩
    intro s hs s' hs'
    simp only
    rw [hY_eq hω (nt t) s hs, hY_eq hω (nt t) s' hs']
    exact hC' ⟨s, hs⟩ ⟨s', hs'⟩

lemma exists_modification_holder_iSup {C : ℕ → Set T} {c : ℕ → ℝ≥0∞} {p q : ℕ → ℝ} {M : ℕ → ℝ≥0}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : ∀ n, IsAEKolmogorovProcess X P (p n) (q n) (M n)) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : ∀ n, d < q n) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (q n - d) / (p n)),
        ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · ω) U := by
  have hp_pos : ∀ n, 0 < p n := fun n ↦ (hX n).p_pos
  by_cases h_bdd : BddAbove (Set.range fun n ↦ (q n - d) / p n)
  swap
  · refine ⟨(hX 0).mk X, (hX 0).IsKolmogorovProcess_mk.measurable,
        fun t ↦ ((hX 0).ae_eq_mk t).symm, fun ω t β hβ_pos hβ_lt ↦ ?_⟩
    simp only [ciSup_of_not_bddAbove h_bdd, Real.sSup_empty] at hβ_lt
    norm_cast at hβ_lt
    exact absurd hβ_pos hβ_lt.not_gt
  have h_ratio_pos n : 0 < (q n - d) / p n := by
    have : 0 < q n - d := by bound
    specialize hp_pos n
    positivity
  let β : ℕ → ℝ≥0 := fun n ↦ ⟨(q n - d) / p n, (h_ratio_pos n).le⟩
  have hβ_pos : ∀ n, 0 < β n := fun n ↦ mod_cast h_ratio_pos n
  have h_exists := fun n ↦ exists_modification_holder' hC (hX n) hc hd_pos (hdq_lt n)
  choose Z hZ_meas hZ_ae_eq hZ_holder using h_exists
  have hZ_cont n ω : Continuous fun t ↦ Z n t ω := by
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    obtain ⟨U, hU_mem, hU⟩ := hZ_holder n ω t
    have hβ_pos_half : 0 < β n / 2 := by specialize hβ_pos n; positivity
    specialize hU (β n / 2) hβ_pos_half ?_
    · simp [β, h_ratio_pos]
    · obtain ⟨_, h⟩ := hU
      exact (h.continuousOn hβ_pos_half).continuousAt hU_mem
  have hZ_ae_eq' n : ∀ᵐ ω ∂P, ∀ t, Z n t ω = Z 0 t ω := by
    refine indistinduishable_of_modification (ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_) ?_
    · exact hZ_cont n ω
    · exact hZ_cont 0 ω
    · intro t
      filter_upwards [hZ_ae_eq n t, hZ_ae_eq 0 t] with ω hω₁ hω₂ using hω₁.trans hω₂.symm
  rw [← ae_all_iff] at hZ_ae_eq'
  let A := {ω | ∀ n t, Z n t ω = Z 0 t ω}
  have hA : MeasurableSet A := by
    have : A = ⋂ n, {ω | ∀ t, Z n t ω = Z 0 t ω} := by ext; simp [A]
    rw [this]
    refine MeasurableSet.iInter (fun n ↦ ?_)
    refine StronglyMeasurable.measurableSet_eq_of_continuous (fun ω ↦ ?_) (fun ω ↦ ?_) ?_ ?_
    · exact hZ_cont n ω
    · exact hZ_cont 0 ω
    · exact fun t ↦ (hZ_meas n t).stronglyMeasurable
    · exact fun t ↦ (hZ_meas 0 t).stronglyMeasurable
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := hZ_ae_eq'
  classical
  let Y (t : T) (ω : Ω) : E := if ω ∈ A then Z 0 t ω else Nonempty.some inferInstance
  refine ⟨Y, fun t ↦ Measurable.ite hA (hZ_meas 0 t) (by fun_prop), fun t ↦ ?_, ?_⟩
  · filter_upwards [hA_ae, hZ_ae_eq 0 t] with ω hω hω₂
    simpa only [hω, ↓reduceIte, Y] using hω₂
  · intro ω t β₀ hβ₀_pos hβ₀_lt
    by_cases hω : ω ∈ A
    swap; · exact ⟨.univ, by simp [hω, Y, HolderOnWith]⟩
    simp only [hω, ↓reduceIte, Y]
    obtain ⟨n, hn⟩ : ∃ n, β₀ < β n := by
      rwa [lt_ciSup_iff h_bdd] at hβ₀_lt
    refine ⟨(hZ_holder n ω t).choose, (hZ_holder n ω t).choose_spec.1, ?_⟩
    simp_rw [← hω n]
    exact (hZ_holder n ω t).choose_spec.2 β₀ hβ₀_pos hn

end EMetricSpace

end ProbabilityTheory
