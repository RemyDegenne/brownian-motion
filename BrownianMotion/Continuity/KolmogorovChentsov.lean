/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.EDistEgorov
import BrownianMotion.Continuity.HasBoundedInternalCoveringNumber
import BrownianMotion.Continuity.IsKolmogorovProcess

/-!
# Kolmogorov-Chentsov theorem

-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section aux

section EDistTendstoInMeasure

variable {α ι κ E : Type*} {m : MeasurableSpace α} {μ : Measure α}
variable [EMetricSpace E]
variable {f : ℕ → α → E} {g : α → E}

-- copy of a Mathlib lemma, but with `edist` instead of `dist`
theorem tendstoInMeasure_of_tendsto_ae_of_stronglyMeasurable' [IsFiniteMeasure μ]
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
      ∀ ε, 0 < ε → Tendsto (fun i => μ { x | ε ≤ edist (f i x) (g x) }) atTop (𝓝 0) := by
  refine fun ε hε => ENNReal.tendsto_atTop_zero.mpr fun δ hδ => ?_
  by_cases hδi : δ = ∞
  · simp only [hδi, imp_true_iff, le_top, exists_const]
  lift δ to ℝ≥0 using hδi
  rw [gt_iff_lt, ENNReal.coe_pos, ← NNReal.coe_pos] at hδ
  obtain ⟨t, _, ht, hunif⟩ := tendstoUniformlyOn_of_ae_tendsto''' hf hg hfg hδ
  rw [ENNReal.ofReal_coe_nnreal] at ht
  rw [EMetric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif ε hε)
  refine ⟨N, fun n hn => ?_⟩
  suffices { x : α | ε ≤ edist (f n x) (g x) } ⊆ t from (measure_mono this).trans ht
  rw [← Set.compl_subset_compl]
  intro x hx
  rw [Set.mem_compl_iff, Set.notMem_setOf_iff, edist_comm, not_le]
  exact hN n hn x hx

end EDistTendstoInMeasure

theorem lintegral_eq_zero_of_zero_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} : f =ᵐ[μ] 0 →  ∫⁻ a, f a ∂μ = 0 :=
  fun h ↦ (lintegral_congr_ae h).trans lintegral_zero

-- copied from Etienne's fork
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

lemma _root_.MeasureTheory.Measure.measure_inter_eq_of_measure_eq_measure_univ
    {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) (h : μ t = μ .univ)
    (ht_ne_top : μ t ≠ ∞) : μ (t ∩ s) = μ s := by
  rw [Measure.measure_inter_eq_of_measure_eq hs h (Set.subset_univ _) ht_ne_top, Set.univ_inter]

lemma _root_.MeasureTheory.Measure.measure_inter_eq_of_ae
    {α : Type*} {_ : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
    {s t : Set α} (hs : MeasurableSet s) (ht : NullMeasurableSet t μ) (h : ∀ᵐ a ∂μ, a ∈ t)
    (ht_ne_top : μ t ≠ ∞) : μ (t ∩ s) = μ s := by
  rw [Measure.measure_inter_eq_of_measure_eq hs _ (Set.subset_univ _) ht_ne_top, Set.univ_inter]
  rwa [ae_iff_measure_eq] at h
  exact ht

theorem biSup_prod' {α β γ : Type*} [CompleteLattice α] {f : β → γ → α} {s : Set β} {t : Set γ} :
  ⨆ x ∈ s ×ˢ t, f x.1 x.2 = ⨆ a ∈ s, ⨆ b ∈ t, f a b := biSup_prod

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

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}

section PseudoEMetricSpace

variable [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]

lemma lintegral_div_edist_le_sum_integral_edist_le (hT : EMetric.diam (Set.univ : Set T) < ∞)
    (hX : IsKolmogorovProcess X P p q M)
    (hβ : 0 < β) (hp : 0 < p) (hq : 0 < q) {J : Set T} [Countable J] :
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
    (hβ_pos : 0 < β) (T' : Set T) [hT' : Finite T'] :
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
  apply le_trans
    (lintegral_div_edist_le_sum_integral_edist_le h_diam hX hβ_pos hp_pos hq_pos)
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
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q) (hβ_pos : 0 < β)
    (T' : Set T) [Countable T'] :
    ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ M * constL T c d p q β := by
  let K := (FiniteExhaustion.choice T')
  simp only [iSup_subtype, Subtype.edist_mk_mk, ← biSup_prod', ← (K.prod K).iUnion_eq,
    Set.mem_iUnion, iSup_exists, K.prod_apply, iSup_comm (ι' := ℕ)]
  simp only [biSup_prod]
  simp only [← iSup_subtype'']
  rw [MeasureTheory.lintegral_iSup', iSup_le_iff]
  · exact fun n ↦ finite_kolmogorov_chentsov hT hX hd_pos hp_pos hdq_lt hβ_pos (K n)
  · intro n
    fun_prop (disch := exact hX)
  · filter_upwards with ω
    intro _ _ h
    simp only [iSup_subtype, ← biSup_prod']
    exact iSup_le_iSup_of_subset (Set.prod_mono (K.subset h) (K.subset h))

end PseudoEMetricSpace

section EMetricSpace

variable [EMetricSpace E] [MeasurableSpace E] [BorelSpace E]

lemma ae_iSup_rpow_edist_div_lt_top (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsMeasurableKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    {T' : Set T} (hT' : T'.Countable) :
    ∀ᵐ ω ∂P, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) < ∞ := by
  have : Countable T' := hT'
  refine ae_lt_top' ?_ ((countable_kolmogorov_chentsov hT hX.IsKolmogorovProcess hd_pos hp_pos
    hdq_lt hβ_pos T').trans_lt ?_).ne
  · refine AEMeasurable.iSup (fun s ↦ AEMeasurable.iSup (fun t ↦ ?_))
    exact AEMeasurable.div (hX.measurable_edist.aemeasurable.pow_const _) (by fun_prop)
  · exact ENNReal.mul_lt_top (by simp) (constL_lt_top hc hd_pos hp_pos hdq_lt hβ_pos hβ_lt)

omit [MeasurableSpace E] [BorelSpace E] in
def holderSet (X : T → Ω → E) (T' : Set T) (p β : ℝ) : Set Ω :=
  {ω | ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) < ∞
      ∧ ∀ (s t : T'), edist s t = 0 → edist (X s ω) (X t ω) = 0}

omit [MeasurableSpace E] [BorelSpace E] in
lemma IsMeasurableKolmogorovProcess.measurableSet_holderSet
    (hX : IsMeasurableKolmogorovProcess X P p q M)
    {T' : Set T} (hT' : T'.Countable) :
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
    letI C ω := ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
    UniformContinuous fun (t : T') ↦ X t ω :=
      (holderWith_of_mem_holderSet hT hd_pos hp_pos hβ_pos hω).uniformContinuous hβ_pos

omit [MeasurableSpace E] [BorelSpace E] in
lemma continuous_of_mem_holderSet (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hβ_pos : 0 < β)
    {T' : Set T} {ω : Ω} (hω : ω ∈ holderSet X T' p β) :
    letI C ω := ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
    Continuous fun (t : T') ↦ X t ω :=
  (holderWith_of_mem_holderSet hT hd_pos hp_pos hβ_pos hω).continuous hβ_pos

lemma tendstoInMeasure_of_mem_holderSet
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsMeasurableKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hβ_pos : 0 < β)
    {T' : Set T} {u : ℕ → T'} {t : T}
    (hu : Tendsto (fun n ↦ (u n : T)) atTop (𝓝 t)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun n ↦ P {ω | ε ≤ edist (X (u n) ω) (X t ω)}) atTop (𝓝 0) := by
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
    sorry -- no problem, except for the lack of `ContinuousMul ℝ≥0∞`
  suffices Tendsto (fun n ↦ P {ω | ε ^ p ≤ edist (X (u n) ω) (X t ω) ^ p}) atTop (𝓝 0) by
    convert this using 3 with n
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [ENNReal.rpow_le_rpow_iff hp_pos]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le') ?_
    (h := fun n ↦ (ε ^ p)⁻¹ * ∫⁻ ω, edist (X (u n) ω) (X t ω) ^ p ∂P)
  · sorry
  · refine fun n ↦ (meas_ge_le_lintegral_div ?_ ?_ ?_).trans_eq ?_
    · exact ((hX.measurable_edist).pow_const _).aemeasurable
    · simp [hε.ne', hp_pos.le]
    · simp [hε.ne', hε_top]
    · rw [ENNReal.div_eq_inv_mul]

-- TODO: I (Rémy) gave up on separability of `E`. The measurability checks are driving me crazy.
variable [Nonempty E] [SecondCountableTopology T] [CompleteSpace E] [SecondCountableTopology E]
  [IsFiniteMeasure P]

lemma _root_.Dense.holderWith_extend {A : Set T} (hA : Dense A) {f : A → E} {C β : ℝ≥0}
    (hf : HolderWith C β f) :
    HolderWith C β (hA.extend f) := by
  sorry

-- TODO: in this lemma we use the notion of convergence in measure, but since we use `edist` and not
-- `dist`, we can't use the existing definition `TendstoInMeasure`.
lemma exists_modification_holder_aux (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsMeasurableKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  -- Let `T'` be a countable dense subset of `T`
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  have : Countable T' := hT'_countable
  have h_ae_zero : ∀ᵐ ω ∂P, ∀ (s t : T'), edist s t = 0 → edist (X s ω) (X t ω) = 0 := by
    simp_rw [ae_all_iff]
    exact fun s t hst ↦ hX.IsKolmogorovProcess.edist_eq_zero hp_pos (hd_pos.trans hdq_lt) hst
  -- For each `ω`, `C ω < ∞` is a bound on `edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)`
  let C ω := ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
  have hC_lt_top : ∀ᵐ ω ∂P, C ω < ∞ :=
    ae_iSup_rpow_edist_div_lt_top hT hX hc hd_pos hp_pos hdq_lt hβ_pos hβ_lt hT'_countable
  -- Let `A` be the event that `C ω < ∞` and `X s ω = X t ω` for `edist s t = 0`.
  -- This is an event of probability 1.
  let A := holderSet X T' p β
  have hA : MeasurableSet A := hX.measurableSet_holderSet hT'_countable
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := by
    filter_upwards [hC_lt_top, h_ae_zero] with ω hω₁ hω₂ using ⟨hω₁, hω₂⟩
  have hPA {s : Set Ω} (hs : MeasurableSet s) : P (s ∩ A) = P s := by
    rw [Set.inter_comm,
      Measure.measure_inter_eq_of_ae hs hA.nullMeasurableSet hA_ae (measure_ne_top _ _)]
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
    exact hT'_dense.extend_eq (continuous_of_mem_holderSet hT hd_pos hp_pos hβ_pos hω) t
  have hY_unif ω : UniformContinuous (fun t ↦ Y t ω) := by
    by_cases hω : ω ∈ A
    · simp only [hω, ↓reduceIte, Y]
      refine hT'_dense.uniformContinuous_extend ?_
      exact uniformContinuous_of_mem_holderSet hT hd_pos hp_pos hβ_pos hω
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
    have h_tendsto_X (ε : ℝ≥0∞) (hε : 0 < ε) :
        Tendsto (fun n ↦ P {ω | ε ≤ edist (X (u n) ω) (X t ω)}) atTop (𝓝 0) :=
      tendstoInMeasure_of_mem_holderSet hT hX hd_pos hp_pos hβ_pos hu hε
    -- `Y (u n)` converges in measure to `Y t`
    have h_tendsto_Y (ε : ℝ≥0∞) (hε : 0 < ε) :
        Tendsto (fun n ↦ P {ω | ε ≤ edist (Y (u n) ω) (Y t ω)}) atTop (𝓝 0) := by
      have h_ae ω : Tendsto (fun n ↦ Y (u n) ω) atTop (𝓝 (Y t ω)) :=
        ((hY_cont ω).tendsto t).comp hu
      refine tendstoInMeasure_of_tendsto_ae_of_stronglyMeasurable' ?_ ?_ ?_ ε hε
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
      _ = P {ω | ε / 2 + ε / 2 ≤ edist (Y (u n) ω) (Y t ω) + edist (X (u n) ω) (X t ω)} := by
        simp only [ENNReal.add_halves]
        rw [hPA]
        refine measurableSet_le (by fun_prop) ?_
        exact ((hY (u n)).edist (hY t)).add ((hX.measurable (u n)).edist (hX.measurable t))
      _ ≤ P ({ω | ε / 2 ≤ edist (Y (u n) ω) (Y t ω)}
          ∪ {ω | ε / 2 ≤ edist (X (u n) ω) (X t ω)}) := by
          gcongr
          intro ω
          simp only [ENNReal.add_halves, Set.mem_setOf_eq, Set.mem_union]
          contrapose!
          intro ⟨h1, h2⟩
          calc _
          _ < ε / 2 + ε / 2 := by gcongr
          _ = ε := by simp
      _ ≤ P {ω | ε / 2 ≤ edist (Y (u n) ω) (Y t ω)}
          + P {ω | ε / 2 ≤ edist (X (u n) ω) (X t ω)} := measure_union_le _ _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le') hP_le
    rw [← add_zero (0 : ℝ≥0∞)]
    exact Tendsto.add (h_tendsto_Y (ε / 2) (ENNReal.half_pos hε.ne'))
      (h_tendsto_X (ε / 2) (ENNReal.half_pos hε.ne'))
  · by_cases hω : ω ∈ A
    swap; · simp only [hω, ↓reduceIte, Y]; exact ⟨0, by simp [HolderWith]⟩
    simp only [hω, ↓reduceIte, Y, A]
    refine ⟨(C ω ^ p⁻¹).toNNReal, ?_⟩
    refine hT'_dense.holderWith_extend (holderWith_of_mem_holderSet hT hd_pos hp_pos hβ_pos hω)

lemma exists_modification_holder (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsMeasurableKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p),
        ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  sorry

lemma exists_modification_holder' {C : ℕ → Set T} {c : ℕ → ℝ≥0∞}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : IsMeasurableKolmogorovProcess X P p q M) (hp_pos : 0 < p) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p),
        ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  sorry

lemma exists_modification_holder_iSup {C : ℕ → Set T} {c : ℕ → ℝ≥0∞} {p q : ℕ → ℝ} {M : ℕ → ℝ≥0}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : ∀ n, IsMeasurableKolmogorovProcess X P (p n) (q n) (M n))
    (hp_pos : ∀ n, 0 < p n) (hdq_lt : ∀ n, d < q n) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < ⨆ n, (q n - d) / (p n)),
        ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  sorry

end EMetricSpace

end ProbabilityTheory
