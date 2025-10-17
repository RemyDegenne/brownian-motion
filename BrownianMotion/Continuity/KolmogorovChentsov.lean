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

lemma UniformContinuous.exists_tendsto {α β : Type*} [UniformSpace α] [FirstCountableTopology α]
    [UniformSpace β] [CompleteSpace β] {s : Set α} (hs : Dense s)
    {f : s → β} (hf : UniformContinuous f) (a : α) :
    ∃ c, Tendsto f (comap Subtype.val (𝓝 a)) (𝓝 c) := by
  have (u : ℕ → s) (hu : Tendsto (fun n ↦ (u n : α)) atTop (𝓝 a)) :
      ∃ c, Tendsto (f ∘ u) atTop (𝓝 c) := by
    refine cauchySeq_tendsto_of_complete ?_
    refine hf.comp_cauchySeq ?_
    have h_cauchy := hu.cauchySeq
    rw [cauchySeq_iff] at h_cauchy
    rw [cauchySeq_iff, uniformity_subtype]
    simp only [mem_comap, ge_iff_le, forall_exists_index, and_imp] at h_cauchy ⊢
    intro V s hs hsV
    obtain ⟨N, hN⟩ := h_cauchy s hs
    exact ⟨N, fun k hNk l hNl ↦ hsV (hN k hNk l hNl)⟩
  choose c hc using this
  obtain ⟨u, hu⟩ : ∃ u : ℕ → s, Tendsto (fun n ↦ (u n : α)) atTop (𝓝 a) := by
    have ht_mem_closure : a ∈ closure s := by simp [hs.closure_eq]
    rw [mem_closure_iff_seq_limit] at ht_mem_closure
    obtain ⟨u, hu⟩ := ht_mem_closure
    exact ⟨fun n ↦ ⟨u n, hu.1 n⟩, hu.2⟩
  refine ⟨c u hu, ?_⟩
  refine tendsto_of_seq_tendsto fun v hv' ↦ ?_
  have hv : Tendsto (fun n ↦ (v n : α)) atTop (𝓝 a) := by rwa [tendsto_comap_iff] at hv'
  refine (hc u hu).congr_uniformity ?_
  change Tendsto ((fun p ↦ (f p.1, f p.2)) ∘ (fun n ↦ (u n, v n))) atTop (uniformity β)
  rw [UniformContinuous] at hf
  refine hf.comp ?_
  have hu' : Tendsto u atTop (comap Subtype.val (𝓝 a)) := by rwa [tendsto_comap_iff]
  have hv' : Tendsto v atTop (comap Subtype.val (𝓝 a)) := by rwa [tendsto_comap_iff]
  refine Tendsto.mono_right (hu'.prodMk hv') ?_
  rw [← Filter.comap_prodMap_prod, ← nhds_prod_eq, uniformity_subtype]
  refine comap_mono ?_
  exact nhds_le_uniformity a

theorem measurable_limUnder_of_exists_tendsto {ι X E : Type*}
    {mX : MeasurableSpace X} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [MeasurableSpace E] [BorelSpace E] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → X → E} [hE : Nonempty E]
    (h_conv : ∀ x, ∃ c, Tendsto (f · x) l (𝓝 c)) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x ↦ limUnder l (f · x)) := by
  obtain rfl | hl := eq_or_neBot l
  · simp [limUnder, Filter.map_bot]
  refine measurable_of_tendsto_metrizable' l hf (tendsto_pi_nhds.mpr fun x ↦ ?_)
  exact tendsto_nhds_limUnder (h_conv x)

theorem measurable_limUnder {ι X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → X → E} [hE : Nonempty E] (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x ↦ limUnder l (f · x)) := by
  let conv := {x | ∃ c, Tendsto (f · x) l (𝓝 c)}
  have mconv : MeasurableSet conv := measurableSet_exists_tendsto hf
  have : (fun x ↦ _root_.limUnder l (f · x)) = ((↑) : conv → X).extend
      (fun x ↦ _root_.limUnder l (f · x)) (fun _ ↦ hE.some) := by
    ext x
    by_cases hx : x ∈ conv
    · rw [Function.extend_val_apply hx]
    · rw [Function.extend_val_apply' hx, limUnder_of_not_tendsto hx]
  rw [this]
  refine (MeasurableEmbedding.subtype_coe mconv).measurable_extend ?_ measurable_const
  exact measurable_limUnder_of_exists_tendsto (fun x ↦ x.2)
    (fun i ↦ (hf i).comp measurable_subtype_coe)

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

instance {α : Type*} {s : Set α} : RelHomClass (FiniteExhaustion s) LE.le HasSubset.Subset where
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
        refine Set.image_mono fun _ h ↦ ?_
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
    simp only [add_neg_cancel, zero_add]
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
  simp only [constL, ← ENNReal.tsum_mul_left, ge_iff_le] at *
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
  · simp only [not_ne_iff.mp hc, ne_eq, ENNReal.rpow_eq_zero_iff, OfNat.ofNat_ne_zero, false_and,
      ENNReal.ofNat_ne_top, or_self, not_false_eq_true, ENNReal.mul_top, ENNReal.toReal_top,
      Real.logb_zero, zero_add]
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
  · simp only [ENNReal.toReal_mul, hc_zero, mul_zero, zero_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_pow, ENNReal.toReal_inv, inv_pow, mul_inv_rev, inv_inv, Real.logb_zero,
      ENNReal.ofReal_zero, zero_add]
    gcongr
    exact zero_le _
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
lemma exists_tendsto_of_mem_holderSet [CompleteSpace E]
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hβ_pos : 0 < β)
    {T' : Set T} (hT'_dense : Dense T') {ω : Ω} (hω : ω ∈ holderSet X T' p β) (t : T) :
    ∃ c, Tendsto (fun t' : T' ↦ X t' ω) (comap Subtype.val (𝓝 t)) (𝓝 c) :=
  (uniformContinuous_of_mem_holderSet hT hd_pos hp_pos hβ_pos hω).exists_tendsto hT'_dense t

omit [MeasurableSpace E] [BorelSpace E] in
lemma IsKolmogorovProcess.tendstoInMeasure_of_mem_holderSet
    (hX : IsKolmogorovProcess X P p q M)
    (hq_pos : 0 < q) {T' : Set T} {u : ℕ → T'} {t : T}
    (hu : Tendsto (fun n ↦ (u n : T)) atTop (𝓝 t)) :
    TendstoInMeasure P (fun n ↦ X (u n)) atTop (X t) := by
  refine tendstoInMeasure_of_ne_top fun ε hε hε_top ↦ ?_
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

variable [hE : Nonempty E] [SecondCountableTopology T] [CompleteSpace E]

section FromPR

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [PseudoEMetricSpace E]
variable {f : ℕ → α → E} {g : α → E}

theorem tendstoInMeasure_of_tendsto_ae_of_measurable_edist [IsFiniteMeasure μ]
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : TendstoInMeasure μ f atTop g :=
  sorry -- in a Mathlib PR

end FromPR

lemma limUnder_prod {α β X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [Nonempty Y] [T2Space X] [T2Space Y] {f : Filter α} {f' : Filter β}
    [NeBot f] [NeBot f'] {g : α → X} {g' : β → Y}
    (h₁ : ∃ x, Tendsto g f (𝓝 x)) (h₂ : ∃ x', Tendsto g' f' (𝓝 x')) :
    limUnder (f ×ˢ f') (fun x ↦ (g x.1, g' x.2)) = (limUnder f g, limUnder f' g') := by
  rw [Filter.Tendsto.limUnder_eq]
  rw [nhds_prod_eq]
  apply Filter.Tendsto.prodMk
  · exact (tendsto_nhds_limUnder h₁).comp tendsto_fst
  · exact (tendsto_nhds_limUnder h₂).comp tendsto_snd

noncomputable
def _root_.Set.indicatorSome {α E : Type*} [hE : Nonempty E] (s : Set α) (f : α → E) : α → E :=
  haveI := Classical.decPred (· ∈ s)
  fun a ↦ if a ∈ s then f a else hE.some

section IndicatorProcess

variable {A : Set Ω}

noncomputable
def indicatorProcess (X : T → Ω → E) (A : Set Ω) : T → Ω → E := fun t ω ↦ A.indicatorSome (X t) ω

omit [PseudoMetricSpace T] [EMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology T] [CompleteSpace E] in
@[simp]
lemma indicatorProcess_apply (X : T → Ω → E) (A : Set Ω) (t : T) (ω : Ω) [Decidable (ω ∈ A)] :
    indicatorProcess X A t ω = if ω ∈ A then X t ω else hE.some := by
  simp [indicatorProcess, Set.indicatorSome]

omit [PseudoMetricSpace T] [EMetricSpace E] [BorelSpace E] [SecondCountableTopology T]
  [CompleteSpace E] in
lemma measurable_indicatorProcess (hA : MeasurableSet A) (hX : ∀ t, Measurable (X t)) (t : T) :
    Measurable (indicatorProcess X A t) :=
  Measurable.ite hA (hX t) measurable_const

omit [PseudoMetricSpace T] [EMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology T] [CompleteSpace E] in
lemma induction_indicatorProcess (p : (T → E) → Prop)
    (hp_const : p (fun _ ↦ hE.some)) (A : Set Ω) (ω : Ω) (hpX : p (X · ω)) :
    p (indicatorProcess X A · ω) := by
  by_cases hω : ω ∈ A
  · simp only [hω, indicatorProcess, Set.indicatorSome]; exact hpX
  · simp only [hω, indicatorProcess, Set.indicatorSome]; exact hp_const

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology T] [CompleteSpace E] in
lemma uniformContinuous_subtype_indicatorProcess {T' : Set T} (ω : Ω)
    (hX : UniformContinuous fun (t : T') ↦ X t ω) :
    UniformContinuous fun (t : T') ↦ indicatorProcess X A t ω :=
  induction_indicatorProcess (p := fun f ↦ UniformContinuous fun (t : T') ↦ f t)
    uniformContinuous_const A ω hX

omit [CompleteSpace E] in
lemma measurable_pair_indicatorProcess {T₁ T₂ : Type*}
    [PseudoMetricSpace T₁] [PseudoMetricSpace T₂] {X₁ : T₁ → Ω → E} {X₂ : T₂ → Ω → E}
    (hX₁ : ∀ t, Measurable (X₁ t)) (hX₂ : ∀ t, Measurable (X₂ t))
    (hX₁₂ : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X₁ i ω, X₂ j ω))
    {A₁ A₂ : Set Ω} (hA₁ : MeasurableSet A₁) (hA₂ : MeasurableSet A₂) (s : T₁) (t : T₂) :
    Measurable[_, borel (E × E)]
      (fun ω ↦ (indicatorProcess X₁ A₁ s ω, indicatorProcess X₂ A₂ t ω)) := by
  classical
  have h_eq : (fun ω ↦ (indicatorProcess X₁ A₁ s ω, indicatorProcess X₂ A₂ t ω)) =
      fun ω ↦ if ω ∈ A₁ then if ω ∈ A₂ then (X₁ s ω, X₂ t ω) else (X₁ s ω, hE.some)
        else if ω ∈ A₂ then (hE.some, X₂ t ω) else (hE.some, hE.some) := by
    ext ω <;> by_cases hω₁ : ω ∈ A₁ <;> by_cases hω₂ : ω ∈ A₂
      <;> simp [indicatorProcess, Set.indicatorSome, hω₁, hω₂]
  rw [h_eq]
  borelize (E × E)
  refine Measurable.ite hA₁ ?_ ?_
  · refine Measurable.ite hA₂ (hX₁₂ s t) ?_
    change Measurable ((fun x : E ↦ (x, hE.some)) ∘ X₁ s)
    refine Measurable.comp ?_ (hX₁ _)
    clear hX₁₂ -- Lean crashes without this
    fun_prop
  · refine Measurable.ite hA₂ ?_ measurable_const
    change Measurable ((fun x : E ↦ (hE.some, x)) ∘ X₂ t)
    refine Measurable.comp ?_ (hX₂ _)
    clear hX₁₂
    fun_prop

omit [CompleteSpace E] in
lemma measurable_edist_indicatorProcess {T₁ T₂ : Type*}
    [PseudoMetricSpace T₁] [PseudoMetricSpace T₂] {X₁ : T₁ → Ω → E} {X₂ : T₂ → Ω → E}
    (hX₁ : ∀ t, Measurable (X₁ t)) (hX₂ : ∀ t, Measurable (X₂ t))
    (hX₁₂ : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X₁ i ω, X₂ j ω))
    {A₁ A₂ : Set Ω} (hA₁ : MeasurableSet A₁) (hA₂ : MeasurableSet A₂) (s : T₁) (t : T₂) :
    Measurable (fun ω ↦ edist (indicatorProcess X₁ A₁ s ω) (indicatorProcess X₂ A₂ t ω)) := by
  borelize (E × E)
  refine StronglyMeasurable.measurable ?_
  exact continuous_edist.stronglyMeasurable.comp_measurable
    (measurable_pair_indicatorProcess hX₁ hX₂ hX₁₂ hA₁ hA₂ s t)

end IndicatorProcess

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
lemma measurable_pair_limUnder_comap {T₁ T₂ : Type*}
    [PseudoEMetricSpace T₁] [PseudoEMetricSpace T₂] {X₁ : T₁ → Ω → E} {X₂ : T₂ → Ω → E}
    {T₁' : Set T₁} (hT₁'_dense : Dense T₁') {T₂' : Set T₂} (hT₂'_dense : Dense T₂')
    (hX₁₂ : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X₁ i ω, X₂ j ω))
    (s : T₁) (t : T₂)
    (hX₁_tendsto : ∀ ω, ∃ x, Tendsto (fun t' : T₁' ↦ X₁ t' ω) (comap Subtype.val (𝓝 s)) (𝓝 x))
    (hX₂_tendsto : ∀ ω, ∃ x, Tendsto (fun t' : T₂' ↦ X₂ t' ω) (comap Subtype.val (𝓝 t)) (𝓝 x)) :
    Measurable[_, borel (E × E)] fun ω ↦
      (limUnder (comap Subtype.val (𝓝 s)) fun t' : T₁' ↦ X₁ t' ω,
        limUnder (comap Subtype.val (𝓝 t)) fun t' : T₂' ↦ X₂ t' ω) := by
  have : @NeBot { x // x ∈ T₁' } (comap Subtype.val (𝓝 s)) := by
    apply IsDenseInducing.comap_nhds_neBot (Dense.isDenseInducing_val hT₁'_dense)
  have : @NeBot { x // x ∈ T₂' } (comap Subtype.val (𝓝 t)) := by
    apply IsDenseInducing.comap_nhds_neBot (Dense.isDenseInducing_val hT₂'_dense)
  conv =>
    enter [1, ω]
    rw [← limUnder_prod]
    rfl
    tactic => exact hX₁_tendsto ω
    tactic => exact hX₂_tendsto ω
  let f (x : T₁' × T₂') (ω : Ω) := (X₁ x.1 ω, X₂ x.2 ω)
  borelize (E × E)
  refine measurable_limUnder_of_exists_tendsto (f := f) (fun ω ↦ ?_) (fun i ↦ hX₁₂ i.1 i.2)
  obtain ⟨c₀, h₀⟩ := hX₁_tendsto ω
  obtain ⟨c₁, h₁⟩ := hX₂_tendsto ω
  use (c₀, c₁)
  rw [nhds_prod_eq]
  apply Filter.Tendsto.prodMk
  · exact h₀.comp tendsto_fst
  · exact h₁.comp tendsto_snd

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
lemma measurable_edist_limUnder_comap {T₁ T₂ : Type*}
    [PseudoEMetricSpace T₁] [PseudoEMetricSpace T₂] {X₁ : T₁ → Ω → E} {X₂ : T₂ → Ω → E}
    {T₁' : Set T₁} (hT₁'_dense : Dense T₁') {T₂' : Set T₂} (hT₂'_dense : Dense T₂')
    (hX₁₂ : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X₁ i ω, X₂ j ω))
    (s : T₁) (t : T₂)
    (hX₁_tendsto : ∀ ω, ∃ x, Tendsto (fun t' : T₁' ↦ X₁ t' ω) (comap Subtype.val (𝓝 s)) (𝓝 x))
    (hX₂_tendsto : ∀ ω, ∃ x, Tendsto (fun t' : T₂' ↦ X₂ t' ω) (comap Subtype.val (𝓝 t)) (𝓝 x)) :
    Measurable fun ω ↦ edist
      (limUnder (comap Subtype.val (𝓝 s)) fun t' : T₁' ↦ X₁ t' ω)
        (limUnder (comap Subtype.val (𝓝 t)) fun t' : T₂' ↦ X₂ t' ω) := by
  borelize (E × E)
  refine StronglyMeasurable.measurable ?_
  exact continuous_edist.stronglyMeasurable.comp_measurable
    (measurable_pair_limUnder_comap hT₁'_dense hT₂'_dense hX₁₂ s t hX₁_tendsto hX₂_tendsto)

noncomputable
def holderModification (X : T → Ω → E) (β : ℝ≥0) (p : ℝ) (T' : Set T) (hT'_dense : Dense T') :
    T → Ω → E :=
  fun t ω ↦ hT'_dense.extend (fun t' : T' ↦ indicatorProcess X (holderSet X T' p β) t' ω) t

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology T] [CompleteSpace E] in
lemma holderModification_eq (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M) (hd_pos : 0 < d) (hβ_pos : 0 < β)
    {T' : Set T} (hT'_dense : Dense T') (t' : T') {ω : Ω} (hω : ω ∈ holderSet X T' p β) :
    holderModification X β p T' hT'_dense t' ω = X t' ω := by
  simp only [holderModification, indicatorProcess, Set.indicatorSome, hω, ↓reduceIte]
  refine hT'_dense.extend_eq ?_ _
  exact continuous_of_mem_holderSet hT hd_pos hX.p_pos hβ_pos hω

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology T] in
lemma exists_tendsto_indicatorProcess_holderSet
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M) (hd_pos : 0 < d) (hβ_pos : 0 < β)
    {T' : Set T} (hT'_dense : Dense T') (t : T) (ω : Ω) :
    ∃ c, Tendsto (fun x : T' ↦ indicatorProcess X (holderSet X T' p β) x ω)
      (comap Subtype.val (𝓝 t)) (𝓝 c) := by
  by_cases hω : ω ∈ holderSet X T' p β
  · simp only [hω, ↓reduceIte, Set.indicatorSome, indicatorProcess]
    exact exists_tendsto_of_mem_holderSet hT hd_pos hX.p_pos hβ_pos hT'_dense hω t
  · simp only [hω, ↓reduceIte, Set.indicatorSome, indicatorProcess]
    exact ⟨hE.some, tendsto_const_nhds⟩

omit [SecondCountableTopology T] in
lemma measurable_holderModification (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hβ_pos : 0 < β)
    {T' : Set T} (hT'_dense : Dense T') (hT'_countable : T'.Countable) (t : T) :
    Measurable (holderModification X β p T' hT'_dense t) := by
  refine measurable_limUnder_of_exists_tendsto
    (f := fun (t' : T') ω ↦ (holderSet X T' p β).indicatorSome (X t') ω) ?_ (fun t ↦ ?_)
  · exact exists_tendsto_indicatorProcess_holderSet hT hX hd_pos hβ_pos hT'_dense t
  · exact Measurable.ite (hX.measurableSet_holderSet hT'_countable) (hX.measurable t)
      measurable_const

lemma measurable_pair_holderModification {T₁ T₂ : Type*}
    [PseudoMetricSpace T₁] [PseudoMetricSpace T₂]
    {X₁ : T₁ → Ω → E} {X₂ : T₂ → Ω → E} {c₁ c₂ : ℝ≥0∞} {p₁ p₂ q₁ q₂ d₁ d₂ : ℝ} {M₁ M₂ β₁ β₂ : ℝ≥0}
    (hT₁ : HasBoundedInternalCoveringNumber (Set.univ : Set T₁) c₁ d₁)
    (hT₂ : HasBoundedInternalCoveringNumber (Set.univ : Set T₂) c₂ d₂)
    (hX₁ : IsKolmogorovProcess X₁ P p₁ q₁ M₁)
    (hX₂ : IsKolmogorovProcess X₂ P p₂ q₂ M₂)
    (hd₁_pos : 0 < d₁) (hd₂_pos : 0 < d₂)
    (hβ₁_pos : 0 < β₁) (hβ₂_pos : 0 < β₂)
    {T₁' : Set T₁} (hT₁'_dense : Dense T₁') (hT₁'_countable : T₁'.Countable)
    {T₂' : Set T₂} (hT₂'_dense : Dense T₂') (hT₂'_countable : T₂'.Countable)
    (hX₁₂ : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X₁ i ω, X₂ j ω))
    (s : T₁) (t : T₂) :
    Measurable[_, borel (E × E)]
      (fun ω ↦ (holderModification X₁ β₁ p₁ T₁' hT₁'_dense s ω,
        holderModification X₂ β₂ p₂ T₂' hT₂'_dense t ω)) := by
  simp only [Dense.extend, IsDenseInducing.extend, holderModification]
  refine measurable_pair_limUnder_comap hT₁'_dense hT₂'_dense
    (X₁ := indicatorProcess X₁ (holderSet X₁ T₁' p₁ β₁)) (fun s t ↦ ?_) s t (fun ω ↦ ?_) fun ω ↦ ?_
  · exact measurable_pair_indicatorProcess (hX₁.measurable) (hX₂.measurable) hX₁₂
      (hX₁.measurableSet_holderSet hT₁'_countable)
      (hX₂.measurableSet_holderSet hT₂'_countable) s t
  · exact exists_tendsto_indicatorProcess_holderSet hT₁ hX₁ hd₁_pos hβ₁_pos hT₁'_dense s ω
  · exact exists_tendsto_indicatorProcess_holderSet hT₂ hX₂ hd₂_pos hβ₂_pos hT₂'_dense t ω

omit [SecondCountableTopology T] in
lemma measurable_pair_holderModification_self
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hβ_pos : 0 < β)
    {T' : Set T} (hT'_dense : Dense T') (hT'_countable : T'.Countable)
    [∀ ω, Decidable (ω ∈ holderSet X T' p β)]
    (s t : T) :
    Measurable[_, borel (E × E)]
      (fun ω ↦ (holderModification X β p T' hT'_dense s ω,
        holderModification X β p T' hT'_dense t ω)) :=
  measurable_pair_holderModification hT hT hX hX hd_pos hd_pos hβ_pos hβ_pos hT'_dense
    hT'_countable hT'_dense hT'_countable hX.measurablePair s t

lemma measurable_edist_holderModification {T₁ T₂ : Type*}
    [PseudoMetricSpace T₁] [PseudoMetricSpace T₂]
    {X₁ : T₁ → Ω → E} {X₂ : T₂ → Ω → E} {c₁ c₂ : ℝ≥0∞} {p₁ p₂ q₁ q₂ d₁ d₂ : ℝ} {M₁ M₂ β₁ β₂ : ℝ≥0}
    (hT₁ : HasBoundedInternalCoveringNumber (Set.univ : Set T₁) c₁ d₁)
    (hT₂ : HasBoundedInternalCoveringNumber (Set.univ : Set T₂) c₂ d₂)
    (hX₁ : IsKolmogorovProcess X₁ P p₁ q₁ M₁)
    (hX₂ : IsKolmogorovProcess X₂ P p₂ q₂ M₂)
    (hd₁_pos : 0 < d₁) (hd₂_pos : 0 < d₂)
    (hβ₁_pos : 0 < β₁) (hβ₂_pos : 0 < β₂)
    {T₁' : Set T₁} (hT₁'_dense : Dense T₁') (hT₁'_countable : T₁'.Countable)
    {T₂' : Set T₂} (hT₂'_dense : Dense T₂') (hT₂'_countable : T₂'.Countable)
    (hX₁₂ : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X₁ i ω, X₂ j ω))
    [∀ ω, Decidable (ω ∈ holderSet X₁ T₁' p₁ β₁)] [∀ ω, Decidable (ω ∈ holderSet X₂ T₂' p₂ β₂)]
    (s : T₁) (t : T₂) :
    Measurable (fun ω ↦ edist (holderModification X₁ β₁ p₁ T₁' hT₁'_dense s ω)
        (holderModification X₂ β₂ p₂ T₂' hT₂'_dense t ω)) := by
  borelize (E × E)
  refine StronglyMeasurable.measurable ?_
  exact continuous_edist.stronglyMeasurable.comp_measurable
    (measurable_pair_holderModification hT₁ hT₂ hX₁ hX₂ hd₁_pos hd₂_pos hβ₁_pos hβ₂_pos
      hT₁'_dense hT₁'_countable hT₂'_dense hT₂'_countable hX₁₂ s t)

omit [SecondCountableTopology T] in
lemma measurable_edist_holderModification' {β₁ β₂ : ℝ≥0}
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M) (hd_pos : 0 < d) (hβ₁_pos : 0 < β₁) (hβ₂_pos : 0 < β₂)
    {T' : Set T} (hT'_dense : Dense T') (hT'_countable : T'.Countable)
    [∀ ω, Decidable (ω ∈ holderSet X T' p β₁)] [∀ ω, Decidable (ω ∈ holderSet X T' p β₂)]
    (s t : T) :
    Measurable (fun ω ↦ edist (holderModification X β₁ p T' hT'_dense s ω)
      (holderModification X β₂ p T' hT'_dense t ω)) :=
  measurable_edist_holderModification hT hT hX hX hd_pos hd_pos hβ₁_pos hβ₂_pos
      hT'_dense hT'_countable hT'_dense hT'_countable hX.measurablePair s t

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology T] in
lemma uniformContinuous_holderModification
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M) (hd_pos : 0 < d) (hβ_pos : 0 < β)
    {T' : Set T} (hT'_dense : Dense T')
    [∀ ω, Decidable (ω ∈ holderSet X T' p β)] (ω : Ω) :
    UniformContinuous (fun t : T ↦ holderModification X β p T' hT'_dense t ω) := by
  refine hT'_dense.uniformContinuous_extend ?_
  by_cases hω : ω ∈ holderSet X T' p β
  · simp only [hω, ↓reduceIte, Set.indicatorSome, indicatorProcess]
    exact uniformContinuous_of_mem_holderSet hT hd_pos hX.p_pos hβ_pos hω
  · simp only [hω, ↓reduceIte, Set.indicatorSome, indicatorProcess]
    exact uniformContinuous_const

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology T] in
lemma continuous_holderModification
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M) (hd_pos : 0 < d) (hβ_pos : 0 < β)
    {T' : Set T} (hT'_dense : Dense T')
    [∀ ω, Decidable (ω ∈ holderSet X T' p β)] (ω : Ω) :
    Continuous (fun t : T ↦ holderModification X β p T' hT'_dense t ω) :=
  (uniformContinuous_holderModification hT hX hd_pos hβ_pos hT'_dense ω).continuous

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology T] in
lemma holderWith_holderModification
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M) (hd_pos : 0 < d) (hβ_pos : 0 < β)
    {T' : Set T} (hT'_dense : Dense T')
    [∀ ω, Decidable (ω ∈ holderSet X T' p β)] (ω : Ω) :
    ∃ C : ℝ≥0, HolderWith C β (holderModification X β p T' hT'_dense · ω) := by
  let C ω := ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
  by_cases hω : ω ∈ holderSet X T' p β
  · simp only [holderModification, hω, ↓reduceIte, Set.indicatorSome,indicatorProcess]
    refine ⟨(C ω ^ p⁻¹).toNNReal, ?_⟩
    exact hT'_dense.holderWith_extend (holderWith_of_mem_holderSet hT hd_pos hX.p_pos hβ_pos hω)
      hβ_pos
  · simp only [hω, ↓reduceIte, holderModification, Set.indicatorSome, indicatorProcess]
    exact ⟨0, hT'_dense.holderWith_extend (by simp [HolderWith]) hβ_pos⟩

variable [IsFiniteMeasure P]

omit hE [SecondCountableTopology T] [CompleteSpace E] [IsFiniteMeasure P] in
lemma ae_mem_holderSet (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    {T' : Set T} (hT'_countable : T'.Countable) :
    ∀ᵐ ω ∂P, ω ∈ holderSet X T' p β := by
  have : Countable T' := hT'_countable
  have h_ae_zero : ∀ᵐ ω ∂P, ∀ (s t : T'), edist s t = 0 → edist (X s ω) (X t ω) = 0 := by
    simp_rw [ae_all_iff]
    exact fun s t hst ↦ hX.IsAEKolmogorovProcess.edist_eq_zero hst
  let C ω := ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
  have hC_lt_top : ∀ᵐ ω ∂P, C ω < ∞ :=
    hX.ae_iSup_rpow_edist_div_lt_top hT hc hd_pos hdq_lt hβ_pos hβ_lt hT'_countable
  filter_upwards [hC_lt_top, h_ae_zero] with ω hω₁ hω₂ using ⟨hω₁, hω₂⟩

omit [SecondCountableTopology T] in
lemma modification_holderModification (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    {T' : Set T} (hT'_dense : Dense T') (hT'_countable : T'.Countable) (t : T) :
    holderModification X β p T' hT'_dense t =ᵐ[P] X t := by
  -- For each `ω`, `C ω < ∞` is a bound on `edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)`
  let C ω := ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
  -- Let `A` be the event that `C ω < ∞` and `X s ω = X t ω` for `edist s t = 0`.
  -- This is an event of probability 1.
  let A := holderSet X T' p β
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := ae_mem_holderSet hT hX hc hd_pos hdq_lt hβ_pos hβ_lt hT'_countable
  have hPA {s : Set Ω} : P (s ∩ A) = P s := by
    rw [Set.inter_comm, Measure.measure_inter_eq_of_ae hA_ae]
  -- Properties of the modification
  let Y := holderModification X β p T' hT'_dense
  have hY_eq {ω : Ω} (hω : ω ∈ A) (t : T') : Y t ω = X t ω := by
    exact holderModification_eq hT hX hd_pos hβ_pos hT'_dense t hω
  classical
  have hY_unif ω : UniformContinuous (fun t ↦ Y t ω) :=
    uniformContinuous_holderModification hT hX hd_pos hβ_pos hT'_dense ω
  have hY_cont ω : Continuous (fun t ↦ Y t ω) := (hY_unif ω).continuous
  -- Main proof
  suffices ∀ᵐ ω ∂P, edist (Y t ω) (X t ω) ≤ 0 by
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
    refine tendstoInMeasure_of_tendsto_ae_of_measurable_edist (fun n ↦ ?_) (ae_of_all _ h_ae)
    exact measurable_edist_holderModification' hT hX hd_pos hβ_pos hβ_pos
      hT'_dense hT'_countable (u n) t
  refine (ae_le_const_iff_forall_gt_measure_zero _ _).mpr fun ε hε ↦ ?_
  suffices Tendsto (fun n : ℕ ↦ P {ω | ε ≤ edist (Y t ω) (X t ω)}) atTop (𝓝 0) by
    simpa using this
  have hP_le n : P {ω | ε ≤ edist (Y t ω) (X t ω)}
      ≤ P {ω | ε/2 ≤ edist (Y (u n) ω) (Y t ω)} + P {ω | ε/2 ≤ edist (X (u n) ω) (X t ω)} := by
    calc P {ω | ε ≤ edist (Y t ω) (X t ω)}
    _ = P ({ω | ε ≤ edist (Y t ω) (X t ω)} ∩ A) := by rw [hPA]
    _ ≤ P ({ω | ε ≤ edist (Y (u n) ω) (Y t ω) + edist (X (u n) ω) (X t ω)} ∩ A) := by
      refine measure_mono fun ω ↦ ?_
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_imp]
      refine fun hε_le hω ↦ ⟨(hε_le.trans (h_le n hω)).trans_eq ?_, hω⟩
      rw [edist_comm]
    _ = P {ω | ε ≤ edist (Y (u n) ω) (Y t ω) + edist (X (u n) ω) (X t ω)} := by rw [hPA]
    _ ≤ P {ω | ε / 2 ≤ edist (Y (u n) ω) (Y t ω)}
        + P {ω | ε / 2 ≤ edist (X (u n) ω) (X t ω)} := measure_add_ge_le_add_measure_ge_half
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le') hP_le
  rw [← add_zero (0 : ℝ≥0∞)]
  exact Tendsto.add (h_tendsto_Y (ε / 2) (ENNReal.half_pos hε.ne'))
    (h_tendsto_X (ε / 2) (ENNReal.half_pos hε.ne'))

def IsLimitOfIndicator (Y X : T → Ω → E) (P : Measure Ω) : Prop :=
  ∃ (T' : Set T) (hT'_dense : Dense T') (A : Set Ω), Countable T' ∧ MeasurableSet A ∧
    (∀ᵐ ω ∂P, ω ∈ A) ∧
    (∀ t, ∀ ω ∈ A, ∃ c, Tendsto (fun t' : T' ↦ X t' ω) (comap Subtype.val (𝓝 t)) (𝓝 c)) ∧
    ∀ t ω, Y t ω = hT'_dense.extend (fun t' : T' ↦ indicatorProcess X A t' ω) t

omit [SecondCountableTopology T] [CompleteSpace E] [IsFiniteMeasure P] in
lemma IsLimitOfIndicator.measurable_pair {T' : Type*} [PseudoMetricSpace T']
    {Y X : T → Ω → E} {Z X' : T' → Ω → E}
    (hX : ∀ t, Measurable (X t)) (hX' : ∀ t, Measurable (X' t))
    (hX_pair : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X i ω, X' j ω))
    (hY : IsLimitOfIndicator Y X P) (hZ : IsLimitOfIndicator Z X' P)
    (s : T) (t : T') :
    Measurable[_, borel (E × E)] (fun ω ↦ (Y s ω, Z t ω)) := by
  obtain ⟨T₁', hT₁'_dense, A₁, hT₁'_countable, hA₁, hA₁_ae, hY_tendsto, hY_eq⟩ := hY
  obtain ⟨T₂', hT₂'_dense, A₂, hT₂'_countable, hA₂, hA₂_ae, hZ_tendsto, hZ_eq⟩ := hZ
  simp_rw [hY_eq, hZ_eq]
  simp only [Dense.extend, IsDenseInducing.extend]
  refine measurable_pair_limUnder_comap hT₁'_dense hT₂'_dense ?_ _ _ ?_ ?_
    (X₁ := indicatorProcess X A₁)
  · exact fun i j ↦ measurable_pair_indicatorProcess hX hX' hX_pair hA₁ hA₂ i j
  · intro ω
    by_cases hω : ω ∈ A₁
    · simpa [hω, indicatorProcess, Set.indicatorSome] using hY_tendsto s ω hω
    · simp only [indicatorProcess, Set.indicatorSome, hω, ↓reduceIte]
      exact ⟨hE.some, tendsto_const_nhds⟩
  · intro ω
    by_cases hω : ω ∈ A₂
    · simpa [hω, indicatorProcess, Set.indicatorSome] using hZ_tendsto t ω hω
    · simp only [indicatorProcess, Set.indicatorSome, hω, ↓reduceIte]
      exact ⟨hE.some, tendsto_const_nhds⟩

omit [SecondCountableTopology T] [CompleteSpace E] [IsFiniteMeasure P] in
lemma IsLimitOfIndicator.measurable_edist {T' : Type*} [PseudoMetricSpace T']
    {Y X : T → Ω → E} {Z X' : T' → Ω → E}
    (hX : ∀ t, Measurable (X t)) (hX' : ∀ t, Measurable (X' t))
    (hX_pair : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X i ω, X' j ω))
    (hY : IsLimitOfIndicator Y X P) (hZ : IsLimitOfIndicator Z X' P)
    (s : T) (t : T') :
    Measurable (fun ω ↦ edist (Y s ω) (Z t ω)) := by
  borelize (E × E)
  refine StronglyMeasurable.measurable ?_
  exact continuous_edist.stronglyMeasurable.comp_measurable
    (hY.measurable_pair hX hX' hX_pair hZ s t)

omit [SecondCountableTopology T] [IsFiniteMeasure P] in
lemma isLimitOfIndicator_holderModification
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    {T' : Set T} (hT'_dense : Dense T') (hT'_countable : T'.Countable)
    [∀ ω, Decidable (ω ∈ holderSet X T' p β)] :
    IsLimitOfIndicator (holderModification X β p T' hT'_dense) X P := by
  let A := holderSet X T' p β
  have hA_meas : MeasurableSet A := hX.measurableSet_holderSet hT'_countable
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := ae_mem_holderSet hT hX hc hd_pos hdq_lt hβ_pos hβ_lt hT'_countable
  refine ⟨T', hT'_dense, A, hT'_countable, hA_meas, hA_ae, fun t ω hω ↦ ?_, fun t ω ↦ rfl⟩
  exact exists_tendsto_of_mem_holderSet hT hd_pos hX.p_pos hβ_pos hT'_dense hω t

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology T] [CompleteSpace E]
  [IsFiniteMeasure P] in
lemma IsLimitOfIndicator.indicatorProcess {Y X : T → Ω → E}
    (hY : IsLimitOfIndicator Y X P) (A : Set Ω) (hA_meas : MeasurableSet A)
    (hA_ae : ∀ᵐ ω ∂P, ω ∈ A) :
    IsLimitOfIndicator (fun t ↦ indicatorProcess Y A t) X P := by
  obtain ⟨T', hT'_dense, A', hT'_countable, hA', hA'_ae, hY_tendsto, hY_eq⟩ := hY
  refine ⟨T', hT'_dense, A ∩ A', hT'_countable,
    MeasurableSet.inter hA_meas hA', ?_, fun t ω hω ↦ ?_, fun t ω ↦ ?_⟩
  · filter_upwards [hA_ae, hA'_ae] with ω hω₁ hω₂ using ⟨hω₁, hω₂⟩
  · exact hY_tendsto t ω hω.2
  · classical
    by_cases hω : ω ∈ A
    · simp [hω, hY_eq]
    · simp only [indicatorProcess_apply, hω, ↓reduceIte, Set.mem_inter_iff, false_and]
      rw [Dense.extend_eq_of_tendsto]
      exact tendsto_const_nhds

lemma exists_modification_holder_aux' (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t) ∧
      (∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω)) ∧ IsLimitOfIndicator Y X P := by
  -- Let `T'` be a countable dense subset of `T`
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  -- We build a modification `Y` of `X`, by using `Dense.extend` on `X · ω` if `ω ∈ A` and by taking
  -- an arbitrary constant value if `ω ∉ A`.
  classical
  refine ⟨holderModification X β p T' hT'_dense, ?_, ?_, ?_, ?_⟩
  · exact measurable_holderModification hT hX hd_pos hβ_pos hT'_dense hT'_countable
  · exact modification_holderModification hT hX hc hd_pos hdq_lt hβ_pos hβ_lt
      hT'_dense hT'_countable
  · exact holderWith_holderModification hT hX hd_pos hβ_pos hT'_dense
  · refine ⟨T', hT'_dense, holderSet X T' p β,
      hT'_countable, hX.measurableSet_holderSet hT'_countable, ?_, fun t ω hω ↦ ?_, fun t ω ↦ rfl⟩
    · exact ae_mem_holderSet hT hX hc hd_pos hdq_lt hβ_pos hβ_lt hT'_countable
    · exact exists_tendsto_of_mem_holderSet hT hd_pos hX.p_pos hβ_pos hT'_dense hω t

lemma exists_modification_holder_aux (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)∧
      ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  obtain ⟨Y, hY_meas, hY_eq, hY_holder, _⟩ :=
    exists_modification_holder_aux' hT hX.IsKolmogorovProcess_mk hc hd_pos hdq_lt
      hβ_pos hβ_lt
  refine ⟨Y, hY_meas, fun t ↦ ?_, hY_holder⟩
  filter_upwards [hX.ae_eq_mk t, hY_eq t] with ω hω1 hω2 using hω2.trans hω1.symm

omit [MeasurableSpace E] [BorelSpace E] [Nonempty E] [CompleteSpace E] in
lemma StronglyMeasurable.measurableSet_eq_of_continuous {f g : T → Ω → E}
    (hf : ∀ ω, Continuous (f · ω)) (hg : ∀ ω, Continuous (g · ω))
    (hf_meas : ∀ t, StronglyMeasurable (f t)) (hg_meas : ∀ t, StronglyMeasurable (g t)) :
    MeasurableSet {ω | ∀ t, f t ω = g t ω} := by
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

omit [MeasurableSpace E] [BorelSpace E] [Nonempty E] [CompleteSpace E] in
lemma Measurable.measurableSet_eq_of_continuous {f g : T → Ω → E}
    (hf : ∀ ω, Continuous (f · ω)) (hg : ∀ ω, Continuous (g · ω))
    (h_meas : ∀ t, Measurable (fun ω ↦ edist (f t ω) (g t ω))) :
    MeasurableSet {ω | ∀ t, f t ω = g t ω} := by
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
  suffices MeasurableSet {ω | edist (f t ω) (g t ω) = 0} by
    convert this with ω
    simp
  exact StronglyMeasurable.measurableSet_eq_fun (h_meas t).stronglyMeasurable (by fun_prop)

lemma exists_modification_holder'' (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t) ∧
      (∀ (β : ℝ≥0), 0 < β → β < (q - d) / p → ∀ ω, MemHolder β (Y · ω)) ∧
      IsLimitOfIndicator Y X P := by
  have h_ratio_pos : 0 < (q - d) / p := by
    have : 0 < p := hX.p_pos
    bound
  obtain ⟨β', hβ'_mono, hβ'_mem, hβ'_tendsto⟩ := exists_seq_strictMono_tendsto' h_ratio_pos
  let β : ℕ → ℝ≥0 := fun n ↦ ⟨β' n, (hβ'_mem n).1.le⟩
  have hβ_pos : ∀ n, 0 < β n := fun n ↦ mod_cast (hβ'_mem n).1
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  classical
  have := fun n ↦ exists_modification_holder_aux' hT hX hc hd_pos hdq_lt
    (hβ_pos n) (mod_cast (hβ'_mem n).2)
  choose Z hZ_meas hZ_ae_eq hZ_holder hZ_isLimit using this
  have hZ_ae_eq' n : ∀ᵐ ω ∂P, ∀ t, Z n t ω = Z 0 t ω := by
    refine indistinguishable_of_modification (ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_) ?_
    · obtain ⟨_, h⟩ := hZ_holder n ω
      exact h.continuous (hβ_pos n)
    · obtain ⟨_, h⟩ := hZ_holder 0 ω
      exact h.continuous (hβ_pos 0)
    · intro t
      filter_upwards [hZ_ae_eq n t, hZ_ae_eq 0 t] with ω hω₁ hω₂ using hω₁.trans hω₂.symm
  rw [← ae_all_iff] at hZ_ae_eq'
  let A := {ω | ∀ n t, Z n t ω = Z 0 t ω}
  have hA : MeasurableSet A := by
    have : A = ⋂ n, {ω | ∀ t, Z n t ω = Z 0 t ω} := by ext; simp [A]
    rw [this]
    refine MeasurableSet.iInter (fun n ↦ ?_)
    refine Measurable.measurableSet_eq_of_continuous (fun ω ↦ ?_) (fun ω ↦ ?_) fun t ↦ ?_
    · obtain ⟨_, h⟩ := hZ_holder n ω
      exact h.continuous (hβ_pos n)
    · obtain ⟨_, h⟩ := hZ_holder 0 ω
      exact h.continuous (hβ_pos 0)
    · refine IsLimitOfIndicator.measurable_edist hX.measurable hX.measurable
        hX.measurablePair (hZ_isLimit n) (hZ_isLimit 0) t t
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := hZ_ae_eq'
  classical
  let Y (t : T) (ω : Ω) : E := indicatorProcess (Z 0) A t ω
  refine ⟨Y, fun t ↦ Measurable.ite hA (hZ_meas 0 t) (by fun_prop), fun t ↦ ?_, ?_, ?_⟩
  · filter_upwards [hA_ae, hZ_ae_eq 0 t] with ω hω hω₂
    simpa only [hω, ↓reduceIte, Y, indicatorProcess, Set.indicatorSome] using hω₂
  · intro β₀ hβ₀_pos hβ₀_lt ω
    by_cases hω : ω ∈ A
    swap; · simp [hω, Y]
    simp only [hω, ↓reduceIte, Y, indicatorProcess, Set.indicatorSome]
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
  · exact IsLimitOfIndicator.indicatorProcess (hZ_isLimit 0) A hA hA_ae

lemma exists_modification_holder (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ (β : ℝ≥0) (_ : 0 < β) (_ : β < (q - d) / p) ω, MemHolder β (Y · ω) := by
  obtain ⟨Y, hY_meas, hY_eq, hY_holder, _⟩ :=
    exists_modification_holder'' hT hX.IsKolmogorovProcess_mk hc hd_pos hdq_lt
  refine ⟨Y, hY_meas, fun t ↦ ?_, hY_holder⟩
  filter_upwards [hX.ae_eq_mk t, hY_eq t] with ω hω1 hω2 using hω2.trans hω1.symm

omit [SecondCountableTopology T] in
lemma _root_.IsCoverWithBoundedCoveringNumber.hasBoundedInternalCoveringNumber_univ
    {C : ℕ → Set T} {c : ℕ → ℝ≥0∞}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d)) (n : ℕ) :
    HasBoundedInternalCoveringNumber (Set.univ : Set (C n)) (c n) d := by
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

lemma exists_modification_holder''' {C : ℕ → Set T} {c : ℕ → ℝ≥0∞}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : IsKolmogorovProcess X P p q M) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t) ∧
      (∀ ω t, ∃ U ∈ 𝓝 t, ∀ (β : ℝ≥0), 0 < β → β < (q - d) / p → ∃ C, HolderOnWith C β (Y · ω) U) ∧
      IsLimitOfIndicator Y X P := by
  have hp_pos : 0 < p := hX.p_pos
  have h_div_pos : 0 < (q - d) / p := by
    have : 0 < q - d := by bound
    positivity
  let ⟨β₀', hβ₀_pos', hβ₀_lt'⟩ := exists_between h_div_pos
  let β₀ : ℝ≥0 := ⟨β₀', hβ₀_pos'.le⟩
  have hβ₀_pos : 0 < β₀ := mod_cast hβ₀_pos'
  have hβ₀_lt : β₀ < (q - d) / p := mod_cast hβ₀_lt'
  let Xn : (n : ℕ) → (C n) → Ω → E := fun n t ω ↦ X t ω
  have hXn n : IsKolmogorovProcess (Xn n) P p q M := by
    constructor
    · exact fun s t ↦ hX.measurablePair s t
    · exact fun s t ↦ hX.kolmogorovCondition s t
    · exact hp_pos
    · exact hX.q_pos
  have hC' n : HasBoundedInternalCoveringNumber (Set.univ : Set (C n)) (c n) d :=
    hC.hasBoundedInternalCoveringNumber_univ n
  choose Z hZ hZ_eq hZ_holder hZ_extend
    using fun n ↦ exists_modification_holder'' (hC' n) (hXn n) (hc n) hd_pos hdq_lt
  have hZ_ae_eq : ∀ᵐ ω ∂P,
      ∀ n t (ht : t ∈ C n), Z n ⟨t, ht⟩ ω = Z (n + 1) ⟨t, hC.mono _ _ (Nat.le_succ _) ht⟩ ω := by
    rw [ae_all_iff]
    intro n
    suffices ∀ᵐ ω ∂P, ∀ (t : C n), Z n ⟨t, t.2⟩ ω
        = Z (n + 1) ⟨t, hC.mono _ _ (Nat.le_succ _) t.2⟩ ω by
      filter_upwards [this] with ω hω t ht using hω ⟨t, ht⟩
    refine indistinguishable_of_modification (ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_) ?_
    · obtain ⟨_, h⟩ := hZ_holder n β₀ hβ₀_pos hβ₀_lt ω
      exact h.continuous hβ₀_pos
    · obtain ⟨_, h⟩ := hZ_holder (n + 1) β₀ hβ₀_pos hβ₀_lt ω
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
    refine Measurable.measurableSet_eq_of_continuous (fun ω ↦ ?_) (fun ω ↦ ?_) fun t ↦ ?_
    · obtain ⟨_, h⟩ :=  hZ_holder n β₀ hβ₀_pos hβ₀_lt ω
      exact h.continuous hβ₀_pos
    · obtain ⟨_, h⟩ :=  hZ_holder (n + 1) β₀ hβ₀_pos hβ₀_lt ω
      have h_cont := h.continuous hβ₀_pos
      fun_prop
    · refine IsLimitOfIndicator.measurable_edist ?_ ?_ ?_ (hZ_extend n) (hZ_extend (n + 1)) _ _
      · exact (hXn _).measurable
      · exact (hXn _).measurable
      · intro i j
        exact hX.measurablePair i j
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := hZ_ae_eq
  classical
  have h_mem t : ∃ n, t ∈ C n := by
    have ht : t ∈ ⋃ n, C n := hC.subset_iUnion (by simp : t ∈ Set.univ)
    simpa using ht
  let nt t := Nat.find (h_mem t)
  have hnt t : t ∈ C (nt t) := Nat.find_spec (h_mem t)
  choose T' hT'_dense A' hA'_countable hA'_meas hA'_ae hZ_tendsto hZ_eq' using hZ_extend
  let Y (t : T) (ω : Ω) : E := if ω ∈ (A ∩ ⋂ n, A' n) then Z (nt t) ⟨t, hnt t⟩ ω else hE.some
  have hY_eq {ω} (hω : ω ∈ A ∩ ⋂ n, A' n) n (t : T) (ht : t ∈ C n) : Y t ω = Z n ⟨t, ht⟩ ω := by
    simp only [hω, ↓reduceIte, Y]
    exact hA_eq_le hω.1 (Nat.find_le ht) ⟨t, hnt t⟩
  have hA_inter_meas : MeasurableSet (A ∩ ⋂ n, A' n) :=
    MeasurableSet.inter hA (MeasurableSet.iInter hA'_meas)
  have hA_inter_ae : ∀ᵐ ω ∂P, ω ∈ A ∩ ⋂ n, A' n := by
    simp only [Set.mem_inter_iff, Set.mem_iInter, eventually_and, ae_all_iff]
    exact ⟨hA_ae, hA'_ae⟩
  refine ⟨Y, fun t ↦ Measurable.ite hA_inter_meas (hZ _ _) (by fun_prop), fun t ↦ ?_, ?_, ?_⟩
  · specialize hZ (nt t) ⟨t, hnt t⟩
    filter_upwards [hA_inter_ae, hZ_eq (nt t) ⟨t, hnt t⟩] with ω hω hω₂
    simp only [hω, ↓reduceIte, hω₂, Y, A, Xn]
  · intro ω t
    refine ⟨C (nt t), (hC.isOpen (nt t)).mem_nhds (hnt t), ?_⟩
    intro β₀ hβ₀_pos hβ₀_lt
    by_cases hω : ω ∈ A ∩ ⋂ n, A' n
    swap
    · unfold Y
      simp_rw [if_neg hω]
      simp [HolderOnWith]
    obtain ⟨C', hC'⟩ := hZ_holder (nt t) β₀ hβ₀_pos hβ₀_lt ω
    refine ⟨C', ?_⟩
    intro s hs s' hs'
    simp only
    rw [hY_eq hω (nt t) s hs, hY_eq hω (nt t) s' hs']
    exact hC' ⟨s, hs⟩ ⟨s', hs'⟩
  · refine ⟨⋃ n, T' n, ?_, A ∩ ⋂ n, A' n, ?_, ?_, ?_, ?_, ?_⟩
    · sorry
    · simp only [Set.countable_coe_iff, Set.countable_iUnion_iff]
      intro n
      exact Set.Countable.image (hA'_countable n) Subtype.val
    · exact hA.inter (MeasurableSet.iInter hA'_meas)
    · simp only [Set.mem_inter_iff, Set.mem_iInter, eventually_and, ae_all_iff]
      exact ⟨hA_ae, hA'_ae⟩
    · intro t ω hω
      sorry
    · intro t ω
      classical
      by_cases hω : ω ∈ A ∩ ⋂ n, A' n
      swap
      · simp only [hω, ↓reduceIte, indicatorProcess_apply, Y]
        rw [Dense.extend_eq_of_tendsto]
        exact tendsto_const_nhds
      simp only [hZ_eq', indicatorProcess_apply, hω, ↓reduceIte, Y]
      simp only [Set.mem_inter_iff, Set.mem_iInter] at hω
      simp only [hω, ↓reduceIte]
      sorry

lemma exists_modification_holder' {C : ℕ → Set T} {c : ℕ → ℝ≥0∞}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : IsAEKolmogorovProcess X P p q M) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t, ∃ U ∈ 𝓝 t, ∀ (β : ℝ≥0) (_ : 0 < β) (_ : β < (q - d) / p),
        ∃ C, HolderOnWith C β (Y · ω) U := by
  obtain ⟨Y, hY_meas, hY_eq, hY_holder, _⟩ :=
    exists_modification_holder''' hC hX.IsKolmogorovProcess_mk hc hd_pos hdq_lt
  refine ⟨Y, hY_meas, fun t ↦ ?_, hY_holder⟩
  filter_upwards [hX.ae_eq_mk t, hY_eq t] with ω hω1 hω2 using hω2.trans hω1.symm

lemma exists_modification_holder_iSup' {C : ℕ → Set T} {c : ℕ → ℝ≥0∞} {p q : ℕ → ℝ} {M : ℕ → ℝ≥0}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : ∀ n, IsKolmogorovProcess X P (p n) (q n) (M n)) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : ∀ n, d < q n) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (q n - d) / (p n)),
        ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · ω) U := by
  have hp_pos : ∀ n, 0 < p n := fun n ↦ (hX n).p_pos
  by_cases h_bdd : BddAbove (Set.range fun n ↦ (q n - d) / p n)
  swap
  · refine ⟨X, (hX 0).measurable, fun _ ↦ EventuallyEq.rfl, fun ω t β hβ_pos hβ_lt ↦ ?_⟩
    simp only [ciSup_of_not_bddAbove h_bdd, Real.sSup_empty] at hβ_lt
    norm_cast at hβ_lt
    exact absurd hβ_pos hβ_lt.not_gt
  have h_ratio_pos n : 0 < (q n - d) / p n := by
    have : 0 < q n - d := by bound
    specialize hp_pos n
    positivity
  let β : ℕ → ℝ≥0 := fun n ↦ ⟨(q n - d) / p n, (h_ratio_pos n).le⟩
  have hβ_pos : ∀ n, 0 < β n := fun n ↦ mod_cast h_ratio_pos n
  have h_exists := fun n ↦ exists_modification_holder''' hC (hX n) hc hd_pos (hdq_lt n)
  choose Z hZ_meas hZ_ae_eq hZ_holder hZ_limit using h_exists
  have hZ_cont n ω : Continuous fun t ↦ Z n t ω := by
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    obtain ⟨U, hU_mem, hU⟩ := hZ_holder n ω t
    have hβ_pos_half : 0 < β n / 2 := by specialize hβ_pos n; positivity
    specialize hU (β n / 2) hβ_pos_half ?_
    · simp [β, h_ratio_pos]
    · obtain ⟨_, h⟩ := hU
      exact (h.continuousOn hβ_pos_half).continuousAt hU_mem
  have hZ_ae_eq' n : ∀ᵐ ω ∂P, ∀ t, Z n t ω = Z 0 t ω := by
    refine indistinguishable_of_modification (ae_of_all _ (hZ_cont n)) (ae_of_all _ (hZ_cont 0)) ?_
    intro t
    filter_upwards [hZ_ae_eq n t, hZ_ae_eq 0 t] with ω hω₁ hω₂ using hω₁.trans hω₂.symm
  rw [← ae_all_iff] at hZ_ae_eq'
  let A := {ω | ∀ n t, Z n t ω = Z 0 t ω}
  have hA : MeasurableSet A := by
    have : A = ⋂ n, {ω | ∀ t, Z n t ω = Z 0 t ω} := by ext; simp [A]
    rw [this]
    refine MeasurableSet.iInter (fun n ↦ ?_)
    refine Measurable.measurableSet_eq_of_continuous (hZ_cont n) (hZ_cont 0) fun t ↦ ?_
    refine IsLimitOfIndicator.measurable_edist (hX n).measurable (hX 0).measurable
      (hX 0).measurablePair (hZ_limit n) (hZ_limit 0) t t
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

lemma exists_modification_holder_iSup {C : ℕ → Set T} {c : ℕ → ℝ≥0∞} {p q : ℕ → ℝ} {M : ℕ → ℝ≥0}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : ∀ n, IsAEKolmogorovProcess X P (p n) (q n) (M n)) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : ∀ n, d < q n) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (q n - d) / (p n)),
        ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · ω) U := by
  let X' := (hX 0).mk X
  have hX' : ∀ n, IsKolmogorovProcess X' P (p n) (q n) (M n) := fun n ↦ by
    constructor
    · exact fun s t ↦ (hX 0).IsKolmogorovProcess_mk.measurablePair s t
    · intro s t
      have h_le := (hX n).kolmogorovCondition s t
      refine le_trans (le_of_eq ?_) h_le
      refine lintegral_congr_ae ?_
      filter_upwards [(hX 0).ae_eq_mk s, (hX 0).ae_eq_mk t] with ω hω1 hω2 using by rw [hω1, hω2]
    · exact (hX n).p_pos
    · exact (hX n).q_pos
  obtain ⟨Y, hY_meas, hY_eq, hY_holder⟩ :=
    exists_modification_holder_iSup' hC hX' hc hd_pos hdq_lt
  refine ⟨Y, hY_meas, fun t ↦ ?_, hY_holder⟩
  filter_upwards [ (hX 0).ae_eq_mk t, hY_eq t] with ω hω1 hω2 using hω2.trans hω1.symm

end EMetricSpace

end ProbabilityTheory
