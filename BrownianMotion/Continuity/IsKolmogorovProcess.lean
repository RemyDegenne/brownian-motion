/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.MeanInequalities
import BrownianMotion.Continuity.Chaining
import BrownianMotion.Continuity.HasBoundedInternalCoveringNumber
import BrownianMotion.Continuity.LogSizeBallSequence

/-!
# Stochastic processes satisfying the Kolmogorov condition

-/

open MeasureTheory
open scoped ENNReal NNReal Finset

section Aux

-- This is in mathlib, but our mathlib is too old.
@[to_additive]
lemma iSup_mul_le {α : Type*} {ι : Sort*} [CompleteLattice α] [Mul α] [MulLeftMono α]
    [MulRightMono α] (u v : ι → α) : ⨆ i, u i * v i ≤ (⨆ i, u i) * ⨆ i, v i :=
  iSup_le fun _ ↦ mul_le_mul' (le_iSup ..) (le_iSup ..)

theorem Finset.iSup_sum_le {α ι : Type*} {β : Sort*} [CompleteLattice α] [AddCommMonoid α]
    [IsOrderedAddMonoid α] {I : Finset ι} (f : ι → β → α) :
    ⨆ (b), ∑ i ∈ I, f i b ≤ ∑ i ∈ I, ⨆ (b), f i b := by
  classical
  induction I using Finset.induction with
  | empty => simp
  | insert i I hi ih => simpa only [Finset.sum_insert hi] using (iSup_add_le _ _).trans (by gcongr)

lemma Finset.sup_le_sum {α β : Type*} [AddCommMonoid β] [LinearOrder β] [OrderBot β]
    [IsOrderedAddMonoid β] (s : Finset α) (f : α → β) (hfs : ∀ i ∈ s, 0 ≤ f i) :
    s.sup f ≤ ∑ a ∈ s, f a :=
  Finset.sup_le_iff.2 (fun _ hb => Finset.single_le_sum hfs hb)

lemma log2_le_logb_two (n : ℕ) : Nat.log2 n ≤ Real.logb 2 n := by
  calc (Nat.log2 n : ℝ)
  _ = Nat.log 2 n := mod_cast Nat.log2_eq_log_two
  _ ≤ Real.logb 2 n := Real.natLog_le_logb _ _

end Aux

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E]
  {p q : ℝ} {M : ℝ≥0}
  {P : Measure Ω}
  {X : T → Ω → E}

structure IsKolmogorovProcess (X : T → Ω → E) (P : Measure Ω) (p q : ℝ) (M : ℝ≥0) : Prop where
  aemeasurablePair : ∀ s t : T, @AEMeasurable _ _ (borel (E × E)) _ (fun ω ↦ (X s ω, X t ω)) P
  kolmogorovCondition : ∀ s t : T,
    ∫⁻ ω, (edist (X s ω) (X t ω)) ^ p ∂P ≤ M * edist s t ^ q

section Measurability

variable [MeasurableSpace E] [BorelSpace E]

lemma IsKolmogorovProcess.aemeasurable (hX : IsKolmogorovProcess X P p q M) (s : T) :
    AEMeasurable (X s) P := by
  have : Measurable[borel (E × E), _] (Prod.fst : E × E → E) :=
    measurable_fst.mono prod_le_borel_prod le_rfl
  exact @Measurable.comp_aemeasurable Ω E (E × E) _ _ _ (borel (E × E)) _ _ this
    (hX.aemeasurablePair s s)

omit [PseudoEMetricSpace T] in
lemma aemeasurable_pair_of_aemeasurable [SecondCountableTopology E] (hX : ∀ s, AEMeasurable (X s) P)
    (s t : T) :
    @AEMeasurable _ _ (borel (E × E)) _ (fun ω ↦ (X s ω, X t ω)) P := by
  suffices AEMeasurable (fun ω ↦ (X s ω, X t ω)) P by
    rwa [(Prod.borelSpace (α := E) (β := E)).measurable_eq] at this
  fun_prop

lemma IsKolmogorovProcess.mk_of_secondCountableTopology [SecondCountableTopology E]
    (h_meas : ∀ s, AEMeasurable (X s) P)
    (h_kol : ∀ s t : T, ∫⁻ ω, (edist (X s ω) (X t ω)) ^ p ∂P ≤ M * edist s t ^ q) :
    IsKolmogorovProcess X P p q M where
  aemeasurablePair := aemeasurable_pair_of_aemeasurable h_meas
  kolmogorovCondition := h_kol

omit [MeasurableSpace E] [BorelSpace E] in
lemma IsKolmogorovProcess.aestronglyMeasurable_edist
    (hX : IsKolmogorovProcess X P p q M) {s t : T} :
    AEStronglyMeasurable (fun ω ↦ edist (X s ω) (X t ω)) P := by
  have h_str : StronglyMeasurable[borel (E × E)] (fun p : E × E ↦ edist p.1 p.2) := by
    refine @Continuous.stronglyMeasurable _ _ (borel (E × E)) _ ?_ _ _ _ _ continuous_edist
    refine @BorelSpace.opensMeasurable _ _ (borel (E × E)) ?_
    exact @BorelSpace.mk _ _ (borel (E × E)) rfl
  exact h_str.aestronglyMeasurable.comp_aemeasurable (hX.aemeasurablePair s t)

omit [MeasurableSpace E] [BorelSpace E] in
@[fun_prop]
lemma IsKolmogorovProcess.aemeasurable_edist (hX : IsKolmogorovProcess X P p q M) {s t : T} :
    AEMeasurable (fun ω ↦ edist (X s ω) (X t ω)) P := hX.aestronglyMeasurable_edist.aemeasurable

end Measurability

lemma IsKolmogorovProcess.edist_eq_zero (hX : IsKolmogorovProcess X P p q M)
    (hp : 0 < p) (hq : 0 < q) {s t : T} (h : edist s t = 0) :
    ∀ᵐ ω ∂P, edist (X s ω) (X t ω) = 0 := by
  suffices ∀ᵐ ω ∂P, edist (X s ω) (X t ω) ^ p = 0 by
    filter_upwards [this] with ω hω
    simpa [hp, not_lt_of_gt hp] using hω
  refine (lintegral_eq_zero_iff' ?_).mp ?_
  · change AEMeasurable ((fun x ↦ x ^ p) ∘ (fun ω ↦ edist (X s ω) (X t ω))) P
    exact Measurable.comp_aemeasurable (by fun_prop) hX.aemeasurable_edist
  refine le_antisymm ?_ zero_le'
  calc ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
  _ ≤ M * edist s t ^ q := hX.kolmogorovCondition s t
  _ = 0 := by simp [h, hq]

lemma IsKolmogorovProcess.lintegral_sup_rpow_edist_eq_zero (hX : IsKolmogorovProcess X P p q M)
    (hp : 0 < p) (hq : 0 < q) {T' : Set T} (hT' : T'.Countable)
    (h : ∀ s ∈ T', ∀ t ∈ T', edist s t = 0) :
    ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p ∂P = 0 := by
  have : Countable T' := by simp [hT']
  refine (lintegral_eq_zero_iff' ?_).mpr ?_
  · refine AEMeasurable.iSup (fun s ↦ AEMeasurable.iSup (fun t ↦ ?_))
    change AEMeasurable ((fun x ↦ x ^ p) ∘ (fun ω ↦ edist (X s ω) (X t ω))) P
    exact Measurable.comp_aemeasurable (by fun_prop) hX.aemeasurable_edist
  suffices ∀ᵐ ω ∂P, ∀ s : T', ∀ t : T', edist (X s ω) (X t ω) = 0 by
    filter_upwards [this] with ω hω
    simp [hω, hp]
  simp_rw [ae_all_iff]
  exact fun s t ↦ hX.edist_eq_zero hp hq (h s.1 s.2 t.1 t.2)

lemma lintegral_sup_rpow_edist_le_card_mul_rpow (hq : 0 ≤ q) (hX : IsKolmogorovProcess X P p q M)
    {ε : ℝ≥0∞} (C : Finset (T × T)) (hC : ∀ u ∈ C, edist u.1 u.2 ≤ ε) :
    ∫⁻ ω, ⨆ u : C, edist (X u.1.1 ω) (X u.1.2 ω) ^ p ∂P
      ≤ #C * M * ε ^ q := calc
  _ = ∫⁻ ω, C.sup (fun u => edist (X u.1 ω) (X u.2 ω) ^ p) ∂P := by
        simp only [iSup_subtype, Finset.sup_eq_iSup]
  _ ≤ ∫⁻ ω, ∑ u ∈ C, edist (X u.1 ω) (X u.2 ω) ^ p ∂P := by gcongr; apply Finset.sup_le_sum; simp
  _ = ∑ u ∈ C, ∫⁻ ω, edist (X u.1 ω) (X u.2 ω) ^ p ∂P :=
        lintegral_finset_sum' _ (fun _ _ => AEMeasurable.pow_const hX.aemeasurable_edist _)
  _ ≤ ∑ u ∈ C, M * edist u.1 u.2 ^ q := by gcongr; apply hX.kolmogorovCondition
  _ ≤ ∑ u ∈ C, M * ε ^ q := by gcongr; apply hC; assumption
  _ = #C * M * ε ^ q := by simp [mul_assoc]

lemma lintegral_sup_rpow_edist_le_card_mul_rpow_of_dist_le (hp : 0 < p) (hq : 0 ≤ q)
    (hX : IsKolmogorovProcess X P p q M) {J : Finset T} {a c : ℝ≥0∞} {n : ℕ}
    (hJ_card : #J ≤ a ^ n) (ha : 1 < a) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ c }), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 2 ^ p * a * #J * M * (c * n) ^ q := by
  obtain ⟨K, ⟨-, _, hKeps, hKle⟩⟩ := pair_reduction J hJ_card ha E
  calc
    _ = ∫⁻ ω, (⨆ (s : J) (t : { t : J // edist s t ≤ c}), edist (X s ω) (X t ω)) ^ p ∂P := ?_
    _ ≤ ∫⁻ ω, (2 * ⨆ p : K, edist (X p.1.1 ω) (X p.1.2 ω)) ^ p ∂P := ?_
    _ = 2 ^ p * ∫⁻ ω, (⨆ p : K, edist (X p.1.1 ω) (X p.1.2 ω)) ^ p ∂P := ?_
    _ ≤ 2 ^ p * (#K * M * (n * c) ^ q) := ?_
    _ ≤ 2 ^ p * a * #J * M * (c * n) ^ q := ?_
  · simp only [← (ENNReal.monotone_rpow_of_nonneg (le_of_lt hp)).map_iSup_of_continuousAt
      ENNReal.continuous_rpow_const.continuousAt (by simp [hp])]
  · gcongr with omega
    apply hKle (X · omega)
  · simp only [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hp)]
    rw [lintegral_const_mul'']
    apply AEMeasurable.pow_const
    apply AEMeasurable.iSup (fun _ => hX.aemeasurable_edist)
  · gcongr
    simp only [(ENNReal.monotone_rpow_of_nonneg (le_of_lt hp)).map_iSup_of_continuousAt
      ENNReal.continuous_rpow_const.continuousAt (by simp [hp])]
    exact lintegral_sup_rpow_edist_le_card_mul_rpow hq hX K (fun u hu => hKeps u.1 u.2 hu)
  · simp only [← mul_assoc]
    rw [mul_assoc _ a, mul_comm _ c]
    gcongr

section FirstTerm

variable {J : Set T}

lemma lintegral_sup_rpow_edist_cover_of_dist_le (hp : 0 < p) (hq : 0 ≤ q)
    (hX : IsKolmogorovProcess X P p q M) {C : Finset T} {ε : ℝ≥0∞}
    (hC_card : #C = internalCoveringNumber ε J)
    {c : ℝ≥0∞} :
    ∫⁻ ω, ⨆ (s : C) (t : { t : C // edist s t ≤ c}), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 2 ^ (p + 1) * M * (2 * c * Nat.log2 (internalCoveringNumber ε J).toNat) ^ q
        * internalCoveringNumber ε J := by
  -- Trivial cases
  refine (eq_or_ne #C 0).elim (fun h => by simp_all [iSup_subtype]) (fun hC₀ => ?_)
  by_cases hC₁ : #C = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hC₁
    simp [iSup_subtype, ENNReal.zero_rpow_of_pos hp]

  -- Definition and properties of rbar
  let rbar := 1 + Nat.log2 #C
  have h₀ : #C ≤ 2 ^ rbar := by simpa [rbar, add_comm 1] using le_of_lt Nat.lt_log2_self
  have h₀' : (#C : ℝ≥0∞) ≤ 2 ^ rbar := by norm_cast
  have h₁ : rbar ≤ 2 * Nat.log2 #C := by
    suffices 1 ≤ Nat.log2 #C by omega
    rw [Nat.le_log2] <;> omega
  refine (lintegral_sup_rpow_edist_le_card_mul_rpow_of_dist_le hp hq hX h₀' (by norm_num)).trans ?_
  simp only [← hC_card, ENat.toNat_coe, ENat.toENNReal_coe]
  calc 2 ^ p * 2 * #C * M * (c * rbar) ^ q = 2 ^ (p + 1) * M * (c * rbar) ^ q * #C := ?_
    _ ≤ 2 ^ (p + 1) * M * (2 * c * Nat.log2 #C) ^ q * #C := ?_
  · rw [ENNReal.rpow_add _ _ (by norm_num) (by norm_num), ENNReal.rpow_one]
    ring
  · rw [mul_comm 2 c, mul_assoc c 2]
    gcongr
    norm_cast

lemma lintegral_sup_rpow_edist_cover_rescale (hX : IsKolmogorovProcess X P p q M) (hJ : J.Finite)
    {C : ℕ → Finset T} {ε₀ : ℝ≥0∞}
    (hC : ∀ i, IsCover (C i) (ε₀ * 2⁻¹ ^ i) J) (hC_subset : ∀ i, (C i : Set T) ⊆ J)
    (hC_card : ∀ i, #(C i) = internalCoveringNumber (ε₀ * 2⁻¹ ^ i) J)
    {δ : ℝ≥0∞} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 4 * ε₀)
    {k m : ℕ} (hm : m = ⌊Real.logb 2 (4 * ε₀ / δ).toReal⌋₊)
    (hmk : m ≤ k) :
    ∫⁻ ω, ⨆ (s : C k) (t : { t : C k // edist s t ≤ δ }),
        edist (X (chainingSequence hC s.2 m) ω) (X (chainingSequence hC t.1.2 m) ω) ^ p ∂P
      ≤ 2 ^ (p + 1) * M
        * (16 * δ * Nat.log2 (internalCoveringNumber (δ/4) J).toNat) ^ q
        * internalCoveringNumber (δ/4) J := by
  sorry

end FirstTerm

section SecondTerm

variable {J : Set T} {C : ℕ → Finset T} {ε : ℕ → ℝ≥0∞} {j k m : ℕ}

lemma lintegral_sup_rpow_edist_succ (hq : 0 ≤ q) (hX : IsKolmogorovProcess X P p q M)
    (hC : ∀ n, IsCover (C n) (ε n) J) (hC_subset : ∀ n, (C n : Set T) ⊆ J) (hjk : j < k) :
    ∫⁻ ω, ⨆ (t : C k),
        edist (X (chainingSequence hC t.2 j) ω) (X (chainingSequence hC t.2 (j + 1)) ω) ^ p ∂P
      ≤ #(C (j + 1)) * M * ε j ^ q := by
  refine (Set.eq_empty_or_nonempty J).elim (by rintro rfl; simp_all [iSup_subtype]) (fun hJ => ?_)

  -- Define the set `C'`, which is called `C` in the blueprint
  let f₀ : { x : T // x ∈ C (j + 1) } → T × T := fun x => (chainingSequence hC x.2 j, x.1)
  have hf₀ : Function.Injective f₀ := fun x y h => Subtype.ext (congrArg Prod.snd h)
  let C' : Finset (T × T) := (C (j + 1)).attach.map ⟨f₀, hf₀⟩
  have hC' : #C' = #(C (j + 1)) := by simp [C']

  -- First step: reindex from a `C k`-indexed supremum to a `C'`-indexed supremum
  let f (ω : Ω) : { x : T × T // x ∈ C' } → ℝ≥0∞ :=
    fun x => (edist (X x.1.1 ω) (X x.1.2 ω)) ^ p
  let g (ω : Ω) : { x : T // x ∈ C k } → { x : T × T // x ∈ C' } :=
    fun x => ⟨f₀ ⟨chainingSequence hC x.2 (j + 1),
      chainingSequence_mem hC hJ x.2 (j + 1) (by omega)⟩, by simp [C']⟩
  have hle := lintegral_mono_fn (μ := P) (fun ω => iSup_comp_le (f ω) (g ω))
  simp only [f, g, f₀] at hle
  conv_lhs at hle =>
    right; ext ω; congr; ext x;
      rw [chainingSequence_chainingSequence _ hJ _ _ (by omega) _ (by omega)]

  -- Second step: apply previous results
  refine hle.trans (hC' ▸ lintegral_sup_rpow_edist_le_card_mul_rpow hq hX (ε := ε j) C' ?_)
  rintro u hu
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.1 hu
  simp only [Function.Embedding.coeFn_mk, f₀]
  apply edist_chainingSequence_add_one_self _ hC_subset

lemma lintegral_sup_rpow_edist_le_sum_rpow (hp : 1 ≤ p) (hX : IsKolmogorovProcess X P p q M)
    (hC : ∀ n, IsCover (C n) (ε n) J) (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence hC t.2 m) ω) ^ p ∂P
      ≤ (∑ i ∈ Finset.range (k - m), (∫⁻ ω, ⨆ (t : C k),
        edist (X (chainingSequence hC t.2 (m + i)) ω)
          (X (chainingSequence hC t.2 (m + i + 1)) ω) ^ p ∂P) ^ (1 / p)) ^ p := by
  have hp' : 0 < p := by bound
  simp only [← (ENNReal.monotone_rpow_of_nonneg (le_of_lt hp')).map_iSup_of_continuousAt
    ENNReal.continuous_rpow_const.continuousAt (by simp [hp']), iSup_subtype']
  refine le_trans ?_ (ENNReal.monotone_rpow_of_nonneg (le_of_lt hp')
    (ENNReal.lintegral_Lp_finsum_le
      (fun _ _ => AEMeasurable.iSup (fun _ => hX.aemeasurable_edist)) hp))
  dsimp only
  rw [one_div, ENNReal.rpow_inv_rpow (by bound)]
  gcongr with ω
  simp only [Finset.sum_apply, iSup_subtype']
  refine le_trans ?_ (Finset.iSup_sum_le _)
  gcongr
  exact edist_chainingSequence_le_sum_edist (X · ω) hm

lemma lintegral_sup_rpow_edist_le_sum (hp : 1 ≤ p) (hX : IsKolmogorovProcess X P p q M) (hq : 0 ≤ q)
    (hC : ∀ n, IsCover (C n) (ε n) J) (hC_subset : ∀ n, (C n : Set T) ⊆ J) (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence hC t.2 m) ω) ^ p ∂P
      ≤ M * (∑ i ∈ Finset.range (k - m), #(C (m + i + 1)) ^ (1 / p)
              * ε (m + i) ^ (q / p)) ^ p := by
  refine (lintegral_sup_rpow_edist_le_sum_rpow hp hX hC hm).trans ?_
  calc (∑ i ∈ Finset.range (k - m),
      (∫⁻ ω, ⨆ (t : C k), edist (X (chainingSequence hC t.2 (m + i)) ω)
        (X (chainingSequence hC t.2 (m + i + 1)) ω) ^ p ∂P) ^ (1 / p)) ^ p
  _ ≤ (∑ i ∈ Finset.range (k - m), (#(C (m + i + 1)) * M * ε (m + i) ^ q) ^ (1 / p)) ^ p := by
    gcongr with i hi
    refine (lintegral_sup_rpow_edist_succ hq hX _ hC_subset ?_).trans_eq (by ring)
    simp only [Finset.mem_range] at hi
    omega
  _ = (∑ i ∈ Finset.range (k - m),
      M ^ (1 / p) * #(C (m + i + 1)) ^ (1 / p) * ε (m + i) ^ (q / p)) ^ p := by
    congr with i
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
    ring_nf
  _ = M * (∑ i ∈ Finset.range (k - m), #(C (m + i + 1)) ^ (1 / p) * ε (m + i) ^ (q / p)) ^ p := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
    field_simp

lemma lintegral_sup_rpow_edist_le_of_minimal_cover (hp : 1 ≤ p)
    (hX : IsKolmogorovProcess X P p q M)
    (hε : ∀ n, ε n ≤ EMetric.diam J)
    (hC : ∀ n, IsCover (C n) (ε n) J) (hC_subset : ∀ n, (C n : Set T) ⊆ J)
    (hC_card : ∀ n, #(C n) = internalCoveringNumber (ε n) J)
    {c₁ : ℝ≥0∞} {d : ℝ} (hd_pos : 0 < d) (hdq : d ≤ q)
    (h_cov : HasBoundedInternalCoveringNumber J c₁ d)
    (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence hC t.2 m) ω) ^ p ∂P
      ≤ M * c₁
        * (∑ j ∈ Finset.range (k - m), ε (m + j + 1) ^ (- d / p) * ε (m + j) ^ (q / p)) ^ p := by
  refine (lintegral_sup_rpow_edist_le_sum hp hX ?_ hC hC_subset hm).trans ?_
  · exact (hd_pos.trans_le hdq).le -- `positivity` fails?
  rw [mul_assoc]
  gcongr _ * ?_
  have hC_card' n : (#(C n) : ℝ≥0∞) = internalCoveringNumber (ε n) J := mod_cast hC_card n
  simp_rw [hC_card']
  calc (∑ x ∈ Finset.range (k - m), (internalCoveringNumber (ε (m + x + 1)) J) ^ (1 / p)
      * ε (m + x) ^ (q / p)) ^ p
  _ ≤ (∑ x ∈ Finset.range (k - m), (c₁ * (ε (m + x + 1))⁻¹ ^ d) ^ (1 / p)
      * ε (m + x) ^ (q / p)) ^ p := by
    gcongr with x hx
    exact h_cov (ε (m + x + 1)) (hε _)
  _ = c₁ * (∑ x ∈ Finset.range (k - m), ((ε (m + x + 1))⁻¹ ^ (d / p))
      * ε (m + x) ^ (q / p)) ^ p := by
    have : c₁= (c₁ ^ (1 / p)) ^ p := by rw [← ENNReal.rpow_mul]; field_simp
    conv_rhs => rw [this]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), Finset.mul_sum]
    congr with i
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, mul_assoc]
    field_simp
  _ = c₁ * (∑ j ∈ Finset.range (k - m), ε (m + j + 1) ^ (-d / p) * ε (m + j) ^ (q / p)) ^ p := by
    congr with i
    rw [ENNReal.inv_rpow, neg_div, ENNReal.rpow_neg]

lemma lintegral_sup_rpow_edist_le_of_minimal_cover_two (hp : 1 ≤ p)
    (hX : IsKolmogorovProcess X P p q M) {ε₀ : ℝ≥0∞} (hε : ε₀ ≤ EMetric.diam J)
    (hC : ∀ n, IsCover (C n) (ε₀ * 2⁻¹ ^ n) J) (hC_subset : ∀ n, (C n : Set T) ⊆ J)
    (hC_card : ∀ n, #(C n) = internalCoveringNumber (ε₀ * 2⁻¹ ^ n) J)
    {c₁ : ℝ≥0∞} {d : ℝ} (hd_pos : 0 < d) (hdq : d < q)
    (h_cov : HasBoundedInternalCoveringNumber J c₁ d)
    (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence hC t.2 m) ω) ^ p ∂P
      ≤ 2 ^ d * M * c₁ * (2 * ε₀ * 2⁻¹ ^ m) ^ (q - d) / (2 ^ ((q - d) / p) - 1) ^ p := by
  sorry

lemma lintegral_sup_rpow_edist_le_sum_rpow_of_le_one (hp_pos : 0 < p) (hp : p ≤ 1)
    (hX : IsKolmogorovProcess X P p q M)
    (hC : ∀ n, IsCover (C n) (ε n) J) (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence hC t.2 m) ω) ^ p ∂P
      ≤ ∑ i ∈ Finset.range (k - m), ∫⁻ ω, ⨆ (t : C k),
        edist (X (chainingSequence hC t.2 (m + i)) ω)
          (X (chainingSequence hC t.2 (m + i + 1)) ω) ^ p ∂P := by
  rw [← lintegral_finset_sum' _ (fun _ _ => .iSup (fun _ => hX.aemeasurable_edist.pow_const _))]
  gcongr with ω
  refine le_trans ?_ (Finset.iSup_sum_le _)
  gcongr with t
  refine le_trans ?_ (ENNReal.rpow_finsetSum_le_finsetSum_rpow hp_pos hp)
  gcongr
  exact edist_chainingSequence_le_sum_edist (X · ω) hm

lemma lintegral_sup_rpow_edist_le_sum_of_le_one (hp_pos : 0 < p) (hp : p ≤ 1) (hq : 0 ≤ q)
    (hX : IsKolmogorovProcess X P p q M)
    (hC : ∀ n, IsCover (C n) (ε n) J) (hC_subset : ∀ n, (C n : Set T) ⊆ J) (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence hC t.2 m) ω) ^ p ∂P
      ≤ M * ∑ i ∈ Finset.range (k - m), #(C (m + i + 1)) * ε (m + i) ^ q := by
  refine (lintegral_sup_rpow_edist_le_sum_rpow_of_le_one hp_pos hp hX hC hm).trans ?_
  rw [Finset.mul_sum]
  gcongr with i hi
  refine (lintegral_sup_rpow_edist_succ hq hX _ hC_subset ?_).trans_eq (by ring)
  simp only [Finset.mem_range] at hi
  omega

lemma lintegral_sup_rpow_edist_le_of_minimal_cover_of_le_one (hp_pos : 0 < p) (hp : p ≤ 1)
    (hX : IsKolmogorovProcess X P p q M)
    (hε : ∀ n, ε n ≤ EMetric.diam J)
    (hC : ∀ n, IsCover (C n) (ε n) J) (hC_subset : ∀ n, (C n : Set T) ⊆ J)
    (hC_card : ∀ n, #(C n) = internalCoveringNumber (ε n) J)
    {c₁ : ℝ≥0∞} {d : ℝ} (hd_pos : 0 < d) (hdq : d ≤ q)
    (h_cov : HasBoundedInternalCoveringNumber J c₁ d)
    (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence hC t.2 m) ω) ^ p ∂P
      ≤ M * c₁
        * ∑ j ∈ Finset.range (k - m), ε (m + j + 1) ^ (- d) * ε (m + j) ^ q := by
  refine (lintegral_sup_rpow_edist_le_sum_of_le_one hp_pos hp ?_ hX hC hC_subset hm).trans ?_
  · exact (hd_pos.trans_le hdq).le -- `positivity` fails?
  simp_rw [Finset.mul_sum, mul_assoc]
  gcongr ∑ i ∈ _, _ * ?_ with i hi
  rw [← mul_assoc]
  gcongr
  refine le_trans (le_of_eq ?_) ((h_cov (ε (m + i + 1)) (hε _)).trans_eq ?_)
  · norm_cast
    exact hC_card _
  · rw [ENNReal.inv_rpow, ENNReal.rpow_neg]

lemma lintegral_sup_rpow_edist_le_of_minimal_cover_two_of_le_one (hp_pos : 0 < p) (hp : p ≤ 1)
    (hX : IsKolmogorovProcess X P p q M) {ε₀ : ℝ≥0∞} (hε : ε₀ ≤ EMetric.diam J)
    (hC : ∀ n, IsCover (C n) (ε₀ * 2⁻¹ ^ n) J) (hC_subset : ∀ n, (C n : Set T) ⊆ J)
    (hC_card : ∀ n, #(C n) = internalCoveringNumber (ε₀ * 2⁻¹ ^ n) J)
    {c₁ : ℝ≥0∞} {d : ℝ} (hd_pos : 0 < d) (hdq : d < q)
    (h_cov : HasBoundedInternalCoveringNumber J c₁ d)
    (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence hC t.2 m) ω) ^ p ∂P
      ≤ 2 ^ d * M * c₁ * (2 * ε₀ * 2⁻¹ ^ m) ^ (q - d) / (2 ^ (q - d) - 1) := by
  sorry

noncomputable
def Cp (d p q : ℝ) : ℝ≥0∞ :=
  max (1 / ((2 ^ ((q - d) / p)) - 1) ^ p) (1 / (2 ^ (q - d) - 1))

lemma second_term_bound {C : ℕ → Finset T} {k m : ℕ} (hp_pos : 0 < p)
    (hX : IsKolmogorovProcess X P p q M) {ε₀ : ℝ≥0∞} (hε : ε₀ ≤ EMetric.diam J)
    (hC : ∀ n, IsCover (C n) (ε₀ * 2⁻¹ ^ n) J) (hC_subset : ∀ n, (C n : Set T) ⊆ J)
    (hC_card : ∀ n, #(C n) = internalCoveringNumber (ε₀ * 2⁻¹ ^ n) J)
    {c₁ : ℝ≥0∞} {d : ℝ} (hc₁_pos : 0 < c₁) (hd_pos : 0 < d) (hdq : d < q)
    (h_cov : HasBoundedInternalCoveringNumber J c₁ d)
    (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence hC t.2 m) ω) ^ p ∂P
      ≤ 2 ^ d * M * c₁ * (2 * ε₀ * 2⁻¹ ^ m) ^ (q - d) * Cp d p q := by
  sorry

end SecondTerm

section Together

variable {M : ℝ≥0} {d p q : ℝ} {J : Set T} {c δ : ℝ≥0∞}

lemma lintegral_sup_cover_eq_of_lt_iInf_dist {C : Finset T}
    (hX : IsKolmogorovProcess X P p q M) (hJ : J.Finite) (hC : IsCover C δ J)
    (hC_subset : (C : Set T) ⊆ J) (hδ_lt : δ < ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t) :
    ∫⁻ ω, ⨆ (s : C) (t : { t : C // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
      = ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P := by
  sorry

lemma finite_set_bound_of_edist_le_of_diam_le (hJ : HasBoundedInternalCoveringNumber J c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hδ : δ ≠ 0) (hδ_le : EMetric.diam J ≤ δ / 4) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ}), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 2 ^ q * M * c * δ ^ (q - d) * Cp d p q := by
  sorry

lemma finite_set_bound_of_edist_le_of_le_diam (hJ : HasBoundedInternalCoveringNumber J c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hδ : δ ≠ 0) (hδ_le : δ / 4 ≤ EMetric.diam J) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 4 ^ (p + 2 * q + 1) * M * δ ^ (q - d)
        * (δ ^ d * (Nat.log2 (internalCoveringNumber (δ / 4) J).toNat) ^ q
              * internalCoveringNumber (δ / 4) J
            + c * Cp d p q) := by
  sorry

lemma finite_set_bound_of_edist_le_of_le_diam' (hJ : HasBoundedInternalCoveringNumber J c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hδ : δ ≠ 0) (hδ_le : δ / 4 ≤ EMetric.diam J) (h_diam : EMetric.diam J ≠ ∞) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 4 ^ (p + 2 * q + 1) * M * c * δ ^ (q - d)
        * (4 ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q
            + Cp d p q) := by
  refine (finite_set_bound_of_edist_le_of_le_diam hJ hX hd_pos hp_pos hdq_lt hδ hδ_le).trans ?_
  simp_rw [mul_assoc]
  gcongr _ * (_ * ?_)
  simp_rw [mul_add, ← mul_assoc]
  gcongr ?_ + ?_
  · rw [mul_comm c]
    simp_rw [mul_assoc]
    gcongr _ * ?_
    simp_rw [← mul_assoc]
    have hδ_ne_top : δ ≠ ∞ := by
      refine ne_of_lt ?_
      calc δ
      _ ≤ 4 * EMetric.diam J := by rwa [ENNReal.div_le_iff' (by simp) (by simp)] at hδ_le
      _ < ∞ := ENNReal.mul_lt_top (by simp) h_diam.lt_top
    have hJδ := hJ (δ / 4) hδ_le
    have hJ' : internalCoveringNumber (δ / 4) J ≤ c * 4 ^ d * δ⁻¹ ^ d := by
      refine hJδ.trans_eq ?_
      rw [ENNReal.inv_div, ENNReal.div_rpow_of_nonneg, div_eq_mul_inv, ENNReal.inv_rpow]
      · ring
      · exact hd_pos.le
      · simp
      · exact .inr hδ
    have hJ'' : Nat.log2 (internalCoveringNumber (δ / 4) J).toNat
        ≤ ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d)) := by
      by_cases h0 : Nat.log2 (internalCoveringNumber (δ / 4) J).toNat = 0
      · simp [h0]
      refine (ENNReal.natCast_le_ofReal h0).mpr ?_
      calc (Nat.log2 (internalCoveringNumber (δ / 4) J).toNat : ℝ)
      _ ≤ Real.logb 2 (internalCoveringNumber (δ / 4) J).toNat := log2_le_logb_two _
      _ ≤ Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d) := by
        have h_ne_top : internalCoveringNumber (δ / 4) J ≠ ⊤ := by
          refine (hJ.internalCoveringNumber_lt_top ?_ hc hd_pos.le).ne
          simp [hδ]
        gcongr
        · simp
        · by_contra h_eq
          simp only [Nat.cast_pos, not_lt, nonpos_iff_eq_zero, ENat.toNat_eq_zero, h_ne_top,
            or_false] at h_eq
          simp [h_eq] at h0
        have h_toReal : c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d
            = (c * 4 ^ d * δ⁻¹ ^ d).toReal := by simp [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
        rw [h_toReal, ← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, ENNReal.ofReal_toReal]
        · refine le_trans (le_of_eq ?_) hJ'
          norm_cast
          simp [h_ne_top]
        · finiteness
    have hq_pos : 0 < q := hd_pos.trans hdq_lt
    calc δ ^ d * (Nat.log2 (internalCoveringNumber (δ / 4) J).toNat) ^ q
        * (internalCoveringNumber (δ / 4) J)
    _ ≤ δ ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q
        * (c * 4 ^ d * δ⁻¹ ^ d) := by gcongr
    _ = c * 4 ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q := by
      rw [ENNReal.inv_rpow]
      simp_rw [mul_assoc]
      rw [mul_comm]
      simp_rw [← mul_assoc, mul_assoc]
      rw [ENNReal.inv_mul_cancel]
      · ring
      · simp [hδ, hd_pos.le]
      · simp [hδ_ne_top, hδ]
  · exact le_of_eq (by ring)

lemma finite_set_bound_of_edist_le (hJ : HasBoundedInternalCoveringNumber J c d)
    (hX : IsKolmogorovProcess X P p q M) (hc : c ≠ ∞)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q) (hδ : δ ≠ 0) (h_diam : EMetric.diam J ≠ ∞) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 4 ^ (p + 2 * q + 1) * M * c * δ ^ (q - d)
        * (4 ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q
            + Cp d p q) := by
  by_cases hδ_le : δ / 4 ≤ EMetric.diam J
  · exact finite_set_bound_of_edist_le_of_le_diam' hJ hX hc hd_pos hp_pos hdq_lt hδ hδ_le h_diam
  refine (finite_set_bound_of_edist_le_of_diam_le hJ hX hd_pos hp_pos hdq_lt hδ ?_).trans ?_
  · exact (not_le.mp hδ_le).le
  have hq_pos : 0 < q := hd_pos.trans hdq_lt
  calc 2 ^ q * ↑M * c * δ ^ (q - d) * Cp d p q
  _ ≤ 4 ^ (p + 2 * q + 1) * ↑M * c * δ ^ (q - d) * Cp d p q := by
    gcongr
    calc (2 : ℝ≥0∞) ^ q
    _ ≤ 4 ^ q := by
      gcongr
      norm_cast
    _ ≤ 4 ^ q * 4 ^ (p + q + 1) := by
      conv_lhs => rw [← mul_one ((4 : ℝ≥0∞) ^ q)]
      gcongr
      exact ENNReal.one_le_rpow (by norm_cast) (by positivity)
    _ = 4 ^ (p + 2 * q + 1) := by
      rw [← ENNReal.rpow_add _ _ (by positivity) (by simp)]
      ring_nf
  _ ≤ 4 ^ (p + 2 * q + 1) * ↑M * c * δ ^ (q - d) *
      (4 ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q
      + Cp d p q) := by
    rw [mul_add]
    exact le_add_self

end Together

end ProbabilityTheory
