/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.HasLaw
public import BrownianMotion.Continuity.KolmogorovChentsov
public import BrownianMotion.Gaussian.CovMatrix
public import BrownianMotion.Gaussian.GaussianProcess
public import BrownianMotion.Gaussian.Moment
public import BrownianMotion.Gaussian.ProjectiveLimit
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Independence.BoundedContinuousFunction
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Brownian motion

-/

@[expose] public section

open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

namespace ProbabilityTheory

section IsPreBrownianReal

variable (X : ℝ≥0 → Ω → ℝ)

variable {X} {P : Measure Ω}

lemma IsPreBrownianReal.hasLaw_gaussianLimit (hX : IsPreBrownianReal X P)
    (hXm : AEMeasurable (fun ω ↦ (X · ω)) P) :
    HasLaw (fun ω ↦ (X · ω)) gaussianLimit P where
  aemeasurable := hXm
  map_eq := by
    refine isProjectiveLimit_gaussianLimit.unique (fun I ↦ ?_) |>.symm
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hXm]
    exact (IsPreBrownianReal.hasLaw hX I).map_eq

lemma HasLaw.IsPreBrownianReal (hX : HasLaw (fun ω ↦ (X · ω)) gaussianLimit P) :
    IsPreBrownianReal X P where
  hasLaw _ := hasLaw_restrict_gaussianLimit.comp hX

lemma IsPreBrownianReal.isAEKolmogorovProcess {n : ℕ} (hn : 0 < n) (h : IsPreBrownianReal X P) :
    IsAEKolmogorovProcess X P (2 * n) n (Nat.doubleFactorial (2 * n - 1)) := by
  let Y t ω := (h.aemeasurable t).mk (X t) ω
  have hXY t := (h.aemeasurable t).ae_eq_mk
  have hY := h.congr hXY
  refine ⟨Y, ?_, ?_⟩
  constructor
  · intro s t
    rw [← BorelSpace.measurable_eq]
    refine Measurable.prodMk (h.aemeasurable s).measurable_mk (h.aemeasurable t).measurable_mk
  rotate_left
  · positivity
  · positivity
  · exact fun t ↦ (h.aemeasurable t).ae_eq_mk
  refine fun s t ↦ Eq.le ?_
  norm_cast
  simp_rw [edist_dist, Real.dist_eq]
  change ∫⁻ ω, (fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    ((Y s - Y t) ω) ∂_ = _
  rw [(hY.hasLaw_sub s t).lintegral_comp (f := fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    (by fun_prop)]
  simp_rw [← fun x ↦ ENNReal.ofReal_pow (abs_nonneg x)]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [pow_abs_two_mul]
    rw [← centralMoment_of_integral_id_eq_zero _ (by simp), ← NNReal.sq_sqrt (nndist _ _),
    centralMoment_fun_two_mul_gaussianReal, ENNReal.ofReal_mul (by positivity), mul_comm]
    norm_cast
    congr
    rw [pow_mul, NNReal.sq_sqrt]
    simp only [val_eq_coe, NNReal.coe_pow, coe_nndist, dist_nonneg, ENNReal.ofReal_pow]
    congr
  · simp_rw [← Real.norm_eq_abs]
    apply MemLp.integrable_norm_pow'
    exact IsGaussian.memLp_id _ _ (ENNReal.natCast_ne_top (2 * n))
  · exact ae_of_all _ fun _ ↦ by positivity

/-- If `X` is a pre-Brownian process then there exists a modification of `X` which is measurable
and locally β-Hölder for `0 < β < 1/2` (and thus continuous). See `IsPreBrownianReal.mk`. -/
lemma IsPreBrownianReal.exists_continuous_modification (h : IsPreBrownianReal X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))),
        ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · ω) U :=
  haveI := h.isGaussianProcess.isProbabilityMeasure
  exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ h.isAEKolmogorovProcess (by positivity : 0 < n + 2))
    (fun n ↦ by finiteness) zero_lt_one (fun n ↦ by simp; norm_cast; omega)

/-- If `h : IsPreBrownianReal X P`, then `h.mk X` is a continuous modification of `X`. -/
protected noncomputable def IsPreBrownianReal.mk (X) (h : IsPreBrownianReal X P) : ℝ≥0 → Ω → ℝ :=
  h.exists_continuous_modification.choose

lemma IsPreBrownianReal.memHolder_mk (h : IsPreBrownianReal X P) (ω : Ω) (t : ℝ≥0) (β : ℝ≥0)
    (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) :
    ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (h.mk X · ω) U := by
  convert h.exists_continuous_modification.choose_spec.2.2 ω t β hβ_pos ?_
  · rfl
  suffices ⨆ n, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)) = 2⁻¹ by rw [this]; norm_cast
  refine iSup_eq_of_forall_le_of_tendsto (F := Filter.atTop) (fun n ↦ ?_) ?_
  · calc
    ((↑(n + 2) : ℝ) - 1) / (2 * ↑(n + 2)) = 2⁻¹ * (n + 1) / (n + 2) := by
      simp only [Nat.cast_add, Nat.cast_ofNat]; field_simp; ring
    _ ≤ 2⁻¹ * 1 := by grw [mul_div_assoc, (div_le_one₀ (by positivity)).2]; linarith
    _ = 2⁻¹ := mul_one _
  · have : (fun n : ℕ ↦ ((↑(n + 2) : ℝ) - 1) / (2 * ↑(n + 2))) =
        (fun n : ℕ ↦ 2⁻¹ * ((n : ℝ) / (n + 1))) ∘ (fun n ↦ n + 1) := by
      ext n
      simp only [Nat.cast_add, Nat.cast_ofNat, Function.comp_apply, Nat.cast_one]
      field_simp
      ring
    rw [this]
    refine Filter.Tendsto.comp ?_ (Filter.tendsto_add_atTop_nat 1)
    nth_rw 2 [← mul_one 2⁻¹]
    exact (tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul _

@[fun_prop]
lemma IsPreBrownianReal.measurable_mk (h : IsPreBrownianReal X P) (t : ℝ≥0) :
    Measurable (h.mk X t) :=
  h.exists_continuous_modification.choose_spec.1 t

lemma IsPreBrownianReal.mk_ae_eq (h : IsPreBrownianReal X P) (t : ℝ≥0) :
    h.mk X t =ᵐ[P] X t :=
  h.exists_continuous_modification.choose_spec.2.1 t

lemma IsPreBrownianReal.continuous_mk (h : IsPreBrownianReal X P) (ω : Ω) :
    Continuous (h.mk X · ω) := by
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  obtain ⟨U, hu_mem, ⟨C, h⟩⟩ := h.memHolder_mk ω t 4⁻¹ (by norm_num)
    (NNReal.inv_lt_inv (by norm_num) (by norm_num))
  exact (h.continuousOn (by norm_num)).continuousAt hu_mem

/-- A pre-Brownian motion `X` is **filtered** with respect to a filtration `𝓕` if it is adapted
to `𝓕` and the increments of `X` after time `t` are independent of `𝓕 t` -/
class IsFilteredPreBrownian (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop
  extends IsPreBrownianReal X P where
    stronglyAdapted : StronglyAdapted 𝓕 X
    indep : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (X t - X s) inferInstance) (𝓕 s) P

lemma IsPreBrownianReal.isFilteredPreBrownian (h : IsPreBrownianReal X P)
    (hX : ∀ t : ℝ≥0, Measurable (X t)) :
    IsFilteredPreBrownian X (natural X (fun t ↦ (hX t).stronglyMeasurable)) P where
  stronglyAdapted := stronglyAdapted_natural (fun t ↦ (hX t).stronglyMeasurable)
  indep s t hst := by
    have h := (IndepFun_iff_Indep _ _ _).1 (h.indepFun_shift s)
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
    · have hX : X t - X s = (fun f ↦ f (t - s)) ∘ (fun ω u ↦ (X (s + u) ω - X s ω)) := by
        funext; simp [add_tsub_cancel_of_le, hst]
      rw [hX, ←comap_comp]; apply comap_mono (Measurable.comap_le _); fun_prop
    · refine iSup_le fun u => iSup_le fun hu => ?_
      have hX : (X u) = ((fun f ↦ f ⟨u,hu⟩) ∘ (fun ω (t : Set.Iic s) ↦ X t ω)) := by
        funext; simp
      rw [hX, ←comap_comp]; apply comap_mono (Measurable.comap_le _); fun_prop
  hasLaw := h.hasLaw

lemma IsPreBrownianReal.isMartingale (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    [IsProbabilityMeasure P] [hX : IsFilteredPreBrownian X 𝓕 P] : Martingale X 𝓕 P := by
  refine ⟨hX.stronglyAdapted, fun s t hst => ?_⟩
  have hM := fun t ↦ ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_no_cond : P[X t - X s | 𝓕 s] =ᵐ[P] fun _ ↦ P[X t - X s] := by
    refine condExp_indep_eq ?_ (𝓕.le s) ?_ (hX.indep s t hst)
    · exact Measurable.comap_le (Measurable.sub (hM t) (hM s))
    · exact (comap_measurable (X t - X s)).stronglyMeasurable
  have h_integral_zero : P[X t - X s] = 0 := calc
    P[X t - X s] = P[X t] - P[X s] := integral_sub (hX.integrable_eval t) (hX.integrable_eval s)
    _ = ↑0 := by simp [hX.integral_eval]
  calc
    _ = P[(X t - X s) + X s | 𝓕 s] := by simp
    _ =ᵐ[P] P[X t - X s | 𝓕 s] + P[X s | 𝓕 s] := condExp_add ((Integrable.sub
      (hX.integrable_eval t) (hX.integrable_eval s))) (hX.integrable_eval s) (𝓕 s)
    _ = P[X t - X s | 𝓕 s] + X s := by
      rw [condExp_of_stronglyMeasurable (𝓕.le s) (hX.stronglyAdapted s) (hX.integrable_eval s)]
    _ =ᵐ[P] (fun _ ↦ P[X t - X s]) + X s := by filter_upwards [h_no_cond] with ω hω; simp [hω]
    _ = X s := by aesop

end IsPreBrownianReal

section IsBrownianReal

variable (X : ℝ≥0 → Ω → ℝ)

variable {X}

lemma IsPreBrownianReal.isBrownianReal_mk (h : IsPreBrownianReal X P) :
    IsBrownianReal (h.mk X) P where
  toIsPreBrownianReal := h.congr fun _ ↦ (h.mk_ae_eq _).symm
  cont := ae_of_all _ h.continuous_mk

lemma IsBrownianReal.mk_ae_forall_eq (h : IsBrownianReal X P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (h.toIsPreBrownianReal.mk) t ω = X t ω := by
  apply indistinguishable_of_modification _ h.cont h.toIsPreBrownianReal.mk_ae_eq
  exact .of_forall h.toIsPreBrownianReal.continuous_mk

lemma IsBrownianReal.aemeasurable (h : IsBrownianReal X P) :
    AEMeasurable (fun ω t ↦ X t ω) P := by
  refine ⟨Function.swap h.toIsPreBrownianReal.mk, by measurability, ?_⟩
  exact h.mk_ae_forall_eq.mono <| fun _ ↦ by aesop

/-- If `X` is a Brownian motion then so is `fun t ω ↦ t * (B (1 / t) ω)`. -/
theorem IsBrownianReal.inv (h : IsBrownianReal X P) :
    IsBrownianReal (fun t ω ↦ t * (X (1 / t) ω)) P where
  toIsPreBrownianReal := h.toIsPreBrownianReal.inv
  cont := by
    obtain ⟨s, cs, ds⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
    let Y := fun t ω ↦ t * X (1 / t) ω
    have hY : IsPreBrownianReal Y P := h.toIsPreBrownianReal.inv
    have h1 : ∀ᵐ ω ∂P, ∀ q : s, Y q ω = hY.mk Y q ω :=
      haveI : Countable s := cs
      ae_all_iff.2 fun q ↦ (hY.mk_ae_eq q).symm
    have h2 : ∀ᵐ ω ∂P, Set.EqOn (Y · ω) (hY.mk Y · ω) (s \ {0}) := by
      filter_upwards [h1] with ω hω
      rintro t ⟨ht, -⟩
      exact hω ⟨t, ht⟩
    have h3 : ∀ᵐ ω ∂P, ContinuousOn (Y · ω) {t | t ≠ 0} := by
      filter_upwards [h.cont] with ω hω
      intro t (ht : t ≠ 0)
      simp_rw [Y]
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := positivity)
    have : ∀ᵐ ω ∂P, ∀ t ≠ 0, Y t ω = hY.mk Y t ω := by
      filter_upwards [h2, h3] with ω h1 h2
      convert h1.of_subset_closure h2 (hY.continuous_mk ω |>.continuousOn) (by grind) _
      · rfl
      convert Set.subset_univ _
      exact (ds.sdiff_singleton 0).closure_eq
    have h4 : ∀ᵐ ω ∂P, ∀ t, Y t ω = hY.mk Y t ω := by
      filter_upwards [this, (hY.isBrownianReal_mk.hasLaw_eval 0).ae_eq_const_of_gaussianReal]
        with ω h1 h2 t
      obtain rfl | ht := eq_or_ne t 0
      · simp_all [Y]
      exact h1 t ht
    filter_upwards [h4] with ω h
    simp_rw [Y] at h
    simp_rw [h]
    exact hY.continuous_mk ω

lemma IsBrownianReal.tendsto_div_id_atTop (h : IsBrownianReal X P) :
    ∀ᵐ ω ∂P, Filter.Tendsto (fun t ↦ (X t ω) / t) .atTop (𝓝 0) := by
  filter_upwards [h.inv.tendsto_nhds_zero] with ω hω
  have : (fun t ↦ (X t ω) / t) = (fun t ↦ t * (X (1 / t) ω)) ∘ (fun t ↦ t⁻¹) := by ext; simp [field]
  rw [this]
  exact hω.comp tendsto_inv_atTop_zero

/-- **Blumenthal's zero-one law**: Let `𝓕` be the canonical filtration associated to a Brownian
motion. Then the `σ`-algebra `⨅ s > 0, 𝓕 s` is trivial. -/
theorem IsBrownianReal.indep_zero (h : IsBrownianReal X P) (hX : ∀ t, Measurable (X t))
    (hX' : ∀ ω, Continuous (X · ω)) {A : Set Ω}
    (hA : MeasurableSet[⨅ s > 0, natural X (fun t ↦ (hX t).stronglyMeasurable) s] A) :
    P A = 0 ∨ P A = 1 := by
  have := h.isGaussianProcess.isProbabilityMeasure
  -- We consider three different `σ`-algebras. `m1` is the one generated by the process `X`.
  let m1 : MeasurableSpace Ω := .comap (fun ω t ↦ X t ω) inferInstance
  -- `m2` is the one generated by the restriction of `X` to positive real numbers.
  let m2 : MeasurableSpace Ω := .comap (fun ω (t : Set.Ioi (0 : ℝ≥0)) ↦ X t ω) inferInstance
  -- `m3` is `⨅ s > 0, 𝓕 s`, which we want to show to be trivial.
  set m3 : MeasurableSpace Ω := ⨅ s > 0, natural X (fun t ↦ (hX t).stronglyMeasurable) s
-- We easily have that `m3 ≤ m1 ≤ mΩ`.
  have hm1 : m1 ≤ mΩ := by
    apply Measurable.comap_le
    apply @Measurable.of_eval _ _ _ mΩ
    exact hX
  have hm3 : m3 ≤ m1 := by
    apply iInf₂_le_of_le 1 (by simp)
    rw [natural_eq_comap]
    exact comap_le_comap (fun x t ↦ x t.1) (by fun_prop) (by ext; simp)
  have hm3' := hm3.trans hm1
  -- Because `X` is continuous, `X t ⟶ X 0` as `t → 0⁺`, thus
  -- the random variable `X 0` is actually measurable with respect to `m2`, so `m1 ≤ m2`.
  have : m1 ≤ m2 := by
    simp_rw [m1, m2, comap_process]
    rw [iSup_split_single _ 0, sup_le_iff]
    constructor; swap
    · simp_rw [← pos_iff_ne_zero, iSup_subtype, Set.mem_Ioi]
      rfl
    rw [← measurable_iff_comap_le]
    have this : Filter.Tendsto (X ∘ ((↑) : Set.Ioi (0 : ℝ≥0) → ℝ≥0))
        ((𝓝[≠] 0).comap ((↑) : _ → ℝ≥0)) (𝓝 (X 0)) := by
      refine Filter.tendsto_comap'_iff ?_ |>.2
        (tendsto_pi_nhds.2 fun ω ↦ continuousAt_iff_punctured_nhds.1 (hX' ω).continuousAt)
      convert self_mem_nhdsWithin
      ext; simp [pos_iff_ne_zero]
    have l : NeBot ((𝓝[≠] (0 : ℝ≥0)).comap ((↑) : Set.Ioi (0 : ℝ≥0) → ℝ≥0)) := by
      refine comap_coe_neBot_of_le_principal <| le_principal_iff.2 ?_
      convert self_mem_nhdsWithin
      ext; simp [pos_iff_ne_zero]
    exact @measurable_of_tendsto_metrizable' _ _ (iSup _) _ _ _ _ _ _ _ _ l _
      (fun t ↦ (comap_measurable _).iSup' t) this
  -- We prove the result by showing that `m3` is independent of itself.
  refine measure_eq_zero_or_one_of_indep_self ?_ hA
  -- To do so, we show that for all `A ∈ m3`, all finite set `I ⊆ (0, +∞)` and all
  -- bounded continuous function `f : (I → ℝ) → ℝ`,
  -- `∫ ω in A, f (fun t ↦ X t) ∂P = P.real A * ∫ ω, f (fun t ↦ X t) ∂P`.
  refine indep_of_indep_of_le_right ?_ (hm3.trans this)
  refine indep_comap_process_of_bcf hm3' (fun _ ↦ (hX _).aemeasurable) fun A hA I f ↦ ?_
  -- If `I` is empty, there is nothing to do.
  obtain rfl | hI := I.eq_empty_or_nonempty
  · have : Subsingleton ((∅ : Finset (Set.Ioi (0 : ℝ≥0))) → ℝ) := inferInstance
    simp [this.eq_zero]
  -- We now assume `I` is not empty. We then prove that for all `ε > 0` such that `ε ≤ min I`,
  -- `∫ ω in A, f (fun t ↦ X t ω - X ε ω) ∂P = P.real A * ∫ ω, f (fun t ↦ X t ω - X ε ω) ∂P`.
  -- This follows from the fact that, because `A ∈ m3` in particular `A` is measurable
  -- with respect to `σ(X t | t ≤ ε)`. This `σ`-algebra is independent from
  -- `σ(X (ε + t) - X ε | t ≥ 0)` by the weak Markov property.
  have key (ε : ℝ≥0) (hε1 : 0 < ε) (hε2 : ε ≤ I.min' hI) :
      ∫ ω in A, f (fun t ↦ X t ω - X ε ω) ∂P = P.real A * ∫ ω, f (fun t ↦ X t ω - X ε ω) ∂P := by
    rw [IndepSets.setIntegral_eq_mul _ (by fun_prop) (hm3' A hA) (by fun_prop)]
    have := (IndepFun_iff_Indep _ _ _).1 <| h.indepFun_shift ε |>.symm
    refine indepSets_of_indepSets_of_le_right (Indep.singleton_indepSets this ?_) ?_
    · suffices m3 ≤ (.comap (fun ω (t : Set.Iic ε) ↦ X t ω) MeasurableSpace.pi) from this A hA
      apply iInf₂_le_of_le ε hε1
      rw [natural_eq_comap]
    simp only [Set.ofPred_subset_ofPred, ← measurableSpace_le_iff]
    apply comap_le_comap (fun x t ↦ x (t.1 - ε)) (by fun_prop)
    ext ω t
    simp only [Function.comp_apply, sub_left_inj]
    rw [add_tsub_cancel_of_le]
    exact hε2.trans (I.min'_le t.1 t.2)
  -- Because `f` is continuous and `X t ⟶ 0` almost surely as `t → 0`,
  -- we deduce that almost surely `f (fun t ↦ X t - X ε) ⟶ f (fun t ↦ X t)` as `t → 0`.
  have lol : ∀ᵐ ω ∂P, Tendsto (fun ε ↦ f (fun t ↦ X t ω - X ε ω)) (𝓝[>] 0)
      (𝓝 (f (fun t ↦ X t ω))) := by
    filter_upwards [h.tendsto_nhds_zero] with ω hω
    refine f.continuous.tendsto _ |>.comp (tendsto_pi_nhds.2 fun t ↦ ?_)
    convert (tendsto_nhdsWithin_of_tendsto_nhds hω).const_sub (X t ω)
    simp
  -- Because `f` is also bounded, we can apply the dominated convergence theorem to show that
  -- `∫ ω in A, f (fun t ↦ X t ω - X ε ω) ∂P ⟶ ∫ ω in A, f (fun t ↦ X t ω) ∂P`
  -- as `ε → 0⁺`.
  have h1 : Tendsto (fun ε ↦ ∫ ω in A, f (fun t ↦ X t ω - X ε ω) ∂P) (𝓝[>] 0)
      (𝓝 (∫ ω in A, f (fun t ↦ X t ω) ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖) ?_ ?_
      (integrable_const _) (ae_restrict_of_ae lol)
    · exact Eventually.of_forall fun _ ↦ Measurable.aestronglyMeasurable (by fun_prop)
    · exact Eventually.of_forall fun _ ↦ ae_of_all _ fun _ ↦ f.norm_coe_le_norm _
  -- But similarly we have that
  -- `P.real A * ∫ ω, f (fun t ↦ X t ω - X ε ω) ∂P ⟶ P.real A * ∫ ω in A, f (fun t ↦ X t ω) ∂P`
  -- as `ε → 0⁺`, and we can conclude by uniqueness of the limit.
  refine tendsto_nhds_unique h1 ?_
  refine Tendsto.congr' (f₁ := fun ε ↦ P.real A * ∫ ω, f (fun t ↦ X t ω - X ε ω) ∂P) ?_ ?_
  · apply eventually_nhdsGT (Set.mem_Ioi.mp (I.min' hI).2)
    rintro ε ⟨h1, h2⟩
    exact (key ε h1 h2).symm
  refine Filter.Tendsto.const_mul (b := P.real A) ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖) ?_ ?_
    (integrable_const _) lol
  · exact Eventually.of_forall fun _ ↦ Measurable.aestronglyMeasurable (by fun_prop)
  · exact Eventually.of_forall fun _ ↦ ae_of_all _ fun _ ↦ f.norm_coe_le_norm _

end IsBrownianReal

def preBrownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω ↦ ω t

@[fun_prop]
lemma measurable_preBrownian (t : ℝ≥0) : Measurable (preBrownian t) := by
  unfold preBrownian
  fun_prop

lemma hasLaw_preBrownian : HasLaw (fun ω ↦ (preBrownian · ω)) gaussianLimit gaussianLimit where
  aemeasurable := (Measurable.of_eval measurable_preBrownian).aemeasurable
  map_eq := Measure.map_id

lemma isPreBrownianReal_preBrownian : IsPreBrownianReal preBrownian gaussianLimit :=
  hasLaw_preBrownian.IsPreBrownianReal

-- for blueprint
lemma isGaussianProcess_preBrownian : IsGaussianProcess preBrownian gaussianLimit :=
  isPreBrownianReal_preBrownian.isGaussianProcess

lemma hasLaw_restrict_preBrownian (I : Finset ℝ≥0) :
    HasLaw (fun ω ↦ I.restrict (preBrownian · ω)) (gaussianProjectiveFamily I) gaussianLimit :=
  isPreBrownianReal_preBrownian.hasLaw I

lemma hasLaw_preBrownian_eval (t : ℝ≥0) :
    HasLaw (preBrownian t) (gaussianReal 0 t) gaussianLimit :=
  isPreBrownianReal_preBrownian.hasLaw_eval t

lemma hasLaw_preBrownian_sub (s t : ℝ≥0) :
    HasLaw (preBrownian s - preBrownian t) (gaussianReal 0 (nndist s t)) gaussianLimit :=
  isPreBrownianReal_preBrownian.hasLaw_sub s t

lemma isKolmogorovProcess_preBrownian {n : ℕ} (hn : 0 < n) :
    IsKolmogorovProcess preBrownian gaussianLimit (2 * n) n
      (Nat.doubleFactorial (2 * n - 1)) := by
  constructor
  · intro s t
    rw [← BorelSpace.measurable_eq]
    fun_prop
  rotate_left
  · positivity
  · positivity
  refine fun s t ↦ Eq.le ?_
  norm_cast
  simp_rw [edist_dist, Real.dist_eq]
  change ∫⁻ ω, (fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    ((preBrownian s - preBrownian t) ω) ∂_ = _
  rw [(hasLaw_preBrownian_sub s t).lintegral_comp (f := fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    (by fun_prop)]
  simp_rw [← fun x ↦ ENNReal.ofReal_pow (abs_nonneg x)]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [pow_abs_two_mul]
    rw [← centralMoment_of_integral_id_eq_zero _ (by simp), ← NNReal.sq_sqrt (nndist _ _),
    centralMoment_fun_two_mul_gaussianReal, ENNReal.ofReal_mul (by positivity), mul_comm]
    norm_cast
    congr
    rw [pow_mul, NNReal.sq_sqrt, ← ENNReal.ofReal_pow dist_nonneg]
    simp only [NNReal.coe_pow, coe_nndist, dist_nonneg, ENNReal.ofReal_pow]
  · simp_rw [← Real.norm_eq_abs]
    apply MemLp.integrable_norm_pow'
    exact IsGaussian.memLp_id _ _ (ENNReal.natCast_ne_top (2 * n))
  · exact ae_of_all _ fun _ ↦ by positivity

noncomputable
def brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := isPreBrownianReal_preBrownian.mk

@[fun_prop]
lemma measurable_brownian (t : ℝ≥0) : Measurable (brownian t) :=
  isPreBrownianReal_preBrownian.measurable_mk t

lemma brownian_ae_eq_preBrownian (t : ℝ≥0) :
    brownian t =ᵐ[gaussianLimit] preBrownian t :=
  isPreBrownianReal_preBrownian.mk_ae_eq t

lemma memHolder_brownian (ω : ℝ≥0 → ℝ) (t : ℝ≥0) (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) :
    ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (brownian · ω) U :=
  isPreBrownianReal_preBrownian.memHolder_mk ω t β hβ_pos hβ_lt

@[fun_prop]
lemma continuous_brownian (ω : ℝ≥0 → ℝ) : Continuous (brownian · ω) :=
  isPreBrownianReal_preBrownian.continuous_mk ω

theorem isBrownianReal_brownian : IsBrownianReal brownian gaussianLimit :=
  isPreBrownianReal_preBrownian.isBrownianReal_mk

-- for blueprint
lemma isGaussianProcess_brownian : IsGaussianProcess brownian gaussianLimit :=
  isBrownianReal_brownian.toIsPreBrownianReal.isGaussianProcess

lemma hasLaw_restrict_brownian {I : Finset ℝ≥0} :
    HasLaw (fun ω ↦ I.restrict (brownian · ω)) (gaussianProjectiveFamily I) gaussianLimit :=
  isBrownianReal_brownian.hasLaw I

lemma hasLaw_brownian : HasLaw (fun ω ↦ (brownian · ω)) gaussianLimit gaussianLimit :=
  isBrownianReal_brownian.hasLaw_gaussianLimit
    (Measurable.of_eval fun t ↦ measurable_brownian t).aemeasurable

lemma hasLaw_brownian_eval {t : ℝ≥0} :
    HasLaw (brownian t) (gaussianReal 0 t) gaussianLimit :=
  isBrownianReal_brownian.hasLaw_eval t

lemma hasLaw_brownian_sub {s t : ℝ≥0} :
    HasLaw (brownian s - brownian t) (gaussianReal 0 (nndist s t)) gaussianLimit :=
  isBrownianReal_brownian.hasLaw_sub s t

lemma measurable_brownian_uncurry : Measurable brownian.uncurry :=
  measurable_uncurry_of_continuous_of_measurable continuous_brownian measurable_brownian

lemma isKolmogorovProcess_brownian {n : ℕ} (hn : 0 < n) :
    IsKolmogorovProcess brownian gaussianLimit (2 * n) n
      (Nat.doubleFactorial (2 * n - 1)) where
  measurablePair := measurable_pair_of_measurable measurable_brownian
  kolmogorovCondition := (isKolmogorovProcess_preBrownian hn).IsAEKolmogorovProcess.congr
    (fun t ↦ (brownian_ae_eq_preBrownian t).symm) |>.kolmogorovCondition
  p_pos := by positivity
  q_pos := by positivity

lemma covariance_brownian (s t : ℝ≥0) : cov[brownian s, brownian t; gaussianLimit] = min s t :=
    isBrownianReal_brownian.covariance_eval s t

lemma hasIndepIncrements_brownian : HasIndepIncrements brownian gaussianLimit :=
  isBrownianReal_brownian.hasIndepIncrements

section Measure

noncomputable
def wienerMeasureAux : Measure {f : ℝ≥0 → ℝ // Continuous f} :=
  gaussianLimit.map (fun ω ↦ (⟨fun t ↦ brownian t ω, continuous_brownian ω⟩))

noncomputable
def wienerMeasure : Measure C(ℝ≥0, ℝ) :=
  wienerMeasureAux.map (MeasurableEquiv.continuousMapToFun ℝ≥0 ℝ).symm

end Measure

end ProbabilityTheory
