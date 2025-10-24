/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.HasGaussianLaw
import BrownianMotion.Continuity.KolmogorovChentsov
import BrownianMotion.Gaussian.GaussianProcess
import BrownianMotion.Gaussian.Moment
import BrownianMotion.Gaussian.ProjectiveLimit
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Brownian motion

-/

open MeasureTheory NNReal WithLp Finset
open scoped ENNReal NNReal Topology

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

namespace Finset

/-! ### Indexing the elements of a finset in order -/

variable [LinearOrder T] (I : Finset T)

/-- Given a finite set `I : Finset T` of cardinality `n`, `ofFin : Fin #I → T`
is the map `(t₁, ..., tₙ)`, where `t₁ < ... < tₙ` are the elements of `I`. -/
noncomputable def ofFin (i : Fin #I) : T := (I.sort (· ≤ ·)).get
  (Fin.cast (I.length_sort (· ≤ ·)).symm i)

lemma monotone_ofFin : Monotone I.ofFin :=
  fun i j hij ↦ (I.sort_sorted (· ≤ ·)).rel_get_of_le (by simpa)

lemma ofFin_mem (i : Fin #I) : I.ofFin i ∈ I := I.mem_sort (· ≤ ·) |>.1 <| List.get_mem _ _

/-- Given a finite set `I : Finset T`, and `t : I`,
`I.toFin t` returns the position of `t` in `I`. -/
noncomputable def toFin (i : I) : Fin #I :=
  haveI : NeZero #I := ⟨Nonempty.card_ne_zero ⟨i.1, i.2⟩⟩
  Fin.ofNat #I ((I.sort (· ≤ ·)).idxOf i.1)

@[simp]
lemma ofFin_toFin (i : I) : I.ofFin (I.toFin i) = i.1 := by
  rw [toFin, ofFin]
  nth_rw 2 [← (I.sort (· ≤ ·)).idxOf_get (a := i.1)]
  · congr
    ext
    simp only [Fin.ofNat_eq_cast, Fin.coe_cast, Fin.val_natCast]
    rw [Nat.mod_eq_of_lt]
    rw [← I.length_sort (· ≤ ·)]
    exact List.idxOf_lt_length_of_mem <| I.mem_sort (· ≤ ·) |>.2 i.2
  exact List.idxOf_lt_length_of_mem <| I.mem_sort (· ≤ ·) |>.2 i.2

@[simp]
lemma toFin_ofFin (i : Fin #I) : I.toFin ⟨I.ofFin i, ofFin_mem I i⟩ = i := by
  simp_rw [toFin, ofFin]
  rw [List.get_idxOf (sort_nodup ..)]
  simp

section Bot

variable [Bot T]

/-- Given a finite set `I : Finset T` of cardinality `n`, `ofFin' : Fin (#I + 1) → T`
is the map `(⊥, t₁, ..., tₙ)`, where `t₁ < ... < tₙ` are the elements of `I`. -/
noncomputable def ofFin' (i : Fin (#I + 1)) : T :=
  if h : i = 0
    then ⊥
    else I.ofFin (i.pred h)

@[simp]
lemma ofFin'_zero : I.ofFin' 0 = ⊥ := rfl

lemma ofFin'_of_ne_zero (i : Fin (#I + 1)) (hi : i ≠ 0) :
    I.ofFin' i = I.ofFin (i.pred hi) := by rw [ofFin', dif_neg hi]

@[simp]
lemma ofFin'_succ (i : Fin #I) :
    I.ofFin' i.succ = I.ofFin i := by
  rw [ofFin'_of_ne_zero, Fin.pred_succ]
  simp

lemma ofFin'_mem (i : Fin (#I + 1)) (hi : i ≠ 0) : I.ofFin' i ∈ I := by
  rw [ofFin'_of_ne_zero _ _ hi]
  exact ofFin_mem I _

end Bot

lemma monotone_ofFin' [OrderBot T] : Monotone (I.ofFin') := by
  intro i j hij
  obtain rfl | hi := eq_or_ne i 0
  · simp
  rw [ofFin'_of_ne_zero I i hi, ofFin'_of_ne_zero I j (by aesop)]
  apply monotone_ofFin
  simpa

end Finset

namespace ProbabilityTheory

section Increments

/-! ### Independent increments -/

/-- A process `X : T → Ω → E` has independent increments if for any `n ≥ 1` and `t₁ ≤ ... ≤ tₙ`,
the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are independent. -/
def HasIndepIncrements [Preorder T] [Sub E] [MeasurableSpace E] (X : T → Ω → E) (P : Measure Ω) :
    Prop :=
  ∀ n, ∀ t : Fin (n + 1) → T, Monotone t →
    iIndepFun (fun (i : Fin n) ω ↦ X (t i.succ) ω - X (t i.castSucc) ω) P

/-- `incrementsToRestrict I` is a continuous linear map `f` such that
`f (xₜ₁, xₜ₂ - xₜ₁, ..., xₜₙ - xₜₙ₋₁) = (xₜ₁, ..., xₜₙ)`. -/
noncomputable def incrementsToRestrict [LinearOrder T] (R : Type*) [Semiring R] [AddCommMonoid E]
    [Module R E] [TopologicalSpace E] [ContinuousAdd E] (I : Finset T) :
    (Fin #I → E) →L[R] (I → E) :=
  { toFun x i := ∑ j ≤ I.toFin i, x j
    map_add' x y := by ext; simp [sum_add_distrib]
    map_smul' m x := by ext; simp [smul_sum]
    cont := by fun_prop }

lemma incrementsToRestrict_increments_ofFin'_ae_eq_restrict [LinearOrder T] (R : Type*) [OrderBot T]
    [Semiring R] [AddCommGroup E] [Module R E] [TopologicalSpace E] [ContinuousAdd E]
    {X : T → Ω → E} (h : ∀ᵐ ω ∂P, X ⊥ ω = 0) (I : Finset T) :
    (fun ω ↦ I.restrict (X · ω)) =ᵐ[P]
      (incrementsToRestrict R I) ∘
        (fun ω i ↦ X (I.ofFin' i.succ) ω - X (I.ofFin' i.castSucc) ω) := by
  filter_upwards [h] with ω hω
  ext t
  simp only [restrict, incrementsToRestrict, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply]
  rw [Fin.sum_Iic_sub (I.toFin t) (fun j ↦ X (I.ofFin' j) ω)]
  simp [hω]

lemma HasIndepIncrements.indepFun_sub_sub [Preorder T] [MeasurableSpace E] [AddGroup E]
    {X : T → Ω → E} (h : HasIndepIncrements X P) {r s t : T} (hrs : r ≤ s) (hst : s ≤ t) :
    IndepFun (X s - X r) (X t - X s) P := by
  let τ : Fin (2 + 1) → T := ![r, s, t]
  have hτ : Monotone τ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    any_goals simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, le_refl, τ]
    any_goals assumption
    any_goals contradiction
    exact hrs.trans hst
  have h' : (0 : Fin (1 + 1)) ≠ (1 : Fin (1 + 1)) := by simp
  simpa using (h 2 τ hτ).indepFun h'

lemma HasIndepIncrements.indepFun_eval_sub [Preorder T] [MeasurableSpace E] [AddGroup E]
    {X : T → Ω → E} (h : HasIndepIncrements X P) {r s t : T} (hrs : r ≤ s) (hst : s ≤ t)
    (hX : ∀ᵐ ω ∂P, X r ω = 0) :
    IndepFun (X s) (X t - X s) P := by
  have := h.indepFun_sub_sub hrs hst
  refine this.congr ?_ .rfl
  filter_upwards [hX] with ω hω using by simp [hω]

/-- A stochastic process `X` with independent increments and such that `X t` is gaussian for
all `t` is a Gaussian process. -/
lemma HasIndepIncrements.isGaussianProcess [LinearOrder T] [OrderBot T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    {X : T → Ω → E} (law : ∀ t, HasGaussianLaw (X t) P) (h_bot : ∀ᵐ ω ∂P, X ⊥ ω = 0)
    (incr : HasIndepIncrements X P) :
    IsGaussianProcess X P where
  hasGaussianLaw I := by
    have := (law ⊥).isProbabilityMeasure
    obtain rfl | hI := I.eq_empty_or_nonempty
    · constructor
      have : P.map (fun ω ↦ Finset.restrict ∅ fun x ↦ X x ω) = .dirac Classical.ofNonempty := by
        ext s -
        apply Subsingleton.set_cases (p := fun s ↦ Measure.map _ _ s = _)
        · simp
        simp only [measure_univ]
        exact @measure_univ _ _ _
          (Measure.isProbabilityMeasure_map (aemeasurable_pi_lambda _ fun _ ↦ (law _).aemeasurable))
      rw [this]
      infer_instance
    have := incrementsToRestrict_increments_ofFin'_ae_eq_restrict ℝ h_bot I
    refine @HasGaussianLaw.congr _ _ _ _ _ _ _ _ _ _ ?_ this.symm
    refine @HasGaussianLaw.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
    exact (incr _ _ (monotone_ofFin' I)).hasGaussianLaw fun i ↦
      incr.indepFun_eval_sub bot_le
        (monotone_ofFin' I (Fin.castSucc_le_succ i)) h_bot |>.hasGaussianLaw_sub (law _) (law _)

end Increments

section IsPreBrownian

variable (X : ℝ≥0 → Ω → ℝ)

/-- A stochastic process is called **pre-Brownian** if its finite-dimensional laws are those
of a Brownian motion, see `gaussianProjectiveFamily`. -/
class IsPreBrownian (P : Measure Ω := by volume_tac) : Prop where
  mk' ::
  hasLaw : ∀ I : Finset ℝ≥0, HasLaw (fun ω ↦ I.restrict (X · ω)) (gaussianProjectiveFamily I) P

variable {X} {P : Measure Ω}

lemma IsPreBrownian.congr {Y : ℝ≥0 → Ω → ℝ} [hX : IsPreBrownian X P] (h : ∀ t, X t =ᵐ[P] Y t) :
    IsPreBrownian Y P where
  hasLaw I := by
    refine (hX.hasLaw I).congr ?_
    have : ∀ᵐ ω ∂P, ∀ i : I, X i ω = Y i ω := ae_all_iff.2 fun _ ↦ h _
    filter_upwards [this] with ω hω using funext fun i ↦ (hω i).symm

instance IsPreBrownian.isGaussianProcess [IsPreBrownian X P] : IsGaussianProcess X P where
  hasGaussianLaw I := (IsPreBrownian.hasLaw I).hasGaussianLaw

lemma IsPreBrownian.aemeasurable [IsPreBrownian X P] (t : ℝ≥0) : AEMeasurable (X t) P :=
  HasGaussianLaw.aemeasurable

lemma IsPreBrownian.hasLaw_gaussianLimit [IsPreBrownian X P]
    (hX : AEMeasurable (fun ω ↦ (X · ω)) P) :
    HasLaw (fun ω ↦ (X · ω)) gaussianLimit P where
  aemeasurable := hX
  map_eq := by
    refine isProjectiveLimit_gaussianLimit.unique (fun I ↦ ?_) |>.symm
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
    exact (IsPreBrownian.hasLaw I).map_eq

lemma HasLaw.isPreBrownian (hX : HasLaw (fun ω ↦ (X · ω)) gaussianLimit P) :
    IsPreBrownian X P where
  hasLaw _ := hasLaw_restrict_gaussianLimit.comp hX

lemma IsPreBrownian.hasLaw_eval [h : IsPreBrownian X P] (t : ℝ≥0) :
    HasLaw (X t) (gaussianReal 0 t) P :=
  (hasLaw_eval_gaussianProjectiveFamily ⟨t, by simp⟩).comp (h.hasLaw {t})

lemma IsPreBrownian.hasLaw_sub [IsPreBrownian X P] (s t : ℝ≥0) :
    HasLaw (X s - X t) (gaussianReal 0 (max (s - t) (t - s))) P :=
  (hasLaw_eval_sub_eval_gaussianProjectiveFamily {s, t} ⟨s, by simp⟩ ⟨t, by simp⟩).comp
    (IsPreBrownian.hasLaw _)

lemma IsPreBrownian.integral_eval [h : IsPreBrownian X P] (t : ℝ≥0) :
    P[X t] = 0 := by
  rw [(h.hasLaw_eval t).integral_eq, integral_id_gaussianReal]

lemma IsPreBrownian.covariance_eval [h : IsPreBrownian X P] (s t : ℝ≥0) :
    cov[X s, X t; P] = min s t := by
  convert (h.hasLaw {s, t}).covariance_comp
    (f := Function.eval ⟨s, by simp⟩) (g := Function.eval ⟨t, by simp⟩) ?_ ?_
  · rw [covariance_eval_gaussianProjectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)

lemma IsPreBrownian.covariance_fun_eval [h : IsPreBrownian X P] (s t : ℝ≥0) :
    cov[fun ω ↦ X s ω, fun ω ↦ X t ω; P] = min s t :=
  h.covariance_eval s t

lemma IsPreBrownian.isAEKolmogorovProcess {n : ℕ} (hn : 0 < n) [h : IsPreBrownian X P] :
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
  · simp_rw [pow_two_mul_abs]
    rw [← centralMoment_of_integral_id_eq_zero _ (by simp), ← NNReal.sq_sqrt (max _ _),
    centralMoment_fun_two_mul_gaussianReal, ENNReal.ofReal_mul (by positivity), mul_comm]
    norm_cast
    rw [pow_mul, NNReal.sq_sqrt, ← ENNReal.ofReal_pow dist_nonneg, ← NNReal.nndist_eq,
      NNReal.coe_pow, coe_nndist]
  · simp_rw [← Real.norm_eq_abs]
    apply MemLp.integrable_norm_pow'
    exact IsGaussian.memLp_id _ _ (ENNReal.natCast_ne_top (2 * n))
  · exact ae_of_all _ fun _ ↦ by positivity

/-- If `X` is a pre-Brownian process then there exists a modification of `X` which is measurable
and locally β-Hölder for `0 < β < 1/2` (and thus continuous). See `IsPreBrownian.mk`. -/
lemma IsPreBrownian.exists_continuous_modification [h : IsPreBrownian X P] :
    ∃ Y : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))),
        ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · ω) U :=
  haveI := h.isGaussianProcess.isProbabilityMeasure
  exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ h.isAEKolmogorovProcess (by positivity : 0 < n + 2))
    (fun n ↦ by finiteness) zero_lt_one (fun n ↦ by simp; norm_cast; omega)

/-- If `h : IsPreBrownian X P`, then `h.mk X` is a continuous modification of `X`. -/
protected noncomputable def IsPreBrownian.mk (X) [h : IsPreBrownian X P] : ℝ≥0 → Ω → ℝ :=
  h.exists_continuous_modification.choose

lemma IsPreBrownian.memHolder_mk [h : IsPreBrownian X P] (ω : Ω) (t : ℝ≥0) (β : ℝ≥0)
    (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) :
    ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (h.mk X · ω) U := by
  convert h.exists_continuous_modification.choose_spec.2.2 ω t β hβ_pos ?_
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
lemma IsPreBrownian.measurable_mk [h : IsPreBrownian X P] (t : ℝ≥0) :
    Measurable (h.mk X t) :=
  h.exists_continuous_modification.choose_spec.1 t

lemma IsPreBrownian.mk_ae_eq [h : IsPreBrownian X P] (t : ℝ≥0) :
    h.mk X t =ᵐ[P] X t :=
  h.exists_continuous_modification.choose_spec.2.1 t

lemma IsPreBrownian.continuous_mk [h : IsPreBrownian X P] (ω : Ω) :
    Continuous (h.mk X · ω) := by
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  obtain ⟨U, hu_mem, ⟨C, h⟩⟩ := h.memHolder_mk ω t 4⁻¹ (by norm_num)
    (NNReal.inv_lt_inv (by norm_num) (by norm_num))
  exact (h.continuousOn (by norm_num)).continuousAt hu_mem

lemma IsPreBrownian.hasIndepIncrements [h : IsPreBrownian X P] : HasIndepIncrements X P := by
  have : IsProbabilityMeasure P := h.isGaussianProcess.isProbabilityMeasure
  refine fun n t ht ↦ HasGaussianLaw.iIndepFun_of_covariance_eq_zero fun i j hij ↦ ?_
  rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right]
  · simp_rw [IsPreBrownian.covariance_fun_eval]
    wlog h' : i < j generalizing i j
    · simp_rw [← this j i hij.symm (by omega), min_comm]
      ring
    have h1 : i.succ ≤ j.succ := Fin.strictMono_succ h' |>.le
    have h2 : i.castSucc ≤ j.succ := Fin.le_of_lt h1
    have h3 : i.castSucc ≤ j.castSucc := Fin.le_castSucc_iff.mpr h1
    rw [min_eq_left (ht h1), min_eq_left (ht h'), min_eq_left (ht h2), min_eq_left (ht h3)]
    simp
  all_goals exact HasGaussianLaw.memLp_two

lemma IsGaussianProcess.isPreBrownian_of_covariance (h1 : IsGaussianProcess X P)
    (h2 : ∀ t, P[X t] = 0) (h3 : ∀ s t, s ≤ t → cov[X s, X t; P] = s) :
    IsPreBrownian X P where
  hasLaw I := by
    refine ⟨aemeasurable_pi_lambda _ fun _ ↦ h1.aemeasurable _, ?_⟩
    apply (MeasurableEquiv.toLp 2 (_ → ℝ)).map_measurableEquiv_injective
    rw [MeasurableEquiv.coe_toLp, ← PiLp.continuousLinearEquiv_symm_apply 2 ℝ]
    apply IsGaussian.ext
    · rw [integral_map, integral_map, integral_map]
      · simp only [PiLp.continuousLinearEquiv_symm_apply, id_eq]
        simp_rw [← PiLp.continuousLinearEquiv_symm_apply 2 ℝ, ← ContinuousLinearEquiv.coe_coe]
        rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_gaussianProjectiveFamily,
          ContinuousLinearMap.integral_comp_comm]
        · simp only [ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply]
          congr with i
          rw [eval_integral]
          · simpa using h2 _
          · exact fun _ ↦ h1.hasGaussianLaw_eval.integrable
        · exact Integrable.of_eval fun _ ↦ h1.hasGaussianLaw_eval.integrable
        · exact IsGaussian.integrable_id
      any_goals fun_prop
      exact aemeasurable_pi_lambda _ fun _ ↦ h1.aemeasurable _
    · refine ContinuousBilinForm.ext_of_isSymm (isPosSemidef_covInnerBilin ?_).isSymm
        (isPosSemidef_covInnerBilin ?_).isSymm fun x ↦ ?_
      any_goals exact IsGaussian.memLp_two_id
      rw [PiLp.continuousLinearEquiv_symm_apply, covInnerBilin_apply_pi, covInnerBilin_apply_pi]
      · congrm ∑ i, ∑ j, _ * ?_
        rw [covariance_eval_gaussianProjectiveFamily, covariance_map]
        · wlog hij : i.1 ≤ j.1 generalizing i j
          · rw [covariance_comm, this j i (by grind), min_comm]
          rw [min_eq_left hij]
          exact h3 i j hij
        any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
        exact aemeasurable_pi_lambda _ (fun _ ↦ h1.aemeasurable _)
      all_goals exact fun _ ↦ HasGaussianLaw.memLp_two

lemma HasIndepIncrements.isPreBrownian_of_hasLaw
    (law : ∀ t, HasLaw (X t) (gaussianReal 0 t) P) (incr : HasIndepIncrements X P) :
    IsPreBrownian X P := by
  apply IsGaussianProcess.isPreBrownian_of_covariance
  · exact incr.isGaussianProcess (fun t ↦ (law t).hasGaussianLaw)
      (law 0).ae_eq_const_of_gaussianReal
  · intro t
    rw [(law t).integral_eq, integral_id_gaussianReal]
  · intro s t hst
    have h1 := incr.indepFun_eval_sub (zero_le s) hst (law 0).ae_eq_const_of_gaussianReal
    have := (law 0).isProbabilityMeasure_iff.1 inferInstance
    have h2 : X t = X t - X s + X s := by simp
    rw [h2, covariance_add_right, h1.covariance_eq_zero, covariance_self, (law s).variance_eq,
      variance_id_gaussianReal]
    · simp
    · exact (law s).aemeasurable
    · exact (law s).hasGaussianLaw.memLp_two
    · exact (law t).hasGaussianLaw.memLp_two.sub (law s).hasGaussianLaw.memLp_two
    · exact (law s).hasGaussianLaw.memLp_two
    · exact (law t).hasGaussianLaw.memLp_two.sub (law s).hasGaussianLaw.memLp_two
    · exact (law s).hasGaussianLaw.memLp_two

lemma IsPreBrownian.smul [IsPreBrownian X P] {c : ℝ≥0} (hc : c ≠ 0) :
    IsPreBrownian (fun t ω ↦ (X (c * t) ω) / √c) P := by
  refine IsGaussianProcess.isPreBrownian_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · have this t ω : X (c * t) ω / √c = (1 / √c) • ((X ∘ (c * ·)) t ω) := by
      simp [inv_mul_eq_div]
    simp_rw [this]
    exact (IsGaussianProcess.comp_right _).smul _
  · rw [integral_div, IsPreBrownian.integral_eval, zero_div]
  · rw [covariance_fun_div_left, covariance_fun_div_right, IsPreBrownian.covariance_eval,
      min_eq_left]
    · simp [field]
    · exact mul_le_mul_left' hst c

lemma IsPreBrownian.shift [h : IsPreBrownian X P] (t₀ : ℝ≥0) :
    IsPreBrownian (fun t ω ↦ X (t₀ + t) ω - X t₀ ω) P := by
  refine IsGaussianProcess.isPreBrownian_of_covariance ⟨fun I ↦ ?_⟩ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · let L : (({t₀} ∪ I.image (t₀ + ·) : Finset ℝ≥0) → ℝ) →L[ℝ] I → ℝ :=
      { toFun x t := x ⟨t₀ + t.1, by simp⟩ - x ⟨t₀, by simp⟩
        map_add' x y := by ext; simp; ring
        map_smul' c x := by ext; simp; ring }
    have : (fun ω ↦ I.restrict (fun t ↦ X (t₀ + t) ω - X t₀ ω)) =
        L ∘ (fun ω ↦ ({t₀} ∪ I.image (t₀ + ·)).restrict (X · ω)) := by ext; simp [L]
    rw [this]
    infer_instance
  · rw [integral_sub, IsPreBrownian.integral_eval, IsPreBrownian.integral_eval, sub_zero]
    all_goals exact HasGaussianLaw.integrable
  · have := h.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right,
      h.covariance_eval, h.covariance_eval, h.covariance_eval, h.covariance_eval, ← add_min,
      min_eq_left hst, min_eq_right, min_eq_left, min_self]
    any_goals simp
    all_goals exact HasGaussianLaw.memLp_two

lemma IsPreBrownian.inv [h : IsPreBrownian X P] :
    IsPreBrownian (fun t ω ↦ t * (X (1 / t) ω)) P := by
  refine IsGaussianProcess.isPreBrownian_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · exact (IsGaussianProcess.comp_right _).smul _
  · rw [integral_const_mul, IsPreBrownian.integral_eval, mul_zero]
  · have := h.isGaussianProcess.isProbabilityMeasure
    rw [covariance_mul_left, covariance_mul_right, h.covariance_eval]
    obtain rfl | hs := eq_or_ne s 0
    · simp
    have : 0 < t := (pos_of_ne_zero hs).trans_le hst
    rw [min_eq_right]
    · norm_cast
      field_simp
    exact one_div_le_one_div_of_le (pos_of_ne_zero hs) hst

end IsPreBrownian

section IsBrownian

variable (X : ℝ≥0 → Ω → ℝ)

/-- A stochastic process is called **Brownian** if its finite-dimensional laws are those
of a Brownian motion, see `IsPreBrownian`, and if it has almost-sure continuous paths. -/
class IsBrownian (X) (P : Measure Ω := by volume_tac) : Prop extends IsPreBrownian X P where
  cont : ∀ᵐ ω ∂P, Continuous (X · ω)

variable {X}

instance IsPreBrownian.isBrownian_mk [h : IsPreBrownian X P] :
    IsBrownian (h.mk X) P where
  toIsPreBrownian := h.congr fun _ ↦ (h.mk_ae_eq _).symm
  cont := ae_of_all _ h.continuous_mk

lemma IsBrownian.smul [h : IsBrownian X P] {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownian (fun t ω ↦ (X (c * t) ω) / √c) P where
  toIsPreBrownian := h.toIsPreBrownian.smul hc
  cont := by
    filter_upwards [h.cont] with ω h
    fun_prop

lemma IsBrownian.shift [h : IsBrownian X P] (t₀ : ℝ≥0) :
    IsBrownian (fun t ω ↦ X (t₀ + t) ω - X t₀ ω) P where
  toIsPreBrownian := h.toIsPreBrownian.shift t₀
  cont := by
    filter_upwards [h.cont] with ω h
    fun_prop

/-- If `X` is a Brownian motion then so is `fun t ω ↦ t * (B (1 / t) ω)`. -/
lemma IsBrownian.inv [h : IsBrownian X P] :
    IsBrownian (fun t ω ↦ t * (X (1 / t) ω)) P where
  toIsPreBrownian := h.toIsPreBrownian.inv
  cont := by
    obtain ⟨s, cs, ds⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
    let Y := fun t ω ↦ t * X (1 / t) ω
    have hY : IsPreBrownian Y P := h.toIsPreBrownian.inv
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
      convert Set.subset_univ _
      exact (ds.diff_singleton 0).closure_eq
    have h4 : ∀ᵐ ω ∂P, ∀ t, Y t ω = hY.mk Y t ω := by
      filter_upwards [this, (hY.isBrownian_mk.hasLaw_eval 0).ae_eq_const_of_gaussianReal]
        with ω h1 h2 t
      obtain rfl | ht := eq_or_ne t 0
      · simp_all [Y]
      exact h1 t ht
    filter_upwards [h4] with ω h
    simp_rw [Y] at h
    simp_rw [h]
    exact hY.continuous_mk ω

lemma IsBrownian.tendsto_nhds_zero [h : IsBrownian X P] :
    ∀ᵐ ω ∂P, Filter.Tendsto (X · ω) (𝓝 0) (𝓝 0) := by
  filter_upwards [h.cont, (h.hasLaw_eval 0).ae_eq_const_of_gaussianReal] with ω h1 h2
  convert h1.tendsto 0
  exact h2.symm

lemma IsBrownian.tendsto_div_id_atTop [h : IsBrownian X P] :
    ∀ᵐ ω ∂P, Filter.Tendsto (fun t ↦ (X t ω) / t) .atTop (𝓝 0) := by
  filter_upwards [h.inv.tendsto_nhds_zero] with ω hω
  have : (fun t ↦ (X t ω) / t) = (fun t ↦ t * (X (1 / t) ω)) ∘ (fun t ↦ t⁻¹) := by ext; simp [field]
  rw [this]
  exact hω.comp tendsto_inv_atTop_zero

end IsBrownian

def preBrownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω ↦ ω t

@[fun_prop]
lemma measurable_preBrownian (t : ℝ≥0) : Measurable (preBrownian t) := by
  unfold preBrownian
  fun_prop

lemma hasLaw_preBrownian : HasLaw (fun ω ↦ (preBrownian · ω)) gaussianLimit gaussianLimit where
  aemeasurable := (measurable_pi_lambda _ measurable_preBrownian).aemeasurable
  map_eq := Measure.map_id

instance isPreBrownian_preBrownian : IsPreBrownian preBrownian gaussianLimit :=
  hasLaw_preBrownian.isPreBrownian

-- for blueprint
instance isGaussianProcess_preBrownian : IsGaussianProcess preBrownian gaussianLimit :=
  inferInstance

lemma hasLaw_restrict_preBrownian (I : Finset ℝ≥0) :
    HasLaw (fun ω ↦ I.restrict (preBrownian · ω)) (gaussianProjectiveFamily I) gaussianLimit :=
  IsPreBrownian.hasLaw I

lemma hasLaw_preBrownian_eval (t : ℝ≥0) :
    HasLaw (preBrownian t) (gaussianReal 0 t) gaussianLimit :=
  IsPreBrownian.hasLaw_eval t

lemma hasLaw_preBrownian_sub (s t : ℝ≥0) :
    HasLaw (preBrownian s - preBrownian t) (gaussianReal 0 (max (s - t) (t - s))) gaussianLimit :=
  IsPreBrownian.hasLaw_sub s t

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
  · simp_rw [pow_two_mul_abs]
    rw [← centralMoment_of_integral_id_eq_zero _ (by simp), ← NNReal.sq_sqrt (max _ _),
    centralMoment_fun_two_mul_gaussianReal, ENNReal.ofReal_mul (by positivity), mul_comm]
    norm_cast
    rw [pow_mul, NNReal.sq_sqrt, ← ENNReal.ofReal_pow dist_nonneg, ← NNReal.nndist_eq,
      NNReal.coe_pow, coe_nndist]
  · simp_rw [← Real.norm_eq_abs]
    apply MemLp.integrable_norm_pow'
    exact IsGaussian.memLp_id _ _ (ENNReal.natCast_ne_top (2 * n))
  · exact ae_of_all _ fun _ ↦ by positivity

noncomputable
def brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := isPreBrownian_preBrownian.mk

@[fun_prop]
lemma measurable_brownian (t : ℝ≥0) : Measurable (brownian t) :=
  IsPreBrownian.measurable_mk t

lemma brownian_ae_eq_preBrownian (t : ℝ≥0) :
    brownian t =ᵐ[gaussianLimit] preBrownian t :=
  IsPreBrownian.mk_ae_eq t

lemma memHolder_brownian (ω : ℝ≥0 → ℝ) (t : ℝ≥0) (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) :
    ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (brownian · ω) U :=
  IsPreBrownian.memHolder_mk ω t β hβ_pos hβ_lt

@[fun_prop]
lemma continuous_brownian (ω : ℝ≥0 → ℝ) : Continuous (brownian · ω) :=
  IsPreBrownian.continuous_mk ω

instance IsBrownian_brownian : IsBrownian brownian gaussianLimit :=
  IsPreBrownian.isBrownian_mk

-- for blueprint
instance isGaussianProcess_brownian : IsGaussianProcess brownian gaussianLimit :=
  inferInstance

lemma hasLaw_restrict_brownian {I : Finset ℝ≥0} :
    HasLaw (fun ω ↦ I.restrict (brownian · ω)) (gaussianProjectiveFamily I) gaussianLimit :=
  IsPreBrownian.hasLaw I

lemma hasLaw_brownian : HasLaw (fun ω ↦ (brownian · ω)) gaussianLimit gaussianLimit :=
  IsPreBrownian.hasLaw_gaussianLimit
    (measurable_pi_lambda _ fun t ↦ measurable_brownian t).aemeasurable

lemma hasLaw_brownian_eval {t : ℝ≥0} :
    HasLaw (brownian t) (gaussianReal 0 t) gaussianLimit :=
  IsPreBrownian.hasLaw_eval t

lemma hasLaw_brownian_sub {s t : ℝ≥0} :
    HasLaw (brownian s - brownian t) (gaussianReal 0 (max (s - t) (t - s))) gaussianLimit :=
  IsPreBrownian.hasLaw_sub s t

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
    IsPreBrownian.covariance_eval s t

lemma hasIndepIncrements_brownian : HasIndepIncrements brownian gaussianLimit :=
  IsPreBrownian.hasIndepIncrements

section Measure

noncomputable
def wienerMeasureAux : Measure {f : ℝ≥0 → ℝ // Continuous f} :=
  gaussianLimit.map (fun ω ↦ (⟨fun t ↦ brownian t ω, continuous_brownian ω⟩))

section ContinuousMap.MeasurableSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

instance : MeasurableSpace C(X, Y) := borel _
instance : BorelSpace C(X, Y) where
  measurable_eq := rfl

lemma isClosed_sUnion_of_finite {X : Type*} [TopologicalSpace X] {s : Set (Set X)}
    (h1 : s.Finite) (h2 : ∀ t ∈ s, IsClosed t) : IsClosed (⋃₀ s) := by
  rw [Set.sUnion_eq_biUnion]
  exact h1.isClosed_biUnion h2

open TopologicalSpace in
lemma ContinuousMap.borel_eq_iSup_comap_eval [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y] :
    borel C(X, Y) = ⨆ a : X, (borel Y).comap fun b ↦ b a := by
  -- https://math.stackexchange.com/questions/4789531/when-does-the-borel-sigma-algebra-of-compact-convergence-coincide-with-the-pr
  apply le_antisymm
  swap
  · refine iSup_le fun x ↦ ?_
    simp_rw [← measurable_iff_comap_le, ← BorelSpace.measurable_eq]
    exact Continuous.measurable (by fun_prop)
  -- Denote by `M(K, U)` the set of functions `f` such that `Set.MapsTo f K U`. These form a
  -- basis for the compact-open topology when `K` is compact and `U` is open.
  -- Because `C(X, Y)` is second-countable, it suffices to prove that those sets are measurable.
  -- Let therefore `K` be a compact set of `X` and `U` an open set of `Y`.
  rw [borel_eq_generateFrom_of_subbasis ContinuousMap.compactOpen_eq]
  refine MeasurableSpace.generateFrom_le fun s hs ↦ ?_
  obtain ⟨K, hK, U, hU, hs⟩ := hs
  rw [← hs]
  -- Consider `V` a countable basis of the topology on Y.
  let V := countableBasis Y
  have hV : IsTopologicalBasis V := isBasis_countableBasis Y
  have cV : V.Countable := countable_countableBasis Y
  let W₁ := {v | v ∈ V ∧ closure v ⊆ U}
  -- Consider `W` the set of `closure v`, where `v ∈ V` and `closure v ⊆ U`.
  let W := {v | ∃ u ∈ V, v ⊆ U ∧ v = closure u}
  -- Because `V` is countable, so is `W`.
  have cW : W.Countable := by
    apply (cV.image closure ).mono
    rintro - ⟨u, hu, -, rfl⟩
    exact ⟨u, hu, rfl⟩
  -- Because `Y` is regular, we can write that `U = ⋃_{v ∈ W} v`.
  have U_eq_sUnion_W : U = ⋃₀ W := by
    ext x
    rw [Set.mem_sUnion]
    constructor
    · intro hx
      obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := hV.nhds_basis_closure x |>.mem_iff.1 <| hU.mem_nhds hx
      exact ⟨closure v, ⟨v, hv2, hv3, rfl⟩, subset_closure hv1⟩
    · rintro ⟨-, ⟨t, ht1, ht2, rfl⟩, hx⟩
      exact ht2 hx
  -- Similarly, we can write that `U = ⋃_{v ∈ V, closure v ⊆ U} v`.
  have U_eq_sUnion_W₁ : U = ⋃₀ W₁ := by
    ext x
    rw [Set.mem_sUnion]
    refine ⟨fun hx ↦ ?_, fun ⟨t, ⟨ht1, ht2⟩, hx⟩ ↦ ht2 <| subset_closure hx⟩
    obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := hV.nhds_basis_closure x |>.mem_iff.1 <| hU.mem_nhds hx
    exact ⟨v, ⟨hv2, hv3⟩, hv1⟩
  -- For any continuous `f` such that `f '' K ⊆ U`, because `K` is compact, `f '' K` is compact.
  -- But we just proved that `U = ⋃_{v ∈ V, closure v ⊆ U} v`, and each `v ∈ V` is open,
  -- so there exists `J` a finite set of `v ∈ V` such that `closure v ⊆ U` and
  -- `f '' K ⊆ ⋃ v ∈ J, v`. We thus have `f '' K ⊆ ⋃ v ∈ J, closure v`. This is equivalent to
  -- having `I` a finite subset of `W` such that `f '' K ⊆ ⋃ v ∈ I, v`.
  have (f : C(X, Y)) (hf : K.MapsTo f U) : ∃ I, I.Finite ∧ I ⊆ W ∧ K.MapsTo f (⋃₀ I) := by
    simp_rw [Set.mapsTo_iff_image_subset] at hf ⊢
    rw [U_eq_sUnion_W₁, Set.sUnion_eq_biUnion] at hf
    have : ∀ i ∈ {v | v ∈ V ∧ closure v ⊆ U}, IsOpen i :=
      fun x ⟨hx, _⟩ ↦ hV.isOpen hx
    obtain ⟨b, hb1, hb2, hb3⟩ := (hK.image f.continuous).elim_finite_subcover_image this hf
    refine ⟨closure '' b, hb2.image _, ?_, ?_⟩
    · rintro - ⟨v, hv, rfl⟩
      exact ⟨v, (hb1 hv).1, (hb1 hv).2, rfl⟩
    rw [← Set.sUnion_eq_biUnion] at hb3
    exact hb3.trans <| Set.sUnion_mono_subsets fun _ ↦ subset_closure
  -- Therefore, we obtain that
  -- `M(K, U) = ⋃_{I ⊆ W, I finite}, M(K, ⋃ v ∈ I, v)`.
  have : {f : C(X, Y) | K.MapsTo f U} =
      ⋃₀ {v | ∃ I, I.Finite ∧ I ⊆ W ∧ v = {f : C(X, Y) | K.MapsTo f (⋃₀ I)}} := by
    ext f
    rw [Set.mem_sUnion]
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨I, hI1, hI2, hI3⟩ := this f h
      exact ⟨{f : C(X, Y) | K.MapsTo f (⋃₀ I)}, ⟨I, hI1, hI2, rfl⟩, hI3⟩
    · rintro ⟨-, ⟨I, hI1, hI2, rfl⟩, h⟩
      simp only [Set.mapsTo_iff_image_subset] at h ⊢
      rw [U_eq_sUnion_W]
      exact h.trans <| Set.sUnion_subset_sUnion hI2
  simp only
  rw [this]
  -- In particular, because `W` is countable, si this is a countable union.
  -- To show measurability it is therefore enough to show the measurability of each term.
  apply MeasurableSet.sUnion
  · let f : Set (Set Y) → Set C(X, Y) := fun I ↦ {f : C(X, Y) | Set.MapsTo (⇑f) K (⋃₀ I)}
    refine ((Set.countable_setOf_finite_subset cW).image f).mono ?_
    rintro - ⟨I, hI1, hI2, rfl⟩
    exact ⟨I, ⟨hI1, hI2⟩, rfl⟩
  -- Consider now `I` a finite subset of `W`.
  rintro - ⟨I, hI1, hI2, rfl⟩
  -- First, `⋃ v ∈ I, v` is closed as a finite union of closed sets.
  have hI : IsClosed (⋃₀ I) := by
    refine isClosed_sUnion_of_finite hI1 fun x hx ↦ ?_
    obtain ⟨u, -, -, rfl⟩ := hI2 hx
    exact isClosed_closure
  -- Consider `Q` a countable dense subset of `K`, which exists by second-countability assumption.
  obtain ⟨Q, cQ, dQ⟩ := TopologicalSpace.exists_countable_dense K
  have Q_sub_K : Subtype.val '' Q ⊆ K := Subtype.coe_image_subset K Q
  -- Because `f` is continuous and `⋃ v ∈ I, v` is closed and `Q` is dense in `K`, having
  -- `f '' K ⊆ ⋃ v ∈ I, v` is the same as `f '' Q ⊆ ⋃ v ∈ I, v`.
  have : {f : C(X, Y) | K.MapsTo f (⋃₀ I)} =
      {f : C(X, Y) | (Subtype.val '' Q).MapsTo f (⋃₀ I)} := by
    ext f
    refine ⟨fun h x hx ↦ h (Q_sub_K hx), fun h x hx ↦ ?_⟩
    obtain ⟨u, hu1, hu2⟩ := mem_closure_iff_seq_limit.1 <| Subtype.dense_iff.1 dQ hx
    exact hI.mem_of_tendsto ((f.continuous.tendsto x).comp hu2)
      (Filter.Eventually.of_forall fun n ↦ h (hu1 n))
  -- We can write `M(Q, ⋃ v ∈ I, v) = ⋂ q ∈ Q, (fun f ↦ f q) ⁻¹' (⋃ v ∈ I, v)`.
  have : {f : C(X, Y) | K.MapsTo f (⋃₀ I)} =
      ⋂ q ∈ Subtype.val '' Q, (fun f ↦ f q) ⁻¹' (⋃₀ I) := by
    rw [this]
    ext f
    rw [Set.mem_iInter₂]
    exact ⟨fun h x hx ↦ h hx, fun h x hx ↦ h x hx⟩
  rw [this]
  -- This is a countable intersection, so it suffices to prove that each term is measurable.
  -- Because `⋃ v ∈ I, v` is closed, it is measurable, so it suffices to prove that
  -- for any `q ∈ Q`, `fun f ↦ f q` is measurable for the product σ-algebra.
  -- The latter is the coarsest σ-algebra which makes the maps `fun f ↦ f x` measurable,
  -- so we are done.
  refine MeasurableSet.biInter (cQ.image _)
    fun q hq ↦ MeasurableSet.preimage hI.measurableSet (Measurable.le (le_iSup _ q) ?_)
  rw [BorelSpace.measurable_eq (α := Y)]
  exact comap_measurable _

lemma ContinuousMap.measurableSpace_eq_iSup_comap_eval
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y] :
    (inferInstance : MeasurableSpace C(X, Y))
      = ⨆ a : X, (inferInstance : MeasurableSpace Y).comap fun b ↦ b a := by
  simp_rw [BorelSpace.measurable_eq, borel_eq_iSup_comap_eval]

lemma ContinuousMap.measurable_iff_eval {α : Type*} [MeasurableSpace α]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (g : α → C(X, Y)) :
    Measurable g ↔ ∀ (x : X), Measurable fun (a : α) ↦ g a x := by
  simp_rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, measurable_iff_comap_le,
    MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp, Function.comp_def]

end ContinuousMap.MeasurableSpace

def MeasurableEquiv.continuousMap : {f : ℝ≥0 → ℝ // Continuous f} ≃ᵐ C(ℝ≥0, ℝ) where
  toFun := fun f ↦ ContinuousMap.mk f.1 f.2
  invFun := fun f ↦ ⟨f, f.continuous⟩
  left_inv f := rfl
  right_inv f := rfl
  measurable_toFun := by
    simp only [Equiv.coe_fn_mk]
    rw [ContinuousMap.measurable_iff_eval]
    intro x
    simp only [ContinuousMap.coe_mk]
    revert x
    rw [← measurable_pi_iff]
    exact measurable_subtype_coe
  measurable_invFun := by
    simp only [Equiv.coe_fn_symm_mk]
    refine Measurable.subtype_mk ?_
    rw [measurable_pi_iff]
    exact fun _ ↦ Continuous.measurable (by fun_prop)

noncomputable
def wienerMeasure : Measure C(ℝ≥0, ℝ) := wienerMeasureAux.map MeasurableEquiv.continuousMap

end Measure

end ProbabilityTheory
