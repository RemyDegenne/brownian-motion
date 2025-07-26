/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Continuity.KolmogorovChentsov
import BrownianMotion.Gaussian.GaussianProcess
import BrownianMotion.Gaussian.Moment
import BrownianMotion.Gaussian.ProjectiveLimit
import Mathlib.Probability.Independence.Integrable
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Brownian motion

-/

open MeasureTheory NNReal WithLp Finset
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

def preBrownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω ↦ ω t

@[fun_prop]
lemma measurable_preBrownian (t : ℝ≥0) : Measurable (preBrownian t) := by
  unfold preBrownian
  fun_prop

lemma hasLaw_preBrownian : HasLaw (fun ω ↦ (preBrownian · ω)) gaussianLimit gaussianLimit where
  aemeasurable := (measurable_pi_lambda _ measurable_preBrownian).aemeasurable
  map_eq := Measure.map_id

lemma hasLaw_restrict_preBrownian (I : Finset ℝ≥0) :
    HasLaw (fun ω ↦ I.restrict (preBrownian · ω)) (gaussianProjectiveFamily I) gaussianLimit :=
  hasLaw_restrict_gaussianLimit.comp hasLaw_preBrownian

lemma hasLaw_preBrownian_eval (t : ℝ≥0) :
    HasLaw (preBrownian t) (gaussianReal 0 t) gaussianLimit :=
  (hasLaw_eval_gaussianProjectiveFamily ⟨t, by simp⟩).comp
    (hasLaw_restrict_preBrownian ({t} : Finset ℝ≥0))

instance isGaussianProcess_preBrownian : IsGaussianProcess preBrownian gaussianLimit where
  hasGaussianLaw I := (hasLaw_restrict_preBrownian I).hasGaussianLaw

lemma hasLaw_preBrownian_sub (s t : ℝ≥0) :
    HasLaw (preBrownian s - preBrownian t) (gaussianReal 0 (max (s - t) (t - s)))
      gaussianLimit := by
  have : preBrownian s - preBrownian t =
      ((fun x ↦ x ⟨s, by simp⟩) - (fun x ↦ x ⟨t, by simp⟩)) ∘ ({s, t} : Finset ℝ≥0).restrict := by
    ext; simp [preBrownian]
  rw [this]
  exact (hasLaw_eval_sub_eval_gaussianProjectiveFamily _ _).comp hasLaw_restrict_gaussianLimit

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

lemma exists_brownian :
    ∃ Y : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[gaussianLimit] preBrownian t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))),
          ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · ω) U :=
  exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ (isKolmogorovProcess_preBrownian (by positivity : 0 < n + 2)).IsAEKolmogorovProcess)
    (fun n ↦ by finiteness) zero_lt_one (fun n ↦ by simp; norm_cast; omega)

noncomputable
def brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  exists_brownian.choose

@[fun_prop]
lemma measurable_brownian (t : ℝ≥0) : Measurable (brownian t) :=
  exists_brownian.choose_spec.1 t

lemma brownian_ae_eq_preBrownian (t : ℝ≥0) :
    brownian t =ᵐ[gaussianLimit] preBrownian t :=
  exists_brownian.choose_spec.2.1 t

lemma memHolder_brownian (ω : ℝ≥0 → ℝ) (t : ℝ≥0) (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) :
    ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (brownian · ω) U := by
  convert exists_brownian.choose_spec.2.2 ω t β hβ_pos ?_
  suffices ⨆ n, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)) = 2⁻¹ by rw [this]; norm_cast
  refine iSup_eq_of_forall_le_of_tendsto (F := Filter.atTop) (fun n ↦ ?_) ?_
  · calc
    ((↑(n + 2) : ℝ) - 1) / (2 * ↑(n + 2)) = 2⁻¹ * (n + 1) / (n + 2) := by field_simp; ring
    _ ≤ 2⁻¹ * 1 := by grw [mul_div_assoc, (div_le_one₀ (by positivity)).2]; linarith
    _ = 2⁻¹ := mul_one _
  · have : (fun n : ℕ ↦ ((↑(n + 2) : ℝ) - 1) / (2 * ↑(n + 2))) =
        (fun n : ℕ ↦ 2⁻¹ * ((n : ℝ) / (n + 1))) ∘ (fun n ↦ n + 1) := by ext n; field_simp; ring
    rw [this]
    refine Filter.Tendsto.comp ?_ (Filter.tendsto_add_atTop_nat 1)
    nth_rw 2 [← mul_one 2⁻¹]
    exact (tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul _

@[fun_prop]
lemma continuous_brownian (ω : ℝ≥0 → ℝ) : Continuous (brownian · ω) := by
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  obtain ⟨U, hu_mem, ⟨C, h⟩⟩ := memHolder_brownian ω t 4⁻¹ (by norm_num)
    (NNReal.inv_lt_inv (by norm_num) (by norm_num))
  exact (h.continuousOn (by norm_num)).continuousAt hu_mem

lemma hasLaw_restrict_brownian {I : Finset ℝ≥0} :
    HasLaw (fun ω ↦ I.restrict (brownian · ω)) (gaussianProjectiveFamily I) gaussianLimit := by
  refine (hasLaw_restrict_preBrownian I).congr ?_
  filter_upwards [ae_all_iff.2 fun i : I ↦ brownian_ae_eq_preBrownian i.1] with ω hω
  ext; simp [hω]

lemma hasLaw_brownian : HasLaw (fun ω ↦ (brownian · ω)) gaussianLimit gaussianLimit where
  aemeasurable := (measurable_pi_lambda _ measurable_brownian).aemeasurable
  map_eq := by
    symm
    refine isProjectiveLimit_gaussianLimit.unique fun I ↦ ?_
    rw [Measure.map_map (by fun_prop) (measurable_pi_lambda _ measurable_brownian)]
    exact hasLaw_restrict_brownian.map_eq

lemma hasLaw_brownian_eval {t : ℝ≥0} :
    HasLaw (brownian t) (gaussianReal 0 t) gaussianLimit :=
  (hasLaw_preBrownian_eval t).congr (brownian_ae_eq_preBrownian t)

lemma hasLaw_brownian_sub {s t : ℝ≥0} :
    HasLaw (brownian s - brownian t) (gaussianReal 0 (max (s - t) (t - s))) gaussianLimit :=
  (hasLaw_preBrownian_sub s t).congr
    ((brownian_ae_eq_preBrownian s).sub (brownian_ae_eq_preBrownian t))

instance isGaussianProcess_brownian : IsGaussianProcess brownian gaussianLimit :=
  isGaussianProcess_preBrownian.modification fun t ↦ (brownian_ae_eq_preBrownian t).symm

open NNReal Filter Topology in
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

lemma iIndepFun_iff_charFun_eq_pi {ι Ω : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Π i, Ω → (E i)}
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] (mX : ∀ i, AEMeasurable (X i) μ) :
    iIndepFun X μ ↔ ∀ t,
      charFun (μ.map fun ω ↦ toLp 2 (X · ω)) t = ∏ i, charFun (μ.map (X i)) (t i) := sorry
-- PR #26269 in Mathlib

lemma indepFun_iff_charFun_eq_mul {Ω E F : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [MeasurableSpace E]
    [MeasurableSpace F] [CompleteSpace E] [CompleteSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → E} {Y : Ω → F} (mX : AEMeasurable X P) (mY : AEMeasurable Y P) :
    IndepFun X Y P ↔ ∀ t,
      charFun (P.map fun ω ↦ toLp 2 (X ω, Y ω)) t =
      charFun (P.map X) t.fst * charFun (P.map Y) t.snd := sorry
-- PR #26269 in Mathlib

lemma IndepFun.integral_mul_eq_mul_integral {Ω 𝓧 𝓨 𝕜 : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace 𝓧] [MeasurableSpace 𝓨] [RCLike 𝕜] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → 𝕜} {g : 𝓨 → 𝕜} (hXY : IndepFun X Y P)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) (hf : AEStronglyMeasurable f (P.map X))
    (hg : AEStronglyMeasurable g (P.map Y)) :
    ∫ ω, f (X ω) * g (Y ω) ∂P = (∫ ω, f (X ω) ∂P) * ∫ ω, g (Y ω) ∂P := by
  change ∫ ω, (fun x ↦ f x.1 * g x.2) (X ω, Y ω) ∂P = _
  rw [← integral_map (f := fun x ↦ f x.1 * g x.2) (φ := fun ω ↦ (X ω, Y ω)),
    (indepFun_iff_map_prod_eq_prod_map_map hX hY).1 hXY, integral_prod_mul, integral_map,
    integral_map]
  any_goals fun_prop
  rw [(indepFun_iff_map_prod_eq_prod_map_map hX hY).1 hXY]
  refine AEStronglyMeasurable.mul ?_ ?_
  · exact hf.comp_fst
  · exact hg.comp_snd

lemma IndepFun.charFun_add_eq_mul {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [CompleteSpace E] [BorelSpace E]
    [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : IndepFun X Y P) :
    charFun (P.map (X + Y)) = charFun (P.map X) * charFun (P.map Y) := by
  ext t
  rw [charFun, integral_map]
  · simp only [Pi.add_apply, inner_add_left, Complex.ofReal_add, add_mul, Complex.exp_add,
      Pi.mul_apply]
    rw [hXY.integral_mul_eq_mul_integral
        (f := fun x ↦ Complex.exp ((inner ℝ x t) * Complex.I))
        (g := fun y ↦ Complex.exp ((inner ℝ y t) * Complex.I)), charFun, charFun, integral_map,
      integral_map]
    any_goals assumption
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact mX.add mY
  · exact Measurable.aestronglyMeasurable (by fun_prop)

-- PR #26269 in Mathlib

lemma HasGaussianLaw.iIndepFun_of_covariance_eq_zero {ι Ω : Type*} [Fintype ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → ℝ}
    [h1 : HasGaussianLaw (fun ω ↦ (X · ω)) P] (h2 : ∀ i j : ι, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P := by
  refine iIndepFun_iff_charFun_eq_pi (fun _ ↦ h1.aemeasurable.eval) |>.2 fun ξ ↦ ?_
  simp_rw [HasGaussianLaw.charFun_toLp, ← sum_sub_distrib, Complex.exp_sum,
    HasGaussianLaw.charFun_map_real]
  congrm ∏ i, Complex.exp (_ - ?_)
  rw [Fintype.sum_eq_single i]
  · simp [covariance_self, h1.aemeasurable.eval, pow_two, mul_div_assoc]
  · exact fun j hj ↦ by simp [h2 i j hj.symm]

lemma HasGaussianLaw.indepFun_of_covariance_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    [h1 : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] (h2 : cov[X, Y; P] = 0) :
    IndepFun X Y P := by
  refine indepFun_iff_charFun_eq_mul h1.aemeasurable.fst h1.aemeasurable.snd |>.2 fun ξ ↦ ?_
  simp_rw [HasGaussianLaw.charFun_toLp', h1.fst.charFun_map_real,
    h1.snd.charFun_map_real, ← Complex.exp_add, h2, Complex.ofReal_zero, mul_zero]
  congr
  ring

lemma iIndepFun.hasGaussianLaw {ι Ω : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Π i, Ω → (E i)}
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] [∀ i, HasGaussianLaw (X i) μ] ( hX : iIndepFun X μ) :
    HasGaussianLaw (fun ω ↦ (X · ω)) μ := by
  constructor
  rw [← isGaussian_map_equiv_iff (PiLp.continuousLinearEquiv 2 ℝ E).symm,
    isGaussian_iff_gaussian_charFun]
  let f : ContinuousBilinForm ℝ (PiLp 2 E) :=
    letI g : LinearMap.BilinForm ℝ (PiLp 2 E) := LinearMap.mk₂ ℝ
      (fun x y : PiLp 2 E ↦ ∑ i, covInnerBilin (μ.map (X i)) (x i) (y i))
      (fun x y z ↦ by simp [Finset.sum_add_distrib])
      (fun c m n ↦ by simp [Finset.mul_sum])
      (fun x y z ↦ by simp [Finset.sum_add_distrib])
      (fun c m n ↦ by simp [Finset.mul_sum])
    g.mkContinuous₂ (∑ i, ‖covInnerBilin (μ.map (X i))‖) <| by
      intro x y
      simp only [LinearMap.mk₂_apply, Real.norm_eq_abs, g]
      grw [Finset.abs_sum_le_sum_abs, Finset.sum_mul, Finset.sum_mul]
      gcongr with i _
      grw [← Real.norm_eq_abs, ContinuousLinearMap.le_opNorm₂, PiLp.norm_apply_le x,
        PiLp.norm_apply_le y]
  refine ⟨toLp 2 fun i ↦ (μ.map (X i))[id], f, ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩, ?_⟩
  · simp only [LinearMap.mkContinuous₂_apply, LinearMap.mk₂_apply, f]
    congr with i
    rw [covInnerBilin_comm]
    exact HasGaussianLaw.memLp_two
  · simp only [LinearMap.mkContinuous₂_apply, LinearMap.mk₂_apply, map_sum, RCLike.re_to_real, f]
    refine Fintype.sum_nonneg fun i ↦ ?_
    convert covInnerBilin_self_nonneg _ (x i)
    · infer_instance
    · exact HasGaussianLaw.memLp_two
  intro t
  rw [PiLp.continuousLinearEquiv_symm_apply, AEMeasurable.map_map_of_aemeasurable]
  · change charFun (μ.map fun ω ↦ toLp 2 (X · ω)) t = _
    rw [(iIndepFun_iff_charFun_eq_pi _).1 hX]
    · simp only [PiLp.inner_apply, PiLp.toLp_apply, Complex.ofReal_sum, sum_mul,
        LinearMap.mkContinuous₂_apply, LinearMap.mk₂_apply, sum_div, ← sum_sub_distrib,
        Complex.exp_sum, f]
      congr with i
      rw [IsGaussian.charFun_eq]
    · exact fun i ↦ HasGaussianLaw.aemeasurable
  · fun_prop
  · exact aemeasurable_pi_lambda _ fun _ ↦ HasGaussianLaw.aemeasurable

/-- A process `X : T → Ω → E` has independent increments if for any `n ≥ 2` and `t₁ ≤ ... ≤ tₙ`,
the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are independent. -/
def HasIndepIncrements {Ω T E : Type*} {mΩ : MeasurableSpace Ω} [Sub E]
    [Preorder T] [MeasurableSpace E] (X : T → Ω → E) (P : Measure Ω) : Prop :=
  ∀ n, ∀ t : Fin (n + 2) → T, Monotone t →
    iIndepFun (fun (i : Fin (n + 1)) ω ↦ X (t i.succ) ω - X (t i.castSucc) ω) P

lemma mem_pair_iff {α : Type*} [DecidableEq α] {x y z : α} :
    x ∈ ({y, z} : Finset α) ↔ x = y ∨ x = z := by simp

lemma covariance_brownian (s t : ℝ≥0) : cov[brownian s, brownian t; gaussianLimit] = min s t := by
  have h1 : brownian s = (fun x ↦ x ⟨s, by simp⟩) ∘
      (fun ω ↦ ({s, t} : Finset ℝ≥0).restrict (brownian · ω)) := by ext; simp
  have h2 : brownian t = (fun x ↦ x ⟨t, by simp⟩) ∘
      (fun ω ↦ ({s, t} : Finset ℝ≥0).restrict (brownian · ω)) := by ext; simp
  rw [h1, h2, ← covariance_map]
  · simp_rw [hasLaw_restrict_brownian.map_eq]
    rw [covariance_eval_gaussianProjectiveFamily]
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  exact Measurable.aemeasurable <| by fun_prop

lemma hasIndepIncrements_brownian : HasIndepIncrements brownian gaussianLimit := by
  refine fun n t ht ↦ HasGaussianLaw.iIndepFun_of_covariance_eq_zero (h1 := ?_) ?_
  · let L : ((Finset.univ.image t) → ℝ) →L[ℝ] Fin (n + 1) → ℝ :=
      { toFun := (fun x (i : Fin (n + 1)) ↦ x i.succ - x i.castSucc) ∘
          (fun x (i : Fin (n + 2)) ↦ x ⟨t i, by simp⟩)
        map_add' x y := by ext; simp; ring
        map_smul' m x := by ext; simp; ring
        cont := by fun_prop }
    have : (fun ω i ↦ brownian (t i.succ) ω - brownian (t i.castSucc) ω) =
        L ∘ fun ω ↦ (Finset.univ.image t).restrict (brownian · ω) := by ext; simp [L]
    rw [this]
    infer_instance
  intro i j hij
  rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right]
  · simp_rw [covariance_brownian]
    wlog h : i < j
    · simp_rw [← this n t ht j i hij.symm (by omega), min_comm]
      ring
    have h1 : i.succ ≤ j.succ := Fin.succ_le_succ_iff.mpr h.le
    have h2 : i.castSucc ≤ j.succ := Fin.le_of_lt h1
    have h3 : i.castSucc ≤ j.castSucc := Fin.le_castSucc_iff.mpr h1
    rw [min_eq_left (ht h1), min_eq_left (ht h), min_eq_left (ht h2), min_eq_left (ht h3)]
    simp
  all_goals exact HasGaussianLaw.memLp_two

section IsBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (X : ℝ≥0 → Ω → ℝ)

class IsBrownian (P : Measure Ω := by volume_tac) : Prop where
  hasLaw : ∀ I : Finset ℝ≥0, HasLaw (fun ω ↦ I.restrict (X · ω)) (gaussianProjectiveFamily I) P
  cont : ∀ᵐ ω ∂P, Continuous (X · ω)

variable {X} {P : Measure Ω}

instance IsBrownian.isGaussianProcess [h : IsBrownian X P] : IsGaussianProcess X P where
  hasGaussianLaw I := (h.hasLaw I).hasGaussianLaw

lemma IsBrownian.aemeasurable [IsBrownian X P] (t : ℝ≥0) : AEMeasurable (X t) P :=
  HasGaussianLaw.aemeasurable

lemma IsBrownian.hasLaw_gaussianLimit [IsBrownian X P] (hX : AEMeasurable (fun ω ↦ (X · ω)) P) :
    HasLaw (fun ω ↦ (X · ω)) gaussianLimit P where
  aemeasurable := hX
  map_eq := by
    refine isProjectiveLimit_gaussianLimit.unique ?_ |>.symm
    intro I
    rw [AEMeasurable.map_map_of_aemeasurable _ hX]
    · exact (IsBrownian.hasLaw I).map_eq
    · fun_prop

lemma isBrownian_of_hasLaw_gaussianLimit (cont : ∀ᵐ ω ∂P, Continuous (X · ω))
    (hX : HasLaw (fun ω ↦ (X · ω)) gaussianLimit P) : IsBrownian X P where
  hasLaw _ := hasLaw_restrict_gaussianLimit.comp hX
  cont := cont

instance isBrownian_brownian : IsBrownian brownian gaussianLimit :=
  isBrownian_of_hasLaw_gaussianLimit (ae_of_all _ continuous_brownian) hasLaw_brownian

@[gcongr]
private lemma mono_cast (n m : ℕ) (h : n = m) (i j : Fin n) (hij : i ≤ j) :
    h ▸ i ≤ h ▸ j := by
  cases h
  exact hij

private lemma fin_cast_eq (n m : ℕ) (h : n = m) (i : Fin n) :
    h ▸ i = Fin.cast h i := by
  cases h; rfl

section secret

variable {I : Finset ℝ≥0} (hI : I.Nonempty)

noncomputable def toFin : Fin (#I - 1 + 2) → ℝ≥0 := fun i ↦ if h : i = 0 then 0 else
      I.sort (· ≤ ·) |>.get (I.length_sort (· ≤ ·) ▸
        (haveI := hI.card_ne_zero; by omega : #I - 1 + 1 = #I) ▸ i.pred h)

lemma monotone_toFin : Monotone (toFin hI) := by
  intro i j hij
  obtain rfl | hi := eq_or_ne i 0
  · simp [toFin]
  rw [← Fin.pos_iff_ne_zero] at hi
  simp only [List.get_eq_getElem, hi.ne', ↓reduceDIte, (hi.trans_le hij).ne', toFin]
  apply (I.sort_sorted (· ≤ ·)).rel_get_of_le
  simp only [Fin.eta]
  gcongr
  exact Fin.pred_le_pred_iff.mpr hij

end secret

lemma IsBrownian.hasLaw_eval [h : IsBrownian X P] (t : ℝ≥0) : HasLaw (X t) (gaussianReal 0 t) P :=
  (hasLaw_eval_gaussianProjectiveFamily ⟨t, by simp⟩).comp (h.hasLaw {t})

lemma IsBrownian.law_zero [IsBrownian X P] : X 0 =ᵐ[P] 0 := by
  change id ∘ (X 0) =ᵐ[P] (fun _ ↦ 0) ∘ (X 0)
  apply ae_eq_comp
  · exact IsBrownian.aemeasurable 0
  · rw [(IsBrownian.hasLaw_eval 0).map_eq, gaussianReal_zero_var]
    exact MeasureTheory.ae_eq_dirac _

lemma IsBrownian.covariance_fun_eval [h : IsBrownian X P] (s t : ℝ≥0) :
    cov[fun ω ↦ X s ω, fun ω ↦ X t ω; P] = min s t := by
  convert (h.hasLaw {s, t}).covariance_fun_comp (f := Function.eval ⟨s, by simp⟩)
    (g := Function.eval ⟨t, by simp⟩) _ _
  · simp [covariance_eval_gaussianProjectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)

lemma IsBrownian.hasIndepIncrements [h : IsBrownian X P] : HasIndepIncrements X P := by
  have : IsProbabilityMeasure P := HasGaussianLaw.isProbabilityMeasure (X := X 0)
  refine fun n t ht ↦ HasGaussianLaw.iIndepFun_of_covariance_eq_zero (h1 := ?_) ?_
  · let L : ((Finset.univ.image t) → ℝ) →L[ℝ] Fin (n + 1) → ℝ :=
      { toFun := (fun x (i : Fin (n + 1)) ↦ x i.succ - x i.castSucc) ∘
          (fun x (i : Fin (n + 2)) ↦ x ⟨t i, by simp⟩)
        map_add' x y := by ext; simp; ring
        map_smul' m x := by ext; simp; ring
        cont := by fun_prop }
    have : (fun ω i ↦ X (t i.succ) ω - X (t i.castSucc) ω) =
        L ∘ fun ω ↦ (Finset.univ.image t).restrict (X · ω) := by ext; simp [L]
    rw [this]
    infer_instance
  intro i j hij
  rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right]
  · repeat rw [IsBrownian.covariance_fun_eval]
    wlog h' : i < j generalizing i j
    · simp_rw [← this j i hij.symm (by omega), min_comm]
      ring
    have h1 : i.succ ≤ j.succ := Fin.succ_le_succ_iff.mpr h'.le
    have h2 : i.castSucc ≤ j.succ := Fin.le_of_lt h1
    have h3 : i.castSucc ≤ j.castSucc := Fin.le_castSucc_iff.mpr h1
    rw [min_eq_left (ht h1), min_eq_left (ht h'), min_eq_left (ht h2), min_eq_left (ht h3)]
    simp
  all_goals exact HasGaussianLaw.memLp_two

noncomputable def lin (I : Finset ℝ≥0) : (Fin (#I - 1 + 1) → ℝ) →L[ℝ] (I → ℝ) :=
  { toFun x i := ∑ j ≤ (I.sort (· ≤ ·)).idxOf i.1, x (Fin.ofNat _ j)
    map_add' x y := by ext; simp [sum_add_distrib]
    map_smul' m x := by ext; simp [mul_sum]
    cont := by fun_prop }

lemma aux (h : ∀ᵐ ω ∂P, X 0 ω = 0) {I : Finset ℝ≥0} (hI : I.Nonempty) :
    (fun ω ↦ I.restrict (X · ω)) =ᵐ[P]
        (lin I) ∘ (fun ω i ↦ X (toFin hI i.succ) ω - X (toFin hI i.castSucc) ω) := by
  filter_upwards [h] with ω hω
  ext t
  simp only [restrict, Fin.ofNat_eq_cast, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, toFin, Fin.succ_ne_zero, ↓reduceDIte, Fin.pred_succ, List.get_eq_getElem,
    Fin.castSucc_eq_zero_iff, Function.comp_apply, Fin.natCast_eq_zero, lin]
  rw [← Finset.Iio_succ_eq_Iic, Nat.succ_eq_succ, Finset.Iio_eq_Ico]
  symm
  have : #I ≠ 0 := hI.card_ne_zero
  have : NeZero (#I - 1 + 2) := ⟨by omega⟩
  convert Finset.sum_Ico_sub (fun n ↦ X (toFin hI (Fin.ofNat _ n)) ω) (bot_le)
    with n hn
  · simp only [toFin, Fin.ofNat_eq_cast, Fin.natCast_eq_zero, List.get_eq_getElem]
    have : n + 1 < #I - 1 + 2 := by
      have := Finset.mem_Ico.1 hn |>.2
      have := (I.sort (· ≤ ·)).idxOf_le_length (a := t)
      rw [I.length_sort (· ≤ ·)] at this
      have : (I.sort (· ≤ ·)).idxOf t.1 < #I := by
        rw [← I.length_sort (· ≤ ·)]
        apply List.idxOf_lt_length_of_mem
        rw [Finset.mem_sort]
        exact t.2
      omega
    split_ifs with h
    · have := Nat.le_of_dvd (by simp) h
      omega
    · congr
      change _ = (Fin.ofNat (#I - 1 + 2) (n + (Fin.val (1 : Fin (#I - 1 + 2))))).pred _
      conv_rhs => enter [1]; rw [← Fin.ofNat_add]
      rw [Fin.pred_add_one]
      · simp only [Fin.ofNat_eq_cast]
        ext
        simp only [Fin.val_natCast, Fin.coe_castLT]
        rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
        · omega
        · omega
      simp only [Fin.ofNat_eq_cast, Fin.val_natCast]
      apply Nat.mod_lt_of_lt
      omega
  · have : n + 1 < #I - 1 + 2 := by
      have := Finset.mem_Ico.1 hn |>.2
      have := (I.sort (· ≤ ·)).idxOf_le_length (a := t)
      rw [I.length_sort (· ≤ ·)] at this
      have : (I.sort (· ≤ ·)).idxOf t.1 < #I := by
        rw [← I.length_sort (· ≤ ·)]
        apply List.idxOf_lt_length_of_mem
        rw [Finset.mem_sort]
        exact t.2
      omega
    simp only [toFin, Fin.ofNat_eq_cast, Fin.natCast_eq_zero, List.get_eq_getElem]
    split_ifs with h1 h2 h3
    · rfl
    · have : n ≠ 0 := by
        by_contra!
        rw [this] at h2
        exact h2 (Nat.dvd_zero _)
      have := Nat.le_of_dvd (NE.ne.pos this) h1
      omega
    · have : n ≠ 0 := by
        by_contra!
        rw [this] at h1
        exact h1 (Nat.dvd_zero _)
      have := Nat.le_of_dvd (NE.ne.pos this) h3
      omega
    · congr
      ext
      simp only [Fin.coe_castSucc, Fin.val_natCast]
      rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
      · omega
      · omega
  · simp only [toFin, Nat.succ_eq_add_one, Fin.ofNat_eq_cast, Fin.natCast_eq_zero,
    List.get_eq_getElem, bot_eq_zero', dvd_zero, ↓reduceDIte, hω, sub_zero]
    split_ifs with h
    · have : (I.sort (· ≤ ·)).idxOf t.1 < #I := by
        rw [← I.length_sort (· ≤ ·)]
        apply List.idxOf_lt_length_of_mem
        rw [Finset.mem_sort]
        exact t.2
      have := Nat.le_of_dvd (by simp) h
      omega
    · congr
      have : (I.sort (· ≤ ·)).idxOf t.1 < (I.sort (· ≤ ·)).length := by
        apply List.idxOf_lt_length_of_mem
        rw [Finset.mem_sort]
        exact t.2
      have this' : (I.sort (· ≤ ·)).idxOf t.1 < #I := by
        rw [← I.length_sort (· ≤ ·)]
        apply List.idxOf_lt_length_of_mem
        rw [Finset.mem_sort]
        exact t.2
      · nth_rw 1 [← List.idxOf_get this]
        congr
        rw [fin_cast_eq, Fin.coe_cast, fin_cast_eq, Fin.coe_cast, Fin.coe_pred, Fin.val_natCast,
          Nat.mod_eq_of_lt, Nat.add_sub_cancel]
        omega

-- lemma IndepFun.hasLaw_sub_of_gaussian {X Y : Ω → ℝ} {μX μY : ℝ} {vX vY : ℝ≥0}
--     (hX : HasLaw X (gaussianReal μX vX) P) (hY : HasLaw Y (gaussianReal μY vY) P)
--     (h : IndepFun X Y P) :
--     HasLaw (X - Y) (gaussianReal (μX - μY) (vX + vY)) P where
--   aemeasurable := hX.aemeasurable.sub hY.aemeasurable
--   map_eq := by
--     have : IsProbabilityMeasure P := hX.hasGaussianLaw.isProbabilityMeasure
--     apply Measure.ext_of_charFun
--     ext t
--     rw [charFun, integral_map]
--     · simp only [Pi.sub_apply, sub_eq_add_neg, RCLike.inner_apply, conj_trivial, mul_add, mul_neg,
--         Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, add_mul, neg_mul,
--         Complex.exp_add]
--       have : ∫ ω, Complex.exp (t * X ω * Complex.I) * Complex.exp (-(t * Y ω * Complex.I)) ∂P
--        = ∫ ω, (fun x ↦ Complex.exp (t * x.1 * Complex.I) * Complex.exp (-(t * x.2 * Complex.I)))
--           (X ω, Y ω) ∂P := by congr
--       rw [this, ← integral_map
--           (f := (fun x ↦ Complex.exp (t * x.1 * Complex.I) * Complex.exp (-(t * x.2 * Complex.I))))
--           (φ := (fun ω ↦ (X ω, Y ω))), (indepFun_iff_map_prod_eq_prod_map_map _ _).1,
--         integral_prod_mul (μ := P.map X) (ν := P.map Y) (fun x ↦ Complex.exp (t * x * Complex.I))
--           (fun x ↦ Complex.exp (-(t * x * Complex.I))), hX.map_eq, hY.map_eq]
--       · simp_rw [← neg_mul]
--         have h1 : ∫ (x : ℝ), Complex.exp (↑t * ↑x * Complex.I) ∂gaussianReal μX vX =
--             charFun (gaussianReal μX vX) t := by
--           rw [charFun]
--           simp
--         have h2 : ∫ (x : ℝ), Complex.exp (-↑t * ↑x * Complex.I) ∂gaussianReal μY vY =
--             charFun (gaussianReal μY vY) (-t) := by
--           rw [charFun]
--           simp
--         simp_rw [h1, h2, charFun_gaussianReal, ← Complex.exp_add]
--         congr
--         push_cast
--         ring
--       · exact h
--       · exact hX.aemeasurable
--       · exact hY.aemeasurable
--       · exact hX.aemeasurable.prodMk hY.aemeasurable
--       · fun_prop
--     · exact hX.aemeasurable.sub hY.aemeasurable
--     · fun_prop

lemma IndepFun.hasLaw_sub_of_gaussian {X Y : Ω → ℝ} {μX μY : ℝ} {vX vY : ℝ≥0}
    (hX : HasLaw X (gaussianReal μX vX) P) (hY : HasLaw (X + Y) (gaussianReal μY vY) P)
    (h : IndepFun X Y P) :
    HasLaw Y (gaussianReal (μY - μX) (vY - vX)) P where
  aemeasurable := by
    rw [show Y = X + Y - X by simp]
    exact hY.aemeasurable.sub hX.aemeasurable
  map_eq := by
    have : IsProbabilityMeasure P := hX.hasGaussianLaw.isProbabilityMeasure
    apply Measure.ext_of_charFun
    ext t
    apply mul_left_cancel₀ (a := charFun (P.map X) t)
    · rw [hX.map_eq, charFun_gaussianReal]
      exact Complex.exp_ne_zero _
    · rw [← Pi.mul_apply, ← h.charFun_add_eq_mul, hY.map_eq, hX.map_eq, charFun_gaussianReal,
        charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add, NNReal.coe_sub,
        Complex.ofReal_sub]
      · congr
        field_simp
        ring
      · rw [← @Real.toNNReal_coe vY, ← @variance_id_gaussianReal μY vY, ← hY.variance_eq,
          h.variance_add, hX.variance_eq, variance_id_gaussianReal, Real.toNNReal_add,
          Real.toNNReal_coe]
        · simp
        · simp
        · exact variance_nonneg _ _
        · exact hX.hasGaussianLaw.memLp_two
        · rw [show Y = X + Y - X  by simp]
          exact hY.hasGaussianLaw.memLp_two.sub hX.hasGaussianLaw.memLp_two
      · exact hX.aemeasurable
      · rw [show Y = X + Y - X by simp]
        exact hY.aemeasurable.sub hX.aemeasurable

lemma IndepFun.hasGaussianLaw_sub {X Y : Ω → ℝ}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw (X + Y) P)
    (h : IndepFun X Y P) :
    HasGaussianLaw Y P where
  isGaussian_map := by
    have h1 : HasLaw X (gaussianReal _ _) P := ⟨hX.aemeasurable, hX.map_eq_gaussianReal⟩
    have h2 : HasLaw (X + Y) (gaussianReal _ _) P := ⟨hY.aemeasurable, hY.map_eq_gaussianReal⟩
    have := h.hasLaw_sub_of_gaussian h1 h2
    exact this.hasGaussianLaw.isGaussian_map

lemma HasIndepIncrements.indepFun_incr {Ω T E : Type*} {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    [Preorder T] {X : T → Ω → E} {P : Measure Ω} (h : HasIndepIncrements X P)
    {r s t : T} (hrs : r ≤ s) (hst : s ≤ t) (hX : ∀ᵐ ω ∂P, X r ω = 0) :
    IndepFun (X s) (X t - X s) P := by
  let τ : Fin (1 + 2) → T := ![r, s, t]
  have hτ : Monotone τ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    any_goals simp [τ]
    any_goals assumption
    any_goals contradiction
    exact hrs.trans hst
  have := h 1 τ hτ
  have h' : (0 : Fin (1 + 1)) ≠ (1 : Fin (1 + 1)) := by simp
  have := this.indepFun h'
  simp only [Nat.reduceAdd, Fin.isValue, Fin.succ_zero_eq_one, Matrix.cons_val_one,
    Matrix.cons_val_zero, Fin.castSucc_zero, Fin.succ_one_eq_two, Matrix.cons_val, Fin.castSucc_one,
    τ] at this
  have h' : X s =ᵐ[P] X s - X r := by
    filter_upwards [hX] with ω hω
    simp [hω]
  refine IndepFun.congr ?_ h'.symm ae_eq_rfl
  exact this

lemma covariance_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    cov[X, Y; P] = P[X * Y] - P[X] * P[Y] := by
  simp_rw [covariance, sub_mul, mul_sub]
  rw [integral_sub, integral_sub, integral_sub]
  · simp_rw [integral_mul_const, integral_const_mul, integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul]
    simp
  · exact hY.const_mul _ |>.integrable (by norm_num)
  · exact integrable_const _
  · exact hX.integrable_mul hY
  · conv => enter [1, a]; rw [mul_comm]
    exact hX.const_mul _ |>.integrable (by norm_num)
  · apply Integrable.sub
    · exact hX.integrable_mul hY
    · conv => enter [1, a]; rw [mul_comm]
      exact hX.const_mul _ |>.integrable (by norm_num)
  · apply Integrable.sub
    · exact hY.const_mul _ |>.integrable (by norm_num)
    · exact integrable_const _

lemma IndepFun.covariance_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : Ω → ℝ} (h : IndepFun X Y P) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    cov[X, Y; P] = 0 := by
  by_cases h' : ∀ᵐ ω ∂P, X ω = 0
  · rw [covariance]
    have : ∀ᵐ ω ∂P, (X ω - ∫ (x : Ω), X x ∂P) * (Y ω - ∫ (x : Ω), Y x ∂P) = 0 := by
      filter_upwards [h'] with ω hω
      simp only [hω, zero_sub, neg_mul, neg_eq_zero, mul_eq_zero]
      left
      rw [integral_congr_ae h']
      simp
    rw [integral_congr_ae this]
    simp
  have := hX.isProbabilityMeasure_of_indepFun X Y (by norm_num) (by norm_num) h' h
  rw [covariance_eq hX hY]
  simp only [Pi.mul_apply]
  change ∫ ω, (id (X ω)) * (id (Y ω)) ∂P - _ = _
  rw [h.integral_mul_eq_mul_integral]
  · simp
  · exact hX.aemeasurable
  · exact hY.aemeasurable
  · exact aestronglyMeasurable_id
  · exact aestronglyMeasurable_id

open Fin.NatCast in
lemma isBrownian_of_hasLaw_of_hasIndepIncrements (cont : ∀ᵐ ω ∂P, Continuous (X · ω))
    (law : ∀ t, HasLaw (X t) (gaussianReal 0 t) P) (incr : HasIndepIncrements X P) :
    IsBrownian X P where
  cont := cont
  hasLaw := by
    classical
    have : IsProbabilityMeasure P := (law 0).hasGaussianLaw.isProbabilityMeasure
    refine fun I ↦ ⟨aemeasurable_pi_lambda _ fun _ ↦ (law _).aemeasurable, ?_⟩
    have : IsProbabilityMeasure (P.map fun ω ↦ I.restrict (X · ω)) := by
      apply isProbabilityMeasure_map
      exact aemeasurable_pi_lambda _ fun _ ↦ (law _).aemeasurable
    obtain rfl | hI := I.eq_empty_or_nonempty
    · ext s -
      apply Subsingleton.set_cases (p := fun s ↦ Measure.map _ _ s = _)
      all_goals simp
    have aeeq : ∀ᵐ ω ∂P, X 0 ω = 0 := by
      apply ae_of_ae_map (p := fun x ↦ x = 0)
      · rw [(law 0).map_eq, gaussianReal_zero_var, ae_dirac_iff]
        simp
      · exact (law 0).aemeasurable
    have : IsGaussian (P.map (fun ω ↦ I.restrict fun x ↦ X x ω)) := by
      have := aux aeeq hI
      rw [Measure.map_congr this]
      have : HasGaussianLaw
          (fun ω (i : Fin (#I - 1 + 1)) ↦ X (toFin hI i.succ) ω - X (toFin hI i.castSucc) ω) P := by
        have ind := incr (#I - 1) (toFin hI) (monotone_toFin hI)
        have (i : Fin (#I - 1 + 1)) :
            HasGaussianLaw (fun ω ↦ X (toFin hI i.succ) ω - X (toFin hI i.castSucc) ω) P := by
          have : i.succ ≠ i.castSucc := Fin.castSucc_lt_succ i |>.ne'
          apply IndepFun.hasGaussianLaw_sub (X := X (toFin hI i.castSucc))
            (Y := X (toFin hI i.succ) - X (toFin hI i.castSucc))
          · exact (law _).hasGaussianLaw
          · simpa using (law _).hasGaussianLaw
          apply incr.indepFun_incr (r := 0)
          · simp
          · apply monotone_toFin hI
            exact Fin.castSucc_lt_succ i |>.le
          · exact aeeq
        exact ind.hasGaussianLaw
      infer_instance
    apply (MeasurableEquiv.toLp 2 (_ → ℝ)).map_measurableEquiv_injective
    rw [MeasurableEquiv.coe_toLp, ← PiLp.continuousLinearEquiv_symm_apply 2 ℝ]
    apply IsGaussian.ext
    · rw [integral_map, integral_map, integral_map]
      · simp only [PiLp.continuousLinearEquiv_symm_apply, id_eq]
        simp_rw [← PiLp.continuousLinearEquiv_symm_apply 2 ℝ, ← ContinuousLinearEquiv.coe_coe]
        rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_gaussianProjectiveFamily,
          ContinuousLinearMap.integral_comp_comm]
        · simp only [ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply,
            toLp_zero]
          convert toLp_zero 2
          ext i
          rw [integral_eval]
          · simp only [restrict, Pi.zero_apply]
            rw [(law _).integral_eq, integral_id_gaussianReal]
          · exact fun _ ↦ (law _).hasGaussianLaw.integrable
        · apply Integrable.of_eval
          exact fun _ ↦ (law _).hasGaussianLaw.integrable
        · exact IsGaussian.integrable_id
      · fun_prop
      · exact aestronglyMeasurable_id
      · exact aemeasurable_pi_lambda _ fun _ ↦ (law _).aemeasurable
      · exact Measurable.aestronglyMeasurable (by fun_prop)
      · fun_prop
      · exact aestronglyMeasurable_id
    · refine ContinuousBilinForm.ext_of_isSymm (isPosSemidef_covInnerBilin ?_).isSymm
        (isPosSemidef_covInnerBilin ?_).isSymm fun x ↦ ?_
      · exact IsGaussian.memLp_two_id
      · exact IsGaussian.memLp_two_id
      rw [PiLp.continuousLinearEquiv_symm_apply, covInnerBilin_apply_pi, covInnerBilin_apply_pi]
      · congr with i
        congr with j
        congr 1
        rw [covariance_eval_gaussianProjectiveFamily, covariance_map]
        · change cov[X i, X j; P] = _
          wlog hij : i ≤ j generalizing i j
          · rw [covariance_comm, this j i (le_of_not_ge hij), min_comm]
          rw [show X j = X j - X i + X i  by simp, covariance_add_right,
            IndepFun.covariance_eq_zero, covariance_self, (law _).variance_eq,
            variance_id_gaussianReal]
          · simpa
          · exact (law _).aemeasurable
          · apply incr.indepFun_incr (r := 0)
            · simp
            · simpa
            · exact aeeq
          · exact (law _).hasGaussianLaw.memLp_two
          · exact (law _).hasGaussianLaw.memLp_two.sub (law _).hasGaussianLaw.memLp_two
          · exact (law _).hasGaussianLaw.memLp_two
          · exact (law _).hasGaussianLaw.memLp_two.sub (law _).hasGaussianLaw.memLp_two
          · exact (law _).hasGaussianLaw.memLp_two
        · exact Measurable.aestronglyMeasurable (by fun_prop)
        · exact Measurable.aestronglyMeasurable (by fun_prop)
        · exact aemeasurable_pi_lambda _ (fun _ ↦ (law _).aemeasurable)
      · exact fun _ ↦ HasGaussianLaw.memLp_two
      · exact fun _ ↦ HasGaussianLaw.memLp_two


end IsBrownian

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
    simp_rw [Set.mapsTo'] at hf ⊢
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
      simp only [Set.mapsTo'] at h ⊢
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
