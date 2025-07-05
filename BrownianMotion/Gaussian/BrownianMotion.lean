/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Continuity.KolmogorovChentsov
import BrownianMotion.Gaussian.GaussianProcess
import BrownianMotion.Gaussian.Moment
import BrownianMotion.Gaussian.ProjectiveLimit
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
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
    HasLaw (fun ω ↦ I.restrict (preBrownian · ω)) gaussianLimit (gaussianProjectiveFamily I) :=
  hasLaw_restrict_gaussianLimit.comp hasLaw_preBrownian

lemma hasLaw_preBrownian_eval (t : ℝ≥0) :
    HasLaw (preBrownian t) gaussianLimit (gaussianReal 0 t) :=
  (hasLaw_eval_gaussianProjectiveFamily ⟨t, by simp⟩).comp
    (hasLaw_restrict_preBrownian ({t} : Finset ℝ≥0))

lemma isGaussianProcess_preBrownian : IsGaussianProcess preBrownian gaussianLimit := by
  intro I
  rw [(hasLaw_restrict_preBrownian I).map_eq]
  exact isGaussian_gaussianProjectiveFamily I

lemma hasLaw_preBrownian_sub (s t : ℝ≥0) :
    HasLaw (preBrownian s - preBrownian t) gaussianLimit
      (gaussianReal 0 (max (s - t) (t - s))) := by
  have : preBrownian s - preBrownian t =
      ((fun x ↦ x ⟨s, by simp⟩) - (fun x ↦ x ⟨t, by simp⟩)) ∘ ({s, t} : Finset ℝ≥0).restrict := by
    ext; simp [preBrownian]
  rw [this]
  exact hasLaw_eval_sub_eval_gaussianProjectiveFamily.comp
    hasLaw_restrict_gaussianLimit

lemma isMeasurableKolmogorovProcess_preBrownian (n : ℕ) :
    IsMeasurableKolmogorovProcess preBrownian gaussianLimit (2 * n) n
      (Nat.doubleFactorial (2 * n - 1)) := by
  constructor
  · intro s t
    rw [← BorelSpace.measurable_eq]
    fun_prop
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
    (fun n ↦ (isMeasurableKolmogorovProcess_preBrownian (n + 2)).isKolmogorovProcess)
    (fun n ↦ by finiteness) zero_lt_one (fun n ↦ by positivity) (fun n ↦ by simp; norm_cast; omega)

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
    HasLaw (fun ω ↦ I.restrict (brownian · ω)) gaussianLimit (gaussianProjectiveFamily I) := by
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
    HasLaw (brownian t) gaussianLimit (gaussianReal 0 t) :=
  (hasLaw_preBrownian_eval t).congr (brownian_ae_eq_preBrownian t)

lemma hasLaw_brownian_sub {s t : ℝ≥0} :
    HasLaw (brownian s - brownian t) gaussianLimit (gaussianReal 0 (max (s - t) (t - s))) :=
    (hasLaw_preBrownian_sub s t).congr
      ((brownian_ae_eq_preBrownian s).sub (brownian_ae_eq_preBrownian t))

open NNReal Filter Topology in
lemma measurable_brownian_uncurry : Measurable brownian.uncurry :=
  measurable_uncurry_of_continuous_of_measurable continuous_brownian measurable_brownian

lemma isGaussianProcess_brownian : IsGaussianProcess brownian gaussianLimit :=
  isGaussianProcess_preBrownian.modification fun t ↦ (brownian_ae_eq_preBrownian t).symm

lemma isMeasurableKolmogorovProcess_brownian (n : ℕ) :
    IsMeasurableKolmogorovProcess brownian gaussianLimit (2 * n) n
      (Nat.doubleFactorial (2 * n - 1)) where
  measurablePair := measurable_pair_of_measurable measurable_brownian
  kolmogorovCondition := (isMeasurableKolmogorovProcess_preBrownian n).isKolmogorovProcess.congr
    (fun t ↦ (brownian_ae_eq_preBrownian t).symm) |>.kolmogorovCondition

lemma iIndepFun_iff_charFun_eq_pi {ι Ω : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Π i, Ω → (E i)}
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] (mX : ∀ i, AEMeasurable (X i) μ) :
    iIndepFun X μ ↔ ∀ t,
      charFun (μ.map fun ω ↦ toLp 2 (X · ω)) t = ∏ i, charFun (μ.map (X i)) (t i) := sorry
-- PR #26269 in Mathlib

instance IsGaussian.eval {ι Ω : Type*} {E : ι → Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}
    [h : IsGaussian (P.map (fun ω ↦ (X · ω)))] (i : ι) :
    IsGaussian (P.map (X i)) := by
  have : X i = (ContinuousLinearMap.proj (R := ℝ) (φ := E) i) ∘ (fun ω ↦ (X · ω)) := by ext; simp
  rw [this, ← AEMeasurable.map_map_of_aemeasurable]
  · infer_instance
  · fun_prop
  by_contra!
  rw [Measure.map_of_not_aemeasurable] at h
  · exact h.toIsProbabilityMeasure.ne_zero _ rfl
  · exact this

instance HasGaussianLaw.eval {ι Ω : Type*} {E : ι → Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}
    [h : HasGaussianLaw (fun ω ↦ (X · ω)) P] (i : ι) :
    HasGaussianLaw (X i) P where
  isGaussian_map' := IsGaussian.eval i

lemma test {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ι → Ω → ℝ}
    [h1 : HasGaussianLaw (fun ω ↦ (X · ω)) P]
    (h2 : ∀ i j : ι, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P := by
  have mX : ∀ i, AEMeasurable (X i) P := aemeasurable_pi_iff.1 h1.aemeasurable
  have (i : ι) : (inner ℝ ((EuclideanSpace.basisFun ι ℝ) i) ∘ ⇑(EuclideanSpace.equiv ι ℝ).symm ∘
      fun ω x ↦ X x ω) = X i := by ext; simp [-PiLp.inner_apply]
  refine iIndepFun_iff_charFun_eq_pi mX |>.2 fun ξ ↦ ?_
  change charFun (P.map ((EuclideanSpace.equiv ι ℝ).symm ∘ _)) _ = _
  rw [IsGaussian.charFun_eq, covInnerBilin_self IsGaussian.memLp_two_id]
  nth_rw 1 2 [← (EuclideanSpace.basisFun ι ℝ).sum_repr' ξ]
  simp_rw [sum_inner, basisFun_inner]
  rw [variance_fun_sum]
  · simp_rw [Complex.ofReal_sum, sum_mul, sum_div, ← sum_sub_distrib, Complex.exp_sum]
    congr with i
    rw [real_inner_smul_left, ← integral_inner, Finset.sum_eq_single_of_mem i, covariance_self]
    · simp_rw [real_inner_smul_left, variance_mul]
      conv =>
        enter [1, 1, 1, 1, 1, 2, 2, x]
        change id (inner ℝ (EuclideanSpace.basisFun ι ℝ i) x)
      conv =>
        enter [1, 1, 2, 1, 1, 2, 1]
        change id ∘ (inner ℝ (EuclideanSpace.basisFun ι ℝ i))
      rw [← integral_map, ← variance_map, AEMeasurable.map_map_of_aemeasurable]
      · rw [this, IsGaussian.charFun_eq, covInnerBilin_real_self]
        · simp [mul_comm]
        exact IsGaussian.memLp_two_id
      any_goals fun_prop
    · fun_prop
    · simp
    · rintro j - hj
      simp_rw [real_inner_smul_left, covariance_mul_left, covariance_mul_right]
      rw [covariance_map, this, this, h2 i j hj.symm]
      · simp
      any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
      fun_prop
    · exact IsGaussian.integrable_id
  intro i
  rw [← ContinuousBilinForm.inner_apply'', ← Function.id_comp ⇑(ContinuousBilinForm.inner _ _),
    ← memLp_map_measure_iff]
  · exact IsGaussian.memLp_two_id
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop

def indep_incr {Ω T E : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [Sub E] [Preorder T]
    [MeasurableSpace E] (X : T → Ω → E) : Prop :=
  ∀ n, ∀ t : Fin (n + 2) → T, Monotone t →
    iIndepFun (fun i : Fin (n + 1) ↦ X (t i.succ) - X (t i.castSucc)) P

lemma mem_pair_iff {α : Type*} [DecidableEq α] {x y z : α} :
    x ∈ ({y, z} : Finset α) ↔ x = y ∨ x = z := by
  simp

lemma cov_brownian (s t : ℝ≥0) : cov[brownian s, brownian t; gaussianLimit] = min s t := by
  have h1 : brownian s = (fun x : ({s, t} : Finset ℝ≥0) → ℝ ↦ x ⟨s, by simp⟩) ∘
      (fun ω ↦ ({s, t} : Finset ℝ≥0).restrict (brownian · ω)) := by ext; simp
  have h2 : brownian t = (fun x : ({s, t} : Finset ℝ≥0) → ℝ ↦ x ⟨t, by simp⟩) ∘
      (fun ω ↦ ({s, t} : Finset ℝ≥0).restrict (brownian · ω)) := by ext; simp
  have : (fun ω ↦ ({s, t} : Finset ℝ≥0).restrict (brownian · ω)) =ᵐ[gaussianLimit]
      (fun ω ↦ ({s, t} : Finset ℝ≥0).restrict (preBrownian · ω)) := by
    filter_upwards [brownian_ae_eq_preBrownian s, brownian_ae_eq_preBrownian t] with ω hω₁ hω₂
    ext r
    obtain hr | hr := mem_pair_iff.1 r.2
    all_goals simp [hr, hω₁, hω₂]
  rw [h1, h2, ← covariance_map, Measure.map_congr this]
  · simp_rw [preBrownian, hasLaw_restrict_gaussianLimit.map_eq]
    rw [covariance_eval_gaussianProjectiveFamily]
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  exact Measurable.aemeasurable <| by fun_prop

lemma indep_incr_bm : indep_incr gaussianLimit brownian := by
  intro n t ht
  apply test
  · exact fun i ↦ by fun_prop
  · have : (fun ω ↦
        (EuclideanSpace.measurableEquiv (Fin (n + 1))).symm
        fun i ↦ (brownian (t i.succ) - brownian (t i.castSucc)) ω) =
        (fun x ↦ toLp 2 fun (i : Fin (n + 1)) ↦ x i.succ - x i.castSucc) ∘
        (fun x (i : Fin (n + 2)) ↦ x ⟨t i, by simp⟩) ∘ ((Finset.univ.image t).restrict) ∘
        (fun ω t ↦ brownian t ω) := by ext; simp [EuclideanSpace.measurableEquiv]
    rw [this, ← Function.comp_assoc, ← Measure.map_map]
    · let L : ((Finset.univ.image t) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
        { toFun := (fun x ↦ toLp 2 fun (i : Fin (n + 1)) ↦ x i.succ - x i.castSucc) ∘
            (fun x (i : Fin (n + 2)) ↦ x ⟨t i, by simp⟩)
          map_add' x y := by ext; simp; ring
          map_smul' m x := by ext; simp; ring
          cont := by fun_prop }
      have : (fun x ↦ toLp 2 fun (i : Fin (n + 1)) ↦ x i.succ - x i.castSucc) ∘
          (fun x (i : Fin (n + 2)) ↦ x ⟨t i, by simp⟩) = ⇑L := rfl
      rw [this]
      refine @isGaussian_map _ _ _ _ _ _ _ _ _ _ _ ?_ L
      exact isGaussianProcess_brownian.restrict (Finset.univ.image t)
    · fun_prop
    · fun_prop
  intro i j hij
  rw [covariance_sub_left, covariance_sub_right, covariance_sub_right]
  · simp_rw [cov_brownian]
    obtain h | h := Fin.lt_or_lt_of_ne hij
    · have h1 : i.succ ≤ j.succ := Fin.succ_le_succ_iff.mpr h.le
      have h2 : i.succ ≤ j.castSucc := h
      have h3 : i.castSucc ≤ j.succ := Fin.le_of_lt h1
      have h4 : i.castSucc ≤ j.castSucc := Fin.le_castSucc_iff.mpr h1
      rw [min_eq_left (ht h1), min_eq_left (ht h2), min_eq_left (ht h3), min_eq_left (ht h4)]
      simp
    · have h1 : j.succ ≤ i.succ := Fin.succ_le_succ_iff.mpr h.le
      have h2 : j.succ ≤ i.castSucc := h
      have h3 : j.castSucc ≤ i.succ := Fin.le_of_lt h1
      have h4 : j.castSucc ≤ i.castSucc := Fin.le_castSucc_iff.mpr h1
      rw [min_eq_right (ht h1), min_eq_right (ht h2), min_eq_right (ht h3), min_eq_right (ht h4)]
      simp
  rotate_right
  · exact
      (isGaussianProcess_brownian.memLp_eval (by norm_num)).sub
      (isGaussianProcess_brownian.memLp_eval (by norm_num))
  all_goals
    exact isGaussianProcess_brownian.memLp_eval (by norm_num)

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
