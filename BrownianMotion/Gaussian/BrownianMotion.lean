/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Gaussian.GaussianProcess
import BrownianMotion.Gaussian.Moment
import BrownianMotion.Gaussian.ProjectiveLimit
import BrownianMotion.Continuity.KolmogorovChentsov

/-!
# Brownian motion

-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

def preBrownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω ↦ ω t

@[fun_prop]
lemma measurable_preBrownian (t : ℝ≥0) : Measurable (preBrownian t) := by
  unfold preBrownian
  fun_prop

lemma isGaussianProcess_preBrownian : IsGaussianProcess preBrownian gaussianLimit := by
  intro I
  simp only [preBrownian, Measure.map_id']
  rw [isProjectiveLimit_gaussianLimit]
  exact isGaussian_gaussianProjectiveFamily I

lemma tkt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    Var[X - Y; P] = Var[X; P] - 2 * cov[X, Y; P] + Var[Y; P] := by
  rw [← covariance_same, covariance_sub_left, covariance_sub_right, covariance_sub_right,
    covariance_same, covariance_same, covariance_comm]
  · ring
  any_goals assumption
  · exact hY.aestronglyMeasurable.aemeasurable
  · exact hX.aestronglyMeasurable.aemeasurable
  · exact hX.sub hY
  · exact hX.aestronglyMeasurable.aemeasurable.sub hY.aestronglyMeasurable.aemeasurable

open scoped RealInnerProductSpace

lemma teste (s t : ℝ≥0) : s + t - 2 * min s t = max (s - t) (t - s) := by
  suffices h : ∀ (s t : ℝ≥0), s ≤ t → s + t - 2 * min s t = max (s - t) (t - s) by
    obtain hst | hts := le_total s t
    · exact h s t hst
    · convert h t s hts using 1
      · rw [add_comm, min_comm]
      · rw [max_comm]
  intro s t hst
  rw [min_eq_left hst, max_eq_right, two_mul, add_tsub_add_eq_tsub_left]
  grw [hst]

lemma map_sub_preBrownian (s t : ℝ≥0) :
    gaussianLimit.map (preBrownian s - preBrownian t) = gaussianReal 0 (max (s - t) (t - s)) := by
  let I : Finset ℝ≥0 := {s, t}
  let u := EuclideanSpace.basisFun I ℝ ⟨s, by simp [I]⟩
  let v := EuclideanSpace.basisFun I ℝ ⟨t, by simp [I]⟩
  let L : EuclideanSpace ℝ ({s, t} : Finset ℝ≥0) →L[ℝ] ℝ :=
    ContinuousBilinForm.inner _ u - ContinuousBilinForm.inner _ v
  have : preBrownian s - preBrownian t = L ∘ I.restrict := by
    ext; simp [L, u, v, preBrownian, I]
  rw [this, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop),
    isProjectiveLimit_gaussianLimit, IsGaussian.map_eq_gaussianReal, L.integral_comp_id_comm,
    integral_id_gaussianProjectiveFamily, map_zero, gaussianProjectiveFamily]
  swap; · exact IsGaussian.integrable_id _
  congr
  simp only [ContinuousLinearMap.coe_sub', ContinuousBilinForm.inner_apply', basisFun_inner, L, I,
    u, v]
  rw [tkt]
  · simp_rw [test, test', brownianCovMatrix_apply, min_self]
    norm_cast
    rw [sub_add_eq_add_sub, ← NNReal.coe_add, ← NNReal.coe_sub, Real.toNNReal_coe, teste]
    rw [two_mul]
    nth_grw 1 [min_le_left, min_le_right]
  all_goals
    simp_rw [← basisFun_inner, ← ContinuousBilinForm.inner_apply']
    exact ContinuousLinearMap.comp_memLp' _ <| IsGaussian.memLp_two_id _

lemma lol {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (p : ℕ)
    (hX : μ[X] = 0) :
    centralMoment X p μ = ∫ ω, X ω ^ p ∂μ := by
  rw [centralMoment]
  simp [hX]

lemma isKolmogorovProcess_preBrownian (n : ℕ) :
    IsKolmogorovProcess preBrownian gaussianLimit (2 * n) n (Nat.doubleFactorial (2 * n - 1)) := by
  constructor
  · intro s t
    rw [← BorelSpace.measurable_eq]
    fun_prop
  intro s t
  apply Eq.le
  norm_cast
  simp_rw [edist_dist, Real.dist_eq]
  change ∫⁻ ω, (fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    ((preBrownian s - preBrownian t) ω) ∂_ = _
  rw [← lintegral_map (f := fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n)), map_sub_preBrownian]
  · simp_rw [← fun x ↦ ENNReal.ofReal_pow (abs_nonneg x)]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · simp_rw [Even.pow_abs (n := 2 * n) ⟨n, by omega⟩]
      rw [← lol, ← NNReal.sq_sqrt (max _ _)]
      · change ENNReal.ofReal (centralMoment id _ _) = _
        rw [centralMoment_two_mul_gaussianReal, ENNReal.ofReal_mul, mul_comm]
        · congr
          · norm_cast
          · norm_cast
            rw [pow_mul, NNReal.sq_sqrt, ← ENNReal.ofReal_pow dist_nonneg]
            congr
            rw [← NNReal.nndist_eq, NNReal.coe_pow, coe_nndist]
        · positivity
      · simp
    · simp_rw [← Real.norm_eq_abs]
      apply MemLp.integrable_norm_pow'
      exact IsGaussian.memLp_id _ _ (ENNReal.natCast_ne_top (2 * n))
    · exact ae_of_all _ fun _ ↦ by positivity
  · fun_prop
  · fun_prop



noncomputable
def brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  (exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ isKolmogorovProcess_preBrownian (n + 2)) (fun n ↦ by positivity)
    (fun n ↦ by simp; norm_cast; omega)).choose

lemma brownian_eq_preBrownian (t : ℝ≥0) :
    brownian t =ᵐ[gaussianLimit] preBrownian t :=
  (exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ isKolmogorovProcess_preBrownian (n + 2)) (fun n ↦ by positivity)
    (fun n ↦ by simp; norm_cast; omega)).choose_spec.1 t

lemma isHolderWith_brownian {β : ℝ≥0} (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) (ω : ℝ≥0 → ℝ) :
    ∃ C : ℝ≥0, HolderWith C β (brownian · ω) := by
  refine (exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ isKolmogorovProcess_preBrownian (n + 2)) (fun n ↦ by positivity)
    (fun n ↦ by simp; norm_cast; omega)).choose_spec.2 β hβ_pos ?_ ω
  have hβ_lt' : (β : ℝ) < 2⁻¹ := by norm_cast
  refine hβ_lt'.trans_eq (iSup_eq_of_forall_le_of_tendsto (F := Filter.atTop) ?_ ?_).symm
  · intro n
    calc
    ((↑(n + 2) : ℝ) - 1) / (2 * ↑(n + 2)) = 2⁻¹ * (n + 1) / (n + 2) := by
      rw [inv_eq_one_div, mul_div_assoc, div_mul_div_comm]
      congr
      · push_cast
        ring
      · push_cast
        rfl
    _ ≤ 2⁻¹ * 1 := by
      rw [mul_div_assoc, mul_le_mul_left, div_le_one₀]
      · linarith
      · norm_cast
        omega
      · norm_num
    _ = 2⁻¹ := mul_one _
  · have : (fun n : ℕ ↦ ((↑(n + 2) : ℝ) - 1) / (2 * ↑(n + 2))) =
        (fun n : ℕ ↦ 2⁻¹ * ((n : ℝ) / (n + 1))) ∘ (fun n ↦ n + 1) := by
      ext n
      simp only [Nat.cast_add, Nat.cast_ofNat, Function.comp_apply, Nat.cast_one]
      rw [inv_eq_one_div, div_mul_div_comm]
      congr 2
      · ring
      · norm_cast
    simp_rw [this]
    refine Filter.Tendsto.comp ?_ (Filter.tendsto_add_atTop_nat 1)
    nth_rw 2 [← mul_one 2⁻¹]
    apply Filter.Tendsto.const_mul
    exact tendsto_natCast_div_add_atTop 1

lemma aemeasurable_brownian_apply (t : ℝ≥0) : AEMeasurable (brownian t) gaussianLimit :=
  ⟨preBrownian t, measurable_preBrownian t, brownian_eq_preBrownian t⟩

lemma continuous_brownian (ω : ℝ≥0 → ℝ) :
    Continuous (brownian · ω) := by
  obtain ⟨C, h⟩ : ∃ C, HolderWith C 4⁻¹ (brownian · ω) := by
    apply isHolderWith_brownian
    · norm_num
    refine NNReal.inv_lt_inv ?_ ?_
    all_goals norm_num
  exact h.continuous (by norm_num)

lemma ok (a b : Type*) (p : Prop) [Decidable p] (u v : b → a) :
    (fun x ↦ if p then u x else v x) = if p then u else v := by
  ext x
  split_ifs <;> rfl

section pause

open Filter MeasureTheory Set TopologicalSpace

open scoped Topology

variable {ι X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [PolishSpace E]
  [MeasurableSpace E] [BorelSpace E] [Countable ι] {l : Filter ι}
  [l.IsCountablyGenerated] {f : ι → X → E}

theorem limUnder_works [hE : Nonempty E] (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x ↦ limUnder l (f · x)) := by
  obtain rfl | hl := eq_or_neBot l
  · simp [limUnder, Filter.map_bot]
  letI := upgradeIsCompletelyMetrizable
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

end pause

lemma aemeasurable_brownian : AEMeasurable (fun ω t ↦ brownian t ω) gaussianLimit := by
  classical
  let X (n : ℕ) (ω : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
    if t = 0 then 0
    else brownian (Nat.ceil (2 ^ n * t) / 2 ^ n) ω
  let Y (n : ℕ) (ω : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
    if t = 0 then 0
    else (aemeasurable_brownian_apply ((Nat.ceil (2 ^ n * t) / 2 ^ n))).mk _ ω
  have hY n : Measurable (Y n) := by
    rw [measurable_pi_iff]
    intro t
    simp_rw [Y, ok]
    split_ifs with ht
    · fun_prop
    · exact AEMeasurable.measurable_mk _
  have (n k : ℕ) : (fun ω ↦ X n ω (k / 2 ^ n)) =ᵐ[gaussianLimit] (fun ω ↦ Y n ω (k / 2 ^ n)) := by
    filter_upwards [(aemeasurable_brownian_apply ((k / 2 ^ n))).ae_eq_mk] with ω hω
    simp_rw [X, Y]
    obtain rfl | hk := eq_zero_or_pos k
    · simp
    rw [if_neg, if_neg]
    · convert hω
      all_goals field_simp
    all_goals
      apply div_ne_zero
      · norm_cast; omega
      · simp
  have hX (n : ℕ) : AEMeasurable (X n) gaussianLimit := by
    refine ⟨Y n, hY n, ?_⟩
    filter_upwards [ae_all_iff.2 (this n)] with ω hω
    simp_rw [X, Y]
    ext t
    split_ifs with ht
    · rfl
    convert hω ⌈2 ^ n * t⌉₊
    · simp_rw [X]
      rw [if_neg]
      · field_simp
      apply div_ne_zero
      · apply LT.lt.ne'
        norm_cast
        rw [Nat.ceil_pos]
        norm_cast
        apply mul_pos
        · simp
        exact NE.ne.pos ht
      · simp
    · simp_rw [Y]
      rw [if_neg]
      · field_simp
      apply div_ne_zero
      · apply LT.lt.ne'
        norm_cast
        rw [Nat.ceil_pos]
        norm_cast
        apply mul_pos
        · simp
        exact NE.ne.pos ht
      · simp
  let Z (ω : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := limUnder Filter.atTop (fun n ↦ Y n ω t)
  have hZ : Measurable Z := by
    rw [measurable_pi_iff]
    intro t
    exact limUnder_works fun n ↦ measurable_pi_iff.1 (hY n) t
  refine ⟨Z, hZ, ?_⟩


    -- rw [measurable_pi_iff]
    -- intro t s hs
    -- have : fun ω ↦ X n ω t ⁻¹' s =

lemma isGaussianProcess_brownian : IsGaussianProcess brownian gaussianLimit :=
  isGaussianProcess_preBrownian.modification fun t ↦ (brownian_eq_preBrownian t).symm

section Measure

-- Subtype measurable space. The measurable space on `ℝ≥0 → ℝ` is the product of Borel σ-algebras
-- #synth MeasurableSpace {f : ℝ≥0 → ℝ // Continuous f}

noncomputable
def wienerMeasureAux : Measure {f : ℝ≥0 → ℝ // Continuous f} :=
  gaussianLimit.map (fun ω ↦ (⟨fun t ↦ brownian t ω, continuous_brownian ω⟩))

-- Compact-open topology
-- #synth TopologicalSpace C(ℝ≥0, ℝ)

section ContinuousMap.MeasurableSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

instance : MeasurableSpace C(X, Y) := borel _
instance : BorelSpace C(X, Y) where
  measurable_eq := rfl

lemma ContinuousMap.borel_eq_iSup_comap_eval [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y] :
    borel C(X, Y) = ⨆ a : X, (borel Y).comap fun b ↦ b a := by
  -- https://math.stackexchange.com/questions/4789531/when-does-the-borel-sigma-algebra-of-compact-convergence-coincide-with-the-pr
  apply le_antisymm
  swap
  · refine iSup_le fun x ↦ ?_
    rw [← measurable_iff_comap_le]
    simp_rw [← BorelSpace.measurable_eq]
    refine Continuous.measurable ?_
    fun_prop
  sorry

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
