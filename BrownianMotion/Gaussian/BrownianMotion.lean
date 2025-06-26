/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Nat
import BrownianMotion.Auxiliary.NNReal
import BrownianMotion.Gaussian.GaussianProcess
import BrownianMotion.Gaussian.Moment
import BrownianMotion.Gaussian.ProjectiveLimit
import BrownianMotion.Continuity.KolmogorovChentsov

/-!
# Brownian motion

-/

open MeasureTheory NNReal
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

lemma map_sub_preBrownian (s t : ℝ≥0) :
    gaussianLimit.map (preBrownian s - preBrownian t) = gaussianReal 0 (max (s - t) (t - s)) := by
  let I : Finset ℝ≥0 := {s, t}
  let L : (I → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj ⟨s, by simp [I]⟩ - ContinuousLinearMap.proj ⟨t, by simp [I]⟩
  have : preBrownian s - preBrownian t = L ∘ I.restrict := by
    ext; simp [L, preBrownian, I]
  rw [this, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop),
    isProjectiveLimit_gaussianLimit, IsGaussian.map_eq_gaussianReal, L.integral_comp_id_comm,
    integral_id_gaussianProjectiveFamily, map_zero]
  swap; · exact IsGaussian.integrable_id
  congr
  simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_proj', I, L]
  rw [variance_sub]
  · simp_rw [variance_eval_gaussianProjectiveFamily, covariance_eval_gaussianProjectiveFamily]
    norm_cast
    rw [sub_add_eq_add_sub, ← NNReal.coe_add, ← NNReal.coe_sub, Real.toNNReal_coe,
      add_sub_two_mul_min_eq_max]
    nth_grw 1 [two_mul, min_le_left, min_le_right]
  all_goals
    rw [← ContinuousLinearMap.coe_proj' ℝ]
    exact ContinuousLinearMap.comp_memLp' _ <| IsGaussian.memLp_two_id

lemma isKolmogorovProcess_preBrownian (n : ℕ) :
    IsKolmogorovProcess preBrownian gaussianLimit (2 * n) n (Nat.doubleFactorial (2 * n - 1)) := by
  constructor
  · intro s t
    rw [← BorelSpace.measurable_eq]
    fun_prop
  refine fun s t ↦ Eq.le ?_
  norm_cast
  simp_rw [edist_dist, Real.dist_eq]
  change ∫⁻ ω, (fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    ((preBrownian s - preBrownian t) ω) ∂_ = _
  rw [← lintegral_map (f := fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n)) (by fun_prop) (by fun_prop),
    map_sub_preBrownian]
  simp_rw [← fun x ↦ ENNReal.ofReal_pow (abs_nonneg x)]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [pow_two_mul_abs]
    rw [← centralMoment_of_integral_id_eq_zero _ (by simp), ← NNReal.sq_sqrt (max _ _)]
    rw [centralMoment_fun_two_mul_gaussianReal, ENNReal.ofReal_mul (by positivity), mul_comm]
    congr
    · norm_cast
    · norm_cast
      rw [pow_mul, NNReal.sq_sqrt, ← ENNReal.ofReal_pow dist_nonneg, ← NNReal.nndist_eq,
        NNReal.coe_pow, coe_nndist]
  · simp_rw [← Real.norm_eq_abs]
    apply MemLp.integrable_norm_pow'
    exact IsGaussian.memLp_id _ _ (ENNReal.natCast_ne_top (2 * n))
  · exact ae_of_all _ fun _ ↦ by positivity

noncomputable
def brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  (exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ isKolmogorovProcess_preBrownian (n + 2)) (fun n ↦ by positivity)
    (fun n ↦ by simp; norm_cast; omega)).choose

lemma brownian_ae_eq_preBrownian (t : ℝ≥0) :
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
  refine hβ_lt'.trans_eq
    (iSup_eq_of_forall_le_of_tendsto (F := Filter.atTop) (fun n ↦ ?_) ?_).symm
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

lemma aemeasurable_brownian_apply (t : ℝ≥0) : AEMeasurable (brownian t) gaussianLimit :=
  ⟨preBrownian t, measurable_preBrownian t, brownian_ae_eq_preBrownian t⟩

lemma continuous_brownian (ω : ℝ≥0 → ℝ) : Continuous (brownian · ω) := by
  obtain ⟨C, h⟩ : ∃ C, HolderWith C 4⁻¹ (brownian · ω) := by
    refine isHolderWith_brownian (by norm_num) (NNReal.inv_lt_inv ?_ ?_) ω
    all_goals norm_num
  exact h.continuous (by norm_num)

theorem measurable_brownian : Measurable (fun ω t ↦ brownian t ω) := sorry

open NNReal Filter Topology in
lemma _root_.Measurable.measurable_uncurry {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E]
    [BorelSpace E] {X : ℝ≥0 → Ω → E} (cont : ∀ ω, Continuous (X · ω))
    (hX : Measurable fun ω t ↦ X t ω) : Measurable X.uncurry := by
  let Y (n : ℕ) (tω : ℝ≥0 × Ω) : E := X ((step n tω.1 + 1) / 2 ^ n) tω.2
  have hY (n : ℕ) (t : ℝ≥0) : Measurable (fun ω ↦ Y n (t, ω)) := by
    simpa [Y] using hX.eval
  have hY n : Measurable (Y n) := by
    intro s hs
    have : Y n ⁻¹' s = {0} ×ˢ ((fun ω ↦ Y n (0, ω)) ⁻¹' s) ∪
        ⋃ k : ℕ, (Set.Ioc (k / 2 ^ n : ℝ≥0) ((k + 1) / 2 ^ n)) ×ˢ
          ((fun ω ↦ Y n ((k + 1) / 2 ^ n, ω)) ⁻¹' s) := by
      ext ⟨t, ω⟩
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · obtain rfl | ht := eq_zero_or_pos t
        · exact Set.mem_union_left _ (by simpa)
        refine Set.mem_union_right _ <| Set.mem_iUnion.2 ⟨step n t, ?_⟩
        refine ⟨⟨step_div_lt ht, le_step_add_one_div t⟩, ?_⟩
        convert h
        simp [Y]
      · simp only [Set.mem_union, Set.mem_prod, Set.mem_singleton_iff, Set.mem_preimage,
          Set.mem_iUnion, Set.mem_Ioc] at h
        obtain ⟨rfl, h⟩ | ⟨i, ⟨hi1, hi2⟩, h⟩ := h
        · exact h
        convert h
        simp only [Set.mem_preimage, step_cast_add_one_div, Y]
        rw [step_eq_of_lt_of_le hi1 hi2]
    rw [this]
    exact measurableSet_singleton 0 |>.prod (hY n 0 hs) |>.union <| .iUnion
      fun _ ↦ measurableSet_Ioc.prod (hY n _ hs)
  have this tω : Tendsto (fun n ↦ Y n tω) atTop (𝓝 (X.uncurry tω)) := by
    simp_rw [Y]
    obtain ⟨t, ω⟩ := tω
    refine cont ω |>.tendsto t |>.comp ?_
    obtain rfl | ht := eq_zero_or_pos t
    · simp [-one_div, ← one_div_pow]
    have h n : (step n t + 1) / 2 ^ n ≤ t + 1 / 2 ^ n := by grw [add_div, step_div_lt ht]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (by simp) ?_ (fun _ ↦ le_step_add_one_div t) h
    nth_rw 2 [← add_zero t]
    exact Tendsto.add (by simp) (by simp [-one_div, ← one_div_pow])
  exact measurable_of_tendsto_metrizable hY <| tendsto_pi_nhds.2 this

open NNReal Filter Topology in
lemma measurable_brownian_uncurry : Measurable brownian.uncurry :=
    measurable_brownian.measurable_uncurry continuous_brownian

lemma isGaussianProcess_brownian : IsGaussianProcess brownian gaussianLimit :=
  isGaussianProcess_preBrownian.modification fun t ↦ (brownian_ae_eq_preBrownian t).symm

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
