/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Continuity.KolmogorovChentsov
import BrownianMotion.Gaussian.GaussianProcess
import BrownianMotion.Gaussian.Moment
import BrownianMotion.Gaussian.ProjectiveLimit
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

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

lemma measurePreserving_preBrownian_eval (t : ℝ≥0) :
    MeasurePreserving (preBrownian t) gaussianLimit (gaussianReal 0 t) where
  measurable := by fun_prop
  map_eq := by
    have : preBrownian t = (fun x ↦ x ⟨t, by simp⟩) ∘ ({t} : Finset ℝ≥0).restrict := by
      ext; simp [preBrownian]
    rw [this,
      (measurePreserving_gaussianProjectiveFamily.comp measurePreserving_gaussianLimit).map_eq]

lemma map_sub_preBrownian (s t : ℝ≥0) :
    MeasurePreserving (preBrownian s - preBrownian t) gaussianLimit
      (gaussianReal 0 (max (s - t) (t - s))) := by
  have : preBrownian s - preBrownian t =
      ((fun x ↦ x ⟨s, by simp⟩) - (fun x ↦ x ⟨t, by simp⟩)) ∘ ({s, t} : Finset ℝ≥0).restrict := by
    ext; simp [preBrownian]
  rw [this]
  exact measurePreserving_gaussianProjectiveFamily₂.comp measurePreserving_gaussianLimit

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
  rw [(map_sub_preBrownian s t).lintegral_comp (f := fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
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
def brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  (exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ (isMeasurableKolmogorovProcess_preBrownian (n + 2)).isKolmogorovProcess)
    (fun n ↦ by positivity) (fun n ↦ by simp; norm_cast; omega)).choose

@[fun_prop]
lemma measurable_brownian (t : ℝ≥0) :
    Measurable (brownian t) :=
  (exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ (isMeasurableKolmogorovProcess_preBrownian (n + 2)).isKolmogorovProcess)
    (fun n ↦ by positivity) (fun n ↦ by simp; norm_cast; omega)).choose_spec.1 t

lemma brownian_ae_eq_preBrownian (t : ℝ≥0) :
    brownian t =ᵐ[gaussianLimit] preBrownian t :=
  (exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ (isMeasurableKolmogorovProcess_preBrownian (n + 2)).isKolmogorovProcess)
    (fun n ↦ by positivity) (fun n ↦ by simp; norm_cast; omega)).choose_spec.2.1 t

lemma isHolderWith_brownian {β : ℝ≥0} (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) (ω : ℝ≥0 → ℝ) :
    ∃ C : ℝ≥0, HolderWith C β (brownian · ω) := by
  refine (exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ (isMeasurableKolmogorovProcess_preBrownian (n + 2)).isKolmogorovProcess)
    (fun n ↦ by positivity)
    (fun n ↦ by simp; norm_cast; omega)).choose_spec.2.2 β hβ_pos ?_ ω
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

lemma continuous_brownian (ω : ℝ≥0 → ℝ) : Continuous (brownian · ω) := by
  obtain ⟨C, h⟩ : ∃ C, HolderWith C 4⁻¹ (brownian · ω) := by
    refine isHolderWith_brownian (by norm_num) (NNReal.inv_lt_inv ?_ ?_) ω
    all_goals norm_num
  exact h.continuous (by norm_num)

lemma measurePreserving_brownian_apply {t : ℝ≥0} :
    MeasurePreserving (brownian t) gaussianLimit (gaussianReal 0 t) where
  measurable := by fun_prop
  map_eq := by
    rw [Measure.map_congr (brownian_ae_eq_preBrownian t),
      (measurePreserving_preBrownian_eval t).map_eq]

lemma measurePreserving_brownian_sub {s t : ℝ≥0} :
    MeasurePreserving (brownian s - brownian t) gaussianLimit
      (gaussianReal 0 (max (s - t) (t - s))) where
  measurable := by fun_prop
  map_eq := by
    rw [Measure.map_congr ((brownian_ae_eq_preBrownian s).sub' (brownian_ae_eq_preBrownian t)),
      (map_sub_preBrownian s t).map_eq]

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

lemma isClosed_sUnion_of_finite {X : Type*} [TopologicalSpace X] {s : Set (Set X)}
    (h1 : s.Finite) (h2 : ∀ t ∈ s, IsClosed t) : IsClosed (⋃₀ s) := by
  rw [Set.sUnion_eq_biUnion]
  exact h1.isClosed_biUnion h2

open Filter TopologicalSpace in
open scoped Topology in
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
  rw [borel_eq_generateFrom_of_subbasis ContinuousMap.compactOpen_eq]
  apply MeasurableSpace.generateFrom_le
  intro s hs
  let V := countableBasis Y
  have hV : IsTopologicalBasis V := isBasis_countableBasis Y
  have cV : Countable V := countable_countableBasis Y
  obtain ⟨K, hK, U, hU, hs⟩ := hs
  rw [← hs]
  let W := {v | ∃ u ∈ V, v ⊆ U ∧ v = closure u}
  have cW : W.Countable := by
    apply Set.Countable.mono (s₂ := closure '' V)
    · rintro - ⟨u, hu, -, rfl⟩
      exact ⟨u, hu, rfl⟩
    apply Set.Countable.image
    exact cV
  have main : U = ⋃₀ W := by
    ext x
    rw [Set.mem_sUnion]
    constructor
    · intro hx
      obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := hV.nhds_basis_closure x |>.mem_iff.1 <| hU.mem_nhds hx
      exact ⟨closure v, ⟨v, hv2, hv3, rfl⟩, subset_closure hv1⟩
    · intro hx
      obtain ⟨-, ⟨t, ht1, ht2, rfl⟩, hx⟩ := hx
      exact ht2 hx
  have h' : U = ⋃₀ {v | v ∈ V ∧ closure v ⊆ U} := by
    ext x
    rw [Set.mem_sUnion]
    constructor
    · intro hx
      obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := hV.nhds_basis_closure x |>.mem_iff.1 <| hU.mem_nhds hx
      exact ⟨v, ⟨hv2, hv3⟩, hv1⟩
    · intro hx
      obtain ⟨t, ⟨ht1, ht2⟩, hx⟩ := hx
      exact ht2 <| subset_closure hx
  have (f : C(X, Y)) (hf : K.MapsTo f U) : ∃ I, I.Finite ∧ I ⊆ W ∧ K.MapsTo f (⋃₀ I) := by
    have := hf.image_subset
    rw [h', Set.sUnion_eq_biUnion] at this
    have h'' : ∀ i ∈ {v | v ∈ V ∧ closure v ⊆ U}, IsOpen i :=
      fun x ⟨hx, _⟩ ↦ hV.isOpen hx
    obtain ⟨b, hb1, hb2, hb3⟩ := (hK.image f.continuous).elim_finite_subcover_image h'' this
    refine ⟨closure '' b, hb2.image _, ?_, ?_⟩
    · rintro - ⟨v, hv, rfl⟩
      exact ⟨v, (hb1 hv).1, (hb1 hv).2, rfl⟩
    rw [← Set.sUnion_eq_biUnion] at hb3
    rw [Set.mapsTo']
    apply hb3.trans
    apply Set.sUnion_mono_subsets
    exact fun _ ↦ subset_closure
  have : {f : C(X, Y) | K.MapsTo f U} =
      ⋃₀ {v | ∃ I, I.Finite ∧ I ⊆ W ∧ v = { f : C(X, Y) | K.MapsTo f (⋃₀ I)}} := by
    ext f
    constructor
    · intro h
      rw [Set.mem_sUnion]
      obtain ⟨I, hI1, hI2, hI3⟩ := this f h
      exact ⟨{f : C(X, Y) | K.MapsTo f (⋃₀ I)}, ⟨I, hI1, hI2, rfl⟩, hI3⟩
    · intro h
      rw [Set.mem_sUnion] at h
      obtain ⟨-, ⟨I, hI1, hI2, rfl⟩, h⟩ := h
      simp only [Set.mapsTo', Set.mem_setOf_eq] at h ⊢
      rw [main]
      apply h.trans
      exact Set.sUnion_subset_sUnion hI2
  simp only
  rw [this]
  apply MeasurableSet.sUnion
  · let f : Set (Set Y) → Set C(X, Y) := fun I ↦ {f : C(X, Y) | Set.MapsTo (⇑f) K (⋃₀ I)}
    have h1 : {I | I.Finite ∧ I ⊆ W}.Countable := by
      apply Set.countable_setOf_finite_subset
      exact cW
    apply (h1.image f).mono
    rintro - ⟨I, hI1, hI2, rfl⟩
    exact ⟨I, ⟨hI1, hI2⟩, rfl⟩
  rintro - ⟨I, hI1, hI2, rfl⟩
  obtain ⟨Q, cQ, dQ⟩ := TopologicalSpace.exists_countable_dense K
  have : {f : C(X, Y) | K.MapsTo f (⋃₀ I)} =
      {f : C(X, Y) | (Subtype.val '' Q ∩ K).MapsTo f (⋃₀ I)} := by
    ext f
    constructor
    · intro h x hx
      exact h (Set.mem_of_mem_inter_right hx)
    · intro h x hx
      have : x ∈ closure (Subtype.val '' Q) := Subtype.dense_iff.1 dQ hx
      rw [mem_closure_iff_seq_limit] at this
      obtain ⟨u, hu1, hu2⟩ := this
      have : ∀ s ∈ I, IsClosed s := by
        intro x hx
        have := hI2 hx
        obtain ⟨u, -, -, rfl⟩ := this
        exact isClosed_closure
      refine (isClosed_sUnion_of_finite hI1 this).mem_of_tendsto
        ((f.continuous.tendsto x).comp hu2)
        (Filter.Eventually.of_forall fun n ↦ h (Set.mem_inter (hu1 n) ?_))
      obtain ⟨y, hy, h'⟩ := hu1 n
      rw [← h']
      exact y.2
  have : {f : C(X, Y) | K.MapsTo f (⋃₀ I)} =
      ⋂ q ∈ Subtype.val '' Q ∩ K, (fun b ↦ b q) ⁻¹' (⋃₀ I) := by
    rw [this]
    ext f
    rw [Set.mem_iInter₂]
    constructor
    · exact fun h x hx ↦ h hx
    · exact fun h x hx ↦ h x hx
  rw [this]
  apply MeasurableSet.biInter
  · exact (cQ.image _).mono Set.inter_subset_left
  intro q hq
  apply MeasurableSet.preimage
  · have : ∀ s ∈ I, IsClosed s := by
      intro x hx
      have := hI2 hx
      obtain ⟨u, -, -, rfl⟩ := this
      exact isClosed_closure
    exact (isClosed_sUnion_of_finite hI1 this).measurableSet
  · apply Measurable.le (le_iSup _ q)
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
