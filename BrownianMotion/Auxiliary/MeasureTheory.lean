import BrownianMotion.Auxiliary.Algebra
import BrownianMotion.Auxiliary.Metric
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance

/-!
# Measure theory lemmas to be upstreamed to Mathlib
-/

open MeasureTheory

open scoped ENNReal NNReal ProbabilityTheory



@[to_additive]
theorem Filter.EventuallyEq.div' {α β : Type*} [Div β] {f f' g g' : α → β} {l : Filter α}
    (h : f =ᶠ[l] g) (h' : f' =ᶠ[l] g') : f / f' =ᶠ[l] g / g' :=
  h.comp₂ (· / ·) h'

namespace MeasureTheory

lemma MemLp.aemeasurable {X Y : Type*} {mX : MeasurableSpace X} {μ : Measure X}
    [MeasurableSpace Y] [ENorm Y] [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    [BorelSpace Y] {f : X → Y} {p : ℝ≥0∞} (hf : MemLp f p μ) : AEMeasurable f μ :=
  hf.aestronglyMeasurable.aemeasurable

end MeasureTheory

namespace ProbabilityTheory

open scoped InnerProductSpace in
lemma charFun_pi {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)] (μ : (i : ι) → Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] (t : PiLp 2 E) :
    charFun (E := PiLp 2 E) (Measure.pi μ) t = ∏ i, charFun (μ i) (t i) := by
  simp_rw [charFun, PiLp.inner_apply, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum,
    PiLp, WithLp]
  rw [integral_fintype_prod_eq_prod (f := fun i x ↦ Complex.exp (⟪x, t i⟫_ℝ * Complex.I))]

@[simp]
lemma charFun_toDual_symm_eq_charFunDual {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [InnerProductSpace ℝ E] {mE : MeasurableSpace E} {μ : Measure E} (L : NormedSpace.Dual ℝ E) :
    charFun μ ((InnerProductSpace.toDual ℝ E).symm L) = charFunDual μ L := by
  rw [charFun_eq_charFunDual_toDualMap]
  congr with x
  simp

lemma eq_gaussianReal_integral_variance {μ : Measure ℝ} {m : ℝ} {v : ℝ≥0}
    (h : μ = gaussianReal m v) : μ = gaussianReal μ[id] Var[id; μ].toNNReal := by
  simp [h]

section iIndepFun

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]

lemma measurePreserving_eval (i : ι) :
    MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) := by
  refine ⟨measurable_pi_apply i, ?_⟩
  ext s hs
  classical
  rw [Measure.map_apply (measurable_pi_apply i) hs, ← Set.univ_pi_update_univ, Measure.pi_pi]
  have : μ i s = (μ i) (Function.update (fun j ↦ Set.univ) i s i) := by simp
  rw [this]
  exact Finset.prod_eq_single_of_mem i (by simp) (fun j _ hj ↦ by simp [hj])

variable {𝒳 : ι → Type*} {m𝒳 : ∀ i, MeasurableSpace (𝒳 i)} {X : Π i, Ω i → 𝒳 i}

lemma iIndepFun_pi (mX : ∀ i, Measurable (X i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ) := by
  refine @iIndepFun_iff_map_fun_eq_pi_map (Π i, Ω i) ι _ (Measure.pi μ) _ 𝒳 _
    (fun i x ↦ X i (x i)) _ ?_ |>.2 ?_
  · exact fun i ↦ Measurable.aemeasurable (by fun_prop)
  · symm
    refine Measure.pi_eq fun s hs ↦ ?_
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
    have : (fun (ω : Π i, Ω i) i ↦ X i (ω i)) ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun i ↦ (X i) ⁻¹' (s i)) := by ext x; simp
    rw [this, Measure.pi_pi]
    congr with i
    rw [Measure.map_apply (by fun_prop) (hs i)]
    change _ = (Measure.pi μ) (((X i) ∘ (fun x ↦ x i)) ⁻¹' s i)
    rw [Set.preimage_comp, ← Measure.map_apply (measurable_pi_apply i) (mX i (hs i)),
      (measurePreserving_eval i).map_eq]

lemma iIndepFun_pi₀ (mX : ∀ i, AEMeasurable (X i) (μ i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ) := by
  have : iIndepFun (fun i ω ↦ (mX i).mk (X i) (ω i)) (Measure.pi μ) :=
    iIndepFun_pi fun i ↦ (mX i).measurable_mk
  refine this.congr fun i ↦ ?_
  change ((mX i).mk (X i)) ∘ Function.eval i =ᶠ[_] (X i) ∘ Function.eval i
  apply ae_eq_comp
  · exact (measurable_pi_apply i).aemeasurable
  · rw [(measurePreserving_eval i).map_eq]
    exact (AEMeasurable.ae_eq_mk (mX i)).symm

lemma variance_pi {X : Π i, Ω i → ℝ} (h : ∀ i, MemLp (X i) 2 (μ i)) :
    Var[∑ i, fun ω ↦ X i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i] := by
  rw [IndepFun.variance_sum]
  · congr with i
    change Var[(X i) ∘ (fun ω ↦ ω i); Measure.pi μ] = _
    rw [← variance_map, (measurePreserving_eval i).map_eq]
    · rw [(measurePreserving_eval i).map_eq]
      exact (h i).aestronglyMeasurable.aemeasurable
    · exact Measurable.aemeasurable (by fun_prop)
  · exact fun i _ ↦ (h i).comp_measurePreserving (measurePreserving_eval i)
  · exact fun i _ j _ hij ↦
      (iIndepFun_pi₀ fun i ↦ (h i).aestronglyMeasurable.aemeasurable).indepFun hij

lemma variance_sub {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[X - Y; μ] = Var[X; μ] - 2 * cov[X, Y; μ] + Var[Y; μ] := by
  rw [← covariance_same, covariance_sub_left hX hY (hX.sub hY), covariance_sub_right hX hX hY,
    covariance_sub_right hY hX hY, covariance_same, covariance_same, covariance_comm]
  · ring
  · exact hY.aemeasurable
  · exact hX.aemeasurable
  · exact hX.aemeasurable.sub hY.aemeasurable

lemma covariance_map_equiv {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} (X Y : Ω → ℝ) (Z : Ω' ≃ᵐ Ω) :
    cov[X, Y; μ.map Z] = cov[X ∘ Z, Y ∘ Z; μ] := by
  simp_rw [covariance, integral_map_equiv]
  rfl

lemma variance_map_equiv {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} (X : Ω → ℝ) (Y : Ω' ≃ᵐ Ω) :
    Var[X; μ.map Y] = Var[X ∘ Y; μ] := by
  simp_rw [variance, evariance, lintegral_map_equiv, integral_map_equiv]
  rfl

lemma centralMoment_of_integral_id_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {X : Ω → ℝ} (p : ℕ) (hX : μ[X] = 0) :
    centralMoment X p μ = ∫ ω, X ω ^ p ∂μ := by
  rw [centralMoment]
  simp [hX]

end iIndepFun

end ProbabilityTheory

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace E]
    [CompleteSpace F] [MeasurableSpace E] {μ : Measure E}

lemma integral_comp_id_comm' (h : Integrable _root_.id μ) (L : E →L[𝕜] F) :
    μ[L] = L μ[_root_.id] := by
  change ∫ x, L (_root_.id x) ∂μ = _
  rw [L.integral_comp_comm h]

lemma integral_comp_id_comm (h : Integrable _root_.id μ) (L : E →L[𝕜] F) :
    μ[L] = L (∫ x, x ∂μ) :=
  L.integral_comp_id_comm' h

variable [OpensMeasurableSpace E] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

lemma integral_id_map (h : Integrable _root_.id μ) (L : E →L[𝕜] F) :
    (μ.map L)[_root_.id] = L μ[_root_.id] := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp [L.integral_comp_id_comm h]

end ContinuousLinearMap

lemma EuclideanSpace.coe_measurableEquiv' {ι : Type*} :
    ⇑(EuclideanSpace.measurableEquiv ι) = ⇑(EuclideanSpace.equiv ι ℝ) := rfl

@[simp]
lemma zero_mem_parallelepiped {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] {v : ι → E} :
    0 ∈ parallelepiped v := ⟨0, by simp, by simp⟩

@[simp]
lemma nonempty_parallelepiped {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] {v : ι → E} :
    (parallelepiped v).Nonempty := ⟨0, zero_mem_parallelepiped⟩

@[simp, nontriviality]
lemma volume_of_nonempty_of_subsingleton {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [Subsingleton E] {s : Set E} (hs : s.Nonempty) :
    volume s = 1 := by
  rw [Subsingleton.eq_univ_of_nonempty hs,
    ← Subsingleton.eq_univ_of_nonempty (nonempty_parallelepiped (v := stdOrthonormalBasis ℝ E))]
  exact (stdOrthonormalBasis ℝ E).toBasis.addHaar_self

--generalizing `MeasureTheory.Measure.addHaar_ball_center`

@[to_additive]
lemma MeasureTheory.Measure.IsMulLeftInvariant.measure_ball_const
    {G : Type*} [Group G] [PseudoMetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [IsIsometricSMul G G]
    [MeasurableMul G] (a b : G) (r : ℝ) :
    μ (Metric.ball a r) = μ (Metric.ball b r) := by
  rw [show a = (b / a)⁻¹ * b by simp, ← Metric.preimage_mul_left_ball, ← Measure.map_apply,
    map_mul_left_eq_self]
  · fun_prop
  · exact Metric.isOpen_ball.measurableSet

@[to_additive]
lemma MeasureTheory.Measure.IsMulRightInvariant.measure_ball_const
    {G : Type*} [CommGroup G] [PseudoMetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [μ.IsMulRightInvariant] [IsIsometricSMul Gᵐᵒᵖ G]
    [MeasurableMul G] (a b : G) (r : ℝ) :
    μ (Metric.ball a r) = μ (Metric.ball b r) := by
  rw [show a = b / (b / a) by simp, ← Metric.preimage_mul_right_ball, ← Measure.map_apply,
    map_mul_right_eq_self]
  · fun_prop
  · exact Metric.isOpen_ball.measurableSet

@[to_additive]
lemma MeasureTheory.Measure.IsMulLeftInvariant.measure_closedBall_const
    {G : Type*} [Group G] [PseudoMetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [IsIsometricSMul G G]
    [MeasurableMul G] (a b : G) (r : ℝ) :
    μ (Metric.closedBall a r) = μ (Metric.closedBall b r) := by
  rw [show a = (b / a)⁻¹ * b by simp, ← Metric.preimage_mul_left_closedBall, ← Measure.map_apply,
    map_mul_left_eq_self]
  · fun_prop
  · exact Metric.isClosed_closedBall.measurableSet

@[to_additive]
lemma MeasureTheory.Measure.IsMulRightInvariant.measure_closeBall_const
    {G : Type*} [CommGroup G] [PseudoMetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [μ.IsMulRightInvariant] [IsIsometricSMul Gᵐᵒᵖ G]
    [MeasurableMul G] (a b : G) (r : ℝ) :
    μ (Metric.closedBall a r) = μ (Metric.closedBall b r) := by
  rw [show a = b / (b / a) by simp, ← Metric.preimage_mul_right_closedBall, ← Measure.map_apply,
    map_mul_right_eq_self]
  · fun_prop
  · exact Metric.isClosed_closedBall.measurableSet

@[to_additive]
lemma MeasureTheory.Measure.IsMulLeftInvariant.measure_ball_const'
    {G : Type*} [Group G] [PseudoEMetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [IsIsometricSMul G G]
    [MeasurableMul G] (a b : G) (r : ℝ≥0∞) :
    μ (EMetric.ball a r) = μ (EMetric.ball b r) := by
  rw [show a = (b / a)⁻¹ * b by simp, ← EMetric.preimage_mul_left_ball, ← Measure.map_apply,
    map_mul_left_eq_self]
  · fun_prop
  · exact EMetric.isOpen_ball.measurableSet

@[to_additive]
lemma MeasureTheory.Measure.IsMulRightInvariant.measure_ball_const'
    {G : Type*} [CommGroup G] [PseudoEMetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [μ.IsMulRightInvariant] [IsIsometricSMul Gᵐᵒᵖ G]
    [MeasurableMul G] (a b : G) (r : ℝ≥0∞) :
    μ (EMetric.ball a r) = μ (EMetric.ball b r) := by
  rw [show a = b / (b / a) by simp, ← EMetric.preimage_mul_right_ball, ← Measure.map_apply,
    map_mul_right_eq_self]
  · fun_prop
  · exact EMetric.isOpen_ball.measurableSet

@[to_additive]
lemma MeasureTheory.Measure.IsMulLeftInvariant.measure_closedBall_const'
    {G : Type*} [Group G] [PseudoEMetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [IsIsometricSMul G G]
    [MeasurableMul G] (a b : G) (r : ℝ≥0∞) :
    μ (EMetric.closedBall a r) = μ (EMetric.closedBall b r) := by
  rw [show a = (b / a)⁻¹ * b by simp, ← EMetric.preimage_mul_left_closedBall, ← Measure.map_apply,
    map_mul_left_eq_self]
  · fun_prop
  · exact EMetric.isClosed_closedBall.measurableSet

@[to_additive]
lemma MeasureTheory.Measure.IsMulRightInvariant.measure_closeBall_const'
    {G : Type*} [CommGroup G] [PseudoEMetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [μ.IsMulRightInvariant] [IsIsometricSMul Gᵐᵒᵖ G]
    [MeasurableMul G] (a b : G) (r : ℝ≥0∞) :
    μ (EMetric.closedBall a r) = μ (EMetric.closedBall b r) := by
  rw [show a = b / (b / a) by simp, ← EMetric.preimage_mul_right_closedBall, ← Measure.map_apply,
    map_mul_right_eq_self]
  · fun_prop
  · exact EMetric.isClosed_closedBall.measurableSet

open Metric

lemma InnerProductSpace.volume_closedBall_div {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (x y : E) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    volume (closedBall x r) / volume (closedBall y s) =
      ENNReal.ofReal (r / s) ^ (Module.finrank ℝ E) := by
  obtain _ | _ := subsingleton_or_nontrivial E
  · simp [hr.le, hs.le]
  rw [InnerProductSpace.volume_closedBall, InnerProductSpace.volume_closedBall,
    ENNReal.mul_div_mul_right _ _ (by positivity) (by simp)]
  simp_rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.div_rpow_of_nonneg _ _ (by simp), ENNReal.ofReal_div_of_pos hs]

lemma InnerProductSpace.volume_closedBall_div' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (x y : E) (r s : ℝ≥0∞) :
    volume (EMetric.closedBall x r) / volume (EMetric.closedBall y s) =
      (r / s) ^ (Module.finrank ℝ E) := by
  nontriviality E
  obtain rfl | hr := eq_top_or_lt_top r <;> obtain rfl | hs := eq_top_or_lt_top s
  any_goals simp
  · lift s to ℝ≥0 using hs.ne
    simp [ENNReal.top_div, emetric_closedBall_nnreal, (isCompact_closedBall _ _).measure_ne_top]
  · obtain rfl | hr' := eq_zero_or_pos r <;> obtain rfl | hs' := eq_zero_or_pos s
    · simp
    · simp
    · simp [ENNReal.div_zero, hr'.ne', EMetric.measure_closedBall_pos volume x hr'.ne' |>.ne']
    lift r to ℝ≥0 using hr.ne
    lift s to ℝ≥0 using hs.ne
    simp_rw [emetric_closedBall_nnreal]
    rw [volume_closedBall_div, ENNReal.ofReal_div_of_pos]
    · simp
    all_goals simp_all
