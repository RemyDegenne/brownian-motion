import BrownianMotion.Auxiliary.Algebra
import BrownianMotion.Auxiliary.Metric
import BrownianMotion.Auxiliary.Topology
import BrownianMotion.Auxiliary.WithLp
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.InnerProductSpace.ProdL2
/-!
# Measure theory lemmas to be upstreamed to Mathlib
-/

open MeasureTheory

open scoped ENNReal NNReal ProbabilityTheory

attribute [fun_prop] aemeasurable_id'

@[to_additive]
theorem Filter.EventuallyEq.div' {α β : Type*} [Div β] {f f' g g' : α → β} {l : Filter α}
    (h : f =ᶠ[l] g) (h' : f' =ᶠ[l] g') : f / f' =ᶠ[l] g / g' :=
  h.comp₂ (· / ·) h'

namespace ProbabilityTheory

open WithLp

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

lemma iIndepFun_iff_charFunDual_eq_pi {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Π i, Ω → (E i)}
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] (mX : ∀ i, AEMeasurable (X i) μ) :
    iIndepFun X μ ↔ ∀ L,
      charFunDual (μ.map fun ω i ↦ X i ω) L =
        ∏ i, charFunDual (μ.map (X i)) (L.comp (.single ℝ E i)) := sorry
-- PR #26269 in Mathlib

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
    [InnerProductSpace ℝ E] {mE : MeasurableSpace E} {μ : Measure E} (L : StrongDual ℝ E) :
    charFun μ ((InnerProductSpace.toDual ℝ E).symm L) = charFunDual μ L := by
  rw [charFun_eq_charFunDual_toDualMap]
  congr with x
  simp

lemma eq_gaussianReal_integral_variance {μ : Measure ℝ} {m : ℝ} {v : ℝ≥0}
    (h : μ = gaussianReal m v) : μ = gaussianReal μ[id] Var[id; μ].toNNReal := by
  simp [h]

section iIndepFun

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)}

variable [∀ i, IsProbabilityMeasure (μ i)]

lemma variance_pi {X : Π i, Ω i → ℝ} (h : ∀ i, MemLp (X i) 2 (μ i)) :
    Var[∑ i, fun ω ↦ X i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i] := by
  rw [IndepFun.variance_sum]
  · congr with i
    change Var[(X i) ∘ (fun ω ↦ ω i); Measure.pi μ] = _
    rw [← variance_map, (measurePreserving_eval i).map_eq]
    · rw [(measurePreserving_eval i).map_eq]
      exact (h i).aemeasurable
    · exact Measurable.aemeasurable (by fun_prop)
  · exact fun i _ ↦ (h i).comp_measurePreserving (measurePreserving_eval _ i)
  · exact fun i _ j _ hij ↦
      (iIndepFun_pi₀ fun i ↦ (h i).aemeasurable).indepFun hij

end iIndepFun

section covariance

lemma centralMoment_of_integral_id_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {X : Ω → ℝ} (p : ℕ) (hX : μ[X] = 0) :
    centralMoment X p μ = ∫ ω, X ω ^ p ∂μ := by
  rw [centralMoment]
  simp [hX]

end covariance

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
    ∫ x, x ∂(μ.map L) = L (∫ x, x ∂μ) := by
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
  · simp
  · lift s to ℝ≥0 using hs.ne
    simp [ENNReal.top_div, emetric_closedBall_nnreal, (isCompact_closedBall _ _).measure_ne_top]
  · simp
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

section eval

namespace MeasureTheory

open Finset

variable {ι Ω : Type*} {E : ι → Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [∀ i, NormedAddCommGroup (E i)] {p : ℝ≥0∞}

section Pi

variable {X : (i : ι) → Ω → E i}

lemma memLp_pi_iff : MemLp (fun ω ↦ (X · ω)) p P ↔ ∀ i, MemLp (X i) p P where
  mp hX i := by
    have : X i = (Function.eval i) ∘ (fun ω ↦ (X · ω)) := by ext; simp
    rw [this]
    exact (LipschitzWith.eval i).comp_memLp (by simp) hX
  mpr hX := by
    classical
    have : (fun ω ↦ (X · ω)) = ∑ i, (Pi.single i) ∘ (X i) := by ext; simp
    rw [this]
    refine memLp_finset_sum' _ fun i _ ↦ ?_
    exact (Isometry.single i).lipschitz.comp_memLp (by simp) (hX i)

lemma memLp_prod_iff {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {X : Ω → E} {Y : Ω → F} :
    MemLp (fun ω ↦ (X ω, Y ω)) p P ↔ MemLp X p P ∧ MemLp Y p P where
  mp h := by
    have h1 : X = Prod.fst ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
    have h2 : Y = Prod.snd ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
    rw [h1, h2]
    exact ⟨LipschitzWith.prod_fst.comp_memLp (by simp) h,
      LipschitzWith.prod_snd.comp_memLp (by simp) h⟩
  mpr h := by
    have : (fun ω ↦ (X ω, Y ω)) = (AddMonoidHom.inl E F) ∘ X + (AddMonoidHom.inr E F) ∘ Y := by
      ext; all_goals simp
    rw [this]
    exact MemLp.add (Isometry.inl.lipschitz.comp_memLp (by simp) h.1)
      (Isometry.inr.lipschitz.comp_memLp (by simp) h.2)

alias ⟨MemLp.eval, MemLp.of_eval⟩ := memLp_pi_iff

lemma integrable_pi_iff : Integrable (fun ω ↦ (X · ω)) P ↔ ∀ i, Integrable (X i) P := by
  simp_rw [← memLp_one_iff_integrable, memLp_pi_iff]

alias ⟨Integrable.eval, Integrable.of_eval⟩ := integrable_pi_iff

variable [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]

lemma integral_eval (hX : ∀ i, Integrable (X i) P) (i : ι) :
    (∫ ω, (X · ω) ∂P) i = ∫ ω, X i ω ∂P := by
  rw [← ContinuousLinearMap.proj_apply (R := ℝ) i (∫ ω, (X · ω) ∂P),
    ← ContinuousLinearMap.integral_comp_comm]
  · simp
  exact Integrable.of_eval hX

end Pi

section PiLp

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] {X : Ω → PiLp q E}

lemma memLp_piLp_iff : MemLp X p P ↔ ∀ i, MemLp (X · i) p P := by
  simp_rw [← memLp_pi_iff, ← PiLp.ofLp_apply, ← Function.comp_apply (f := WithLp.ofLp)]
  exact (PiLp.lipschitzWith_ofLp q E).memLp_comp_iff_of_antilipschitz
    (PiLp.antilipschitzWith_ofLp q E) (by simp) |>.symm

alias ⟨MemLp.eval_piLp, MemLp.of_eval_piLp⟩ := memLp_piLp_iff

lemma memLp_prodLp_iff {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {X : Ω → WithLp q (E × F)} :
      MemLp X p P ↔
      MemLp (fun ω ↦ (X ω).fst) p P ∧
      MemLp (fun ω ↦ (X ω).snd) p P := by
  simp_rw [← memLp_prod_iff, ← WithLp.ofLp_fst, ← WithLp.ofLp_snd,
    ← Function.comp_apply (f := WithLp.ofLp)]
  exact (WithLp.prod_lipschitzWith_ofLp q E F).memLp_comp_iff_of_antilipschitz
    (WithLp.prod_antilipschitzWith_ofLp q E F) (by simp) |>.symm

alias ⟨MemLp.eval_prodLp, MemLp.of_eval_prodLp⟩ := memLp_prodLp_iff

lemma integrable_piLp_iff : Integrable X P ↔ ∀ i, Integrable (X · i) P := by
  simp_rw [← memLp_one_iff_integrable, memLp_piLp_iff]

alias ⟨Integrable.eval_piLp, Integrable.of_eval_piLp⟩ := integrable_piLp_iff

variable [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]

lemma _root_.PiLp.integral_eval (hX : ∀ i, Integrable (X · i) P) (i : ι) :
    (∫ ω, X ω ∂P) i = ∫ ω, X ω i ∂P := by
  rw [← PiLp.proj_apply (𝕜 := ℝ) q E i (∫ ω, X ω ∂P), ← ContinuousLinearMap.integral_comp_comm]
  · simp
  exact Integrable.of_eval_piLp hX

end PiLp

theorem fst_integral_withLp [Fact (1 ≤ p)] {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    [CompleteSpace F] {f : X → WithLp p (E × F)} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ := by
  rw [← WithLp.ofLp_fst]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv p ℝ E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm, fst_integral]
  · rfl
  · simpa

theorem snd_integral_withLp [Fact (1 ≤ p)] {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    [CompleteSpace E] {f : X → WithLp p (E × F)} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ := by
  rw [← WithLp.ofLp_snd]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv p ℝ E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm, snd_integral]
  · rfl
  · simpa

end MeasureTheory

end eval
