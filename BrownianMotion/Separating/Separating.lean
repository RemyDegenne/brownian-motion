import Mathlib.Probability.IdentDistrib

noncomputable section

open Classical BigOperators Topology Set Filter MeasureTheory NNReal ENNReal ProbabilityTheory

/-
Declare variables and assign properties:
- P and P' are measures on Ω, Ω', respectively, but for some results the image measures on E
  are denoted by P and P' as well.
- The topological properties of E have to be declared in the correct order, which is why
  they are specified at each occurence.
-/
variable {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
{P : Measure Ω} {P' : Measure Ω'} {X : Ω → E} {Y : Ω' → E}

lemma IsPiSystem.closed {E : Type*} [TopologicalSpace E] : IsPiSystem {A : Set E | IsClosed A} := by
  dsimp [IsPiSystem]
  intros A hA B hB _
  exact IsClosed.inter hA hB


--What is a good name for the namespace? MeasureTheory already used several times in the mathlib.
namespace Separating

instance ProbabilityMeasureMap
--{Ω E : Type*} {mea_Om : MeasurableSpace Ω} (ae_measX : AEMeasurable X P)[mea_E : MeasurableSpace E] {P : Measure Ω} {X : Ω → E}
[IsProbabilityMeasure P] [ae_measX : Fact (AEMeasurable X P)] : IsProbabilityMeasure (Measure.map X P)  :=
  isProbabilityMeasure_map ae_measX.out


lemma push_forward_iff
--{Ω E : Type*} {mea_Om : MeasurableSpace Ω} [mea_E : MeasurableSpace E] {P : Measure Ω} {X : Ω → E}
[IsProbabilityMeasure P] [ae_meas : Fact (AEMeasurable X P)]
(A : Set E) (hA : MeasurableSet A) : (Measure.map X P) A = P (X⁻¹'A) :=
  Measure.map_apply_of_aemeasurable ae_meas.out hA


lemma ident_distrib_iff
--{E Ω Ω': Type*} {mea_Om : MeasurableSpace Ω} {mea_Om' : MeasurableSpace Ω'}
--[mea_E : MeasurableSpace E] {P : Measure Ω} {P' : Measure Ω'} {X : Ω → E} {Y : Ω' → E}
[IsProbabilityMeasure P] [IsProbabilityMeasure P']
[ae_measX : Fact (AEMeasurable X P)] [ae_measY : Fact (AEMeasurable Y P')] :
((ProbabilityTheory.IdentDistrib X Y P P') ↔ Measure.map X P = Measure.map Y P') := by
  constructor
  · intro h; rw [h.map_eq]
  · intro h1; exact ⟨ ae_measX.out, ae_measY.out, h1⟩


/- Two measures are the same iff they are equal on all closed sets.
-/
theorem measure_eq_iff_closed
--{E : Type*} [mea_E : MeasurableSpace E]
--{P : Measure E} {P' : Measure E}
[top_E : TopologicalSpace E][bor_E : BorelSpace E]
{P P' : Measure E} [is_probP : IsProbabilityMeasure P] [is_probP' : IsProbabilityMeasure P']
 : P = P' ↔ (∀ (A : Set E), IsClosed A → P A = P' A) := by
  constructor
  · intros hP _ _; congr
  · intro h
    let C := {A : Set E | IsClosed A}
    apply MeasureTheory.ext_of_generate_finite C _ IsPiSystem.closed _ _
    · rw [← borel_eq_generateFrom_isClosed]; borelize E; simp
    · intros A hAC; exact h A hAC
    · simp only [MeasureTheory.IsProbabilityMeasure.measure_univ]


/- Two random variables have the same distribution iff their image measures agree on all closed sets.
-/
theorem ident_distrib_iff_closed
--{E Ω Ω': Type*} {mea_Om : MeasurableSpace Ω} {mea_Om' : MeasurableSpace Ω'} [mea_E : MeasurableSpace E]
--{P : Measure Ω} {P' : Measure Ω'} {X : Ω → E} {Y : Ω' → E}
[top_E : TopologicalSpace E] [bor_E : BorelSpace E]
[IsProbabilityMeasure P] [IsProbabilityMeasure P'] [ae_measX : Fact (AEMeasurable X P)] [ae_measY : Fact (AEMeasurable Y P')] :
( (ProbabilityTheory.IdentDistrib X Y P P') ↔ (∀ (A : Set E), IsClosed A → P (X⁻¹'A) = P' (Y⁻¹'A))) := by
  constructor
  · intros h A hA
    apply ProbabilityTheory.IdentDistrib.measure_mem_eq h (IsClosed.measurableSet hA)
  · intro h
    refine ⟨ ae_measX.out, ae_measY.out, ?_⟩
    apply measure_eq_iff_closed.2
    intros A hA
    rw [push_forward_iff, push_forward_iff]
    exact h A hA
    apply IsClosed.measurableSet hA
    apply IsClosed.measurableSet hA


lemma expectation_indicator
--{E : Type*} {mea_E : MeasurableSpace E}
{P : Measure E} [IsProbabilityMeasure P] (A : Set E) (hA : MeasurableSet A) : ∫ (x : E), A.indicator 1 x ∂P = (P A).toReal :=
  MeasureTheory.integral_indicator_one hA


lemma lexpectation_indicator
--{E : Type*} {mea_E : MeasurableSpace E}
{P : Measure E} [IsProbabilityMeasure P] (A : Set E) (hA : MeasurableSet A) : ∫⁻ (a : E), A.indicator 1 a ∂P = (P A) := by
  have h1 : P A = 1* (P A) := by rw [one_mul]
  rw [h1]
  rw [← MeasureTheory.lintegral_indicator_const hA 1]
  congr


lemma lintegral_of_thickened_eq_thickened_aux
--{E : Type*} [mea_E : MeasurableSpace E]
[met_E : PseudoEMetricSpace E] [BorelSpace E] {P : Measure E} [IsProbabilityMeasure P] {δ : ℝ} (δ_pos : 0 < δ) (A : Set E)
: ∫⁻ a, (thickenedIndicatorAux δ A) a ∂P = ∫⁻ a, (thickenedIndicator δ_pos A) a ∂P := by
  congr
  simp only [thickenedIndicator_apply, Option.mem_def, some_eq_coe]
  ext
  rw [coe_toNNReal]
  exact thickenedIndicatorAux_lt_top.ne


/- The lintegral of thickened indicators tends to the measure of a closed set.
-/
theorem lintegral_of_thickened_indicator_tendsto_indicator_closure
--{E : Type*} {mea_E : MeasurableSpace E}
[met_E : PseudoEMetricSpace E] [bor_E : BorelSpace E] {P : Measure E} [IsProbabilityMeasure P]
{δseq : ℕ → ℝ} (δseq_pos : ∀ (n : ℕ), 0 < δseq n) (δseq_lim : Tendsto δseq Filter.atTop (nhds 0)) (A : Set E)
: Tendsto (fun n => ∫⁻ a, (thickenedIndicatorAux (δseq n) A) a ∂P) atTop (𝓝 (P (closure A))) := by
  have h : MeasurableSet (closure A) := by
  {
    apply IsClosed.measurableSet
    simp only [isClosed_closure]
  }
  rw [← lexpectation_indicator (closure A) h]
  apply tendsto_lintegral_of_dominated_convergence
  · intro n
    apply Continuous.measurable
    apply (continuous_thickenedIndicatorAux (δseq_pos n) A)
  · intro n
    apply eventually_of_forall
    apply thickenedIndicatorAux_le_one (δseq n) A
  · simp only [MeasureTheory.IsProbabilityMeasure.measure_univ, MeasureTheory.lintegral_one, ENNReal.one_ne_top, not_false_iff]
    exact one_ne_top
  · apply eventually_of_forall
    intro x
    exact tendsto_pi_nhds.mp (thickenedIndicatorAux_tendsto_indicator_closure δseq_lim A) x


lemma lint
--{E Ω : Type*} {mea_Om : MeasurableSpace Ω} [mea_E : MeasurableSpace E] {P : Measure Ω}
[top_E : TopologicalSpace E] [bor_E :BorelSpace E] [IsProbabilityMeasure P] {X : Ω → E}
[ae_meas : Fact (AEMeasurable X P)] (f : BoundedContinuousFunction E ℝ≥0)
: (∫⁻ x, f (x) ∂(Measure.map X P) = ∫⁻ ω, f (X ω) ∂P) := by
  apply MeasureTheory.lintegral_map'
  · apply Measurable.aemeasurable
    apply Continuous.measurable
    rw [continuous_coe_iff]
    continuity
  · exact ae_meas.out


/- Two measures are the same iff their integrals of all bounded continuous functions agree.
-/
theorem measure_eq_iff_bounded_continuous
--{E : Type*} [mea_E : MeasurableSpace E]
[met_E : PseudoEMetricSpace E] [bor_E : BorelSpace E] {P : Measure E} {P' : Measure E}
[is_probP : IsProbabilityMeasure P] [is_probP' : IsProbabilityMeasure P']
: (P = P' ↔ ∀ (f : BoundedContinuousFunction E ℝ≥0), ∫⁻ a, f a ∂P = ∫⁻ a, f a ∂P') := by
  constructor
  · intros hP f
    congr
  · intro hf
    rw [measure_eq_iff_closed]
    intros A hA
    rw [← IsClosed.closure_eq hA]
    let δseq : ℕ → ℝ := λ n => (1/((n : ℝ) +1))
    have δseq_pos : ∀ (n : ℕ), 0 < (δseq n) := by
      intro n
      simp [δseq]
      norm_cast
      linarith
    have δseq_lim : Tendsto δseq Filter.atTop (nhds 0) := by
      simp only [δseq]
      apply tendsto_one_div_add_atTop_nhds_zero_nat
    have h_thick : ∀ (δ : ℝ) (δ_pos : 0 < δ) (A : Set E), ∫⁻ (a : E), thickenedIndicatorAux δ A a ∂P = ∫⁻ (a : E), thickenedIndicatorAux δ A a ∂P' := by
      intros δ δ_pos A
      rw [lintegral_of_thickened_eq_thickened_aux δ_pos, lintegral_of_thickened_eq_thickened_aux δ_pos]
      exact hf (thickenedIndicator δ_pos A)
    have hlim1 : Tendsto (fun n => ∫⁻ a, (thickenedIndicatorAux (δseq n) A) a ∂P) atTop (𝓝 (P (closure A))) := by
      apply lintegral_of_thickened_indicator_tendsto_indicator_closure δseq_pos δseq_lim A
    have hlim2 : Tendsto (fun n => ∫⁻ a, (thickenedIndicatorAux (δseq n) A) a ∂P') atTop (𝓝 (P' (closure A))) := by
      apply lintegral_of_thickened_indicator_tendsto_indicator_closure δseq_pos δseq_lim A
    let x1 := fun n => ∫⁻ (a : E), thickenedIndicatorAux (δseq n) A a ∂P
    let x2 := fun n => ∫⁻ (a : E), thickenedIndicatorAux (δseq n) A a ∂P'
    change Tendsto x1 atTop (𝓝 (P (closure A))) at hlim1
    change Tendsto x2 atTop (𝓝 (P' (closure A))) at hlim2
    have h_eq : x1 = x2 := by
      simp [x1, x2]
      ext n
      rw [h_thick (δseq n) (δseq_pos n) A]
    rw [h_eq] at hlim1
    exact tendsto_nhds_unique hlim1 hlim2


/- Two random variables have the same distribution iff their expectations of all bounded continuous functions agree. -/
theorem ident_distrib_iff_bounded_continuous
--{E Ω Ω': Type*} {mea_Om : MeasurableSpace Ω} {mea_Om' : MeasurableSpace Ω'} {P : Measure Ω} {P' : Measure Ω'} {X : Ω → E} {Y : Ω' → E}
[mea_E : MeasurableSpace E] [met_E : PseudoEMetricSpace E][bor_E : BorelSpace E]
[IsProbabilityMeasure P] [IsProbabilityMeasure P'] [ae_measX : Fact (AEMeasurable X P)] [ae_measY : Fact (AEMeasurable Y P')]
: ( (ProbabilityTheory.IdentDistrib X Y P P') ↔ (∀ (f : BoundedContinuousFunction E ℝ≥0), ∫⁻ ω, f (X ω) ∂P = ∫⁻ ω', f (Y ω') ∂P')) := by
  rw [ident_distrib_iff]
  simp_rw [← lint _]
  rw [← measure_eq_iff_bounded_continuous]


end Separating
