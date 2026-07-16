/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.Martingale
public import BrownianMotion.StochasticIntegral.Jump
public import BrownianMotion.StochasticIntegral.LocalizingLeastGE
public import BrownianMotion.StochasticIntegral.LocalMartingale
public import Mathlib.Probability.Process.HittingTime

/-! # Square integrable martingales

-/

@[expose] public section

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal Topology NNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

/-- A square integrable martingale is a martingale with cadlag paths and uniformly bounded
second moments. -/
structure IsSquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop where
  martingale : Martingale X 𝓕 P
  cadlag : ∀ ω, IsCadlag (X · ω)
  bounded : ⨆ i, eLpNorm (X i) 2 P < ∞

/-- A stochastic process is locally square-integrable if it satisfies the square-integrable
martingale property locally. -/
def IsLocallySquareIntegrable [OrderBot ι] [OrderTopology ι]
    (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω := by volume_tac) : Prop :=
  Locally (fun Y ↦ IsSquareIntegrable Y 𝓕 P) 𝓕 X P

lemma IsSquareIntegrable.isLocallySquareIntegrable [OrderBot ι] [OrderTopology ι]
    (hX : IsSquareIntegrable X 𝓕 P) :
    IsLocallySquareIntegrable X 𝓕 P :=
  Locally.of_prop hX

omit [TopologicalSpace ι] [NormedSpace ℝ E] in
@[simp, nontriviality]
lemma stronglyAdapted_of_subsingleton_dom [Subsingleton Ω] (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) :
    StronglyAdapted 𝓕 X := by
  intro i
  exact .of_subsingleton_dom

omit [TopologicalSpace ι] [NormedSpace ℝ E] in
@[simp, nontriviality]
lemma stronglyAdapted_of_subsingleton_cod [Subsingleton E] (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) :
    StronglyAdapted 𝓕 X := by
  intro i
  exact .of_subsingleton_cod

omit [TopologicalSpace ι] in
@[simp]
lemma martingale_of_isEmpty [IsEmpty Ω] (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    Martingale X 𝓕 P := by
  refine ⟨?_, ?_⟩
  · exact stronglyAdapted_of_subsingleton_dom _ _
  · intro i j hij
    have : P = 0 := Subsingleton.elim _ _
    simp [this, Filter.EventuallyEq, Filter.eventually_bot]

@[simp]
lemma isSquareIntegrable_of_isEmpty [IsEmpty Ω]
    (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    IsSquareIntegrable X 𝓕 P := by
  refine ⟨?_, ?_, ?_⟩
  · exact martingale_of_isEmpty _ _ _
  · intro ω
    exfalso
    exact isEmptyElim ω
  · simp

@[simp]
lemma isLocallySquareIntegrable_of_isEmpty [OrderBot ι] [OrderTopology ι] [IsEmpty Ω]
    (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    IsLocallySquareIntegrable X 𝓕 P := by
  refine IsSquareIntegrable.isLocallySquareIntegrable ?_
  exact isSquareIntegrable_of_isEmpty _ _ _

lemma isSquareIntegrable_of_le_const (h_mart : Martingale X 𝓕 P) (h_cadlag : ∀ ω, IsCadlag (X · ω))
    {C : ℝ≥0} (h_bound : ∀ i, eLpNorm (X i) 2 P ≤ C) :
    IsSquareIntegrable X 𝓕 P := by
  refine ⟨h_mart, h_cadlag, ?_⟩
  rw [iSup_lt_iff]
  exact ⟨C, by simp, h_bound⟩

lemma IsSquareIntegrable.integrable_sq (hX : IsSquareIntegrable X 𝓕 P) (i : ι) :
    Integrable (fun ω ↦ ‖X i ω‖ ^ 2) P := by
  constructor
  · have hX_meas := (hX.martingale.stronglyAdapted i).mono (𝓕.le i)
    fun_prop
  · have hX_bound : eLpNorm (X i) 2 P < ∞ := by
      calc eLpNorm (X i) 2 P
      _ ≤ ⨆ j, eLpNorm (X j) 2 P := le_iSup (fun j ↦ eLpNorm (X j) 2 P) i
      _ < ∞ := hX.bounded
    simpa [HasFiniteIntegral, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top] using hX_bound

lemma IsSquareIntegrable.add [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    (hY : IsSquareIntegrable Y 𝓕 P) :
    IsSquareIntegrable (fun i ω ↦ X i ω + Y i ω) 𝓕 P := by
  refine ⟨hX.martingale.add hY.martingale, fun ω ↦ (hX.2 ω).add (hY.2 ω), ?_⟩
  have hX_bound : ⨆ i, eLpNorm (X i) 2 P < ∞ := hX.bounded
  have hY_bound : ⨆ i, eLpNorm (Y i) 2 P < ∞ := hY.bounded
  calc ⨆ i, eLpNorm (fun ω ↦ X i ω + Y i ω) 2 P
      ≤ ⨆ i, (eLpNorm (X i) 2 P + eLpNorm (Y i) 2 P) := by
        refine iSup_mono fun i ↦ ?_
        exact eLpNorm_add_le
          ((hX.martingale.stronglyAdapted i).mono (𝓕.le i)).aestronglyMeasurable
          ((hY.martingale.stronglyAdapted i).mono (𝓕.le i)).aestronglyMeasurable (by simp)
    _ ≤ (⨆ i, eLpNorm (X i) 2 P) + ⨆ i, eLpNorm (Y i) 2 P := by
        refine iSup_le fun i => ?_
        gcongr
        · exact le_iSup (fun i => eLpNorm (X i) 2 P) i
        · exact le_iSup (fun i => eLpNorm (Y i) 2 P) i
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hX_bound, hY_bound⟩

lemma IsSquareIntegrable.smul [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) (r : ℝ) :
    IsSquareIntegrable (fun i ω ↦ r • X i ω) 𝓕 P where
  martingale := hX.martingale.smul r
  cadlag ω := by
    simpa [Pi.smul_apply] using (hX.cadlag ω).fun_const_smul r
  bounded := by
    change (⨆ i, eLpNorm (r • X i) 2 P) < ∞
    simp only [eLpNorm_const_smul, ← ENNReal.mul_iSup]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hX.bounded

variable [SigmaFiniteFiltration P 𝓕]

lemma IsSquareIntegrable.submartingale_sq_norm [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) :
    Submartingale (fun i ω ↦ ‖X i ω‖ ^ 2) 𝓕 P := by
  refine hX.1.submartingale_convex_comp (φ := fun x ↦ ‖x‖ ^ 2) ?_ (by fun_prop) fun i ↦ ?_
  · exact ConvexOn.pow convexOn_univ_norm (fun _ _ ↦ by positivity) 2
  · refine MemLp.integrable_norm_pow ⟨?_, ?_⟩ (by linarith)
    · exact hX.1.1.stronglyMeasurable.aestronglyMeasurable
    · exact lt_of_le_of_lt (le_iSup (fun i ↦ eLpNorm (X i) 2 P) i) hX.3

/-- A locally square-integrable martingale has locally submartingale squared norm. -/
lemma IsLocallySquareIntegrable.isLocalSubmartingale_sq_norm
    [OrderBot ι] [OrderTopology ι] [CompleteSpace E]
    (hX : IsLocallySquareIntegrable X 𝓕 P) :
    IsLocalSubmartingale (fun t ω ↦ ‖X t ω‖ ^ 2) 𝓕 P := by
  have h_stopped_sq_norm {τ : Ω → WithTop ι} :
      stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (fun ω ↦ ‖X t ω‖ ^ 2)) τ =
        fun t ω ↦ ‖stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ t ω‖ ^ 2 := by
    ext t ω
    by_cases hτ : ⊥ < τ ω <;> simp [stoppedProcess, hτ]
  unfold IsLocalSubmartingale
  change Locally (fun Y : ι → Ω → ℝ ↦ Submartingale Y 𝓕 P ∧
      ∀ ω, IsCadlag (Y · ω)) 𝓕 (fun t ω ↦ ‖X t ω‖ ^ 2) P
  refine ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  have hXn := hX.stoppedProcess_localSeq n
  constructor
  · simpa [h_stopped_sq_norm] using hXn.submartingale_sq_norm
  · intro ω
    simpa [h_stopped_sq_norm] using IsCadlag.norm_sq (hXn.cadlag ω)

lemma IsSquareIntegrable.eLpNorm_mono [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    {i j : ι} (hij : i ≤ j) :
    eLpNorm (X i) 2 P ≤ eLpNorm (X j) 2 P := by
  have : ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ ∫ ω, ‖X j ω‖ ^ 2 ∂P := by
    simpa using hX.submartingale_sq_norm.setIntegral_le hij MeasurableSet.univ
  calc
  _ = (∫⁻ ω, ‖X i ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂P) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    simp [eLpNorm_eq_lintegral_rpow_enorm_toReal]
  _ = (ENNReal.ofReal (∫ ω, ‖X i ω‖ ^ 2 ∂P)) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    congr
    simpa using (ofReal_integral_norm_eq_lintegral_enorm (hX.integrable_sq i)).symm
  _ ≤ (ENNReal.ofReal (∫ ω, ‖X j ω‖ ^ 2 ∂P)) ^ (1 / (2 : ℝ≥0∞).toReal) := by gcongr
  _ = (∫⁻ ω, ‖X j ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂P) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    congr
    simpa using (ofReal_integral_norm_eq_lintegral_enorm (hX.integrable_sq j))
  _ = eLpNorm (X j) 2 P := by
    simp [eLpNorm_eq_lintegral_rpow_enorm_toReal]

lemma IsSquareIntegrable.ae_tendsto_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
  sorry

lemma IsSquareIntegrable.tendsto_eLpNorm_two_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    Tendsto (fun i ↦ eLpNorm (X i - 𝓕.limitProcess X P) 2 P) atTop (𝓝 0) := by
  sorry

open scoped Function

noncomputable
def stoppedAtNorm {ι : Type*} [ConditionallyCompleteLinearOrderBot ι] (X : ι → Ω → E) (r : ℝ) :
    ι → Ω → E :=
  (stoppedProcess (fun i ↦ {ω | ⊥ < leastGE (fun i ω ↦ ‖X i ω‖) r ω}.indicator (X i))
    (leastGE (fun i ω ↦ ‖X i ω‖) r))

omit [NormedSpace ℝ E] in
@[simp]
lemma stoppedAtNorm_of_nonpos {ι : Type*} [ConditionallyCompleteLinearOrderBot ι]
    (X : ι → Ω → E) {r : ℝ} (hr : r ≤ 0) :
    stoppedAtNorm X r = fun _ _ ↦ 0 := by
  unfold stoppedAtNorm
  ext t ω
  suffices leastGE (fun i ω ↦ ‖X i ω‖) r ω = ⊥ by simp [stoppedProcess, this]
  unfold leastGE hittingAfter
  simp only [bot_le, Set.mem_Ici, true_and]
  have h_le : r ≤ ‖X ⊥ ω‖ := by grw [hr]; positivity
  rw [if_pos ⟨⊥, le_rfl, by simpa⟩]
  simp only [WithTop.coe_eq_bot]
  refine le_antisymm ?_ bot_le
  rw [csInf_le_iff (by simp) ⟨⊥, by simpa⟩]
  refine fun i hi ↦ ?_
  simp only [mem_lowerBounds, Set.mem_setOf_eq] at hi
  exact hi ⊥ h_le

omit [NormedSpace ℝ E] in
lemma stoppedAtNorm_le_add_jump
    {ι : Type*} [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    {X : ι → Ω → E} (h_cadlag : ∀ ω, IsCadlag (X · ω)) (t : ι) (ω : Ω) {n : ℝ} (hn : 0 ≤ n) :
    ‖stoppedAtNorm X n t ω‖ ≤ n + ‖Δ (X · ω) (leastGE (fun i ω ↦ ‖X i ω‖) n ω).untopA‖ := by
  let τ : ℝ → Ω → WithTop ι := fun n ↦ leastGE (fun i ω ↦ ‖X i ω‖) n
  change ‖stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n) t ω‖ ≤
    n + ‖Δ (X · ω) (τ n ω).untopA‖
  have hX_lt {t : ι} {ω : Ω} (ht : t < τ n ω) : ‖X t ω‖ < n := by
    unfold τ leastGE at ht -- todo: missing lemma about lt_leastGE?
    have := notMem_of_lt_hittingAfter ht (by simp)
    grind
  by_cases hτ_bot : τ n ω = ⊥
  · have : (⊥ : WithTop ι).untopA = ⊥ := rfl -- should be simp
    simp [hτ_bot, this, stoppedProcess, hn]
  by_cases hτ_top : τ n ω = ⊤
  · rw [stoppedProcess_eq_of_le (by simp [hτ_top])]
    simp only [Set.mem_setOf_eq, Ne.bot_lt hτ_bot, Set.indicator_of_mem]
    grw [hX_lt (by simp [hτ_top])]
    simp
  rcases lt_or_ge t (τ n ω).untopA with hlt | hge
  · have h_le_n : ‖stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n) t ω‖ ≤ n := by
      have h_lt' : t < τ n ω := by rwa [WithTop.lt_untopA_iff hτ_top] at hlt
      simp [stoppedProcess_eq_of_le h_lt'.le, Ne.bot_lt hτ_bot, (hX_lt h_lt').le]
    grw [h_le_n]
    simp
  · have hge' : τ n ω ≤ t := by rwa [WithTop.untopA_le_iff hτ_top] at hge
    rw [stoppedProcess_eq_of_ge hge']
    simp only [Set.mem_setOf_eq, Ne.bot_lt hτ_bot, Set.indicator_of_mem, ge_iff_le]
    calc ‖X (τ n ω).untopA ω‖
    _ ≤ ‖leftLim (X · ω) (sSup (Set.Iio (τ n ω).untopA))‖ + ‖Δ (X · ω) (τ n ω).untopA‖ := by
      rw [← leftLim_add_jump (f := (X · ω))]
      exact norm_add_le _ _
    _ ≤ n + ‖Δ (fun x ↦ X x ω) (τ n ω).untopA‖ := by
      gcongr
      by_cases h_bot : 𝓝[<] (τ n ω).untopA = ⊥
      · have : sSup (Set.Iio (τ n ω).untopA) < (τ n ω).untopA := by
          have h_nonempty : (Set.Iio (τ n ω).untopA).Nonempty := by
            refine ⟨⊥, ?_⟩
            simp only [Set.mem_Iio]
            rw [WithTop.lt_untopA_iff hτ_top]
            simp [Ne.bot_lt hτ_bot]
          refine lt_of_le_of_ne (sSup_Iio_le_self h_nonempty) ?_
          rw [ne_eq, sSup_Iio_eq_self_iff_nhdsWithin_neBot h_nonempty]
          simpa
        by_cases h_bot' : 𝓝[<] (sSup (Set.Iio (τ n ω).untopA)) = ⊥
        · rw [leftLim_eq_of_eq_bot _ h_bot']
          rw [WithTop.lt_untopA_iff hτ_top] at this
          exact (hX_lt this).le
        have h_NeBot : (𝓝[<] (sSup (Set.Iio (τ n ω).untopA))).NeBot := ⟨h_bot'⟩
        refine le_of_tendsto (f := fun t ↦ ‖X t ω‖) (x := 𝓝[<] (sSup (Set.Iio (τ n ω).untopA)))
          ?_ ?_
        · exact (tendsto_leftLim_of_tendsto ((h_cadlag ω).left_limit _)).norm
        · refine eventually_nhdsWithin_of_forall fun t ht ↦ ?_
          refine (hX_lt ?_).le
          simp only [Set.mem_Iio] at ht
          have ht' := ht.trans this
          rwa [WithTop.lt_untopA_iff hτ_top] at ht'
      rw [sSup_Iio_eq_self_of_nhdsWithin_neBot h_bot]
      have : (𝓝[<] (τ n ω).untopA).NeBot := ⟨h_bot⟩
      refine le_of_tendsto (f := fun t ↦ ‖X t ω‖) (x := 𝓝[<] ((τ n ω).untopA)) ?_ ?_
      · exact (tendsto_leftLim_of_tendsto ((h_cadlag ω).left_limit _)).norm
      · refine eventually_nhdsWithin_of_forall fun t ht ↦ ?_
        refine (hX_lt ?_).le
        simp only [Set.mem_Iio] at ht
        rwa [WithTop.lt_untopA_iff hτ_top] at ht

lemma _root_.MeasureTheory.Martingale.isLocallySquareIntegrable_of_jump_le
    {ι : Type*} [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [PolishSpace ι] [CompleteSpace E] [SecondCountableTopology E]
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [𝓕.IsComplete P] [𝓕.IsRightContinuous] [IsFiniteMeasure P]
    [Approximable 𝓕 P]
    (hX : Martingale X 𝓕 P) (h_cadlag : ∀ ω, IsCadlag (X · ω))
    {C : ℝ} (h_jump : ∀ t ω, ‖Δ (X · ω) t‖ ≤ C) :
    IsLocallySquareIntegrable X 𝓕 P := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact isLocallySquareIntegrable_of_isEmpty _ _ _
  let τ : ℕ → Ω → WithTop ι := fun n ↦ leastGE (fun i ω ↦ ‖X i ω‖) n
  refine ⟨τ, isLocalizingSequence_leastGE 𝓕 hX.stronglyAdapted.norm (fun ω ↦ (h_cadlag ω).norm),
    fun n ↦ ?_⟩
  let Y := (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))
  have hX_lt {t : ι} {ω : Ω} (ht : t < τ n ω) : ‖X t ω‖ < n := by
    unfold τ leastGE at ht -- todo: missing lemma about lt_leastGE?
    have := notMem_of_lt_hittingAfter ht (by simp)
    grind
  have hY_le t ω : ‖Y t ω‖ ≤ (n : ℝ) + ‖Δ (X · ω) (τ n ω).untopA‖ :=
    stoppedAtNorm_le_add_jump h_cadlag t ω (by simp)
  borelize ι
  borelize E
  have h_stop : IsStoppingTime 𝓕 (τ n) := by
    refine isStoppingTime_leastGE P (IsStronglyProgressive.norm ?_) (n : ℝ) (𝓕 := 𝓕)
    exact StronglyAdapted.isStronglyProgressive_of_rightContinuous hX.stronglyAdapted
      fun ω ↦ (h_cadlag ω).right_continuous
  refine isSquareIntegrable_of_le_const (C := NNReal.mk (P.real .univ ^ (2 : ℝ)⁻¹ * (n +  C)) ?_)
    ?_ ?_ fun i ↦ ?_
  · exact hX.stoppedProcess_indicator (fun ω ↦ (h_cadlag ω).right_continuous) h_stop
  · exact isStable_isCadlag (𝓕 := 𝓕) X h_cadlag (τ n) h_stop
  · suffices 0 ≤ C by positivity
    let ω₀ := hΩ.some
    specialize h_jump ⊥ ω₀
    exact (norm_nonneg _).trans h_jump
  · rw [ENNReal.coe_nnreal_eq, NNReal.coe_mk, ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      Measure.real_def, ENNReal.ofReal_toReal (by simp)]
    refine eLpNorm_le_of_ae_bound (ae_of_all _ fun ω ↦ ?_)
    grw [hY_le _ ω]
    gcongr
    exact h_jump _ _

lemma Martingale.isLocallySquareIntegrable_of_continuous
    {ι : Type*} [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [PolishSpace ι] [DenselyOrdered ι] [CompleteSpace E] [SecondCountableTopology E]
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [𝓕.IsComplete P] [𝓕.IsRightContinuous] [IsFiniteMeasure P]
    [Approximable 𝓕 P]
    (hX : Martingale X 𝓕 P) (h_cont : ∀ ω, Continuous (X · ω)) :
    IsLocallySquareIntegrable X 𝓕 P := by
  refine hX.isLocallySquareIntegrable_of_jump_le (fun ω ↦ (h_cont ω).isCadlag) (fun t ω ↦ ?_)
    (C := 0)
  by_cases hτ_bot : t = ⊥
  · simp [hτ_bot]
  rw [(h_cont ω).continuousAt.jump_eq_zero]
  · simp
  · suffices (𝓝[<] t).NeBot from this.ne
    refine nhdsLT_neBot_of_exists_lt ?_
    exact ⟨⊥, by grind⟩

end ProbabilityTheory
