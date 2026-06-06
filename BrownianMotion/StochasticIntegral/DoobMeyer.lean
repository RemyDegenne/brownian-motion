/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.ClassD

/-! # Doob-Meyer decomposition theorem

-/

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
  [MeasurableSpace ι]

omit [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] in
/-- Adding an integrable `𝓕_⊥`-measurable random variable as a time-constant process preserves
the martingale property.  This is the non-local closure fact needed after localization in the
normalized Doob-Meyer proof. -/
lemma _root_.MeasureTheory.Martingale.add_const_fun [SigmaFiniteFiltration P 𝓕]
    {M : ι → Ω → ℝ} {Z : Ω → ℝ} (hM : Martingale M 𝓕 P)
    (hZ_meas : StronglyMeasurable[𝓕 ⊥] Z) (hZ_int : Integrable Z P) :
    Martingale (M + fun _ ↦ Z) 𝓕 P := by
  exact hM.add (martingale_const_fun 𝓕 P hZ_meas hZ_int)

omit [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι] in
/-- Pathwise running-sup estimate for subtracting a time-constant random variable. -/
lemma runningSup_norm_sub_const_le (A : ι → Ω → ℝ) (Z : Ω → ℝ) (t : ι) (ω : Ω) :
    (⨆ s ≤ t, ‖A s ω - Z ω‖ₑ) ≤ (⨆ s ≤ t, ‖A s ω‖ₑ) + ‖Z ω‖ₑ := by
  refine iSup₂_le fun s hs ↦ ?_
  calc
    ‖A s ω - Z ω‖ₑ ≤ ‖A s ω‖ₑ + ‖Z ω‖ₑ := by
      simpa [sub_eq_add_neg] using enorm_add_le (A s ω) (-Z ω)
    _ ≤ (⨆ u ≤ t, ‖A u ω‖ₑ) + ‖Z ω‖ₑ :=
      add_le_add (le_iSup₂_of_le s hs le_rfl) le_rfl

/-- Subtracting an integrable `𝓕_⊥`-measurable time-constant random variable preserves
integrable running sup, under the usual hypotheses that turn strong progressivity into a
strongly measurable running-sup process. -/
lemma HasIntegrableSup.sub_const_fun
    {κ Ω' : Type*} [ConditionallyCompleteLinearOrderBot κ] [TopologicalSpace κ]
    [OrderTopology κ] [MeasurableSpace κ] [BorelSpace κ] [PolishSpace κ]
    [mΩ' : MeasurableSpace Ω'] {P' : Measure Ω'} {𝓕' : Filtration κ mΩ'}
    [IsFiniteMeasure P'] [𝓕'.IsComplete P'] [𝓕'.IsRightContinuous]
    {A : κ → Ω' → ℝ} {Z : Ω' → ℝ}
    (hA_int : HasIntegrableSup (mΩ := mΩ') A P')
    (hA_prog : IsStronglyProgressive 𝓕' A)
    (hZ_meas : StronglyMeasurable[𝓕' ⊥] Z)
    (hZ_int : Integrable (fun ω ↦ ‖Z ω‖ₑ) P') :
    HasIntegrableSup (mΩ := mΩ') (A - fun _ ↦ Z) P' := by
  have hZ_prog : IsStronglyProgressive 𝓕' (fun _ : κ ↦ Z) := by
    intro i
    exact ((hZ_meas.mono (𝓕'.mono bot_le)).comp_measurable measurable_snd)
  have hsup_shift : HasStronglyMeasurableSupProcess (mΩ := mΩ') (A - fun _ : κ ↦ Z) := by
    simpa [Pi.sub_apply] using
      (MeasureTheory.IsStronglyProgressive.hasStronglyMeasurableSupProcess (𝓕 := 𝓕') P'
        (hA_prog.sub hZ_prog))
  refine ⟨hsup_shift, fun t ↦ ?_⟩
  have hdom : Integrable (fun ω ↦ (⨆ s ≤ t, ‖A s ω‖ₑ) + ‖Z ω‖ₑ) P' :=
    (hA_int.2 t).add hZ_int
  refine Integrable.mono_enorm hdom
    (hsup_shift.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    ?_
  filter_upwards with ω
  have hle := runningSup_norm_sub_const_le A Z t ω
  simpa [Pi.sub_apply, enorm_eq_self] using hle

/-- Local version of `HasIntegrableSup.sub_const_fun` for the normalization shift
`A_t - A_⊥`.  The stopped initial value is integrable because it is the running supremum of the
stopped process at `⊥`. -/
lemma HasLocallyIntegrableSup.sub_initial
    {κ Ω' : Type*} [ConditionallyCompleteLinearOrderBot κ] [TopologicalSpace κ]
    [OrderTopology κ] [MeasurableSpace κ] [BorelSpace κ] [PolishSpace κ]
    [mΩ' : MeasurableSpace Ω'] {P' : Measure Ω'} {𝓕' : Filtration κ mΩ'}
    [IsFiniteMeasure P'] [𝓕'.IsComplete P'] [𝓕'.IsRightContinuous]
    {A : κ → Ω' → ℝ}
    (hA_int : HasLocallyIntegrableSup (mΩ := mΩ') A 𝓕' P')
    (hA_prog : IsStronglyProgressive 𝓕' A) :
    HasLocallyIntegrableSup (mΩ := mΩ') (A - fun _ ω ↦ A ⊥ ω) 𝓕' P' := by
  rcases hA_int with ⟨τ, hτ, hτA⟩
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  let Xn : κ → Ω' → ℝ :=
    stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (A i)) (τ n)
  let Zn : Ω' → ℝ := {ω | ⊥ < τ n ω}.indicator (fun ω ↦ A ⊥ ω)
  have hXn_prog : IsStronglyProgressive 𝓕' Xn := by
    exact isStable_isStronglyProgressive A hA_prog (τ n) (hτ.isStoppingTime n)
  have hZn_meas : StronglyMeasurable[𝓕' ⊥] Zn := by
    exact (hA_prog.stronglyAdapted ⊥).indicator
      ((hτ.isStoppingTime n).measurableSet_gt ⊥)
  have hZn_int : Integrable (fun ω ↦ ‖Zn ω‖ₑ) P' := by
    have hbot := (hτA n).2 (⊥ : κ)
    simpa [Xn, Zn, stoppedProcess] using hbot
  have hshift := (hτA n).sub_const_fun hXn_prog hZn_meas hZn_int
  convert hshift using 1
  ext t ω
  by_cases hω : ⊥ < τ n ω <;>
    simp [Zn, stoppedProcess, Pi.sub_apply, hω]

/-- Adding the initial value of a strongly progressive process with locally integrable running
supremum to a local martingale preserves the local martingale property under the usual hypotheses
needed for stopped-martingale stability. -/
lemma IsLocalMartingale.add_initial_of_hasLocallyIntegrableSup
    [SecondCountableTopology ι] [BorelSpace ι] [PseudoMetrizableSpace ι]
    [IsFiniteMeasure P] [Approximable 𝓕 P]
    {M A : ι → Ω → ℝ} (hM : IsLocalMartingale M 𝓕 P)
    (hA_prog : IsStronglyProgressive 𝓕 A)
    (hA_int : HasLocallyIntegrableSup A 𝓕 P) :
    IsLocalMartingale (M + fun _ ω => A ⊥ ω) 𝓕 P := by
  let τ : ℕ → Ω → WithTop ι := hM.localSeq ⊓ hA_int.localSeq
  refine ⟨τ, hM.isLocalizingSequence_localSeq.min hA_int.isLocalizingSequence_localSeq,
    fun n => ?_⟩
  let S : Set Ω := {ω | ⊥ < τ n ω}
  let Z : Ω → ℝ := S.indicator (fun ω => A ⊥ ω)
  have hMτ_mart : Martingale (stoppedProcess (fun i => S.indicator (M i)) (τ n)) 𝓕 P := by
    have hm := (isStable_martingale
      (stoppedProcess (fun i => {ω | ⊥ < hM.localSeq n ω}.indicator (M i))
        (hM.localSeq n))
      (hM.stoppedProcess_localSeq n) (hA_int.localSeq n)
      (hA_int.isLocalizingSequence_localSeq.isStoppingTime n)).1
    convert hm using 1
    ext i ω
    simp_rw [S, τ, stoppedProcess_indicator_comm, Pi.inf_apply, lt_inf_iff,
      inf_comm (hM.localSeq n)]
    rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_comm, Set.setOf_and,
      Set.inter_comm]
    simp_rw [← Set.indicator_indicator]
    rfl
  have hMτ_cad :
      ∀ ω, IsCadlag (stoppedProcess (fun i => S.indicator (M i)) (τ n) · ω) := by
    have hc := (isStable_martingale
      (stoppedProcess (fun i => {ω | ⊥ < hM.localSeq n ω}.indicator (M i))
        (hM.localSeq n))
      (hM.stoppedProcess_localSeq n) (hA_int.localSeq n)
      (hA_int.isLocalizingSequence_localSeq.isStoppingTime n)).2
    intro ω
    convert hc ω using 1
    ext i
    simp_rw [S, τ, stoppedProcess_indicator_comm, Pi.inf_apply, lt_inf_iff,
      inf_comm (hM.localSeq n)]
    rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_comm, Set.setOf_and,
      Set.inter_comm]
    simp_rw [← Set.indicator_indicator]
    rfl
  have hAτ : HasIntegrableSup (stoppedProcess (fun i => S.indicator (A i)) (τ n)) P := by
    have h := isStable_hasIntegrableSup
      (stoppedProcess (fun i => {ω | ⊥ < hA_int.localSeq n ω}.indicator (A i))
        (hA_int.localSeq n))
      (hA_int.stoppedProcess_localSeq n) (hM.localSeq n)
      (hM.isLocalizingSequence_localSeq.isStoppingTime n)
    convert h using 1
    ext i ω
    simp_rw [S, τ, stoppedProcess_indicator_comm, Pi.inf_apply, lt_inf_iff]
    rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_comm, Set.setOf_and]
    simp_rw [← Set.indicator_indicator]
    rfl
  have hZ_meas : StronglyMeasurable[𝓕 ⊥] Z := by
    have hτ_stop := (hM.isLocalizingSequence_localSeq.min
      hA_int.isLocalizingSequence_localSeq).isStoppingTime n
    exact (hA_prog.stronglyAdapted ⊥).indicator (hτ_stop.measurableSet_gt ⊥)
  have hZ_int : Integrable Z P := by
    have hZ_strong : StronglyMeasurable Z := hZ_meas.mono (𝓕.le ⊥)
    have hZ_ae : AEStronglyMeasurable Z P := hZ_strong.aestronglyMeasurable
    rw [← integrable_enorm_iff hZ_ae]
    have hbot := hAτ.2 (⊥ : ι)
    convert hbot using 1
    ext ω
    by_cases hω : ω ∈ S
    · simp only [le_bot_iff, iSup_iSup_eq_left]
      change ‖S.indicator (fun ω => A ⊥ ω) ω‖ₑ =
        ‖S.indicator (fun ω =>
          A (min (((⊥ : ι) : WithTop ι)) (τ n ω)).untopA ω) ω‖ₑ
      rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      rw [show (min (((⊥ : ι) : WithTop ι)) (τ n ω)).untopA = (⊥ : ι) by
        rw [WithTop.coe_bot]
        rw [min_eq_left (bot_le : (⊥ : WithTop ι) ≤ τ n ω)]
        rfl]
    · have hω' : ¬ ⊥ < τ n ω := by simpa [S] using hω
      simp [Z, S, stoppedProcess, hω']
  refine ⟨?_, ?_⟩
  · convert hMτ_mart.add_const_fun hZ_meas hZ_int using 1
    ext i ω
    by_cases hω : ω ∈ S
    · have hω' : ⊥ < τ n ω := by simpa [S] using hω
      simp [Z, S, stoppedProcess, hω']
    · have hω' : ¬ ⊥ < τ n ω := by simpa [S] using hω
      simp [Z, S, stoppedProcess, hω']
  · intro ω
    have hZ_cadlag : IsCadlag (fun _ : ι => Z ω) :=
      (continuous_const : Continuous fun _ : ι => Z ω).isCadlag
    have hsum := (hMτ_cad ω).add hZ_cadlag
    convert hsum using 1
    ext i
    by_cases hω : ω ∈ S
    · have hω' : ⊥ < τ n ω := by simpa [S] using hω
      simp [Z, S, stoppedProcess, hω']
    · have hω' : ¬ ⊥ < τ n ω := by simpa [S] using hω
      simp [Z, S, stoppedProcess, hω']

namespace IsLocalSubmartingale

theorem doob_meyer (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∃ (M A : ι → Ω → ℝ), X = M + A ∧ IsLocalMartingale M 𝓕 P ∧ (∀ ω, IsCadlag (M · ω)) ∧
      IsStronglyProgressive 𝓕 A ∧ (∀ ω, IsCadlag (A · ω)) ∧ (HasLocallyIntegrableSup A 𝓕 P)
      ∧ (∀ ω, Monotone (A · ω)) := by
  sorry

section Normalized

variable {κ Ω' : Type*} [ConditionallyCompleteLinearOrderBot κ] [TopologicalSpace κ]
  [OrderTopology κ] [MeasurableSpace κ] [BorelSpace κ] [PolishSpace κ]
  {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} {X' : κ → Ω' → ℝ}
  {𝓕' : Filtration κ mΩ'} [IsFiniteMeasure P'] [Approximable 𝓕' P']
  [𝓕'.IsComplete P'] [𝓕'.IsRightContinuous]

/-- A normalized local Doob-Meyer decomposition whose predictable part starts from zero. -/
theorem doob_meyer_normalized (hX : IsLocalSubmartingale X' 𝓕' P')
    (hX_cadlag : ∀ ω, IsCadlag (X' · ω)) :
    ∃ (M A : κ → Ω' → ℝ), X' = M + A ∧ IsLocalMartingale M 𝓕' P' ∧
      (∀ ω, IsCadlag (M · ω)) ∧ IsStronglyProgressive 𝓕' A ∧
      (∀ ω, IsCadlag (A · ω)) ∧ HasLocallyIntegrableSup A 𝓕' P' ∧
      (∀ ω, Monotone (A · ω)) ∧ (∀ ω, A ⊥ ω = 0) := by
  classical
  rcases hX.doob_meyer hX_cadlag with
    ⟨M, A, hXA, hM, hM_cadlag, hA_prog, hA_cadlag, hA_int, hA_mono⟩
  let C : κ → Ω' → ℝ := fun _ ω => A ⊥ ω
  have hC_prog : IsStronglyProgressive 𝓕' C := by
    intro i
    exact ((hA_prog.stronglyAdapted ⊥).mono (𝓕'.mono bot_le)).comp_measurable measurable_snd
  have hC_cadlag : ∀ ω, IsCadlag (C · ω) := by
    intro ω
    exact (continuous_const : Continuous fun _ : κ => A ⊥ ω).isCadlag
  refine ⟨M + C, A - C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext t ω
    rw [hXA]
    simp only [Pi.add_apply, Pi.sub_apply, C]
    ring
  · -- Simultaneous localization makes the initial-value shift a local martingale.
    exact hM.add_initial_of_hasLocallyIntegrableSup hA_prog hA_int
  · intro ω
    exact (hM_cadlag ω).add (hC_cadlag ω)
  · simpa only [Pi.sub_apply] using hA_prog.sub hC_prog
  · intro ω
    have hnegC : IsCadlag fun t : κ => (-1 : ℝ) • C t ω := (hC_cadlag ω).const_smul (-1)
    have hadd : IsCadlag ((fun t : κ => A t ω) + fun t => (-1 : ℝ) • C t ω) :=
      (hA_cadlag ω).add hnegC
    simpa [sub_eq_add_neg, C] using hadd
  · -- The locally integrable running supremum is stable under the normalization shift.
    exact hA_int.sub_initial hA_prog
  · intro ω i j hij
    exact sub_le_sub_right (hA_mono ω hij) (A ⊥ ω)
  · intro ω
    simp [C]

/-- The local martingale part of the Doob-Meyer decomposition of the local submartingale. -/
noncomputable
def martingalePart (X : κ → Ω' → ℝ)
    (hX : IsLocalSubmartingale X 𝓕' P') (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    κ → Ω' → ℝ :=
  (hX.doob_meyer_normalized hX_cadlag).choose

/-- The predictable part of the Doob-Meyer decomposition of the local submartingale. -/
noncomputable
def predictablePart (X : κ → Ω' → ℝ)
    (hX : IsLocalSubmartingale X 𝓕' P') (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    κ → Ω' → ℝ :=
  (hX.doob_meyer_normalized hX_cadlag).choose_spec.choose

lemma martingalePart_add_predictablePart
    (hX : IsLocalSubmartingale X' 𝓕' P') (hX_cadlag : ∀ ω, IsCadlag (X' · ω)) :
    X' = hX.martingalePart X' hX_cadlag + hX.predictablePart X' hX_cadlag :=
  (hX.doob_meyer_normalized hX_cadlag).choose_spec.choose_spec.1

lemma isLocalMartingale_martingalePart
    (hX : IsLocalSubmartingale X' 𝓕' P') (hX_cadlag : ∀ ω, IsCadlag (X' · ω)) :
    IsLocalMartingale (hX.martingalePart X' hX_cadlag) 𝓕' P' :=
  (hX.doob_meyer_normalized hX_cadlag).choose_spec.choose_spec.2.1

lemma cadlag_martingalePart
    (hX : IsLocalSubmartingale X' 𝓕' P') (hX_cadlag : ∀ ω, IsCadlag (X' · ω)) :
    ∀ ω, IsCadlag (hX.martingalePart X' hX_cadlag · ω) :=
  (hX.doob_meyer_normalized hX_cadlag).choose_spec.choose_spec.2.2.1

lemma isStronglyProgressive_predictablePart
    (hX : IsLocalSubmartingale X' 𝓕' P') (hX_cadlag : ∀ ω, IsCadlag (X' · ω)) :
    IsStronglyProgressive 𝓕' (hX.predictablePart X' hX_cadlag) :=
  (hX.doob_meyer_normalized hX_cadlag).choose_spec.choose_spec.2.2.2.1

lemma cadlag_predictablePart
    (hX : IsLocalSubmartingale X' 𝓕' P') (hX_cadlag : ∀ ω, IsCadlag (X' · ω)) :
    ∀ ω, IsCadlag (hX.predictablePart X' hX_cadlag · ω) :=
  (hX.doob_meyer_normalized hX_cadlag).choose_spec.choose_spec.2.2.2.2.1

lemma hasLocallyIntegrableSup_predictablePart
    (hX : IsLocalSubmartingale X' 𝓕' P') (hX_cadlag : ∀ ω, IsCadlag (X' · ω)) :
    HasLocallyIntegrableSup (hX.predictablePart X' hX_cadlag) 𝓕' P' :=
  (hX.doob_meyer_normalized hX_cadlag).choose_spec.choose_spec.2.2.2.2.2.1

lemma monotone_predictablePart (hX : IsLocalSubmartingale X' 𝓕' P')
    (hX_cadlag : ∀ ω, IsCadlag (X' · ω)) :
    ∀ ω, Monotone (hX.predictablePart X' hX_cadlag · ω) :=
  (hX.doob_meyer_normalized hX_cadlag).choose_spec.choose_spec.2.2.2.2.2.2.1

lemma predictablePart_bot_eq_zero (hX : IsLocalSubmartingale X' 𝓕' P')
    (hX_cadlag : ∀ ω, IsCadlag (X' · ω)) :
    ∀ ω, hX.predictablePart X' hX_cadlag ⊥ ω = 0 :=
  (hX.doob_meyer_normalized hX_cadlag).choose_spec.choose_spec.2.2.2.2.2.2.2

end Normalized

end IsLocalSubmartingale

end ProbabilityTheory
