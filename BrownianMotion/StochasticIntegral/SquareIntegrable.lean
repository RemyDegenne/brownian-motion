/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.Indistinguishable
public import BrownianMotion.Auxiliary.Martingale
public import BrownianMotion.StochasticIntegral.LocalizingLeastGE
public import BrownianMotion.StochasticIntegral.LocalMartingale
public import Mathlib.Probability.Notation

import BrownianMotion.Auxiliary.Analysis
import BrownianMotion.Auxiliary.LimitProcess
import BrownianMotion.Gaussian.StochasticProcesses

/-! # Square integrable martingales

-/

@[expose] public section

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal Topology NNReal RealInnerProductSpace

namespace ProbabilityTheory

variable {ι Ω E : Type*} [NormedAddCommGroup E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section LinearOrder

variable [LinearOrder ι] [TopologicalSpace ι]
  {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

section NormedSpace

variable [NormedSpace ℝ E]

/-- A square integrable martingale is a martingale with cadlag paths and uniformly bounded
second moments. -/
structure IsSquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop where
  martingale : Martingale X 𝓕 P
  cadlag : ∀ ω, IsCadlag (X · ω)
  bounded : ⨆ i, eLpNorm (X i) 2 P < ∞

lemma IsSquareIntegrable.const [IsFiniteMeasure P] {c : E} :
    IsSquareIntegrable (fun _ _ ↦ c) 𝓕 P where
  martingale := martingale_const 𝓕 P c
  cadlag ω := isCadlag_const c
  bounded := by
    obtain _ | _ := isEmpty_or_nonempty ι
    · simp
    obtain rfl | hP := eq_or_ne P 0
    · simp
    rw [iSup_const, eLpNorm_const c (by simp) hP]
    finiteness

/-- An a.e.-square integrable martingale is a process that is indistinguishable from a
square integrable martingale, see `IsSquareIntegrable`. -/
def IsAESquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop :=
  ∃ Y : ι → Ω → E, IsSquareIntegrable Y 𝓕 P ∧ X ≡ᵐ[P] Y

lemma IsSquareIntegrable.isAESquareIntegrable (hX : IsSquareIntegrable X 𝓕 P) :
    IsAESquareIntegrable X 𝓕 P := ⟨X, hX, by rfl⟩

lemma IsAESquareIntegrable.const [IsFiniteMeasure P] {c : E} :
    IsAESquareIntegrable (fun _ _ ↦ c) 𝓕 P :=
  IsSquareIntegrable.const.isAESquareIntegrable

lemma IsAESquareIntegrable.congr {X Y : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P)
    (hXY : X ≡ᵐ[P] Y) : IsAESquareIntegrable Y 𝓕 P := by
  obtain ⟨Z, hZ1, hZ2⟩ := hX
  exact ⟨Z, hZ1, hXY.symm.trans hZ2⟩

lemma isAESquareIntegrable_congr {X Y : ι → Ω → E} (hXY : X ≡ᵐ[P] Y) :
    IsAESquareIntegrable X 𝓕 P ↔ IsAESquareIntegrable Y 𝓕 P where
  mp h := h.congr hXY
  mpr h := h.congr hXY.symm

/-- A stochastic process is locally square-integrable if it satisfies the square-integrable
martingale property locally. -/
def IsLocallySquareIntegrable [OrderBot ι] [OrderTopology ι]
    (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω := by volume_tac) : Prop :=
  Locally (fun Y ↦ IsSquareIntegrable Y 𝓕 P) 𝓕 X P

lemma IsSquareIntegrable.isLocallySquareIntegrable [OrderBot ι] [OrderTopology ι]
    (hX : IsSquareIntegrable X 𝓕 P) :
    IsLocallySquareIntegrable X 𝓕 P :=
  Locally.of_prop hX

lemma IsSquareIntegrable.memLp_two (hX : IsSquareIntegrable X 𝓕 P) (i : ι) :
    MemLp (X i) 2 P := by
  refine ⟨(hX.martingale.stronglyMeasurable i).aestronglyMeasurable.mono (𝓕.le i), ?_⟩
  grw [le_iSup (fun t ↦ eLpNorm (X t) 2 P)]
  exact hX.bounded

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

@[to_fun]
lemma IsSquareIntegrable.add [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    (hY : IsSquareIntegrable Y 𝓕 P) :
    IsSquareIntegrable (X + Y) 𝓕 P := by
  refine ⟨hX.martingale.add hY.martingale, fun ω ↦ (hX.cadlag ω).add (hY.cadlag ω), ?_⟩
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

@[to_fun]
lemma IsAESquareIntegrable.add [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P)
    (hY : IsAESquareIntegrable Y 𝓕 P) :
    IsAESquareIntegrable (X + Y) 𝓕 P := by
  obtain ⟨Z, hZ1, hZ2⟩ := hX
  obtain ⟨T, hT1, hT2⟩ := hY
  exact ⟨Z + T, hZ1.add hT1, hZ2.add hT2⟩

@[to_fun]
lemma IsSquareIntegrable.smul [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) (r : ℝ) :
    IsSquareIntegrable (r • X) 𝓕 P where
  martingale := hX.martingale.smul r
  cadlag ω := hX.cadlag ω |>.const_smul r
  bounded := by
    change (⨆ i, eLpNorm (r • X i) 2 P) < ∞
    simp only [eLpNorm_const_smul, ← ENNReal.mul_iSup]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hX.bounded

@[to_fun]
lemma IsAESquareIntegrable.smul [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P) (r : ℝ) :
    IsAESquareIntegrable (r • X) 𝓕 P := by
  obtain ⟨Y, hY1, hY2⟩ := hX
  exact ⟨r • Y, hY1.smul r, hY2.const_smul⟩

@[to_fun]
lemma IsSquareIntegrable.neg [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) :
    IsSquareIntegrable (-X) 𝓕 P := by
  simpa using hX.smul (-1)

@[to_fun]
lemma IsAESquareIntegrable.neg [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P) :
    IsAESquareIntegrable (-X) 𝓕 P := by
  simpa using hX.smul (-1)

@[to_fun]
lemma IsSquareIntegrable.sub [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    (hY : IsSquareIntegrable Y 𝓕 P) :
    IsSquareIntegrable (X - Y) 𝓕 P := by
  simpa [sub_eq_add_neg] using (hX.add hY.neg)

@[to_fun]
lemma IsAESquareIntegrable.sub [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P)
    (hY : IsAESquareIntegrable Y 𝓕 P) :
    IsAESquareIntegrable (X - Y) 𝓕 P := by
  simpa [sub_eq_add_neg] using (hX.add hY.neg)

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

variable (𝓕) in
lemma tendsto_ae_condExp' (X : Ω → E) :
    ∀ᵐ ω ∂P, Tendsto (P[X | 𝓕 ·] ω) atTop (𝓝 (P[X | ⨆ t, 𝓕 t] ω)) := by
  sorry

lemma IsSquareIntegrable.condExp_limitProcess_ae_eq (hX : IsSquareIntegrable X 𝓕 P) (t : ι) :
    P[𝓕.limitProcess X P | 𝓕 t] =ᵐ[P] X t := by
  sorry

lemma IsSquareIntegrable.tendsto_eLpNorm_two_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    Tendsto (fun i ↦ eLpNorm (X i - 𝓕.limitProcess X P) 2 P) atTop (𝓝 0) := by
  sorry

lemma IsSquareIntegrable.iSup_eLpNorm_eq_eLpNorm_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    ⨆ i, eLpNorm (X i) 2 P = eLpNorm (𝓕.limitProcess X P) 2 P := by
  sorry

lemma IsSquareIntegrable.memLp_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    MemLp (𝓕.limitProcess X P) 2 P := by
  constructor
  · exact Filtration.stronglyMeasurable_limit_process'.aestronglyMeasurable
  rw [← hX.iSup_eLpNorm_eq_eLpNorm_limitProcess]
  exact hX.bounded

end NormedSpace

section Hilbert

variable [CompleteSpace E] [IsFiniteMeasure P]

section NormedSpace

variable [NormedSpace ℝ E]

variable (ι E P 𝓕) in
/-- The type of square integrable martingales.

TODO: we rely on the already existing `AEEqFun` machinery, but this is about equivalence classes
of strongly measurable functions, while here we are interested in indistinguishability only
so measurablility is the way to go. It seems we will need to duplicate `AEEqFun` for the measurable
case. -/
def SquareIntegrable : Submodule ℝ (Ω →ₘ[P] (ι → E)) where
  carrier := {X | ∃ Y : ι → Ω → E, IsSquareIntegrable Y 𝓕 P ∧ (fun ω t ↦ Y t ω) =ᵐ[P] X}
  add_mem' {X Y} hX hY := by
    obtain ⟨Z, hZ1, hZ2⟩ := hX
    obtain ⟨T, hT1, hT2⟩ := hY
    refine ⟨Z + T, hZ1.add hT1, ?_⟩
    filter_upwards [hZ2, hT2, X.coeFn_add Y] with ω h1 h2 h3
    rw [funext_iff] at h1 h2 ⊢
    simp_all
  zero_mem' := ⟨0, .const, AEEqFun.coeFn_zero.symm⟩
  smul_mem' c {X} hX := by
    obtain ⟨Y, hY1, hY2⟩ := hX
    refine ⟨c • Y, hY1.smul c, ?_⟩
    filter_upwards [hY2, X.coeFn_smul c] with ω h1 h2
    rw [funext_iff] at h1 ⊢
    simp_all

/- This uses `sorry` because a martingale is not necessarily strongly measurable as a map from
`Ω` to `ι → E`. -/
/-- The equivalence class of a process that is indistinguishable from a square integrable
martingale. -/
noncomputable def SquareIntegrable.mk (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P) :
    SquareIntegrable ι E P 𝓕 :=
  ⟨.mk (fun ω t ↦ X t ω) sorry, ⟨hX.choose, hX.choose_spec.1, by
      grw [AEEqFun.coeFn_mk]
      filter_upwards [hX.choose_spec.2] with ω h1
      simp [h1]⟩⟩

open scoped Classical in
/-- Given an equivalence class of square integrable martingales, this is a version that satisfies
`IsSquareIntegrable`. Don't use this directly, use the coercion system instead. -/
@[coe]
noncomputable def SquareIntegrable.out (X : SquareIntegrable ι E P 𝓕) : ι → Ω → E :=
  if h : ∃ c, X = SquareIntegrable.mk (fun _ _ ↦ c) .const
    then (fun _ _ ↦ h.choose)
    else X.2.choose

noncomputable instance : CoeFun (SquareIntegrable ι E P 𝓕) (fun _ ↦ ι → Ω → E) where
  coe := SquareIntegrable.out

lemma SquareIntegrable.isSquareIntegrable_coe (X : SquareIntegrable ι E P 𝓕) :
    IsSquareIntegrable X 𝓕 P := by
  rw [SquareIntegrable.out]
  split_ifs
  · exact .const
  · exact X.2.choose_spec.1

lemma SquareIntegrable.val_indist_coe (X : SquareIntegrable ι E P 𝓕) :
    (fun t ω ↦ X.1 ω t) ≡ᵐ[P] X := by
  rw [SquareIntegrable.out]
  split_ifs with h
  · have := AEEqFun.ext_iff.1 (Subtype.coe_inj.2 h.choose_spec)
    filter_upwards [this,
      AEEqFun.coeFn_mk (fun _ _ ↦ h.choose) aestronglyMeasurable_const] with ω h1 h2 t
    rw [h1, SquareIntegrable.mk, h2]
  filter_upwards [X.2.choose_spec.2] with ω h t
  rw [funext_iff] at h
  rw [← h]

@[ext]
lemma SquareIntegrable.ext {X Y : SquareIntegrable ι E P 𝓕} (h : ↑X ≡ᵐ[P] ↑Y) :
    X = Y := by
  ext
  filter_upwards [h, val_indist_coe X, val_indist_coe Y] with ω h1 h2 h3
  ext t
  rw [h2, h1, h3]

lemma SquareIntegrable.coe_add (X Y : SquareIntegrable ι E P 𝓕) :
    ↑(X + Y) ≡ᵐ[P] ↑X + ↑Y := by
  filter_upwards [val_indist_coe X, val_indist_coe Y, val_indist_coe (X + Y),
    X.1.coeFn_add Y] with ω h1 h2 h3 h4 t
  rw [← h3, Submodule.coe_add, h4]
  simp_all

lemma SquareIntegrable.coe_smul (X : SquareIntegrable ι E P 𝓕) (c : ℝ) :
    ↑(c • X) ≡ᵐ[P] c • ↑X := by
  filter_upwards [val_indist_coe X, val_indist_coe (c • X), X.1.coeFn_smul c] with ω h1 h2 h3 t
  rw [← h2, Submodule.coe_smul, h3]
  simp [h1 t]

lemma SquareIntegrable.coe_neg (X : SquareIntegrable ι E P 𝓕) :
    ↑(-X) ≡ᵐ[P] -↑X := by
  convert SquareIntegrable.coe_smul X (-1 : ℝ) using 1
  · congr
    exact (neg_one_smul ℝ X).symm
  exact (neg_one_smul ℝ _).symm

lemma SquareIntegrable.val_mk (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P)
    (h : AEStronglyMeasurable (fun ω t ↦ X t ω) P) :
    (mk X hX).1 = .mk (fun ω t ↦ X t ω) h := rfl

/- This uses `sorry` because a martingale is not necessarily strongly measurable as a map from
`Ω` to `ι → E`. -/
lemma SquareIntegrable.mk_ae_eq {X : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P) :
    mk X hX ≡ᵐ[P] X := by
  filter_upwards [SquareIntegrable.val_indist_coe (mk X hX),
    AEEqFun.coeFn_mk (fun ω t ↦ X t ω) sorry] with ω h1 h2 t
  rw [SquareIntegrable.val_mk] at h1
  · rw [funext_iff] at h2
    rw [← h1, h2]
  sorry

lemma SquareIntegrable.mk_eq_mk {X Y : ι → Ω → E} {hX : IsAESquareIntegrable X 𝓕 P}
    {hY : IsAESquareIntegrable Y 𝓕 P} :
    SquareIntegrable.mk X hX = SquareIntegrable.mk Y hY ↔ X ≡ᵐ[P] Y where
  mp h := by
    rw [Subtype.ext_iff] at h
    simp only [mk] at h
    filter_upwards [AEEqFun.mk_eq_mk.1 h] with ω h1
    rwa [← funext_iff]
  mpr h := by
    ext
    filter_upwards [mk_ae_eq hX, h, mk_ae_eq hY] with ω h1 h2 h3 t
    rw [h1, h2, h3]

variable (E P 𝓕) in
lemma SquareIntegrable.coe_const (c : E) :
    (mk (fun _ _ ↦ c) .const : SquareIntegrable ι E P 𝓕) ≡ᵐ[P] (fun _ _ ↦ c) :=
  mk_ae_eq _

variable (E P 𝓕) in
lemma SquareIntegrable.coe_zero :
    (0 : SquareIntegrable ι E P 𝓕) ≡ᵐ[P] 0 := by
  filter_upwards [val_indist_coe (0 : SquareIntegrable ι E P 𝓕),
    AEEqFun.coeFn_zero (β := ι → E)] with ω h1 h2 t
  rw [funext_iff] at h2
  rw [← h1, Submodule.coe_zero, h2]
  simp

variable (E P 𝓕) in
lemma SquareIntegrable.coe_const_eq [NeZero P] (c : E) :
    (mk (fun _ _ ↦ c) .const : SquareIntegrable ι E P 𝓕) = (fun _ _ ↦ c : ι → Ω → E) := by
  obtain h | ⟨⟨t⟩⟩ := isEmpty_or_nonempty ι
  · ext t; exact h.elim t
  rw [out]
  split_ifs with h
  swap; · exact h.elim ⟨c, rfl⟩
  have := h.choose_spec
  set b := h.choose with hb
  simp_rw [mk_eq_mk, Indistinguishable] at this
  have ⟨_, h1⟩ := Eventually.exists this
  rw [h1 t]

@[to_fun limitProcess_fun_add]
lemma IsSquareIntegrable.limitProcess_add {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : ι → Ω → E}
    [LinearOrder ι] [Nonempty ι] {𝓕 : Filtration ι mΩ} [NormedAddCommGroup E] [TopologicalSpace ι]
    [SigmaFiniteFiltration P 𝓕] [NormedSpace ℝ E]
    (hX : IsSquareIntegrable X 𝓕 P) (hY : IsSquareIntegrable Y 𝓕 P) :
    𝓕.limitProcess (X + Y) P =ᵐ[P] 𝓕.limitProcess X P + 𝓕.limitProcess Y P := by
  apply 𝓕.limitProcess_ae_eq
    (𝓕.stronglyMeasurable_limitProcess.add 𝓕.stronglyMeasurable_limitProcess)
  filter_upwards [hX.ae_tendsto_limitProcess, hY.ae_tendsto_limitProcess] with ω h1 h2 using
    h1.add h2

open TopologicalSpace in
/-- Two modifications that are right-continuous are indistinguishable. -/
lemma indistinguishable_of_modification' {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : T → Ω → E} [TopologicalSpace E] [TopologicalSpace T]
    [SeparableSpace T] [T2Space E] [Preorder T]
    (hX : ∀ᵐ ω ∂P, IsRightContinuous (X · ω)) (hY : ∀ᵐ ω ∂P, IsRightContinuous (Y · ω))
    (h : ∀ t, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := sorry

variable [Nonempty ι]

variable (ι E P 𝓕) in
/-- The injection of square integrable martingales into the `L^2` given by `X ↦ X ∞`.
This is a `LinearIsometryEquiv` onto the subspace of functions that are strongly measurable
with respect to `⨆ t, 𝓕 t`, see `SquareIntegrable.toL2Isom`. -/
noncomputable def SquareIntegrable.toL2 : SquareIntegrable ι E P 𝓕 →ₗ[ℝ] Lp E 2 P where
  toFun X := (isSquareIntegrable_coe X).memLp_limitProcess.toLp
  map_add' X Y := by
    rw [MemLp.toLp_congr _ _ (𝓕.limitProcess_congr (coe_add X Y)),
      MemLp.toLp_congr _ _ (IsSquareIntegrable.limitProcess_add _ _), MemLp.toLp_add]
    · exact (isSquareIntegrable_coe X).memLp_limitProcess.add
        (isSquareIntegrable_coe Y).memLp_limitProcess
    · exact isSquareIntegrable_coe X
    · exact isSquareIntegrable_coe Y
    · exact ((isSquareIntegrable_coe X).add (isSquareIntegrable_coe Y)).memLp_limitProcess
  map_smul' c X := by
    rw [MemLp.toLp_congr _ _ (𝓕.limitProcess_congr (coe_smul X c)),
      MemLp.toLp_congr _ _ (𝓕.limitProcess_smul _ _), MemLp.toLp_const_smul]
    · simp
    · exact (isSquareIntegrable_coe X).memLp_limitProcess
    · exact (isSquareIntegrable_coe X).memLp_limitProcess.const_smul c
    · exact ((isSquareIntegrable_coe X).smul c).memLp_limitProcess

lemma SquareIntegrable.toL2_def (X : SquareIntegrable ι E P 𝓕) :
    toL2 ι E P 𝓕 X = (isSquareIntegrable_coe X).memLp_limitProcess.toLp := rfl

lemma SquareIntegrable.toL2_ae_eq (X : SquareIntegrable ι E P 𝓕) :
    toL2 ι E P 𝓕 X =ᵐ[P] 𝓕.limitProcess X P := by
  rw [toL2_def]
  exact MemLp.coeFn_toLp _

variable [SeparableSpace ι]

lemma SquareIntegrable.injective_toL2 : Injective (toL2 ι E P 𝓕) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  rw [toL2_def, ← MemLp.toLp_zero, MemLp.toLp_eq_toLp_iff] at hX
  swap; · simp
  ext
  refine .trans ?_ (coe_zero _ _ _).symm
  refine indistinguishable_of_modification' ?_ ?_ fun t ↦ ?_
  · exact ae_of_all _ fun _ ↦ (isSquareIntegrable_coe _).cadlag _
      |>.right_continuous
  · exact ae_of_all _ fun _ ↦ isRightContinuous_const 0
  grw [show (0 : ι → Ω → E) t = 0 from rfl, ← lpNorm_eq_zero _ two_ne_zero, ← toReal_eLpNorm,
    ENNReal.toReal_eq_zero_iff]
  · left
    suffices eLpNorm (X t) 2 P ≤ 0 by simp_all
    grw [le_iSup fun s ↦ eLpNorm (X s) 2 P,
      (isSquareIntegrable_coe _).iSup_eLpNorm_eq_eLpNorm_limitProcess, nonpos_iff_eq_zero,
      ← ofReal_lpNorm, ENNReal.ofReal_eq_zero, lpNorm_congr hX, lpNorm_zero]
    exact (isSquareIntegrable_coe _).memLp_limitProcess
  · exact ((isSquareIntegrable_coe X).martingale.stronglyMeasurable
      t).aestronglyMeasurable.mono (𝓕.le t)
  · exact (isSquareIntegrable_coe X).memLp_two t

noncomputable instance SquareIntegrable.normedAddCommGroup :
    NormedAddCommGroup (SquareIntegrable ι E P 𝓕) :=
  NormedAddCommGroup.induced _ _ (toL2 ι E P 𝓕) injective_toL2

lemma SquareIntegrable.norm_def {X : SquareIntegrable ι E P 𝓕} :
    ‖X‖ = lpNorm (𝓕.limitProcess X P) 2 P := by
  change ‖toL2 ι E P 𝓕 X‖ = _
  rw [toL2_def, Lp.norm_toLp, lpNorm, if_pos]
  exact 𝓕.stronglyMeasurable_limit_process'.aestronglyMeasurable

end NormedSpace

variable [InnerProductSpace ℝ E] [Nonempty ι] [SeparableSpace ι]

noncomputable instance SquareIntegrable.innerProductSpace :
    InnerProductSpace ℝ (SquareIntegrable ι E P 𝓕) :=
  InnerProductSpace.induced (toL2 ι E P 𝓕)

lemma SquareIntegrable.inner_def {X Y : SquareIntegrable ι E P 𝓕} :
    ⟪X, Y⟫ = P[fun ω ↦ ⟪𝓕.limitProcess X P ω, 𝓕.limitProcess Y P ω⟫] := by
  rw [inner_induced_eq, toL2_def, toL2_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (isSquareIntegrable_coe X).memLp_limitProcess,
    MemLp.coeFn_toLp (isSquareIntegrable_coe Y).memLp_limitProcess] with ω h1 h2
  simp_all

/-- Given a martingale `X`, this is a càdlàg martingale that is a modification of `X`. -/
def _root_.MeasureTheory.modif (X : ι → Ω → E) :
    ι → Ω → E := sorry

lemma _root_.MeasureTheory.isCadlag_modif (X : ι → Ω → E) (ω : Ω) :
    IsCadlag (modif X · ω) := sorry

lemma _root_.MeasureTheory.modification_modif (hX : Martingale X 𝓕 P) (t : ι) :
    modif X t =ᵐ[P] X t := sorry

lemma _root_.MeasureTheory.martingale_modif : Martingale (modif X) 𝓕 P := sorry

variable (𝓕) in
lemma isSquareIntegrable_modif_condExp {X : Ω → E} (hX : MemLp X 2 P) :
    IsSquareIntegrable (modif (fun t ↦ P[X | 𝓕 t])) 𝓕 P where
  martingale := martingale_modif
  cadlag := isCadlag_modif _
  bounded := by
    refine LE.le.trans_lt (iSup_le fun i ↦ ?_) hX.2
    grw [eLpNorm_congr_ae (modification_modif (martingale_condExp X 𝓕 P) i), eLpNorm_condExp_le]

/-- The `LinearIsometryEquiv` between square integrable martingales and
the type of `L^2` random variables that are strongly measurable with respect to `⨆ t, 𝓕 t`,
given by `X ↦ X ∞`. -/
noncomputable def SquareIntegrable.toL2Isom [OrderTopology ι] :
    SquareIntegrable ι E P 𝓕 ≃ₗᵢ[ℝ] lpMeas E ℝ (⨆ t, 𝓕 t) 2 P where
  toFun X := ⟨toL2 ι E P 𝓕 X, by {
    rw [mem_lpMeas_iff_aestronglyMeasurable, aestronglyMeasurable_congr (toL2_ae_eq X)]
    exact 𝓕.stronglyMeasurable_limitProcess.aestronglyMeasurable
  }⟩
  invFun X := mk (modif (fun t ↦ P[X.1 | 𝓕 t]))
    (isSquareIntegrable_modif_condExp 𝓕 (Lp.memLp X.1)).isAESquareIntegrable
  map_add' := by simp
  map_smul' := by simp
  left_inv X := by
    ext
    apply indistinguishable_of_modification'
    · exact ae_of_all _ fun _ ↦ ((isSquareIntegrable_coe _).cadlag _).right_continuous
    · exact ae_of_all _ fun _ ↦ ((isSquareIntegrable_coe _).cadlag _).right_continuous
    intro t
    filter_upwards [mk_ae_eq
        (X := modif (fun t ↦ P[(isSquareIntegrable_coe X).memLp_limitProcess.toLp _ | 𝓕 t]))
        (isSquareIntegrable_modif_condExp 𝓕
          (isSquareIntegrable_coe X).memLp_limitProcess).isAESquareIntegrable,
      modification_modif (martingale_condExp
        ((isSquareIntegrable_coe X).memLp_limitProcess.toLp _) 𝓕 P) t,
      condExp_congr_ae ((isSquareIntegrable_coe X).memLp_limitProcess.coeFn_toLp),
      (isSquareIntegrable_coe X).condExp_limitProcess_ae_eq t] with ω h1 h2 h3 h4
    rw! [toL2_def, h1, h2, h3, h4]
    rfl
  right_inv X := by
    ext
    simp only
    grw [toL2_def, MemLp.coeFn_toLp]
    obtain ⟨u, hu⟩ := (atTop : Filter ι).exists_seq_tendsto
    have h1 : ∀ᵐ ω ∂P, ∀ n, modif (fun t ↦ P[X.1 | 𝓕 t]) (u n) ω = P[X.1 | 𝓕 (u n)] ω := by
      rw [ae_all_iff]
      exact fun _ ↦ modification_modif (martingale_condExp X.1 𝓕 P) _
    grw [𝓕.limitProcess_congr (mk_ae_eq _)]
    filter_upwards [h1,
      (isSquareIntegrable_modif_condExp 𝓕 (Lp.memLp X.1)).ae_tendsto_limitProcess,
      tendsto_ae_condExp' 𝓕 X.1,
      condExp_of_aestronglyMeasurable' (iSup_le 𝓕.le) X.2
        ((Lp.memLp X.1).integrable (by simp))] with ω h1 h2 h3 h4
    rw [← h4]
    apply tendsto_nhds_unique ?_ (h3.comp hu)
    apply Tendsto.congr h1 (h2.comp hu)
  norm_map' X := rfl

instance SquareIntegrable.completeSpace [OrderTopology ι] :
    CompleteSpace (SquareIntegrable ι E P 𝓕) :=
  haveI : Fact (⨆ t, 𝓕 t ≤ mΩ) := ⟨iSup_le 𝓕.le⟩
  toL2Isom.toIsometryEquiv.completeSpace

end Hilbert

end LinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedSpace ℝ E]
  {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [𝓕.IsComplete P] [𝓕.IsRightContinuous] [IsFiniteMeasure P]
  [Approximable 𝓕 P]

lemma _root_.MeasureTheory.Martingale.isLocallySquareIntegrable_of_jump_le
    [PolishSpace ι] [CompleteSpace E] [SecondCountableTopology E]
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
  borelize ι E
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

lemma _root_.MeasureTheory.Martingale.isLocallySquareIntegrable_of_continuous
    [PolishSpace ι] [CompleteSpace E] [SecondCountableTopology E] [DenselyOrdered ι]
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

lemma isStable_isSquareIntegrable
    [PolishSpace ι] [CompleteSpace E] [SecondCountableTopology E] [DenselyOrdered ι] :
    IsStable 𝓕 fun X : ι → Ω → E ↦ IsSquareIntegrable X 𝓕 P := by
  borelize ι E
  have h_iff (X : ι → Ω → E) : IsSquareIntegrable X 𝓕 P ↔
      ((Martingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) ∧ ⨆ i, eLpNorm (X i) 2 P < ∞) :=
    ⟨fun h ↦ ⟨⟨h.martingale, h.cadlag⟩, h.bounded⟩, fun h ↦ ⟨h.1.1, h.1.2, h.2⟩⟩
  simp_rw [h_iff]
  refine IsStable.and isStable_martingale ?_
  intro X hX τ hτ
  -- 6.11.1 in He et al., using 6.8.1
  sorry

omit [NormedSpace ℝ E] [𝓕.IsRightContinuous] in
lemma isStable_jump_le {C : ℝ} (hC : 0 ≤ C) :
    IsStable 𝓕 fun X : ι → Ω → E ↦ ∀ t ω, ‖Δ (X · ω) t‖ ≤ C := by
  suffices IsStable 𝓕 fun X ↦ ∀ ω i, ‖Δ (X · ω) i‖ ≤ C by
    convert this
    exact ⟨fun h i ω ↦ h ω i, fun h ω i ↦ h i ω⟩
  refine isStable_pathwise (fun (X : ι → E) i ↦ ‖Δ X i‖ ≤ C) (𝓕 := 𝓕) (fun i ↦ ?_) ?_ ?_
  · simp [hC]
  · intro X i hX j hij
    cases lt_or_eq_of_le hij with
    | inl hij =>
      suffices Δ (fun x ↦ X (min x i)) j = 0 by simp [this, hC]
      unfold jump
      split_ifs with h
      · simp only [hij.le, inf_of_le_right]
        rw [min_eq_right]
        · simp
        · by_contra! h_lt
          have h_covBy := h.choose_spec.2 h_lt
          grind
      · have ht_ne_bot : 𝓝[<] j ≠ ⊥ := by
          rw [ne_eq, nhdsLT_eq_bot_iff]
          simp only [isBot_iff_eq_bot, h, or_false]
          intro ht_bot
          simp [ht_bot] at hij
        simp only [hij.le, inf_of_le_right]
        rw [leftLim_congr' (g := fun _ ↦ X i)]
        · simp [leftLim_eq_of_tendsto (y := X i) ht_ne_bot tendsto_const_nhds]
        · exact ht_ne_bot
        · rw [eventuallyEq_nhdsWithin_iff]
          filter_upwards [eventually_gt_nhds hij] with s hsτ hst
          rw [min_eq_right]
          exact hsτ.le
        · rw [min_eq_right hij.le]
    | inr h =>
      convert hX j using 2
      rw [jump_congr]
      grind
  · intro X Y i ⟨k, hik, hk⟩
    rw [jump_congr]
    intro s hsi
    exact hk s (hsi.trans_lt hik)

omit [NormedSpace ℝ E] [𝓕.IsRightContinuous] [IsFiniteMeasure P] [Approximable 𝓕 P] in
lemma locally_jump_le_iff {C : ℝ} (hC : 0 ≤ C) {X : ι → Ω → E} :
    Locally (fun X ↦ ∀ t ω, ‖Δ (X · ω) t‖ ≤ C) 𝓕 X P ↔ ∀ᵐ ω ∂P, ∀ t, ‖Δ (X · ω) t‖ ≤ C := by
  have h := locally_iff_ae (fun (X : ι → E) t ↦ ‖Δ X t‖ ≤ C) ?_ ?_ (𝓕 := 𝓕) (P := P) (X := X)
  rotate_left
  · simp [hC]
  · intro X Y i ⟨k, hik, hk⟩
    rw [jump_congr]
    intro s hsi
    exact hk s (hsi.trans_lt hik)
  rw [← h]
  congr!
  exact ⟨fun h ω t ↦ h t ω, fun h t ω ↦ h ω t⟩

lemma IsLocalMartingale.isLocallySquareIntegrable_of_jump_le [DenselyOrdered ι]
    [NoMaxOrder ι] [PolishSpace ι]
    [SecondCountableTopology E] [CompleteSpace E]
    (hX : IsLocalMartingale X 𝓕 P) {C : ℝ} (hC : 0 ≤ C)
    (h_jump : ∀ᵐ ω ∂P, ∀ t, ‖Δ (X · ω) t‖ ≤ C) :
    IsLocallySquareIntegrable X 𝓕 P := by
  borelize ι E
  rw [← locally_jump_le_iff (𝓕 := 𝓕) hC] at h_jump
  refine IsStable.locally_induction₂
    (r := fun X : ι → Ω → E ↦ Martingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω))
    (p := fun X : ι → Ω → E ↦ ∀ t ω, ‖Δ (X · ω) t‖ ≤ C) ?_ isStable_martingale
    (isStable_jump_le hC) isStable_isSquareIntegrable hX h_jump
  intro X hX hX_jump
  exact hX.1.isLocallySquareIntegrable_of_jump_le hX.2 hX_jump

lemma IsLocalMartingale.isLocallySquareIntegrable_of_continuous [DenselyOrdered ι]
    [NoMaxOrder ι] [PolishSpace ι]
    [SecondCountableTopology E] [CompleteSpace E]
    (hX : IsLocalMartingale X 𝓕 P) (h_cont : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    IsLocallySquareIntegrable X 𝓕 P := by
  borelize ι E
  rw [← locally_continuous_iff (𝓕 := 𝓕)] at h_cont
  refine IsStable.locally_induction₂
    (r := fun X : ι → Ω → E ↦ Martingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω))
    (p := fun X : ι → Ω → E ↦ ∀ ω, Continuous (X · ω)) ?_ isStable_martingale
    isStable_continuous isStable_isSquareIntegrable hX h_cont
  intro X hX hX_cont
  exact hX.1.isLocallySquareIntegrable_of_continuous hX_cont

end ConditionallyCompleteLinearOrderBot

end ProbabilityTheory
