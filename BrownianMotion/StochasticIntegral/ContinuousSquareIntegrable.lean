/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import BrownianMotion.StochasticIntegral.SquareIntegrable

/-!

# Continuous square integrable martingales

-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter Function TopologicalSpace MeasureTheory.AEEqProcess
open scoped Topology ENNReal RealInnerProductSpace

variable {ι Ω E : Type*} [NormedAddCommGroup E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [LinearOrder ι] [TopologicalSpace ι] {X Y Z : ι → Ω → E} {𝓕 : Filtration ι mΩ}
  {τ : Ω → WithTop ι} [CompleteSpace E] [IsFiniteMeasure P]

/-! ### Continuous square integrable martingales -/

section NormedSpace

variable [NormedSpace ℝ E]

variable (E P 𝓕) in
/-- The set of continuous square integrable martingales, as a submodule of the type of
square-integrable martingales, see `SquareIntegrable`. -/
def continuousSquareIntegrable : Submodule ℝ (SquareIntegrable E P 𝓕) where
  carrier := {X | ∃ Y : ι → Ω → E, (∀ ω, Continuous (Y · ω)) ∧ IsSquareIntegrable Y 𝓕 P ∧ X ≡ᵐ[P] Y}
  add_mem' := by
    rintro X Y ⟨X', hX1, hX2, hX3⟩ ⟨Y', hY1, hY2, hY3⟩
    refine ⟨X' + Y', fun ω ↦ (hX1 ω).add (hY1 ω), hX2.add hY2, ?_⟩
    grw [← hX3, ← hY3, SquareIntegrable.coe_add]
  zero_mem' := ⟨0, by fun_prop, .const, SquareIntegrable.coe_zero E P 𝓕⟩
  smul_mem' := by
    rintro c X ⟨X', hX1, hX2, hX3⟩
    refine ⟨c • X', fun ω ↦ (hX1 ω).const_smul c, hX2.smul c, ?_⟩
    grw [SquareIntegrable.coe_smul X c, hX3]

lemma continuous_coe {X : SquareIntegrable E P 𝓕} (hX : X ∈ continuousSquareIntegrable E P 𝓕)
    (ω : Ω) :
    Continuous (X · ω) := by
  have : ∃ Y : ι → Ω → E,
      (∀ ω, Continuous (Y · ω)) ∧ IsSquareIntegrable Y 𝓕 P ∧ X.1 ≡ᵐ[P] Y := by
    obtain ⟨Y, hY1, hY2, hY3⟩ := hX
    exact ⟨Y, hY1, hY2, by grw [X.val_indist_coe, hY3]⟩
  rw [SquareIntegrable.out, dif_pos this]
  exact this.choose_spec.1 ω

omit [IsFiniteMeasure P] in
lemma IsAESquareIntegrable.isSquareIntegrable_toContinuous [h𝓕 : 𝓕.IsComplete P]
    (hX1 : ∀ᵐ ω ∂P, Continuous (X · ω)) (hX2 : IsAESquareIntegrable X 𝓕 P) :
    IsSquareIntegrable (hX2.toContinuous X) 𝓕 P := by
  have obv : ∀ᵐ ω ∂P, Continuous (hX2.choose · ω) := by
    filter_upwards [hX2.choose_spec.2, hX1] with ω h h'
    simpa [← h]
  refine ⟨hX2.choose_spec.1.martingale.congr (fun t ↦ ?_) (fun t ↦ ?_),
    fun ω ↦ (hX2.continuous_toContinuous ω).isCadlag, ?_⟩
  · obtain ⟨f, hf⟩ := hX2.choose_spec.1.martingale.stronglyAdapted t
    let s := {ω | Continuous (hX2.choose · ω)}
    have hs : MeasurableSet[𝓕 t] s := (h𝓕.measurableSet_of_null obv t).of_compl
    refine ⟨fun n ↦ @SimpleFunc.piecewise Ω E (𝓕 t) s hs (f n) (@SimpleFunc.const Ω E (𝓕 t) 0),
      fun ω ↦ ?_⟩
    by_cases hω : Continuous (hX2.choose · ω)
    · simpa [s, hω, toContinuous] using hf ω
    · simp [s, hω, toContinuous]
  · filter_upwards [obv] with ω h
    simp [toContinuous, h]
  · convert hX2.choose_spec.1.memLp_limitProcess.2
    rw [← hX2.choose_spec.1.iSup_eLpNorm_eq_eLpNorm_limitProcess]
    congr with i
    rw [← eLpNorm_congr_ae ((hX2.indist_toContinuous hX1).ae_eq_eval i),
      eLpNorm_congr_ae (hX2.choose_spec.2.ae_eq_eval i)]

/-- A square integrable martingale that is almost surely continuous is indistinguishable
from a square integrable martingale that is continuous everywhere. -/
lemma mem_continuousSquareIntegrable [𝓕.IsComplete P] {X : SquareIntegrable E P 𝓕}
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) : X ∈ continuousSquareIntegrable E P 𝓕 :=
  ⟨X.isAESquareIntegrable_coe.toContinuous X,
    X.isAESquareIntegrable_coe.continuous_toContinuous,
    X.isAESquareIntegrable_coe.isSquareIntegrable_toContinuous hX,
    X.isAESquareIntegrable_coe.indist_toContinuous hX⟩

/-- A square integrable martingale that is almost surely continuous is indistinguishable
from a square integrable martingale that is continuous everywhere. -/
lemma IsAESquareIntegrable.mk_mem_continuousSquareIntegrable [𝓕.IsComplete P]
    (hX1 : IsAESquareIntegrable X 𝓕 P) (hX2 : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    .mk X hX1 ∈ continuousSquareIntegrable E P 𝓕 := by
  apply mem_continuousSquareIntegrable
  filter_upwards [hX2, SquareIntegrable.mk_indist hX1] with ω h1 h2
  simpa [h2]

/-- If `M` is a sequence of square integrable martingales that converges to `N` in
`SquareIntegrable E P 𝓕`, then there exists `φ : ℕ → ℕ` increasing such that almost surely,
`M n` converges to `N` uniformly. This is needed to show that the space of continuous
square integrable martingales is closed. -/
lemma exists_subsequence_ae_tendsto_uniformly {M : ℕ → ι → Ω → E} {N : ι → Ω → E}
    [OrderTopology ι] [SecondCountableTopology ι]
    (hM : ∀ n, IsAESquareIntegrable (M n) 𝓕 P) (hN : IsAESquareIntegrable N 𝓕 P)
    (h : Tendsto (fun n ↦ eLpNorm (𝓕.limitProcess (M n) P - 𝓕.limitProcess N P) 2 P) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ᵐ ω ∂P, TendstoUniformly (fun n t ↦ M (φ n) t ω) (N · ω) atTop) := by
  obtain hι | _ := isEmpty_or_nonempty ι
  · refine ⟨id, strictMono_id, ae_of_all _ fun _ ↦ ?_⟩
    rw [← tendstoUniformlyOn_univ, Set.univ_eq_empty_iff.2 hι]
    exact tendstoUniformlyOn_empty
  -- We can find a subsequence such that `‖(M (φ n))∞ - N∞‖ₑ ≤ (1 / 2) ^ n`
  have h1 n : ∃ k, ∀ l ≥ k,
      eLpNorm (𝓕.limitProcess (M l) P - 𝓕.limitProcess N P) 2 P ≤ (1 / 2) ^ n := by
    rw [ENNReal.tendsto_atTop_zero] at h
    exact h _ (ENNReal.pow_pos (ENNReal.div_pos (by simp) (by simp)) n)
  obtain ⟨φ, mφ, hφ⟩ := extraction_forall_of_eventually' h1
  have aem_iSup n : AEMeasurable (fun ω ↦ ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ) P := by
    refine ⟨fun ω ↦ ⨆ t, ‖(hM (φ n)).choose t ω - hN.choose t ω‖ₑ, ?_, ?_⟩
    · suffices Measurable (⨆ t, fun ω ↦ ‖(hM (φ n)).choose t ω - hN.choose t ω‖ₑ) by
        convert this with ω
        simp
      refine measurable_iSup_of_rightContinuous (fun ω ↦ ?_) (fun ω ↦ ?_)
      · exact (((hM (φ n)).choose_spec.1.sub hN.choose_spec.1).isRightContinuous ω).continuous_comp
          continuous_enorm
      · exact (continuous_enorm.comp_stronglyMeasurable ((hM (φ n)).choose_spec.1.sub
          hN.choose_spec.1).martingale.stronglyMeasurable').measurable
    · filter_upwards [(hM (φ n)).choose_spec.2, hN.choose_spec.2] with ω h1 h2
      simp_rw [h1, h2]
  use φ, mφ
  /- This implies that the series `∑' n, ‖(M (φ n))∞ - N∞‖ₑ` converges, which by Doob's inequality
  implies that `∑' n, ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ converges. -/
  have : ∫⁻ ω, ∑' n, ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ ∂P < ∞ :=
    calc
    _ = ∑' n, ∫⁻ ω, ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ ∂P := lintegral_tsum aem_iSup
    _ ≤ (P Set.univ) ^ (1 / 2 : ℝ) *
        ∑' n, (∫⁻ ω, (⨆ t, ‖M (φ n) t ω - N t ω‖ₑ) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
      rw [← ENNReal.tsum_mul_left]
      gcongr
      grw [← ENNReal.rpow_rpow_inv (y := 2) (x := ∫⁻ ω, ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ ∂P) (by simp),
        rpow_lintegral_le (aem_iSup n) (by simp), ENNReal.mul_rpow_of_nonneg, one_div]
      · norm_num
      · simp
    _ ≤ (P Set.univ) ^ (1 / 2 : ℝ) * (2 * ∑' n, eLpNorm (𝓕.limitProcess (M (φ n)) P -
        𝓕.limitProcess N P) 2 P) := by
      rw [← ENNReal.tsum_mul_left (a := 2)]
      gcongr
      grw [((hM (φ n)).fun_sub hN).integral_iSup_norm_rpow_rpow_inv_le_limitProcess,
        eLpNorm_congr_ae ((hM (φ n)).limitProcess_fun_sub hN)]
      rfl
    _ ≤ (P Set.univ) ^ (1 / 2 : ℝ) * (2 * ∑' n, (1 / 2 : ℝ≥0∞) ^ n) := by grw [hφ]
    _ < ∞ := by
      refine ENNReal.mul_lt_top ?_ (ENNReal.mul_lt_top (by simp) ?_)
      · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp)
      rw [ENNReal.tsum_geometric]
      simp
  filter_upwards [ae_lt_top' (.tsum aem_iSup) this.ne] with ω h
  -- In particular `⨆ t, ‖M (φ n) t ω - N t ω‖ₑ` tends to `0`, so we have uniform convergence.
  refine Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := ENNReal.tendsto_atTop_zero.1 (ENNReal.tendsto_atTop_zero_of_tsum_ne_top h.ne)
    (.ofReal (ε / 2)) (by simpa)
  refine eventually_atTop.2 ⟨n, fun k hk t ↦ ?_⟩
  rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by simp)]
  · grw [dist_comm, dist_eq_norm, ofReal_norm, le_iSup (fun s ↦ ‖M (φ k) s ω - N s ω‖ₑ), hn k hk,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg]
    · simpa
    · positivity

/-- The submodule of continuous square integrable martingales is closed in the Hilbert space
of square integrable martingales. -/
instance [𝓕.IsComplete P] [Nonempty ι] [OrderTopology ι] [SecondCountableTopology ι] :
    IsClosed (continuousSquareIntegrable E P 𝓕 : Set (SquareIntegrable E P 𝓕)) := by
  refine IsSeqClosed.isClosed fun M N hM1 hM2 ↦ ?_
  have :
      Tendsto (fun n ↦ eLpNorm (𝓕.limitProcess (M n) P - 𝓕.limitProcess N P) 2 P) atTop (𝓝 0) := by
    simp_rw [tendsto_iff_enorm_sub_tendsto_zero, SquareIntegrable.enorm_def] at hM2
    refine hM2.congr fun n ↦ ?_
    rw [eLpNorm_congr_ae <| 𝓕.limitProcess_congr (SquareIntegrable.coe_sub (M n) N),
      eLpNorm_congr_ae (IsAESquareIntegrable.limitProcess_sub ?_ ?_)]
    all_goals exact SquareIntegrable.isAESquareIntegrable_coe _
  obtain ⟨φ, mφ, hφ⟩ := exists_subsequence_ae_tendsto_uniformly
      (fun n ↦ (M n).isAESquareIntegrable_coe) N.isAESquareIntegrable_coe this
  apply mem_continuousSquareIntegrable
  filter_upwards [hφ] with ω h
  exact h.continuous <| .of_forall fun n ↦ continuous_coe (hM1 (φ n)) ω

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E] [Nonempty ι] [OrderTopology ι] [SecondCountableTopology ι]

open scoped Classical in
/-- The continuous martingale part of a square-integrable martingale `X`. This is defined as the
projection of `X` onto the closed subspace of continuous square-integrable martingales. -/
noncomputable def continuousPart (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    [IsFiniteMeasure P] [𝓕.IsComplete P] : ι → Ω → E :=
  if hX : IsAESquareIntegrable X 𝓕 P
    then (continuousSquareIntegrable E P 𝓕).starProjection (SquareIntegrable.mk X hX)
    else 0

section IsComplete

variable [𝓕.IsComplete P]

lemma continuousPart_congr (hXY : X ≡ᵐ[P] Y) :
    continuousPart X 𝓕 P = continuousPart Y 𝓕 P := by
  by_cases hX : IsAESquareIntegrable X 𝓕 P
  · simp only [continuousPart, hX, ↓reduceDIte, hX.congr hXY]
    ext t ω
    congr 2
    rwa [SquareIntegrable.mk_eq_mk]
  simp [continuousPart, hX, (isAESquareIntegrable_congr hXY).not.1 hX]

lemma continuous_continuousPart (X : ι → Ω → E) (ω : Ω) :
    Continuous (continuousPart X 𝓕 P · ω) := by
  rw [continuousPart]
  split_ifs
  · exact continuous_coe ((continuousSquareIntegrable E P 𝓕).starProjection_apply_mem _) ω
  simp [continuous_const]

lemma isSquareIntegrable_continuousPart :
    IsSquareIntegrable (continuousPart X 𝓕 P) 𝓕 P := by
  rw [continuousPart]
  split_ifs
  · exact SquareIntegrable.isSquareIntegrable_coe _
  · exact .const

lemma IsAESquareIntegrable.mk_continuousPart (hX : IsAESquareIntegrable X 𝓕 P) :
    .mk (continuousPart X 𝓕 P) isSquareIntegrable_continuousPart.isAESquareIntegrable =
      (continuousSquareIntegrable E P 𝓕).starProjection (.mk X hX) := by
  ext
  grw [SquareIntegrable.mk_indist, continuousPart, dif_pos hX]

/-- The purely discontinuous martingale part of a square integrable martingale. Purely discontinuous
martingales are the orthogonal submodule of continuous square integrable martingales
in the Hilbert space of square integrable martingales. -/
noncomputable def discontinuousPart (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    [IsFiniteMeasure P] [𝓕.IsComplete P] : ι → Ω → E :=
  X - continuousPart X 𝓕 P

lemma discontinuousPart_def (X : ι → Ω → E) :
    discontinuousPart X 𝓕 P = X - continuousPart X 𝓕 P := rfl

lemma continuousPart_add_discontinuousPart :
    continuousPart X 𝓕 P + discontinuousPart X 𝓕 P = X := by
  simp [discontinuousPart]

lemma IsAESquareIntegrable.discontinuousPart (hX : IsAESquareIntegrable X 𝓕 P) :
    IsAESquareIntegrable (discontinuousPart X 𝓕 P) 𝓕 P :=
  hX.sub isSquareIntegrable_continuousPart.isAESquareIntegrable

end IsComplete

variable (E P 𝓕) in
/-- The submodule of purely discontinuous square integrable martingales. Purely discontinuous
martingales are the orthogonal submodule of continuous square integrable martingales
in the Hilbert space of square integrable martingales. -/
noncomputable def discontinuousSquareIntegrable : Submodule ℝ (SquareIntegrable E P 𝓕) :=
  (continuousSquareIntegrable E P 𝓕).orthogonal

omit [OrderTopology ι] in
/-- A purely discontinuous square integrable martingale is in the submodule of purely discontinuous
square integrable martingales. This statements links the predicate `IsPurelyDiscontinuous`
with the submodule `discontinuousSquareIntegrable`. -/
lemma mem_discontinuousSquareIntegrable {Y : SquareIntegrable E P 𝓕}
    (hY : IsPurelyDiscontinuous Y 𝓕 P) : Y ∈ discontinuousSquareIntegrable E P 𝓕 := by
  rw [discontinuousSquareIntegrable, Submodule.mem_orthogonal']
  intro X hX
  rw [SquareIntegrable.inner_def, hY.2]
  · exact X.isAESquareIntegrable_coe
  · exact ae_of_all _ <| continuous_coe hX

omit [OrderTopology ι] in
/-- A purely discontinuous square integrable martingale is in the submodule of purely discontinuous
square integrable martingales. This statements links the predicate `IsPurelyDiscontinuous`
with the submodule `discontinuousSquareIntegrable`. -/
lemma IsPurelyDiscontinuous.mk_mem_discontinuousSquareIntegrable
    (hY : IsPurelyDiscontinuous Y 𝓕 P) :
    .mk Y hY.1 ∈ discontinuousSquareIntegrable E P 𝓕 := by
  apply mem_discontinuousSquareIntegrable
  exact hY.congr (SquareIntegrable.mk_indist hY.1).symm

variable [𝓕.IsComplete P]

/-- The discontinuous part of square integrable martingale is purely discontinuous. -/
lemma isPurelyDiscontinuous_discontinuousPart (hX : IsAESquareIntegrable X 𝓕 P) :
    IsPurelyDiscontinuous (discontinuousPart X 𝓕 P) 𝓕 P := by
  constructor
  · exact hX.sub isSquareIntegrable_continuousPart.isAESquareIntegrable
  intro Y hY1 hY2
  rw! [hX.discontinuousPart.inner_limitProcess_eq hY1, discontinuousPart, SquareIntegrable.mk_sub,
    hX.mk_continuousPart, Submodule.starProjection_inner_eq_zero]
  · rfl
  · apply mem_continuousSquareIntegrable
    filter_upwards [hY2, SquareIntegrable.mk_indist hY1] with ω h1 h2
    simp_rw [h2]
    exact h1

/-- Uniqueness of the decomposition of a square integrable martingale into a continuous part and
a discontinuous part: If a square integrable martingale `Z` is indistinguishable from `X + Y`
where `X` is continuous and `Y` is discontinuous, then `X` is indistinguishable from the
continuous part of `Z`. -/
lemma indist_continuousPart (hX1 : IsAESquareIntegrable X 𝓕 P)
    (hX2 : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : IsPurelyDiscontinuous Y 𝓕 P)
    (hZ1 : IsAESquareIntegrable Z 𝓕 P) (hZ2 : Z ≡ᵐ[P] X + Y) :
    X ≡ᵐ[P] continuousPart Z 𝓕 P := by
  rw [← SquareIntegrable.mk_eq_mk (hX := hZ1) (hY := hX1.add hY.1),
    SquareIntegrable.mk_add (hX := hX1) (hY := hY.1)] at hZ2
  have := Submodule.eq_starProjection_of_mem_orthogonal' (hX1.mk_mem_continuousSquareIntegrable hX2)
    hY.mk_mem_discontinuousSquareIntegrable hZ2
  rw [continuousPart, dif_pos hZ1, this]
  exact SquareIntegrable.mk_indist hX1 |>.symm

/-- Uniqueness of the decomposition of a square integrable martingale into a continuous part and
a discontinuous part: If a square integrable martingale `Z` is indistinguishable from `X + Y`
where `X` is continuous and `Y` is discontinuous, then `Y` is indistinguishable from the
discontinuous part of `Z`. -/
lemma indist_discontinuousPart {X Y Z : ι → Ω → E} (hX1 : IsAESquareIntegrable X 𝓕 P)
    (hX2 : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY2 : IsPurelyDiscontinuous Y 𝓕 P)
    (hZ1 : IsAESquareIntegrable Z 𝓕 P) (hZ2 : Z ≡ᵐ[P] X + Y) :
    Y ≡ᵐ[P] discontinuousPart Z 𝓕 P := by
  grw [discontinuousPart, ← indist_continuousPart hX1 hX2 hY2 hZ1 hZ2, hZ2]
  simp

omit [𝓕.IsComplete P] in
/-- The stopped process of a purely discontinuous square integrable martingale is again
a purely discontinuous square integrable martingale. -/
nonrec
lemma IsPurelyDiscontinuous.stoppedProcess [OrderBot ι] [Approximable 𝓕 P]
    (hX : IsPurelyDiscontinuous X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    IsPurelyDiscontinuous (stoppedProcess X τ) 𝓕 P := by
  borelize ι
  refine ⟨hX.1.stoppedProcess hτ, fun Y hY1 hY2 ↦ ?_⟩
  rw [← hX.2 (stoppedProcess Y τ), ← integral_condExp hτ.measurableSpace_le,
    ← integral_condExp hτ.measurableSpace_le (f := fun _ ↦ ⟪_, _⟫)]
  · apply integral_congr_ae
    grw [condExp_inner_of_aestronglyMeasurable_left,
      condExp_inner_of_aestronglyMeasurable_right]
    · filter_upwards [hX.1.limitProcess_stoppedProcess hτ, hX.1.condExp_limitProcess_ae_eq' hτ,
        hY1.limitProcess_stoppedProcess hτ, hY1.condExp_limitProcess_ae_eq' hτ] with ω h1 h2 h3 h4
      rw [h1, h2, h3, h4]
    · exact (hY1.aestronglyMeasurable_stoppedValue' hτ).congr
        (hY1.limitProcess_stoppedProcess hτ).symm
    · exact integrable_inner hX.1.memLp_limitProcess (hY1.stoppedProcess hτ).memLp_limitProcess
    · exact hX.1.memLp_limitProcess.integrable (by simp)
    · exact (hX.1.aestronglyMeasurable_stoppedValue' hτ).congr
        (hX.1.limitProcess_stoppedProcess hτ).symm
    · exact integrable_inner (hX.1.stoppedProcess hτ).memLp_limitProcess hY1.memLp_limitProcess
    · exact hY1.memLp_limitProcess.integrable (by simp)
  · exact hY1.stoppedProcess hτ
  · filter_upwards [hY2] with ω h using h.stoppedProcess τ

/-- The continuous part of the stopped process is the stopped process of the continuous part. -/
lemma continuousPart_stoppedProcess [OrderBot ι] [Approximable 𝓕 P]
    {X : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    continuousPart (stoppedProcess X τ) 𝓕 P ≡ᵐ[P] stoppedProcess (continuousPart X 𝓕 P) τ := by
  have : stoppedProcess X τ =
      stoppedProcess (continuousPart X 𝓕 P) τ + stoppedProcess (discontinuousPart X 𝓕 P) τ := by
    rw [← stoppedProcess_add, continuousPart_add_discontinuousPart]
  borelize E
  symm
  apply indist_continuousPart
    (isSquareIntegrable_continuousPart.isAESquareIntegrable.stoppedProcess hτ)
    (ae_of_all _ (fun ω ↦ (continuous_continuousPart X ω).stoppedProcess τ))
    ((isPurelyDiscontinuous_discontinuousPart hX).stoppedProcess hτ)
    (hX.stoppedProcess hτ) (by rw [this])

attribute [to_fun] stoppedProcess_sub

/-- The discontinuous part of the stopped process is
the stopped process of the discontinuous part. -/
lemma discontinuousPart_stoppedProcess [OrderBot ι] [Approximable 𝓕 P]
    {X : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    discontinuousPart (stoppedProcess X τ) 𝓕 P ≡ᵐ[P]
      stoppedProcess (discontinuousPart X 𝓕 P) τ := by
  have : stoppedProcess X τ =
      stoppedProcess (continuousPart X 𝓕 P) τ + stoppedProcess (discontinuousPart X 𝓕 P) τ := by
    rw [← stoppedProcess_add, continuousPart_add_discontinuousPart]
  borelize E
  symm
  apply indist_discontinuousPart
    (isSquareIntegrable_continuousPart.isAESquareIntegrable.stoppedProcess hτ)
    (ae_of_all _ (fun ω ↦ (continuous_continuousPart X ω).stoppedProcess τ))
    ((isPurelyDiscontinuous_discontinuousPart hX).stoppedProcess hτ)
    (hX.stoppedProcess hτ) (by rw [this])

end InnerProductSpace

end ProbabilityTheory
