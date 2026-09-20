/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.DoobMeyerUniqueness

/-! # Doob-Meyer decomposition of local submartingales

A càdlàg local submartingale `X` can be written as `X = M + A`, in which `M` is a càdlàg local
martingale and `A` is a predictable, càdlàg, monotone process with locally integrable supremum.

## Main definitions

* `ProbabilityTheory.IsLocalSubmartingale.martingalePart`: the local martingale part of the
  Doob-Meyer decomposition of a local submartingale.
* `ProbabilityTheory.IsLocalSubmartingale.predictablePart`: the predictable part of the
  Doob-Meyer decomposition of a local submartingale.

## Main statements

* `ProbabilityTheory.IsLocalSubmartingale.doob_meyer`: Doob-Meyer decomposition of a càdlàg local
  submartingale.
-/

@[expose] public section

open MeasureTheory Filter Order ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {ι Ω : Type*} [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
  [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] [PolishSpace ι] [DenselyOrdered ι]
  [NoMaxOrder ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous] [𝓕.IsComplete P]
  [Approximable 𝓕 P]

namespace ProbabilityTheory

namespace IsLocalSubmartingale

/-- **Doob–Meyer decomposition** of a càdlàg local submartingale.

The hypotheses are those of `IsLocalSubmartingale.locally_classD_real`, which imply the ones of
`ClassDL.doob_meyer`, `MeasureTheory.doob_meyer_unique` and `isStable_martingale`. -/
theorem doob_meyer (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∃ (M A : ι → Ω → ℝ), X = M + A ∧ IsLocalMartingale M 𝓕 P ∧ (∀ ω, IsCadlag (M · ω)) ∧
      IsStronglyPredictable 𝓕 A ∧ (∀ ω, IsCadlag (A · ω)) ∧ (HasLocallyIntegrableSup A 𝓕 P)
      ∧ (∀ ω, Monotone (A · ω)) ∧ A ⊥ = 0 := by
  -- a localizing sequence `τ` along which `X` is a càdlàg submartingale of class D
  have h_loc : Locally (fun Y ↦ (Submartingale Y 𝓕 P ∧ ∀ ω, IsCadlag (Y · ω)) ∧ ClassD Y 𝓕 P)
      𝓕 X P :=
    (isStable_submartingale.locally_and_iff isStable_classD).2 ⟨hX, hX.locally_classD_real⟩
  obtain ⟨τ, hτ, hτ_mono, hτX⟩ :=
    (isStable_submartingale.and isStable_classD).exists_monotone_localSeq h_loc
  have hτ_st (n : ℕ) : IsStoppingTime 𝓕 (τ n) := hτ.isStoppingTime n
  have hτ_bot (n : ℕ) : MeasurableSet[𝓕 ⊥] {ω | ⊥ < τ n ω} := (hτ_st n).measurableSet_gt ⊥
  -- the Doob-Meyer decomposition `M' n + A' n` of `X` stopped at `τ n`
  have h_dm (n : ℕ) := ClassDL.doob_meyer (hτX n).2.classDL (hτX n).1.1 (hτX n).1.2
  choose M' A' hMA hM hMc hA hAc hAm hA0 using h_dm
  have hA'_int (n : ℕ) (t : ι) : Integrable (A' n t) P := by
    have h_eq : A' n t = stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n) t
        - M' n t := by
      rw [hMA n]
      simp
    rw [h_eq]
    exact ((hτX n).1.1.integrable t).sub ((hM n).integrable t)
  -- `A' (n + 1)` stopped at `τ n` is indistinguishable from `A' n`, by uniqueness
  have h_cons (n : ℕ) : ∀ᵐ ω ∂P, ∀ t, A' n t ω
      = stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (A' (n + 1) i)) (τ n) t ω := by
    have hS' : stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n)
        = stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (M' (n + 1) i)) (τ n)
          + stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (A' (n + 1) i)) (τ n) := by
      rw [← stoppedProcess_indicator_add, ← hMA (n + 1),
        stoppedProcess_indicator_stoppedProcess_indicator_of_le fun ω ↦ hτ_mono ω n.le_succ]
    refine (doob_meyer_unique_of_integrable (hτX n).1.1.integrable (hMA n) hS' (hM n)
      (isStable_martingale _ ⟨hM (n + 1), hMc (n + 1)⟩ (τ n) (hτ_st n)).1 (hA n)
      (fun ω ↦ (hAc n ω).right_continuous) (hAm n)
      (isStable_isStronglyPredictable _ (hA (n + 1)) (τ n) (hτ_st n))
      (fun ω ↦ (isStable_isCadlag _ (hAc (n + 1)) (τ n) (hτ_st n) ω).right_continuous)
      (fun ω ↦ (hAm (n + 1) ω).stoppedProcess_indicator _ _) ?_).1
    refine ae_of_all _ fun ω ↦ ?_
    rw [stoppedProcess_eq_of_le (by simp)]
    simp [hA0]
  -- the almost sure event on which we glue the processes `A' n`
  let G : Set Ω := {ω | (∀ n t, A' n t ω
      = stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (A' (n + 1) i)) (τ n) t ω)
    ∧ Tendsto (τ · ω) atTop (𝓝 ⊤)}
  have hG_ae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [ae_all_iff.2 h_cons, hτ.tendsto_top] with ω h1 h2 using ⟨h1, h2⟩
  have hG_meas : MeasurableSet[𝓕 ⊥] G :=
    (Filtration.IsComplete.measurableSet_of_null (ae_iff.1 hG_ae) ⊥).of_compl
  have h_succ {ω : Ω} (hω : ω ∈ G) (n : ℕ) {t : ι} (ht : (t : WithTop ι) ≤ τ n ω)
      (h_bot : ⊥ < τ n ω) : A' n t ω = A' (n + 1) t ω := by
    rw [hω.1 n t, stoppedProcess_eq_of_le ht, Set.indicator_of_mem]
    exact h_bot
  have h_le {ω : Ω} (hω : ω ∈ G) {m n : ℕ} (hmn : m ≤ n) {t : ι} (ht : (t : WithTop ι) ≤ τ m ω)
      (h_bot : ⊥ < τ m ω) : A' m t ω = A' n t ω := by
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ k hmk ih =>
      rw [ih, h_succ hω k (ht.trans (hτ_mono ω hmk)) (h_bot.trans_le (hτ_mono ω hmk))]
  have h_ex {ω : Ω} (hω : ω ∈ G) (t : ι) : ∃ n, (t : WithTop ι) < τ n ω :=
    (hω.2.eventually (lt_mem_nhds (WithTop.coe_lt_top t))).exists
  -- the predictable part: `A t ω = A' n t ω` for `ω ∈ G` and any `n` such that `t ≤ τ n ω`
  classical
  let A : ι → Ω → ℝ := fun t ω ↦ if h : ω ∈ G then A' (h_ex h t).choose t ω else 0
  have hA_eq {ω : Ω} (hω : ω ∈ G) {n : ℕ} {t : ι} (ht : (t : WithTop ι) ≤ τ n ω)
      (h_bot : ⊥ < τ n ω) : A t ω = A' n t ω := by
    simp only [A, dif_pos hω]
    have hm : (t : WithTop ι) < τ (h_ex hω t).choose ω := (h_ex hω t).choose_spec
    rcases le_total (h_ex hω t).choose n with hmn | hnm
    · exact h_le hω hmn hm.le (bot_le.trans_lt hm)
    · exact (h_le hω hnm ht h_bot).symm
  have hA_zero {ω : Ω} (hω : ω ∉ G) (t : ι) : A t ω = 0 := by simp [A, hω]
  have hA_pred : IsStronglyPredictable 𝓕 A := by
    refine stronglyMeasurable_of_tendsto atTop
      (f := fun n ↦ Function.uncurry fun t ↦ G.indicator (A' n t))
      (fun n ↦ (hA n).indicator_of_bot hG_meas) (tendsto_pi_nhds.2 fun p ↦ ?_)
    by_cases hp : p.2 ∈ G
    · obtain ⟨n, hn⟩ := h_ex hp p.1
      refine tendsto_atTop_of_eventually_const (i₀ := n) fun k hk ↦ ?_
      have hk' : (p.1 : WithTop ι) < τ k p.2 := hn.trans_le (hτ_mono p.2 hk)
      simp [Function.uncurry, hp, hA_eq hp hk'.le (bot_le.trans_lt hk')]
    · simp only [Function.uncurry, Set.indicator_of_notMem hp, hA_zero hp]
      exact tendsto_const_nhds
  have hA_cadlag (ω : Ω) : IsCadlag (A · ω) := by
    by_cases hω : ω ∈ G
    · have h_ev (x : ι) : ∃ n, ∀ᶠ t in 𝓝 x, A t ω = A' n t ω := by
        obtain ⟨n, hn⟩ := h_ex hω x
        have h_open : IsOpen {t : ι | (t : WithTop ι) < τ n ω} :=
          isOpen_lt WithTop.continuous_coe continuous_const
        refine ⟨n, ?_⟩
        filter_upwards [h_open.mem_nhds hn] with t ht using hA_eq hω ht.le (bot_le.trans_lt ht)
      refine ⟨fun x ↦ ?_, fun x ↦ ?_⟩
      · obtain ⟨n, hn⟩ := h_ev x
        exact ((hAc n ω).right_continuous x).congr_of_eventuallyEq
          (hn.filter_mono nhdsWithin_le_nhds) hn.self_of_nhds
      · obtain ⟨n, hn⟩ := h_ev x
        obtain ⟨l, hl⟩ := (hAc n ω).left_limit x
        exact ⟨l, hl.congr' ((hn.filter_mono nhdsWithin_le_nhds).mono fun t ht ↦ ht.symm)⟩
    · have h_eq : (A · ω) = fun _ ↦ 0 := funext fun t ↦ hA_zero hω t
      rw [h_eq]
      exact ⟨fun _ ↦ continuousWithinAt_const, fun _ ↦ ⟨0, tendsto_const_nhds⟩⟩
  have hA_mono (ω : Ω) : Monotone (A · ω) := by
    intro s t hst
    by_cases hω : ω ∈ G
    · obtain ⟨n, hn⟩ := h_ex hω t
      have hs : (s : WithTop ι) ≤ τ n ω := (WithTop.coe_le_coe.2 hst).trans hn.le
      simp only [hA_eq hω hn.le (bot_le.trans_lt hn), hA_eq hω hs (bot_le.trans_lt hn)]
      exact hAm n ω hst
    · simp [hA_zero hω]
  have hA_bot : A ⊥ = 0 := by
    ext ω
    by_cases hω : ω ∈ G
    · obtain ⟨n, hn⟩ := h_ex hω ⊥
      rw [hA_eq hω hn.le (bot_le.trans_lt hn), hA0 n]
    · exact hA_zero hω ⊥
  have hA_nonneg : 0 ≤ A := fun t ω ↦ by
    have h := hA_mono ω (bot_le (a := t))
    simpa [hA_bot] using h
  -- `A` stopped at `τ n` is indistinguishable from `A' n`
  have hA_stop (n : ℕ) : ∀ᵐ ω ∂P, ∀ t,
      stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (A i)) (τ n) t ω = A' n t ω := by
    filter_upwards [hG_ae] with ω hω t
    rw [hω.1 n t]
    simp only [stoppedProcess_indicator_comm]
    by_cases h_bot : ω ∈ {ω | ⊥ < τ n ω}
    · rw [Set.indicator_of_mem h_bot, Set.indicator_of_mem h_bot]
      simp only [stoppedProcess]
      have h_ne : min (t : WithTop ι) (τ n ω) ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      have hs : (((min (t : WithTop ι) (τ n ω)).untopA : ι) : WithTop ι) ≤ τ n ω := by
        rw [WithTop.untopA_eq_untop h_ne, WithTop.coe_untop]
        exact min_le_right _ _
      rw [hA_eq hω hs h_bot, h_succ hω n hs h_bot]
    · rw [Set.indicator_of_notMem h_bot, Set.indicator_of_notMem h_bot]
  have hA_stop_pred (n : ℕ) : IsStronglyPredictable 𝓕
      (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (A i)) (τ n)) :=
    isStable_isStronglyPredictable _ hA_pred (τ n) (hτ_st n)
  have hA_sup : HasLocallyIntegrableSup A 𝓕 P := by
    refine ⟨τ, hτ, fun n ↦ hasIntegrableSup_of_monotone
      ((hA_stop_pred n).mono 𝓕.predictable_le_prod)
      (fun ω ↦ (hA_mono ω).stoppedProcess_indicator _ _) (fun t ω ↦ ?_) fun t ↦ ?_⟩
    · rw [stoppedProcess_indicator_comm]
      exact Set.indicator_nonneg (fun _ _ ↦ hA_nonneg _ _) _
    · refine (hA'_int n t).congr ?_
      filter_upwards [hA_stop n] with ω hω using (hω t).symm
  -- the local martingale part: `X - A` stopped at `τ n` is a modification of `M' n`
  have hM_loc : IsLocalMartingale (X - A) 𝓕 P := by
    refine ⟨τ, hτ, fun n ↦ ⟨?_, isStable_isCadlag _
      (fun ω ↦ (hX_cadlag ω).sub (hA_cadlag ω)) (τ n) (hτ_st n)⟩⟩
    refine (hM n).congr ?_ fun t ↦ ?_
    · rw [stoppedProcess_indicator_sub]
      exact fun t ↦ ((hτX n).1.1.stronglyAdapted t).sub ((hA_stop_pred n).stronglyAdapted t)
    · filter_upwards [hA_stop n] with ω hω
      rw [stoppedProcess_indicator_sub, Pi.sub_apply, Pi.sub_apply, hω t, hMA n]
      simp
  exact ⟨X - A, A, (sub_add_cancel X A).symm, hM_loc, fun ω ↦ (hX_cadlag ω).sub (hA_cadlag ω),
    hA_pred, hA_cadlag, hA_sup, hA_mono, hA_bot⟩

/-- The local martingale part of the Doob-Meyer decomposition of the local submartingale. -/
noncomputable
def martingalePart (X : ι → Ω → ℝ)
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ :=
  (hX.doob_meyer hX_cadlag).choose

/-- The predictable part of the Doob-Meyer decomposition of the local submartingale. -/
noncomputable
def predictablePart (X : ι → Ω → ℝ)
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose

lemma martingalePart_add_predictablePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    X = hX.martingalePart X hX_cadlag + hX.predictablePart X hX_cadlag :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.1

lemma isLocalMartingale_martingalePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    IsLocalMartingale (hX.martingalePart X hX_cadlag) 𝓕 P :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.1

lemma cadlag_martingalePart (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∀ ω, IsCadlag (hX.martingalePart X hX_cadlag · ω) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.1

lemma isStronglyPredictable_predictablePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    IsStronglyPredictable 𝓕 (hX.predictablePart X hX_cadlag) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.1

lemma cadlag_predictablePart (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∀ ω, IsCadlag (hX.predictablePart X hX_cadlag · ω) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.1

lemma hasLocallyIntegrableSup_predictablePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    HasLocallyIntegrableSup (hX.predictablePart X hX_cadlag) 𝓕 P :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.2.1

lemma monotone_predictablePart (hX : IsLocalSubmartingale X 𝓕 P)
    (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∀ ω, Monotone (hX.predictablePart X hX_cadlag · ω) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.2.2.1

lemma predictablePart_bot (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    hX.predictablePart X hX_cadlag ⊥ = 0 :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.2.2.2

end IsLocalSubmartingale

end ProbabilityTheory
