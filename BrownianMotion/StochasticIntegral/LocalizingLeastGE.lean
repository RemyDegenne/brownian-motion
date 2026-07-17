/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Yongxi Lin
-/
module

public import BrownianMotion.Auxiliary.Adapted
public import BrownianMotion.Choquet.Debut
public import BrownianMotion.StochasticIntegral.Jump
public import Mathlib.Probability.Process.LocalProperty

@[expose] public section

open MeasureTheory Function
open scoped Topology

namespace ProbabilityTheory

variable {Ω E : Type*} [NormedAddCommGroup E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

instance {ι : Type*} [LE ι] [OrderTop ι] [OrderBot ι] : BoundedOrder ι where

lemma isLocalizingSequence_leastGE {ι : Type*} [ConditionallyCompleteLinearOrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι]
    (𝓕 : Filtration ι mΩ) {X : ι → Ω → ℝ} (hX1 : StronglyAdapted 𝓕 X)
    (hX2 : ∀ ω, IsCadlag (X · ω)) [𝓕.IsComplete P] [𝓕.IsRightContinuous] [IsFiniteMeasure P] :
    IsLocalizingSequence 𝓕 (fun n => leastGE X n) P where
  isStoppingTime n := by
    borelize ι
    refine isStoppingTime_leastGE P ?_ _
    · exact hX1.isStronglyProgressive_of_rightContinuous (fun ω ↦ (hX2 ω).right_continuous)
  mono := by filter_upwards with ω n m hnm using
    hittingAfter_anti X ⊥ (Set.Ici_subset_Ici.2 (Nat.cast_le.2 hnm)) ω
  tendsto_top := by
    filter_upwards with ω
    -- Consider two cases. If `ι` has a top element, then `ι` is compact and the range of `X · ω` is
    -- bounded. Hence, `leastGE X n` is eventually equal to `⊤`.
    rcases topOrderOrNoTopOrder ι with ha | hb
    · have : Bornology.IsBounded (Set.range (X · ω)) := by
        have : Set.Icc (⊥ : ι) ⊤ = Set.univ := Set.Icc_bot_top
        exact Set.image_univ ▸ this ▸ isBounded_image_of_isCadlag_of_isCompact (hX2 ω) isCompact_Icc
      obtain ⟨m, hm⟩ : ∃ (m : ℕ), ∀ i, X i ω ≤ m := by
        obtain ⟨x, hx⟩ := bddAbove_def.1 this.bddAbove
        exact ⟨⌈x⌉₊, fun i => (hx (X i ω) (Set.mem_range_self i)).trans (Nat.le_ceil x)⟩
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [Filter.Ioi_mem_atTop m] with n hn
      simpa [leastGE, hittingAfter] using fun i => lt_of_le_of_lt (hm i) (Nat.cast_lt.2 hn)
    -- If `ι` does not have a top element, then it suffices to show that every `i : ι`,
    -- `leastGE X n` is eventually larger than `i`.
    refine nhds_top_basis.tendsto_right_iff.2 fun i hi => ?_
    obtain ⟨c, hc⟩ := (NoTopOrder.to_noMaxOrder ι).exists_gt (i.untop (lt_top_iff_ne_top.1 hi))
    have : Bornology.IsBounded ((X · ω) '' (Set.Icc ⊥ c)) :=
      isBounded_image_of_isCadlag_of_isCompact (hX2 ω) isCompact_Icc
    obtain ⟨m, hm⟩ : ∃ (m : ℕ), ∀ j ≤ c, X j ω ≤ m := by
      obtain ⟨x, hx⟩ := bddAbove_def.1 this.bddAbove
      exact ⟨⌈x⌉₊, fun i hi => (hx (X i ω)
        (Set.mem_image_of_mem _ ⟨bot_le, hi⟩)).trans (Nat.le_ceil x)⟩
    filter_upwards [Filter.Ioi_mem_atTop m] with n hn
    simp only [leastGE, hittingAfter]
    by_cases hj : ∃ j, X j ω ∈ Set.Ici ↑n
    · simp_all only [bot_le, true_and, ↓reduceIte]
      have : c ≤ sInf {j | ↑n ≤ X j ω} := by
        refine le_csInf hj fun k hk1 => ?_
        by_contra! hk2
        grind [Nat.cast_le.1 (hk1.trans (hm k hk2.le))]
      exact lt_of_le_of_lt' (mod_cast this) (by simp_all : i < c)
    · grind

/-- The stopped process at the time when the norm of the process first exceeds a threshold. -/
noncomputable
def stoppedAtNorm {ι : Type*} [ConditionallyCompleteLinearOrderBot ι] (X : ι → Ω → E) (r : ℝ) :
    ι → Ω → E :=
  (stoppedProcess (fun i ↦ {ω | ⊥ < leastGE (fun i ω ↦ ‖X i ω‖) r ω}.indicator (X i))
    (leastGE (fun i ω ↦ ‖X i ω‖) r))

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

@[to_dual]
theorem _root_.WithBot.unbotA_inj {α : Type*} [Nonempty α] {a b : WithBot α}
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    a.unbotA = b.unbotA ↔ a = b := by
  rw [WithBot.unbotA_eq_unbot ha, WithBot.unbotA_eq_unbot hb]
  exact WithBot.unbot_inj ha hb

@[to_dual (attr := simp)]
lemma _root_.WithBot.coe_unbotA {α : Type*} [Nonempty α] {x : WithBot α} (hx : x ≠ ⊥) :
    x.unbotA = x := by
  rw [WithBot.unbotA_eq_unbot hx, WithBot.coe_unbot]

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
    by_cases! h_covBy : ∃ s, s ⋖ (τ n ω).untopA
    · obtain ⟨s, hs_covBy⟩ := h_covBy
      rw [jump_of_covBy hs_covBy]
      calc ‖X (τ n ω).untopA ω‖
      _ = ‖X s ω + (X (τ n ω).untopA ω - X s ω)‖ := by congr; abel
      _ ≤ ‖X s ω‖ + ‖X (τ n ω).untopA ω - X s ω‖ := norm_add_le _ _
      _ ≤ n + ‖X (τ n ω).untopA ω - X s ω‖ := by
        gcongr
        refine (hX_lt ?_).le
        have hs_lt : s < (τ n ω).untopA := hs_covBy.1
        rwa [WithTop.lt_untopA_iff hτ_top] at hs_lt
    · calc ‖X (τ n ω).untopA ω‖
      _ ≤ ‖leftLim (X · ω) (τ n ω).untopA‖ + ‖Δ (X · ω) (τ n ω).untopA‖ := by
        rw [← leftLim_add_jump_of_not_covBy (f := (X · ω)) h_covBy]
        exact norm_add_le _ _
      _ ≤ n + ‖Δ (fun x ↦ X x ω) (τ n ω).untopA‖ := by
        gcongr
        have h_bot : 𝓝[<] (τ n ω).untopA ≠ ⊥ := by
          have h_ne_bot : (τ n ω).untopA ≠ ⊥ := by
            refine fun h_eq_bot ↦ hτ_bot ?_
            rw [← WithTop.coe_untopA hτ_top, h_eq_bot]
            rfl
          simp [h_ne_bot, h_covBy, nhdsLT_eq_bot_iff]
        have : (𝓝[<] (τ n ω).untopA).NeBot := ⟨h_bot⟩
        refine le_of_tendsto (f := fun t ↦ ‖X t ω‖) (x := 𝓝[<] ((τ n ω).untopA)) ?_ ?_
        · exact (tendsto_leftLim_of_tendsto ((h_cadlag ω).left_limit _)).norm
        · refine eventually_nhdsWithin_of_forall fun t ht ↦ ?_
          refine (hX_lt ?_).le
          simp only [Set.mem_Iio] at ht
          rwa [WithTop.lt_untopA_iff hτ_top] at ht

end ProbabilityTheory
