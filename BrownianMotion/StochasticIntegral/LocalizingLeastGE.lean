/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.Adapted
public import BrownianMotion.Choquet.Debut
public import Mathlib.Probability.Process.LocalProperty

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

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

end ProbabilityTheory
