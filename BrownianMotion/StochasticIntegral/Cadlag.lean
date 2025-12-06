/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences

/-! # cadlag functions

-/

open Filter TopologicalSpace Bornology
open scoped Topology

variable {ι E : Type*} [TopologicalSpace ι] [TopologicalSpace E]

/-- The predicate that a function is right continuous. -/
abbrev Function.RightContinuous [PartialOrder ι] (f : ι → E) :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a

/-- A function is cadlag if it is right-continuous and has left limits. -/
structure IsCadlag [PartialOrder ι] (f : ι → E) : Prop where
  right_continuous : Function.RightContinuous f
  left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)

/-- A càdlàg function maps compact sets to bounded sets. -/
lemma isBounded_image_of_isCadlag_of_isCompact {E : Type*} [LinearOrder ι] [PseudoMetricSpace E]
    [FirstCountableTopology ι] {f : ι → E} (hf : IsCadlag f) {s : Set ι} (hs : IsCompact s) :
    IsBounded (f '' s) := by
  by_contra h_nb
  let x := (nonempty_of_not_isBounded h_nb).some
  have h_distx : ∀ n : ℕ, ∃ y ∈ f '' s, n ≤ dist y x := fun n ↦ by
    rw [Metric.isBounded_iff_subset_ball x] at h_nb
    dsimp [Metric.ball] at h_nb
    push_neg at h_nb
    replace h_nb := h_nb n
    rw [Set.not_subset] at h_nb
    rcases h_nb with ⟨y, hy_in, hy_dist⟩
    use y, hy_in
    simpa [Set.mem_setOf_eq, not_lt] using hy_dist
  choose u hu_in hu_dist using h_distx
  have h_dist_infty : Tendsto (fun n ↦ dist (u n) x) atTop atTop :=
    tendsto_atTop_mono hu_dist tendsto_natCast_atTop_atTop
  choose t ht_in ht_eq using hu_in
  obtain ⟨t₀, -, φ, hφ_mono, h_lim⟩ := hs.tendsto_subseq ht_in
  let is_ge := {n | t₀ ≤ t (φ n)}
  by_cases h_freq_ge : Set.Infinite is_ge
  · let ψ := Nat.nth is_ge
    have hψ_mono : StrictMono ψ := Nat.nth_strictMono h_freq_ge
    have hψ_mem : ∀ n, ψ n ∈ is_ge := Nat.nth_mem_of_infinite h_freq_ge
    let sub_idx := φ ∘ ψ
    have h_tendsto_right : Tendsto (t ∘ sub_idx) atTop (𝓝[≥] t₀) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact h_lim.comp hψ_mono.tendsto_atTop
      · filter_upwards with n using hψ_mem n
    have h_right_cont := (hf.right_continuous t₀)
    have h_weak_right : Tendsto f (𝓝[≥] t₀) (𝓝 (f t₀)) := by
      have h_set_eq : Set.Ici t₀ = insert t₀ (Set.Ioi t₀) := by
        exact Eq.symm Set.Ioi_insert
      rw [h_set_eq, nhdsWithin_insert]
      apply tendsto_sup.mpr
      constructor
      · exact tendsto_pure_nhds _ _
      · exact h_right_cont.tendsto
    have h_img_conv : Tendsto (f ∘ t ∘ sub_idx) atTop (𝓝 (f t₀)) :=
      h_weak_right.comp h_tendsto_right
    have h_dist_conv := h_img_conv.dist (tendsto_const_nhds (x := x))
    have h_u_sub : (fun n ↦ dist (u (sub_idx n)) x) = (fun n ↦ dist ((f ∘ t ∘ sub_idx) n) x) := by
      ext n
      simp only [Function.comp_apply, ht_eq]
    rw [←h_u_sub] at h_dist_conv
    have h_dist_boom : Tendsto (fun n ↦ dist (u (sub_idx n)) x) atTop atTop :=
      h_dist_infty.comp (hφ_mono.comp hψ_mono).tendsto_atTop
    apply not_tendsto_nhds_of_tendsto_atTop h_dist_boom
    exact h_dist_conv
  · rw [Set.not_infinite] at h_freq_ge
    let is_lt := {n | t (φ n) < t₀}
    have h_freq_lt : Set.Infinite is_lt := by
      apply Set.infinite_of_finite_compl
      convert h_freq_ge using 1
      ext n
      simp only [is_lt, Set.mem_compl_iff, Set.mem_setOf_eq, is_ge, not_lt]
    let ψ := Nat.nth is_lt
    have hψ_mono : StrictMono ψ := Nat.nth_strictMono h_freq_lt
    have hψ_mem : ∀ n, ψ n ∈ is_lt := Nat.nth_mem_of_infinite h_freq_lt
    let sub_idx := φ ∘ ψ
    have h_tendsto_left : Tendsto (t ∘ sub_idx) atTop (𝓝[<] t₀) := by
       apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
       · exact h_lim.comp hψ_mono.tendsto_atTop
       · filter_upwards with n using hψ_mem n
    obtain ⟨y, hy_lim⟩ := (hf.left_limit t₀)
    have h_img_conv : Tendsto (f ∘ t ∘ sub_idx) atTop (𝓝 y) :=
      hy_lim.comp h_tendsto_left
    have h_dist_conv : Tendsto (fun n ↦ dist ((f ∘ t ∘ sub_idx) n) x) atTop (𝓝 (dist y x)) :=
      h_img_conv.dist (tendsto_const_nhds (x := x))
    have h_u_sub : (fun n ↦ dist (u (sub_idx n)) x) = (fun n ↦ dist ((f ∘ t ∘ sub_idx) n) x) := by
      ext n; simp [ht_eq]
    rw [←h_u_sub] at h_dist_conv
    have h_seq_boom : Tendsto (fun n ↦ dist (u (sub_idx n)) x) atTop atTop :=
      h_dist_infty.comp (hφ_mono.comp hψ_mono).tendsto_atTop
    exact (not_tendsto_nhds_of_tendsto_atTop h_seq_boom _) h_dist_conv
