/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Basic

/-! # cadlag functions

-/

open Filter TopologicalSpace Bornology
open scoped Topology

variable {ι E : Type*} [TopologicalSpace ι] [TopologicalSpace E]

/-- The predicate that a function is right continuous. -/
abbrev Function.RightContinuous [PartialOrder ι] (f : ι → E) :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a

lemma Function.RightContinuous.continuous_comp {F : Type*} [TopologicalSpace F] {g : E → F}
    {f : ι → E} (hg : Continuous g) (hf : RightContinuous f) : RightContinuous (g ∘ f) :=
  fun x ↦ (hg.tendsto (f x)).comp (hf x)

/-- A function is cadlag if it is right-continuous and has left limits. -/
structure IsCadlag [PartialOrder ι] (f : ι → E) : Prop where
  right_continuous : Function.RightContinuous f
  left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)

/-- A càdlàg function maps compact sets to bounded sets. -/
lemma isBounded_image_of_isCadlag_of_isCompact {E : Type*} [LinearOrder ι] [PseudoMetricSpace E]
    {f : ι → E} (hf : IsCadlag f) {s : Set ι} (hs : IsCompact s) :
    IsBounded (f '' s) := by
  by_contra h_nb
  let x := (nonempty_of_not_isBounded h_nb).some
  have h_distx : ∀ n : ℕ, ∃ t_n ∈ s, n ≤ dist (f t_n) x := fun n ↦ by
    rw [Metric.isBounded_iff_subset_ball x] at h_nb
    dsimp [Metric.ball] at h_nb
    push_neg at h_nb
    replace h_nb := h_nb n
    rw [Set.not_subset] at h_nb
    rcases h_nb with ⟨y, ⟨t, ht_in, ht_y⟩, hy_dist⟩
    use t, ht_in
    simpa [Set.mem_setOf_eq, not_lt, ht_y] using hy_dist
  choose t ht_in ht_eq using h_distx
  let V := Ultrafilter.of (map t atTop)
  have h_map_le_V : V ≤ map t atTop  := Ultrafilter.of_le (map t atTop)
  have hs_in_V : s ∈ V := by
    apply h_map_le_V
    rw [mem_map]
    filter_upwards [Filter.univ_mem] with n _ using ht_in n
  rcases IsCompact.ultrafilter_le_nhds' hs V hs_in_V with ⟨c, _, hV_le_nhds⟩
  have h_loc_bdd : ∃ W ∈ 𝓝 c, Bornology.IsBounded (f '' W) := by
    obtain ⟨l, hl⟩ := hf.left_limit c
    rcases Metric.exists_isBounded_image_of_tendsto hl with ⟨U_left, hU_mem, hU_bdd⟩
    rcases Metric.exists_isBounded_image_of_tendsto (hf.right_continuous c).tendsto
      with ⟨_, hV_mem, hV_bdd⟩
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU_mem hV_mem
    rcases hU_mem with ⟨G_left, hGl_nhds, hGl_sub⟩
    rcases hV_mem with ⟨G_right, hGr_nhds, hGr_sub⟩
    let W := G_left ∩ G_right
    have hW_nhds : W ∈ 𝓝 c := Filter.inter_mem hGl_nhds hGr_nhds
    use W, hW_nhds
    apply Bornology.IsBounded.subset ((hU_bdd.union hV_bdd).union
      (isBounded_induced.mp isBounded_singleton : Bornology.IsBounded (f '' {c})))
    rintro _ ⟨y, ⟨hyL, hyR⟩ , rfl⟩
    rcases lt_trichotomy y c with (hlt | heq | hgt)
    · apply Or.inl ∘ Or.inl
      simp_all only [inter_mem_iff, and_self, Set.mem_image, x, V, W]
      refine ⟨y, hGl_sub ?_,  rfl⟩
      simp_all only [Set.mem_inter_iff, Set.mem_Iio, and_self]
    · apply Or.inr
      rw [heq]
      exact Set.mem_image_of_mem f rfl
    · apply  Or.inl ∘ Or.inr
      apply (Set.mem_image _ _ _).mpr ⟨y, hGr_sub ?_,  rfl⟩
      simp_all only [Set.mem_inter_iff, Set.mem_Ioi, and_self]
  rcases h_loc_bdd with ⟨W, hW_nhds, hW_bdd⟩
  rcases hW_bdd.subset_ball (f c) with ⟨R, h_subset⟩
  have h_far : ∀ᶠ n in atTop, dist (f (t n)) x > R + dist (f c) x := by
    have h_dist_infty : Tendsto (fun n ↦ dist (f (t n)) x) atTop atTop :=
      tendsto_atTop_mono (ht_eq ·) tendsto_natCast_atTop_atTop
    rw [tendsto_atTop_atTop] at h_dist_infty
    rcases h_dist_infty (R + dist (f c) x + 1) with ⟨N, hN⟩
    apply eventually_atTop.2 ⟨N, fun n hn ↦ ?_ ⟩
    specialize hN n hn
    linarith
  have h_inter : (t '' {n | dist (f (t n)) x > R + dist (f c) x} ∩ W).Nonempty :=
    Ultrafilter.nonempty_of_mem (inter_mem (h_map_le_V (image_mem_map h_far)) (hV_le_nhds hW_nhds))
  rcases h_inter with ⟨z, ⟨n, hn_far, rfl⟩, hz_in_W⟩
  have h_close : dist (f (t n)) (f c) < R := h_subset (Set.mem_image_of_mem f hz_in_W)
  have h_tri : dist (f (t n)) x ≤ dist (f (t n)) (f c) + dist (f c) x := dist_triangle _ _ _
  dsimp at hn_far
  linarith
