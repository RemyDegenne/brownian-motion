/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.LeftRightLim

/-! # cadlag functions

-/

@[expose] public section

open Filter TopologicalSpace Bornology
open scoped Topology ENNReal

variable {ι E : Type*} [TopologicalSpace ι]

/-- The predicate that a function is right continuous. -/
abbrev Function.IsRightContinuous [TopologicalSpace E] [Preorder ι] (f : ι → E) :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a

lemma Function.IsRightContinuous.continuous_comp {F : Type*} [TopologicalSpace E]
    [TopologicalSpace F] [Preorder ι] {g : E → F}
    {f : ι → E} (hg : Continuous g) (hf : IsRightContinuous f) : IsRightContinuous (g ∘ f) :=
  fun x ↦ (hg.tendsto (f x)).comp (hf x)

@[simp]
lemma Function.isRightContinuous_const [TopologicalSpace E] [Preorder ι] (c : E) :
    IsRightContinuous (fun _ ↦ c : ι → E) :=
  fun _ ↦ continuousWithinAt_const

/-- A function is cadlag if it is right-continuous and has left limits. -/
structure IsCadlag [TopologicalSpace E] [Preorder ι] (f : ι → E) : Prop where
  right_continuous : Function.IsRightContinuous f
  left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)

/-- A continuous function is càdlàg. -/
lemma Continuous.isCadlag [TopologicalSpace E] [PartialOrder ι] {f : ι → E}
    (hf : Continuous f) : IsCadlag f where
  right_continuous x := (hf.continuousAt (x := x)).continuousWithinAt
  left_limit x := ⟨f x, tendsto_nhdsWithin_of_tendsto_nhds (hf.continuousAt (x := x))⟩

section Jump

/-- The set of left jump times of a function. -/
def leftJumpSet [TopologicalSpace E] [LinearOrder ι] (f : ι → E) : Set ι :=
  {t | f.leftLim t ≠ f t}

/-- For a càdlàg function, the left jump times are exactly its discontinuity points. -/
theorem IsCadlag.leftJumpSet_eq_discontinuitySet [LinearOrder ι] [OrderTopology ι]
    [TopologicalSpace E] [T2Space E] {f : ι → E} (hf : IsCadlag f) :
    leftJumpSet f = {t | ¬ ContinuousAt f t} := by
  ext t
  refine ⟨fun h hc => h (hc.continuousWithinAt.leftLim_eq), fun hc h => hc ?_⟩
  refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, hf.right_continuous t⟩
  simpa [ContinuousWithinAt, h] using tendsto_leftLim_of_tendsto (hf.left_limit t)

/-- The set of large left jump times. -/
def largeLeftJumpSet [TopologicalSpace E] [LinearOrder ι] (f : ι → E)
    (v : Set (E × E)) : Set ι :=
  {t | ⟨f t, f.leftLim t⟩ ∉ v}

/-- The set of large left jump times has no accumulation points. TODO: maybe `to_dual` can be
extended to simplify this proof as the proof of the second part is very similar to the first part.
-/
lemma IsCadlag.not_accPt_largeLeftJumpSet [LinearOrder ι] [OrderTopology ι] [UniformSpace E]
    {f : ι → E} (hf : IsCadlag f) {v : Set (E × E)} (hv : v ∈ uniformity E) (t : ι) :
    ¬ AccPt t (𝓟 (largeLeftJumpSet f v)) := by
  obtain ⟨u, hu, husymm, huv⟩ := comp_comp_symm_mem_uniformity_sets hv
  intro ht
  have hsplit :
    (𝓝[<] t ⊓ 𝓟 (largeLeftJumpSet f v)).NeBot ∨ (𝓝[>] t ⊓ 𝓟 (largeLeftJumpSet f v)).NeBot := by
    simp_all [AccPt, ← nhdsLT_sup_nhdsGT t, inf_comm, inf_sup_left]
  refine hsplit.elim (fun h => ?_) (fun h => ?_)
  · have hnb : (𝓝[<] t).NeBot := h.mono inf_le_left
    rw [← frequently_mem_iff_neBot] at h
    contrapose! h
    have htt : ¬ IsBot t := by
      by_contra
      exact (not_neBot.2 <| nhdsLT_eq_bot_iff.2 (Or.inl this)) hnb
    obtain ⟨a, ha⟩ : ∃ a, a < t := by simpa [IsBot] using htt
    -- There exists `b < t` such that for any `x ∈ Ioo b t`, `f x` is close to `f.leftLim t`.
    obtain ⟨b, hb⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' ha).1 <| (Uniform.tendsto_nhds_left.1
      <| (tendsto_leftLim_of_tendsto (hf.left_limit t))).eventually_mem hu
    -- For any `x ∈ Ioo b t`, there exists `s ∈ Ioc b x` such that `f s` is closed `f.leftLim x`.
    have h2 (x) (hx : x ∈ Set.Ioo b t) : ∃ s, s ∈ Set.Ioc b x ∧ (f s, f.leftLim x) ∈ u := by
      by_cases! hn : (𝓝[<] x).NeBot
      · exact ((eventually_mem_set.2 (Ioc_mem_nhdsLT hx.1)).and <|
          (Uniform.tendsto_nhds_left.1 (tendsto_leftLim_of_tendsto
          (hf.left_limit x))).eventually_mem hu).exists
      · rw [leftLim_eq_of_eq_bot f hn]
        exact ⟨x, ⟨hx.1, refl x⟩, refl_mem_uniformity hu⟩
    refine eventually_of_mem (Ioo_mem_nhdsLT hb.1) fun x hx => ?_
    obtain ⟨s, hs⟩ := h2 x hx
    -- `(f x, f.leftLim t) ∈ u` and `(f s, f.leftLim t) ∈ u` imply that `(f x, s) ∈ u ∘ u`, which
    -- can be used with `(f s, f.leftLim x) ∈ u` to imply that `(f x, f.leftLim x) ∈ u ∘ u ∘ u`.
    simpa [largeLeftJumpSet] using huv <| SetRel.prodMk_mem_comp
      (SetRel.prodMk_mem_comp (hb.2 hx) (SetRel.symm _ (hb.2 ⟨hs.1.1, hs.1.2.trans_lt hx.2⟩))) hs.2
  · -- We use a similar argument to prove this part.
    have hnb : (𝓝[>] t).NeBot := h.mono inf_le_left
    rw [← frequently_mem_iff_neBot] at h
    contrapose! h
    have htt : ¬ IsTop t := by
      by_contra
      exact (not_neBot.2 <| nhdsGT_eq_bot_iff.2 (Or.inl this)) hnb
    obtain ⟨a, ha⟩ : ∃ a, t < a := by simpa [IsTop] using htt
    -- Here one can also use the existence of a right limit instead of right continuity, so this
    -- theorem should also be true for functions with both left and right limits at each point.
    obtain ⟨b, hb⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' ha).1 <|
      (Uniform.continuousWithinAt_iff'_left.1 <| hf.right_continuous t).eventually_mem hu
    have h2 (x) (hx : x ∈ Set.Ioo t b) : ∃ s, s ∈ Set.Ioc t x ∧ (f s, f.leftLim x) ∈ u := by
      by_cases! hn : (𝓝[<] x).NeBot
      · exact ((eventually_mem_set.2 (Ioc_mem_nhdsLT hx.1)).and <| (Uniform.tendsto_nhds_left.1
          (tendsto_leftLim_of_tendsto (hf.left_limit x))).eventually_mem hu).exists
      · rw [leftLim_eq_of_eq_bot f hn]
        exact ⟨x, ⟨hx.1, refl x⟩, refl_mem_uniformity hu⟩
    refine eventually_of_mem (Ioo_mem_nhdsGT hb.1) fun x hx => ?_
    obtain ⟨s, hs⟩ := h2 x hx
    simpa [largeLeftJumpSet] using huv <| SetRel.prodMk_mem_comp
      (SetRel.prodMk_mem_comp (hb.2 hx) (SetRel.symm _ (hb.2 ⟨hs.1.1, hs.1.2.trans_lt hx.2⟩))) hs.2

/-- If `ι` is a compact space, then a càdlàg function has only finitely many large jumps. -/
theorem IsCadlag.finite_largeLeftJumpSet [LinearOrder ι] [OrderTopology ι] [CompactSpace ι]
    [UniformSpace E] {f : ι → E} (hf : IsCadlag f) {v : Set (E × E)} (hv : v ∈ uniformity E) :
    (largeLeftJumpSet f v).Finite := by
  by_contra!
  grind [this.exists_accPt_principal, hf.not_accPt_largeLeftJumpSet hv]

end Jump

lemma IsCadlag.add {E : Type*} [Add E] [TopologicalSpace E] [ContinuousAdd E] [Preorder ι]
    {f g : ι → E} (hf : IsCadlag f)
    (hg : IsCadlag g) : IsCadlag (f + g) := by
  refine ⟨fun i ↦ ContinuousWithinAt.add (hf.1 i) (hg.1 i), fun i ↦ ?_⟩
  obtain ⟨r, hr⟩ := hf.2 i
  obtain ⟨s, hs⟩ := hg.2 i
  exact ⟨r + s, hr.add hs⟩

lemma IsCadlag.const_smul {E : Type*} [SMul ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
    [Preorder ι] {f : ι → E} (hf : IsCadlag f) (r : ℝ) :
    IsCadlag (fun i ↦ r • f i) := by
  refine ⟨fun i ↦ ContinuousWithinAt.const_smul (hf.1 i) r, fun i ↦ ?_⟩
  obtain ⟨l, hl⟩ := hf.2 i
  exact ⟨r • l, hl.const_smul r⟩

/-- A continuous map sends càdlàg paths to càdlàg paths. -/
lemma IsCadlag.continuous_comp {F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [PartialOrder ι]
    {g : E → F} {f : ι → E} (hf : IsCadlag f) (hg : Continuous g) :
    IsCadlag (g ∘ f) := by
  refine ⟨Function.IsRightContinuous.continuous_comp hg hf.right_continuous, fun x ↦ ?_⟩
  obtain ⟨l, hl⟩ := hf.left_limit x
  exact ⟨g l, (hg.tendsto l).comp hl⟩

/-- A càdlàg function is locally bounded. -/
lemma isLocallyBounded_of_isCadlag {E : Type*} [LinearOrder ι] [PseudoMetricSpace E]
    {f : ι → E} (hf : IsCadlag f) (x : ι) : ∃ t ∈ 𝓝 x, IsBounded (f '' t) := by
  obtain ⟨l, hl⟩ := hf.2 x
  obtain ⟨U, ⟨⟨A, ⟨hp, ⟨W, hW⟩⟩⟩, hU⟩⟩ := Metric.exists_isBounded_image_of_tendsto hl
  obtain ⟨V, ⟨⟨B, ⟨hq, ⟨R, hR⟩⟩⟩, hV⟩⟩ := Metric.exists_isBounded_image_of_tendsto (hf.1 x).tendsto
  refine ⟨A ∩ B, inter_mem hp hq, ?_⟩
  apply IsBounded.subset ((hU.union hV).union (isBounded_singleton : Bornology.IsBounded ({f x})))
  rintro _ ⟨y, ⟨hyL, hyR⟩ , rfl⟩
  rcases lt_trichotomy y x with (hlt | heq | hgt)
  · have : y ∈ U := hW.2 ▸ ⟨hyL, hW.1 hlt⟩
    grind
  · grind
  · have : y ∈ V := hR.2 ▸ ⟨hyR, hR.1 hgt⟩
    grind

/-- A càdlàg function maps compact sets to bounded sets. -/
lemma isBounded_image_of_isCadlag_of_isCompact {E : Type*} [LinearOrder ι] [PseudoMetricSpace E]
    {f : ι → E} (hf : IsCadlag f) {s : Set ι} (hs : IsCompact s) :
    IsBounded (f '' s) :=
  isBounded_image_of_isLocallyBounded_of_isCompact hs (isLocallyBounded_of_isCadlag hf)
