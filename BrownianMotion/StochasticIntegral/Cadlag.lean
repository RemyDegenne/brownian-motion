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
abbrev Function.IsRightContinuous [TopologicalSpace E] [PartialOrder ι] (f : ι → E) :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a

lemma Function.IsRightContinuous.continuous_comp {F : Type*} [TopologicalSpace E]
    [TopologicalSpace F] [PartialOrder ι] {g : E → F}
    {f : ι → E} (hg : Continuous g) (hf : IsRightContinuous f) : IsRightContinuous (g ∘ f) :=
  fun x ↦ (hg.tendsto (f x)).comp (hf x)

@[simp]
lemma Function.isRightContinuous_const [TopologicalSpace E] [PartialOrder ι] (c : E) :
    IsRightContinuous (fun _ ↦ c : ι → E) :=
  fun _ ↦ continuousWithinAt_const

/-- A function is cadlag if it is right-continuous and has left limits. -/
structure IsCadlag [TopologicalSpace E] [PartialOrder ι] (f : ι → E) : Prop where
  right_continuous : Function.IsRightContinuous f
  left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)

namespace Function

/-- The set of left jump times of a function. -/
noncomputable def jumpSet [TopologicalSpace E] [LinearOrder ι] (f : ι → E) : Set ι :=
  {t | f.leftLim t ≠ f t}

/-- The set of left jump times whose size is larger than `ε`. -/
noncomputable def largeJumpSet [LinearOrder ι] [PseudoEMetricSpace E] (f : ι → E)
    (ε : ℝ≥0∞) : Set ι :=
  {t | ε < edist (f.leftLim t) (f t)}

omit [TopologicalSpace ι] in
@[simp]
lemma leftLim_bot [TopologicalSpace E] [LinearOrder ι] [OrderBot ι] (f : ι → E) :
    f.leftLim (⊥ : ι) = f ⊥ :=
  leftLim_eq_of_isBot (show IsBot (⊥ : ι) from fun _ ↦ bot_le)

omit [TopologicalSpace ι] in
@[simp]
lemma bot_notMem_jumpSet [TopologicalSpace E] [LinearOrder ι] [OrderBot ι] (f : ι → E) :
    (⊥ : ι) ∉ jumpSet f := by
  simp [jumpSet]

end Function

lemma IsCadlag.tendsto_leftLim [TopologicalSpace E] [LinearOrder ι] [OrderTopology ι]
    {f : ι → E} (hf : IsCadlag f) (t : ι) :
    Tendsto f (𝓝[<] t) (𝓝 (f.leftLim t)) :=
  tendsto_leftLim_of_tendsto (hf.left_limit t)

/-- For a càdlàg function, the left-limit function tends to the current value from the right. -/
lemma IsCadlag.tendsto_leftLim_nhdsGT [TopologicalSpace E] [LinearOrder ι] [OrderTopology ι]
    [T3Space E]
    {f : ι → E} (hf : IsCadlag f) (t : ι) :
    Tendsto f.leftLim (𝓝[>] t) (𝓝 (f t)) := by
  rcases eq_or_neBot (𝓝[>] t) with hbot | hne
  · simp [hbot]
  haveI : NeBot (𝓝[>] t) := hne
  obtain ⟨u₀, hu₀⟩ : (Set.Ioi t).Nonempty :=
    Filter.nonempty_of_mem (self_mem_nhdsWithin (a := t))
  apply (closed_nhds_basis (f t)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, htu, hu⟩ : ∃ u, t < u ∧ Set.Ioo t u ⊆ {x | f x ∈ s} := by
    have hs : {x | f x ∈ s} ∈ 𝓝[>] t := (hf.right_continuous t).tendsto s_mem
    simpa using (mem_nhdsGT_iff_exists_Ioo_subset' hu₀).1 hs
  filter_upwards [Ioo_mem_nhdsGT htu] with c hc
  rcases eq_or_neBot (𝓝[<] c) with hc_bot | _hc_ne
  · simpa [hc_bot, leftLim_eq_of_eq_bot] using hu hc
  apply s_closed.mem_of_tendsto (tendsto_leftLim_of_tendsto (hf.left_limit c))
  filter_upwards [Ioo_mem_nhdsLT_of_mem ⟨hc.1, hc.2.le⟩] with d hd using hu hd

lemma IsCadlag.tendsto_edist_leftLim_self_nhdsLT [LinearOrder ι] [OrderTopology ι]
    [PseudoEMetricSpace E] [T3Space E] {f : ι → E} (hf : IsCadlag f) (t : ι) :
    Tendsto (fun s ↦ edist (f.leftLim s) (f s)) (𝓝[<] t) (𝓝 0) := by
  have hleft : Tendsto f.leftLim (𝓝[<] t) (𝓝 (f.leftLim t)) :=
    (continuousWithinAt_leftLim_Iic (hf.tendsto_leftLim t)).tendsto.mono_left
      (nhdsWithin_mono _ Set.Iio_subset_Iic_self)
  simpa using Filter.Tendsto.edist hleft (hf.tendsto_leftLim t)

lemma IsCadlag.tendsto_edist_leftLim_self_nhdsGT [LinearOrder ι] [OrderTopology ι]
    [PseudoEMetricSpace E] [T3Space E] {f : ι → E} (hf : IsCadlag f) (t : ι) :
    Tendsto (fun s ↦ edist (f.leftLim s) (f s)) (𝓝[>] t) (𝓝 0) := by
  simpa using Filter.Tendsto.edist (hf.tendsto_leftLim_nhdsGT t)
    (hf.right_continuous t).tendsto

lemma IsCadlag.tendsto_edist_leftLim_self_nhdsNE [LinearOrder ι] [OrderTopology ι]
    [PseudoEMetricSpace E] [T3Space E] {f : ι → E} (hf : IsCadlag f) (t : ι) :
    Tendsto (fun s ↦ edist (f.leftLim s) (f s)) (𝓝[≠] t) (𝓝 0) := by
  rw [← nhdsLT_sup_nhdsGT t]
  exact (hf.tendsto_edist_leftLim_self_nhdsLT t).sup
    (hf.tendsto_edist_leftLim_self_nhdsGT t)

lemma IsCadlag.not_accPt_largeJumpSet [LinearOrder ι] [OrderTopology ι]
    [PseudoEMetricSpace E] [T3Space E] {f : ι → E} (hf : IsCadlag f)
    {ε : ℝ≥0∞} (hε : 0 < ε) (t : ι) :
    ¬ AccPt t (𝓟 (Function.largeJumpSet f ε)) := by
  intro hacc
  letI : NeBot (𝓝[≠] t ⊓ 𝓟 (Function.largeJumpSet f ε)) := hacc
  have hsmall : ∀ᶠ s in 𝓝[≠] t ⊓ 𝓟 (Function.largeJumpSet f ε),
      edist (f.leftLim s) (f s) < ε :=
    ((hf.tendsto_edist_leftLim_self_nhdsNE t).mono_left inf_le_left).eventually
      (Iio_mem_nhds hε)
  have hlarge : ∀ᶠ s in 𝓝[≠] t ⊓ 𝓟 (Function.largeJumpSet f ε),
      ε < edist (f.leftLim s) (f s) := by
    filter_upwards
      [show Function.largeJumpSet f ε ∈ 𝓝[≠] t ⊓ 𝓟 (Function.largeJumpSet f ε) from
        mem_inf_of_right (by simp)]
      with s hs
    exact hs
  obtain ⟨s, hs_large, hs_small⟩ := (hlarge.and hsmall).exists
  exact (not_lt_of_ge hs_small.le) hs_large

/-- On a compact bounded order, a càdlàg function has only finitely many jumps larger than
any fixed positive threshold. -/
theorem IsCadlag.finite_largeJumpSet [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] [CompactIccSpace ι] [PseudoEMetricSpace E] [T3Space E]
    {f : ι → E} (hf : IsCadlag f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    (Function.largeJumpSet f ε).Finite := by
  by_contra hfinite
  have hinfinite : (Function.largeJumpSet f ε).Infinite := hfinite
  have hcompact : IsCompact (Set.univ : Set ι) := by
    simpa [Set.Icc] using (isCompact_Icc (a := (⊥ : ι)) (b := (⊤ : ι)))
  obtain ⟨t, _ht_mem, ht⟩ :=
    hinfinite.exists_accPt_of_subset_isCompact hcompact (Set.subset_univ _)
  exact hf.not_accPt_largeJumpSet hε t ht

namespace Monotone

/-- A monotone function into a second-countable conditionally complete linear order has only
countably many left jumps. -/
theorem countable_jumpSet {β : Type*} [LinearOrder ι] [OrderTopology ι]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [SecondCountableTopology β] {f : ι → β} (hf : Monotone f) :
    (Function.jumpSet f).Countable := by
  refine hf.countable_not_continuousAt.mono ?_
  intro x hx hcont
  have hleft : ContinuousWithinAt f (Set.Iio x) x := hcont.continuousWithinAt
  exact hx (hf.continuousWithinAt_Iio_iff_leftLim_eq.1 hleft)

end Monotone

/-- A monotone càdlàg function into a second-countable conditionally complete linear order has
only countably many left jumps. -/
theorem IsCadlag.countable_jumpSet_of_monotone {β : Type*} [LinearOrder ι] [OrderTopology ι]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [SecondCountableTopology β] {f : ι → β} (_hf : IsCadlag f) (hmono : Monotone f) :
    (Function.jumpSet f).Countable :=
  hmono.countable_jumpSet

lemma IsCadlag.add {E : Type*} [Add E] [TopologicalSpace E] [ContinuousAdd E] [PartialOrder ι]
    {f g : ι → E} (hf : IsCadlag f)
    (hg : IsCadlag g) : IsCadlag (f + g) := by
  refine ⟨fun i ↦ ContinuousWithinAt.add (hf.1 i) (hg.1 i), fun i ↦ ?_⟩
  obtain ⟨r, hr⟩ := hf.2 i
  obtain ⟨s, hs⟩ := hg.2 i
  exact ⟨r + s, hr.add hs⟩

lemma IsCadlag.const_smul {E : Type*} [SMul ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
    [PartialOrder ι] {f : ι → E} (hf : IsCadlag f) (r : ℝ) :
    IsCadlag (fun i ↦ r • f i) := by
  refine ⟨fun i ↦ ContinuousWithinAt.const_smul (hf.1 i) r, fun i ↦ ?_⟩
  obtain ⟨l, hl⟩ := hf.2 i
  exact ⟨r • l, hl.const_smul r⟩

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
