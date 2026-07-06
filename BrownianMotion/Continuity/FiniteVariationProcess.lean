/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BrownianMotion.Auxiliary.ContinuousBilinForm
public import BrownianMotion.Auxiliary.Filtration
public import BrownianMotion.Choquet.Debut
public import BrownianMotion.StochasticIntegral.LocalMartingale
public import BrownianMotion.StochasticIntegral.Locally
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Finite-Variation Processes

This file shows that a continuous local martingale of locally finite variation is almost surely
constant.

## Main definitions

* `FiniteOpenCover`: finite covers of a set by open sets, preordered by refinement.
* `IccPartition`: finite ordered partitions of an interval `[a, b]`.
* `FiniteOpenCover.iccPartition`: a partition of `[a, b]` subordinate to a finite open cover.

## Main results

* `MeasureTheory.Martingale.integral_inner_sub_sub_self_eq_zero`: the squared increment of a
  continuous martingale of uniformly bounded variation has zero expectation.
* `MeasureTheory.Martingale.ae_eq_of_continuousOn_of_eVariationOn_le`: a continuous martingale of
  uniformly bounded variation is almost surely constant on `[a, b]`.
-/

@[expose] public section

open Filter MeasureTheory Finset Set TopologicalSpace ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace Topology

variable {ι Ω E : Type*}

/-! ### The type of finite open covers and its `atTop` filter -/

section

/-- A finite cover of a set `s` by open sets. -/
structure FiniteOpenCover (α : Type*) [TopologicalSpace α] (s : Set α) where
  /-- The finite set of open sets forming the cover. -/
  carrier : Finset (Opens α)
  /-- The open sets cover `s`. -/
  cover : s ⊆ ⋃ i ∈ carrier, i

variable {α : Type*} [TopologicalSpace α] {s : Set α}

instance : SetLike (FiniteOpenCover α s) (Opens α) where
  coe := fun C ↦ C.carrier
  coe_injective := fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by simpa using Finset.coe_injective h

namespace FiniteOpenCover

instance : Preorder (FiniteOpenCover α s) where
  -- `C ≤ D` iff `D` is a refinement of `C`.
  le C D := ∀ U ∈ D, ∃ V ∈ C, U ≤ V
  le_refl C U hU := ⟨U, hU, le_rfl⟩
  le_trans C D E hCD hDE U hU := by
    obtain ⟨V, hV, hUV⟩ := hDE U hU
    obtain ⟨W, hW, hVW⟩ := hCD V hV
    exact ⟨W, hW, hUV.trans hVW⟩

instance : Nonempty (FiniteOpenCover α s) := ⟨⟨{⊤}, by simp⟩⟩

instance : IsDirected (FiniteOpenCover α s) (· ≤ ·) := by
  classical
  refine ⟨fun B D ↦ ⟨⟨(B.carrier ×ˢ D.carrier).image fun p ↦ p.1 ⊓ p.2, fun x hx ↦ ?_⟩,
    fun W hW ↦ ?_, fun W hW ↦ ?_⟩⟩
  · obtain ⟨U, hU, hxU⟩ := mem_iUnion₂.1 (B.cover hx)
    obtain ⟨V, hV, hxV⟩ := mem_iUnion₂.1 (D.cover hx)
    exact mem_iUnion₂.2 ⟨U ⊓ V, mem_image.2 ⟨(U, V), mem_product.2 ⟨hU, hV⟩, rfl⟩, hxU, hxV⟩
  · obtain ⟨⟨U, V⟩, hUV, rfl⟩ := mem_image.1 hW
    exact ⟨U, (mem_product.1 hUV).1, inf_le_left⟩
  · obtain ⟨⟨U, V⟩, hUV, rfl⟩ := mem_image.1 hW
    exact ⟨V, (mem_product.1 hUV).2, inf_le_right⟩

theorem hasCountableBasis_atTop [SecondCountableTopology α] (hc : IsCompact s) :
    HasCountableBasis (atTop : Filter (FiniteOpenCover α s))
      (fun C ↦ ∀ U ∈ C, U.1 ∈ countableBasis α) Ici where
  mem_iff' t := by
    refine ⟨fun ht => ?_, fun ⟨C, _, hC⟩ => mem_of_superset (Ici_mem_atTop C) hC⟩
    obtain ⟨C₀, hC₀⟩ := mem_atTop_sets.1 ht
    have hVB (x) (hx : x ∈ s) : ∃ B ∈ countableBasis α, ∃ V ∈ C₀, x ∈ B ∧ B ⊆ V := by
      obtain ⟨V, hV, hxV⟩ := mem_iUnion₂.1 (C₀.cover hx)
      obtain ⟨B, hB, hxB, hBV⟩ :=
        (isBasis_countableBasis α).exists_subset_of_mem_open hxV V.2
      exact ⟨B, hB, V, hV, hxB, hBV⟩
    choose! B hBmem V hVmem hxB hBV using hVB
    obtain ⟨T, hT⟩ := hc.elim_finite_subcover (fun x : s ↦ B x)
      (fun x ↦ isOpen_of_mem_countableBasis (hBmem x x.2))
      (fun y hy ↦ mem_iUnion.2 ⟨⟨y, hy⟩, hxB y hy⟩)
    classical
    refine ⟨⟨T.image fun x : s ↦ ⟨B x, isOpen_of_mem_countableBasis (hBmem x x.2)⟩,
      fun y hy ↦ ?_⟩, fun U hU ↦ ?_, fun D hD ↦ hC₀ D (le_trans (fun U hU ↦ ?_) hD)⟩
    · obtain ⟨x, hxT, hyB⟩ := mem_iUnion₂.1 (hT hy)
      exact mem_iUnion₂.2 ⟨_, mem_image_of_mem _ hxT, hyB⟩
    · obtain ⟨x, _, rfl⟩ := mem_image.1 hU
      exact hBmem x x.2
    · obtain ⟨x, _, rfl⟩ := mem_image.1 hU
      exact ⟨V x, hVmem x x.2, hBV x x.2⟩
  countable := by
    have h1 : {U : Opens α | U.1 ∈ countableBasis α}.Countable :=
      (countable_countableBasis α).preimage SetLike.coe_injective
    apply countable_of_injective_of_countable_image
    · exact fun _ _ _ _ h ↦ SetLike.coe_injective h
    · refine (countable_setOf_finite_subset h1).mono ?_
      rintro _ ⟨C, hC, rfl⟩
      exact ⟨C.carrier.finite_toSet, hC⟩

theorem isCountablyGenerated_atTop [SecondCountableTopology α] (hc : IsCompact s) :
    IsCountablyGenerated (atTop : Filter (FiniteOpenCover α s)) :=
  (hasCountableBasis_atTop hc).isCountablyGenerated

instance [SecondCountableTopology α] [Preorder α] [CompactIccSpace α] {a b : α} :
    IsCountablyGenerated (atTop : Filter (FiniteOpenCover α (Set.Icc a b))) :=
  isCountablyGenerated_atTop isCompact_Icc

end FiniteOpenCover

end

/-! ### Existence of an `IccPartition` subordinate to a finite open cover -/

section

/-- A finite ordered partition of `[a, b]` in an ordered space. -/
structure IccPartition (ι : Type*) [Preorder ι] (a b : ι) where
  /-- The number of subintervals of the partition. -/
  card : ℕ
  /-- The ordered partition points. -/
  point : ℕ → ι
  /-- The first partition point is the left endpoint. -/
  left_eq : point 0 = a
  /-- The last partition point is the right endpoint. -/
  right_eq : point card = b
  /-- The partition points are monotone. -/
  mono : Monotone point
  /-- All partition points lie in the interval. -/
  point_mem_Icc i : point i ∈ Set.Icc a b

namespace IccPartition

/-- The unique partition of the degenerate interval `[a, a]`. -/
def refl [Preorder ι] (a : ι) : IccPartition ι a a where
  card := 1
  point _ := a
  left_eq := rfl
  right_eq := rfl
  mono _ _ _ := le_rfl
  point_mem_Icc _ := ⟨le_rfl, le_rfl⟩

/-- The trivial partition of an interval `[a, b]`. -/
def trivial [Preorder ι] {a b : ι} (hab : a ≤ b) : IccPartition ι a b where
  card := 1
  point i := if i = 0 then a else b
  left_eq := rfl
  right_eq := rfl
  mono _ _ := by grind
  point_mem_Icc _ := by grind

/-- If `b ≤ c`, then a partition of `[a, b]` extends to a partition of `[a, c]`. -/
def extend [Preorder ι] {a b c : ι} (π : IccPartition ι a b) (hbc : b ≤ c) :
    IccPartition ι a c where
  card := π.card + 1
  point n := if n ≤ π.card then π.point n else c
  left_eq := by simpa using π.left_eq
  right_eq := by simp
  mono i j h := by
    by_cases hj : j ≤ π.card
    · have hi : i ≤ π.card := h.trans hj
      simpa [hi, hj] using π.mono h
    · by_cases hi : i ≤ π.card
      · simp [hi, hj, (π.point_mem_Icc i).2.trans hbc]
      · simp [hi, hj]
  point_mem_Icc n := by
    have hab : a ≤ b := π.left_eq ▸ (π.point_mem_Icc 0).2
    by_cases h : n ≤ π.card
    · simpa [h] using ⟨(π.point_mem_Icc n).1, (π.point_mem_Icc n).2.trans hbc⟩
    · simp [h, hab.trans hbc]

end IccPartition

/-- If `[x, y]` lies in an element of the cover and there is a subordinate partition of `[a, x]`,
then there is a subordinate partition of `[a, y]`. -/
theorem exists_iccPartition_extend [Preorder ι] [TopologicalSpace ι] {a b x y : ι}
    {C : FiniteOpenCover ι (Set.Icc a b)} (hxy : x ≤ y) {U : Opens ι} (hUC : U ∈ C)
    (hU : Icc x y ⊆ U)
    (hR : ∃ π : IccPartition ι a x, ∀ n, ∃ V ∈ C, Set.Icc (π.point n) (π.point (n + 1)) ⊆ V) :
    ∃ π : IccPartition ι a y, ∀ n, ∃ V ∈ C, Set.Icc (π.point n) (π.point (n + 1)) ⊆ V := by
  obtain ⟨π, hπ⟩ := hR
  refine ⟨π.extend hxy, fun n ↦ ?_⟩
  rcases lt_trichotomy n π.card with hn | hn | hn
  · obtain ⟨V, hVC, hV⟩ := hπ n
    exact ⟨V, hVC, by simpa [IccPartition.extend, hn, hn.le] using hV⟩
  · exact ⟨U, hUC, by simpa [IccPartition.extend, hn, π.right_eq] using hU⟩
  · grind [IccPartition.extend]

/-- Any finite open cover of `[a, b]` is subordinate to some partition of `[a, b]`: each
subinterval of the partition is contained in an element of the cover. -/
theorem FiniteOpenCover.exists_iccPartition [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] {a b : ι} (hab : a ≤ b)
    (C : FiniteOpenCover ι (Set.Icc a b)) :
    ∃ π : IccPartition ι a b, ∀ n, ∃ U ∈ C, Set.Icc (π.point n) (π.point (n + 1)) ⊆ U := by
  let R : Set ι := {x | ∃ π : IccPartition ι a x,
    ∀ n, ∃ U ∈ C, Set.Icc (π.point n) (π.point (n + 1)) ⊆ U}
  obtain ⟨Ua, hUaC, haUa⟩ := Set.mem_iUnion₂.mp (C.cover (Set.left_mem_Icc.2 hab))
  have haR : a ∈ R := by
    refine ⟨IccPartition.refl a, fun n ↦ ⟨Ua, hUaC, ?_⟩⟩
    simpa [IccPartition.refl, Set.Icc_self] using haUa
  have hR_step : ∀ x ∈ closure R, x ∈ Set.Icc a b → ∀ y, x < y → y ≤ b →
      ∃ w ∈ R, w ∈ Set.Ioc x y := by
    intro x hx hxab y hxy hyb
    obtain ⟨U, hUC, hxU⟩ := Set.mem_iUnion₂.mp (C.cover hxab)
    have hU_nhds : (U : Set ι) ∈ 𝓝 x := U.isOpen.mem_nhds hxU
    obtain ⟨u, hu, hIcoU⟩ := exists_Ico_subset_of_mem_nhds' hU_nhds hxy
    obtain ⟨w, hxw, hwu⟩ := exists_between hu.1
    have hIccw : Set.Icc x w ⊆ (U : Set ι) := fun t ht ↦ hIcoU ⟨ht.1, ht.2.trans_lt hwu⟩
    rcases hxab.1.eq_or_lt with hax | hax
    · subst hax
      exact ⟨w, exists_iccPartition_extend hxw.le hUC hIccw haR, hxw, hwu.le.trans hu.2⟩
    · obtain ⟨l, hl, hIocU⟩ := exists_Ioc_subset_of_mem_nhds' hU_nhds hax
      obtain ⟨z, hzmem, hzR⟩ := mem_closure_iff_nhds.mp hx _ (Ioo_mem_nhds hl.2 hxw)
      have hsub : Set.Icc z w ⊆ (U : Set ι) := by
        intro t ht
        rcases le_total t x with htx | hxt
        · exact hIocU ⟨hzmem.1.trans_le ht.1, htx⟩
        · exact hIcoU ⟨hxt, ht.2.trans_lt hwu⟩
      exact ⟨w, exists_iccPartition_extend hzmem.2.le hUC hsub hzR, hxw, hwu.le.trans hu.2⟩
  have hclosure : Set.Icc a b ⊆ closure R ∩ Set.Icc a b := by
    refine ((isClosed_closure.inter isClosed_Icc).inter isClosed_Icc).Icc_subset_of_forall_exists_gt
      ⟨subset_closure haR, left_mem_Icc.2 hab⟩ fun x hx y hy ↦ ?_
    obtain ⟨⟨hxcl, hxab⟩, hxIco⟩ := hx
    obtain ⟨w, hwR, hw⟩ := hR_step x hxcl hxab (min y b) (lt_min hy hxIco.2) (min_le_right y b)
    exact ⟨w, ⟨subset_closure hwR, hxab.1.trans hw.1.le, hw.2.trans (min_le_right y b)⟩,
      hw.1, hw.2.trans (min_le_left y b)⟩
  rcases hab.eq_or_lt with hab' | hab'
  · subst hab'
    exact haR
  · obtain ⟨U, hUC, hbU⟩ := Set.mem_iUnion₂.mp (C.cover (Set.right_mem_Icc.2 hab))
    have hU_nhds : (U : Set ι) ∈ 𝓝 b := U.isOpen.mem_nhds hbU
    obtain ⟨l, hl, hIocU⟩ := exists_Ioc_subset_of_mem_nhds' hU_nhds hab'
    have hlcl := hclosure ⟨hl.1, hl.2.le⟩
    obtain ⟨y, hyR, hy⟩ := hR_step l hlcl.1 hlcl.2 b hl.2 le_rfl
    have hsub : Set.Icc y b ⊆ (U : Set ι) := fun t ht ↦ hIocU ⟨hy.1.trans_le ht.1, ht.2⟩
    exact exists_iccPartition_extend hy.2 hUC hsub hyR

/-- A partition of `[a, b]` subordinate to a given finite open cover. -/
noncomputable def FiniteOpenCover.iccPartition [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] {a b : ι} (hab : a ≤ b)
    (C : FiniteOpenCover ι (Set.Icc a b)) : IccPartition ι a b :=
  (C.exists_iccPartition hab).choose

theorem FiniteOpenCover.iccPartition_spec [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] {a b : ι} (hab : a ≤ b)
    (C : FiniteOpenCover ι (Set.Icc a b)) (n : ℕ) :
    ∃ U ∈ C, Set.Icc ((C.iccPartition hab).point n) ((C.iccPartition hab).point (n + 1)) ⊆ U :=
  (C.exists_iccPartition hab).choose_spec n

/-- If `f` is continuous on a compact set `s`, then there is a finite open cover `C` of `s` such
that for each `U` in `C`, the values of `f` at any two points of `U ∩ s` are `v`-close. -/
theorem ContinuousOn.exists_finiteOpenCover_mem_uniformity [TopologicalSpace ι] {f : ι → E}
    [UniformSpace E] {s : Set ι} (hc : IsCompact s) (hf : ContinuousOn f s) {v : Set (E × E)}
    (hv : v ∈ uniformity E) :
    ∃ C : FiniteOpenCover ι s, ∀ U ∈ C, ∀ᵉ (x ∈ U.1 ∩ s) (y ∈ U.1 ∩ s), (f x, f y) ∈ v := by
  obtain ⟨w, hw, hsymm, hww⟩ := comp_symm_mem_uniformity_sets hv
  have key (x : s) : ∃ V : Opens ι, x.1 ∈ V ∧ ∀ y ∈ V.1 ∩ s, (f x, f y) ∈ w := by
    obtain ⟨V, hVopen, hxV, hVsub⟩ :=
      mem_nhdsWithin.1 (hf x x.2 (UniformSpace.ball_mem_nhds (f x) hw))
    exact ⟨⟨V, hVopen⟩, hxV, hVsub⟩
  choose V hxV hVw using key
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x : s ↦ (V x : Set ι))
    (fun x ↦ (V x).isOpen) fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  classical
  refine ⟨⟨t.image V, fun x hx ↦ ?_⟩, fun U hU x hx y hy ↦ ?_⟩
  · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
    exact mem_iUnion₂.2 ⟨V i, mem_image_of_mem V hi, hxi⟩
  · obtain ⟨i, _, rfl⟩ := mem_image.1 hU
    exact hww (SetRel.prodMk_mem_comp (SetRel.symm w (hVw i x hx)) (hVw i y hy))

/-- If `f` is continuous on a compact set `s`, then there is a finite open cover `C` of `s` such
that `f` has oscillation at most `ε` on `U ∩ s` for each `U` in `C`. -/
theorem ContinuousOn.exists_finiteOpenCover_edist_lt [TopologicalSpace ι] {f : ι → E}
    [PseudoEMetricSpace E] {s : Set ι} (hc : IsCompact s) (hf : ContinuousOn f s) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ C : FiniteOpenCover ι s, ∀ U ∈ C, ∀ᵉ (x ∈ U.1 ∩ s) (y ∈ U.1 ∩ s), edist (f x) (f y) < ε :=
  hf.exists_finiteOpenCover_mem_uniformity hc (edist_mem_uniformity hε)

/-- The largest difference of `f` at adjacent points of a finite ordered partition. -/
noncomputable def partitionOsc [Preorder ι] [PseudoEMetricSpace E] (f : ι → E)
    {a b : ι} (π : IccPartition ι a b) : ℝ≥0∞ :=
  ⨆ i, edist (f (π.point (i + 1))) (f (π.point i))

/-- Along the filter of ever finer finite open covers of `[a, b]`, the partition oscillation of a
function continuous on `[a, b]` tends to zero. -/
theorem ContinuousOn.tendsto_partitionOsc_atTop_nhds_zero [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] {a b : ι} (hab : a ≤ b) {f : ι → E}
    [PseudoEMetricSpace E] (hf : ContinuousOn f (Set.Icc a b)) :
    Tendsto (fun C : FiniteOpenCover ι (Set.Icc a b) ↦ partitionOsc f (C.iccPartition hab))
      atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  obtain ⟨C₀, hC₀⟩ := hf.exists_finiteOpenCover_edist_lt isCompact_Icc hε
  filter_upwards [Ici_mem_atTop C₀] with D hD
  set π := D.iccPartition hab with hπ
  refine iSup_le fun i ↦ ?_
  obtain ⟨U, hU, hsub⟩ := D.iccPartition_spec hab i
  obtain ⟨V, hV, hUV⟩ := hD U hU
  have hUV' : U.1 ⊆ V := SetLike.coe_subset_coe.2 hUV
  refine (hC₀ V hV _ ?_ _ ?_).le
  · exact ⟨hUV' (hsub ⟨π.mono i.le_succ, le_rfl⟩), π.point_mem_Icc (i + 1)⟩
  · exact ⟨hUV' (hsub ⟨le_rfl, π.mono i.le_succ⟩), π.point_mem_Icc i⟩

end

/-! ### Continuous martingales of uniformly bounded variation are constant -/

section

variable {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The difference of a process at two adjacent points in a partition. -/
def partitionDiff [Preorder ι] [AddCommGroup E] (X : ι → Ω → E) {a b : ι}
    (π : IccPartition ι a b) (i : ℕ) : Ω → E :=
  X (π.point (i + 1)) - X (π.point i)

theorem sub_eq_sum_partitionDiff [Preorder ι] [AddCommGroup E] (X : ι → Ω → E) {a b : ι}
    (π : IccPartition ι a b) :
    X b - X a = ∑ i ∈ range π.card, partitionDiff X π i :=
  calc
    X b - X a = X (π.point π.card) - X (π.point 0) := by rw [π.right_eq, π.left_eq]
    _ = ∑ i ∈ range π.card, (X (π.point (i + 1)) - X (π.point i)) :=
      (sum_range_sub (fun i ↦ X (π.point i)) π.card).symm
    _ = ∑ i ∈ range π.card, partitionDiff X π i := rfl

theorem inner_sub_eq_sum_inner_partitionDiff [Preorder ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : ι → Ω → E) {a b : ι} (π : IccPartition ι a b) (ω : Ω) :
    ⟪X b ω - X a ω, X b ω - X a ω⟫_ℝ =
      ∑ i ∈ range π.card, ∑ j ∈ range π.card, ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ := by
  have hsum : X b ω - X a ω = ∑ i ∈ range π.card, partitionDiff X π i ω := by
    simpa using congrFun (sub_eq_sum_partitionDiff X π) ω
  simp_rw [hsum, sum_inner, inner_sum]

/-- Pull-out property for conditional expectation with a Hilbert-space inner product. -/
theorem condExp_inner_of_stronglyMeasurable_left [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f g : Ω → E} (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (fun ω ↦ ⟪f ω, g ω⟫_ℝ) μ) (hg : Integrable g μ) :
    μ[fun ω ↦ ⟪f ω, g ω⟫_ℝ | m] =ᵐ[μ] fun ω ↦ ⟪f ω, μ[g | m] ω⟫_ℝ :=
  condExp_bilin_of_aestronglyMeasurable_left (ContinuousBilinForm.inner E)
    hf.aestronglyMeasurable hfg hg

/-- Increments of a martingale over disjoint ordered intervals are orthogonal in expectation. -/
theorem MeasureTheory.Martingale.integral_inner_sub_sub_eq_zero [Preorder ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration μ 𝓕] (hX : Martingale X 𝓕 μ) {a b c d : ι} (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) :
    ∫ ω, ⟪X b ω - X a ω, X d ω - X c ω⟫_ℝ ∂μ = 0 := by
  by_cases hfg : Integrable (fun ω ↦ ⟪X b ω - X a ω, X d ω - X c ω⟫_ℝ) μ
  · suffices hcond_inner : μ[fun ω ↦ ⟪X b ω - X a ω, X d ω - X c ω⟫_ℝ | 𝓕 c] =ᵐ[μ] 0 from by
      rw [← integral_condExp (𝓕.le c)]
      exact integral_eq_zero_of_ae hcond_inner
    calc
      _ =ᵐ[μ] fun ω ↦ ⟪X b ω - X a ω, μ[X d - X c | 𝓕 c] ω⟫_ℝ := by
        refine condExp_inner_of_stronglyMeasurable_left ?_ hfg ?_
        · exact ((hX.stronglyMeasurable b).mono (𝓕.mono hbc)).sub
            ((hX.stronglyMeasurable a).mono (𝓕.mono (hab.trans hbc)))
        · exact (hX.integrable d).sub (hX.integrable c)
      _ =ᵐ[μ] 0 := by
        filter_upwards [condExp_sub (hX.integrable d) (hX.integrable c) (𝓕 c),
          (hX.condExp_ae_eq hcd).sub (hX.condExp_ae_eq (le_refl c))] with ω hp hq
        simp [hp, hq]
  · exact integral_undef hfg

/-- Partition differences of a martingale along ordered partition points are orthogonal in
expectation. -/
theorem MeasureTheory.Martingale.integral_inner_partitionDiff_eq_zero [Preorder ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {X : ι → Ω → E}
    {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕] (hX : Martingale X 𝓕 μ) {a b : ι}
    (π : IccPartition ι a b) (i j : ℕ) (hij : i < j) :
    ∫ ω, ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ ∂μ = 0 :=
  hX.integral_inner_sub_sub_eq_zero (π.mono i.le_succ) (π.mono hij) (π.mono j.le_succ)

section -- Estimate, Inequalities, Integrability

/-- The quadratic sum along a partition is at most the total variation times the partition
oscillation. -/
theorem ofReal_sum_inner_partitionDiff_le_eVariationOn_mul_partitionOsc [LinearOrder ι]
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] (X : ι → Ω → E) {a b : ι}
    (π : IccPartition ι a b) (ω : Ω) :
    ENNReal.ofReal (∑ i ∈ range π.card, ⟪partitionDiff X π i ω, partitionDiff X π i ω⟫_ℝ) ≤
      eVariationOn (X · ω) (Icc a b) * partitionOsc (X · ω) π := by
  calc
    ENNReal.ofReal (∑ i ∈ range π.card, ⟪partitionDiff X π i ω, partitionDiff X π i ω⟫_ℝ)
      = ∑ i ∈ range π.card, edist (X (π.point (i + 1)) ω) (X (π.point i) ω) ^ 2 := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ real_inner_self_nonneg]
        congr with i
        simp [partitionDiff, edist_eq_enorm_sub]
    _ ≤ ∑ i ∈ range π.card,
          edist (X (π.point (i + 1)) ω) (X (π.point i) ω) * partitionOsc (X · ω) π := by
        simp only [sq]
        gcongr with i hi
        exact le_iSup (fun i ↦ edist (X (π.point (i + 1)) ω) (X (π.point i) ω)) i
    _ = (∑ i ∈ range π.card, edist (X (π.point (i + 1)) ω) (X (π.point i) ω)) *
          partitionOsc (X · ω) π := (sum_mul ..).symm
    _ ≤ eVariationOn (X · ω) (Icc a b) * partitionOsc (X · ω) π :=
        mul_le_mul_left (eVariationOn.sum_le π.mono fun i ↦ π.point_mem_Icc i) _

theorem partitionOsc_le_eVariationOn [LinearOrder ι] [PseudoEMetricSpace E] (X : ι → Ω → E)
    {a b : ι} (π : IccPartition ι a b) (ω : Ω) :
    partitionOsc (X · ω) π ≤ eVariationOn (X · ω) (Icc a b) :=
  iSup_le fun i ↦ eVariationOn.edist_le _ (π.point_mem_Icc (i + 1)) (π.point_mem_Icc i)

/-- The quadratic sum along a partition is at most the squared total variation. -/
theorem ofReal_sum_inner_partitionDiff_le_eVariationOn_sq [LinearOrder ι]
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] (X : ι → Ω → E) {a b : ι}
    (π : IccPartition ι a b) (ω : Ω) :
    ENNReal.ofReal (∑ i ∈ range π.card, ⟪partitionDiff X π i ω, partitionDiff X π i ω⟫_ℝ) ≤
      eVariationOn (X · ω) (Icc a b) ^ 2 :=
  calc
    _ ≤ eVariationOn (X · ω) (Icc a b) * partitionOsc (X · ω) π :=
        ofReal_sum_inner_partitionDiff_le_eVariationOn_mul_partitionOsc X π ω
    _ ≤ eVariationOn (X · ω) (Icc a b) * eVariationOn (X · ω) (Icc a b) :=
        mul_le_mul_right (partitionOsc_le_eVariationOn X π ω) _
    _ = eVariationOn (X · ω) (Icc a b) ^ 2 := (sq _).symm

/-- The quadratic sum along a partition of a process of bounded variation is almost surely
bounded. -/
theorem ae_sum_inner_partitionDiff_le_sq [LinearOrder ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {X : ι → Ω → E} {a b : ι} (π : IccPartition ι a b) {C : ℝ≥0}
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    ∀ᵐ ω ∂μ, ∑ i ∈ range π.card, ⟪partitionDiff X π i ω, partitionDiff X π i ω⟫_ℝ ≤ C ^ 2 := by
  filter_upwards [hfv] with ω hω
  rw [← NNReal.coe_pow C 2, ← ENNReal.ofReal_le_coe]
  exact (ofReal_sum_inner_partitionDiff_le_eVariationOn_sq X π ω).trans (pow_le_pow_left' hω 2)

private theorem norm_partitionDiff_le [LinearOrder ι] [SeminormedAddCommGroup E]
    (X : ι → Ω → E) {a b : ι} (π : IccPartition ι a b) (i : ℕ) {C : ℝ≥0} {ω : Ω}
    (hω : eVariationOn (X · ω) (Set.Icc a b) ≤ C) :
    ‖partitionDiff X π i ω‖ ≤ (C : ℝ) := by
  have hedist : edist (X (π.point (i + 1)) ω) (X (π.point i) ω) ≤ (C : ℝ≥0∞) :=
    (eVariationOn.edist_le (f := fun t ↦ X t ω) (s := Set.Icc a b)
      (π.point_mem_Icc (i + 1)) (π.point_mem_Icc i)).trans hω
  have hnndist : nndist (X (π.point (i + 1)) ω) (X (π.point i) ω) ≤ C := by
    rwa [edist_le_coe] at hedist
  simpa [partitionDiff, nndist_eq_nnnorm, dist_eq_norm] using NNReal.coe_le_coe.2 hnndist

/-- Inner products of partition differences of a process of bounded variation are integrable. -/
theorem integrable_inner_partitionDiff [LinearOrder ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] [IsFiniteMeasure μ] {X : ι → Ω → E} {a b : ι}
    (π : IccPartition ι a b) (i j : ℕ) {C : ℝ≥0} (hmeas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    Integrable (fun ω ↦ ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ) μ := by
  refine Integrable.of_bound ?_ ((C : ℝ) ^ 2) ?_
  · simp only [partitionDiff]; fun_prop
  · filter_upwards [hfv] with ω hω
    calc
      ‖⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ‖
          ≤ ‖partitionDiff X π i ω‖ * ‖partitionDiff X π j ω‖ :=
            norm_inner_le_norm (partitionDiff X π i ω) (partitionDiff X π j ω)
      _ ≤ (C : ℝ) * (C : ℝ) :=
          mul_le_mul (norm_partitionDiff_le X π i hω) (norm_partitionDiff_le X π j hω)
            (norm_nonneg (partitionDiff X π j ω)) C.2
      _ = C ^ 2 := by ring

/-- The squared increment of a process of bounded variation is integrable. -/
theorem integrable_inner_sub [LinearOrder ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] [IsFiniteMeasure μ] {X : ι → Ω → E} {a b : ι} (hab : a ≤ b) {C : ℝ≥0}
    (hmeas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    Integrable (fun ω ↦ ⟪X b ω - X a ω, X b ω - X a ω⟫_ℝ) μ := by
  sorry

end


/-- The expected square norm of a centered martingale partition difference equals the expected
quadratic sum along a partition. -/
theorem MeasureTheory.Martingale.integral_inner_sub_sub_self_eq_integral_sum_inner_partitionDiff
    [LinearOrder ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {X : ι → Ω → E}
    {𝓕 : Filtration ι mΩ} [IsFiniteMeasure μ] (hX : Martingale X 𝓕 μ)
    {a b : ι} (π : IccPartition ι a b) {C : ℝ≥0}
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    ∫ ω, ⟪X b ω - X a ω, X b ω - X a ω⟫_ℝ ∂μ =
      ∫ ω, ∑ i ∈ range π.card, ⟪partitionDiff X π i ω, partitionDiff X π i ω⟫_ℝ ∂μ := by
  let s := range π.card
  have hdiff_meas : ∀ i, AEStronglyMeasurable (partitionDiff X π i) μ := fun i ↦
    (((hX.stronglyMeasurable (π.point (i + 1))).mono (𝓕.le (π.point (i + 1)))).sub
      ((hX.stronglyMeasurable (π.point i)).mono (𝓕.le (π.point i)))).aestronglyMeasurable
  have hint : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω ↦ ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ) μ :=
    fun i _ j _ ↦ integrable_inner_partitionDiff π i j (hdiff_meas i) (hdiff_meas j) hfv
  calc
    ∫ ω, ⟪X b ω - X a ω, X b ω - X a ω⟫_ℝ ∂μ
        = ∫ ω, ∑ i ∈ s, ∑ j ∈ s,
            ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ ∂μ :=
        integral_congr_ae <| Eventually.of_forall fun ω ↦
          inner_sub_eq_sum_inner_partitionDiff X π ω
    _ = ∑ i ∈ s, ∫ ω, ∑ j ∈ s,
          ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ ∂μ :=
        integral_finsetSum s fun i hi ↦ integrable_finsetSum s (hint i hi)
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ ω,
          ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ ∂μ :=
        Finset.sum_congr rfl fun i hi ↦ integral_finsetSum s (hint i hi)
    _ = ∑ i ∈ s, ∫ ω, ⟪partitionDiff X π i ω, partitionDiff X π i ω⟫_ℝ ∂μ := by
        refine Finset.sum_congr rfl fun i hi ↦
          Finset.sum_eq_single_of_mem i hi fun j _ hji ↦ ?_
        rcases lt_or_gt_of_ne hji with hji_lt | hij_lt
        · rw [← hX.integral_inner_partitionDiff_eq_zero π j i hji_lt]
          exact integral_congr_ae <| Eventually.of_forall fun ω ↦
            real_inner_comm (partitionDiff X π j ω) (partitionDiff X π i ω)
        · exact hX.integral_inner_partitionDiff_eq_zero π i j hij_lt
    _ = _ := (integral_finsetSum s fun i hi ↦ hint i hi i hi).symm

/-- For a continuous process of bounded variation, the quadratic sums along the partitions
subordinate to ever finer finite open covers tend to zero almost surely. -/
theorem ae_tendsto_sum_inner_partitionDiff_nhds_zero [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {X : ι → Ω → E} {a b : ι} (hab : a ≤ b) {C : ℝ≥0}
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (X · ω) (Icc a b))
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun D : FiniteOpenCover ι (Set.Icc a b) ↦
      ∑ i ∈ range (D.iccPartition hab).card,
        ⟪partitionDiff X (D.iccPartition hab) i ω, partitionDiff X (D.iccPartition hab) i ω⟫_ℝ)
      atTop (𝓝 0) := by
  filter_upwards [hcont, hfv] with ω hcontω hfvω
  have hosc : Tendsto (fun D : FiniteOpenCover ι (Set.Icc a b) ↦
      partitionOsc (X · ω) (D.iccPartition hab)) atTop (𝓝 0) :=
    hcontω.tendsto_partitionOsc_atTop_nhds_zero hab
  have hCosc : Tendsto (fun D : FiniteOpenCover ι (Set.Icc a b) ↦
      (C : ℝ≥0∞) * partitionOsc (X · ω) (D.iccPartition hab)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hosc (Or.inr ENNReal.coe_ne_top)
  have htoReal : Tendsto (fun D : FiniteOpenCover ι (Set.Icc a b) ↦
      ((C : ℝ≥0∞) * partitionOsc (X · ω) (D.iccPartition hab)).toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hCosc
  refine squeeze_zero (fun D ↦ Finset.sum_nonneg fun i _ ↦ real_inner_self_nonneg)
    (fun D ↦ ?_) htoReal
  have hle : ENNReal.ofReal (∑ i ∈ range (D.iccPartition hab).card,
      ⟪partitionDiff X (D.iccPartition hab) i ω, partitionDiff X (D.iccPartition hab) i ω⟫_ℝ) ≤
      (C : ℝ≥0∞) * partitionOsc (X · ω) (D.iccPartition hab) :=
    (ofReal_sum_inner_partitionDiff_le_eVariationOn_mul_partitionOsc X
      (D.iccPartition hab) ω).trans (mul_le_mul_left hfvω _)
  have hne : (C : ℝ≥0∞) * partitionOsc (X · ω) (D.iccPartition hab) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ne_top_of_le_ne_top ENNReal.coe_ne_top
        ((partitionOsc_le_eVariationOn X (D.iccPartition hab) ω).trans hfvω))
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hle

/-- The squared increment of a continuous martingale of uniformly bounded variation has zero
expectation. -/
theorem MeasureTheory.Martingale.integral_inner_sub_sub_self_eq_zero
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
    [SecondCountableTopology ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [IsFiniteMeasure μ] {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hX : Martingale X 𝓕 μ) {C : ℝ≥0}
    {a b : ι} (hab : a ≤ b) (hcont : ∀ᵐ ω ∂μ, ContinuousOn (X · ω) (Icc a b))
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    ∫ ω, ⟪X b ω - X a ω, X b ω - X a ω⟫_ℝ ∂μ = 0 := by
  have hdiff_meas : ∀ (π : IccPartition ι a b) (i : ℕ),
      AEStronglyMeasurable (partitionDiff X π i) μ := fun π i ↦
    (((hX.stronglyMeasurable (π.point (i + 1))).mono (𝓕.le (π.point (i + 1)))).sub
      ((hX.stronglyMeasurable (π.point i)).mono (𝓕.le (π.point i)))).aestronglyMeasurable
  set F : FiniteOpenCover ι (Set.Icc a b) → Ω → ℝ := fun D ω ↦
    ∑ i ∈ range (D.iccPartition hab).card,
      ⟪partitionDiff X (D.iccPartition hab) i ω, partitionDiff X (D.iccPartition hab) i ω⟫_ℝ
    with hF
  have hF_meas : ∀ᶠ D in (atTop : Filter (FiniteOpenCover ι (Set.Icc a b))),
      AEStronglyMeasurable (F D) μ :=
    Eventually.of_forall fun D ↦
      (integrable_finsetSum _ fun i _ ↦
        integrable_inner_partitionDiff (D.iccPartition hab) i i
          (hdiff_meas _ i) (hdiff_meas _ i) hfv).aestronglyMeasurable
  have h_bound : ∀ᶠ D in (atTop : Filter (FiniteOpenCover ι (Set.Icc a b))),
      ∀ᵐ ω ∂μ, ‖F D ω‖ ≤ (C : ℝ) ^ 2 := by
    refine Eventually.of_forall fun D ↦ ?_
    filter_upwards [ae_sum_inner_partitionDiff_le_sq (D.iccPartition hab) hfv] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ real_inner_self_nonneg)]
    exact hω
  have h_lim : ∀ᵐ ω ∂μ, Tendsto (fun D ↦ F D ω) atTop (𝓝 (0 : ℝ)) :=
    ae_tendsto_sum_inner_partitionDiff_nhds_zero hab hcont hfv
  have htendsto : Tendsto (fun D ↦ ∫ ω, F D ω ∂μ) atTop (𝓝 0) := by
    simpa using tendsto_integral_filter_of_dominated_convergence (fun _ : Ω ↦ (C : ℝ) ^ 2)
      hF_meas h_bound (integrable_const _) h_lim
  have h_eq : ∀ D : FiniteOpenCover ι (Set.Icc a b),
      ∫ ω, ⟪X b ω - X a ω, X b ω - X a ω⟫_ℝ ∂μ = ∫ ω, F D ω ∂μ := fun D ↦
    hX.integral_inner_sub_sub_self_eq_integral_sum_inner_partitionDiff (D.iccPartition hab) hfv
  exact tendsto_const_nhds_iff.mp
    (htendsto.congr' <| Eventually.of_forall fun D ↦ (h_eq D).symm)

/-- For any `a ≤ b` and a continuous martingale `X` of uniformly bounded variation, `X a` is equal
to `X b` almost surely. -/
theorem Martingale.ae_eq_of_continuousOn_of_eVariationOn_le [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] [SecondCountableTopology ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [IsFiniteMeasure μ]
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hX : Martingale X 𝓕 μ) {C : ℝ≥0} {a b : ι}
    (hab : a ≤ b) (hcont : ∀ᵐ ω ∂μ, ContinuousOn (X · ω) (Icc a b))
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    ∀ᵐ ω ∂μ, X a ω = X b ω := by
  have hmeas : AEStronglyMeasurable (fun ω ↦ X b ω - X a ω) μ :=
    (((hX.stronglyMeasurable b).mono (𝓕.le b)).sub
      ((hX.stronglyMeasurable a).mono (𝓕.le a))).aestronglyMeasurable
  have h_int : Integrable (fun ω ↦ ⟪X b ω - X a ω, X b ω - X a ω⟫_ℝ) μ :=
    integrable_inner_sub hab hmeas hfv
  have h_nonneg : 0 ≤ᵐ[μ] fun ω ↦ ⟪X b ω - X a ω, X b ω - X a ω⟫_ℝ :=
    Eventually.of_forall fun _ ↦ real_inner_self_nonneg
  have h_zero : (fun ω ↦ ⟪X b ω - X a ω, X b ω - X a ω⟫_ℝ) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae h_nonneg h_int).1
      (hX.integral_inner_sub_sub_self_eq_zero hab hcont hfv)
  filter_upwards [h_zero] with ω hω
  exact (sub_eq_zero.1 (inner_self_eq_zero.1 hω)).symm

/-! ### Generalization to local martingales with locally finite variation

Following the reduction in Kallenberg, Proposition 18.2, we stop the process once the variation
of its path reaches a level `n`.  Since the index type is not assumed to have a bottom element,
the variation is measured from the left endpoint `a` via `variationOnFromTo` (truncated below `a`
so that the resulting process is adapted). -/

section

/-- The pathwise variation process of `X` measured from time `a`: at time `t ≥ a` and outcome
`ω`, the total variation of the path `X · ω` on `[a, t]`.  For `t ≤ a` the value is `0`, which
makes the process adapted. -/
noncomputable def variationProcess [LinearOrder ι] [PseudoEMetricSpace E] (X : ι → Ω → E)
    (a : ι) : ι → Ω → ℝ :=
  fun t ω ↦ variationOnFromTo (X · ω) Set.univ a (max a t)

theorem variationProcess_nonneg [LinearOrder ι] [PseudoEMetricSpace E] (X : ι → Ω → E)
    (a t : ι) (ω : Ω) : 0 ≤ variationProcess X a t ω :=
  variationOnFromTo.nonneg_of_le _ _ (le_max_left a t)

theorem variationProcess_of_le [LinearOrder ι] [PseudoEMetricSpace E] (X : ι → Ω → E)
    {a t : ι} (hta : t ≤ a) (ω : Ω) : variationProcess X a t ω = 0 := by
  sorry

theorem variationProcess_eq_toReal_eVariationOn_Icc [LinearOrder ι] [PseudoEMetricSpace E]
    (X : ι → Ω → E) {a t : ι} (hat : a ≤ t) (ω : Ω) :
    variationProcess X a t ω = (eVariationOn (X · ω) (Set.Icc a t)).toReal := by
  sorry

theorem monotone_variationProcess [LinearOrder ι] [PseudoEMetricSpace E] {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (a : ι) :
    Monotone fun t ↦ variationProcess X a t ω := by
  sorry

/-- The variation process of a continuous path of locally bounded variation is left-continuous. -/
theorem continuousWithinAt_variationProcess_Iic [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [PseudoEMetricSpace E] {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (hcont : Continuous fun t ↦ X t ω)
    (a c : ι) :
    ContinuousWithinAt (fun t ↦ variationProcess X a t ω) (Set.Iic c) c := by
  sorry

/-- The variation process of a continuous path of locally bounded variation is
right-continuous. -/
theorem continuousWithinAt_variationProcess_Ioi [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [PseudoEMetricSpace E] {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (hcont : Continuous fun t ↦ X t ω)
    (a c : ι) :
    ContinuousWithinAt (fun t ↦ variationProcess X a t ω) (Set.Ioi c) c := by
  sorry

/-- The variation process of a continuous path of locally bounded variation is continuous. -/
theorem continuous_variationProcess [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [PseudoEMetricSpace E] {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (hcont : Continuous fun t ↦ X t ω)
    (a : ι) :
    Continuous fun t ↦ variationProcess X a t ω := by
  sorry

/-- The variation process of an adapted process with continuous paths is adapted. -/
theorem MeasureTheory.StronglyAdapted.variationProcess [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [PseudoEMetricSpace E]
    {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} (hX : StronglyAdapted 𝓕 X)
    (hcont : ∀ ω, Continuous fun t ↦ X t ω) (a : ι) :
    StronglyAdapted 𝓕 (variationProcess X a) := by
  sorry

/-- The variation process of an adapted process with continuous paths is progressively
measurable. -/
theorem isStronglyProgressive_variationProcess [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [MeasurableSpace ι]
    [BorelSpace ι] [PseudoMetrizableSpace ι] [PseudoEMetricSpace E] {𝓕 : Filtration ι mΩ}
    {X : ι → Ω → E} (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, Continuous fun t ↦ X t ω) (a : ι) :
    IsStronglyProgressive 𝓕 (variationProcess X a) := by
  sorry

/-- The first time after `a` at which the variation of `X` measured from `a` reaches `r`. -/
noncomputable def variationHittingTime [ConditionallyCompleteLinearOrder ι]
    [PseudoEMetricSpace E] (X : ι → Ω → E) (a : ι) (r : ℝ) : Ω → WithTop ι :=
  hittingAfter (variationProcess X a) (Set.Ici r) a

theorem monotone_variationHittingTime [ConditionallyCompleteLinearOrder ι] [PseudoEMetricSpace E]
    (X : ι → Ω → E) (a : ι) (ω : Ω) : Monotone fun r ↦ variationHittingTime X a r ω := by
  sorry

/-- As long as the variation stays below `r`, the hitting time has not occurred. -/
theorem lt_variationHittingTime [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [PseudoEMetricSpace E] {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (hcont : Continuous fun t ↦ X t ω)
    {a t : ι} {r : ℝ} (hV : variationProcess X a t ω < r) :
    (t : WithTop ι) < variationHittingTime X a r ω := by
  sorry

/-- Under locally finite variation, the variation hitting times tend to infinity. -/
theorem ae_tendsto_variationHittingTime_nhds_top [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [PseudoEMetricSpace E] {X : ι → Ω → E}
    (hlfv : ∀ᵐ ω ∂μ, LocallyBoundedVariationOn (X · ω) Set.univ)
    (hcont : ∀ᵐ ω ∂μ, Continuous fun t ↦ X t ω) (a : ι) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ variationHittingTime X a n ω) atTop (𝓝 ⊤) := by
  sorry

/-- Hitting times of progressively measurable processes are stopping times, for a `σ`-finite
measure. -/
theorem isStoppingTime_hittingAfter_of_sigmaFinite [MeasurableSpace ι]
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι]
    [BorelSpace ι] {β : Type*} [TopologicalSpace β] [MeasurableSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [BorelSpace β] [SigmaFinite μ]
    {𝓕 : Filtration ι mΩ} [𝓕.IsComplete μ] [𝓕.IsRightContinuous] {Y : ι → Ω → β}
    (hY : IsStronglyProgressive 𝓕 Y) {s : Set β} (hs : MeasurableSet s) (n : ι) :
    IsStoppingTime 𝓕 (hittingAfter Y s n) := by
  sorry

/-- The variation hitting time is a stopping time. -/
theorem isStoppingTime_variationHittingTime [MeasurableSpace ι]
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι]
    [BorelSpace ι] [PseudoEMetricSpace E] [SigmaFinite μ]
    {𝓕 : Filtration ι mΩ} [𝓕.IsComplete μ] [𝓕.IsRightContinuous] {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, Continuous fun t ↦ X t ω) (a : ι) (r : ℝ) :
    IsStoppingTime 𝓕 (variationHittingTime X a r) :=
  isStoppingTime_hittingAfter_of_sigmaFinite (μ := μ) (s := Set.Ici r)
    (isStronglyProgressive_variationProcess hX hcont a) measurableSet_Ici a

/-- The variation hitting times form a localizing sequence. -/
theorem isLocalizingSequence_variationHittingTime [MeasurableSpace ι]
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι]
    [BorelSpace ι] [PseudoEMetricSpace E] [SigmaFinite μ]
    {𝓕 : Filtration ι mΩ} [𝓕.IsComplete μ] [𝓕.IsRightContinuous] {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hlfv : ∀ᵐ ω ∂μ, LocallyBoundedVariationOn (X · ω) Set.univ)
    (hcont : ∀ ω, Continuous fun t ↦ X t ω) (a : ι) :
    IsLocalizingSequence 𝓕 (fun n : ℕ ↦ variationHittingTime X a n) μ := by
  sorry

/-- The variation of the path stopped at the variation hitting time is bounded by the level at
which it was stopped. -/
theorem variationProcess_variationHittingTime_le [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [PseudoEMetricSpace E] {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (hcont : Continuous fun t ↦ X t ω)
    {a c : ι} {r : ℝ} (hr : 0 ≤ r) (hτ : variationHittingTime X a r ω = c) :
    variationProcess X a c ω ≤ r := by
  sorry

/-- If the stopping time `τ` occurs at `c` and the variation from `a` up to `c` is at most `C`,
then the variation of the stopped process on `[a, b]` is at most `C`. -/
theorem eVariationOn_stoppedProcess_Icc_le [LinearOrder ι] [Nonempty ι] [PseudoEMetricSpace E]
    {X : ι → Ω → E} {ω : Ω} (hX : LocallyBoundedVariationOn (X · ω) Set.univ)
    {τ : Ω → WithTop ι} {a b c : ι} (hτ : τ ω = c) {C : ℝ≥0}
    (hV : variationProcess X a c ω ≤ C) :
    eVariationOn (stoppedProcess X τ · ω) (Set.Icc a b) ≤ C := by
  sorry

/-- The process stopped at the variation hitting time of level `n` has variation at most `n`
on `[a, b]`. -/
theorem eVariationOn_stoppedProcess_variationHittingTime_le [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [PseudoEMetricSpace E] {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (hcont : Continuous fun t ↦ X t ω)
    (a b : ι) (n : ℕ) :
    eVariationOn (stoppedProcess X (variationHittingTime X a n) · ω) (Set.Icc a b) ≤ n := by
  sorry

/-- Stopping preserves continuity of paths. -/
theorem continuous_stoppedProcess [LinearOrder ι] [Nonempty ι] [TopologicalSpace ι]
    [OrderTopology ι] [TopologicalSpace E] {X : ι → Ω → E} (τ : Ω → WithTop ι) {ω : Ω}
    (hcont : Continuous fun t ↦ X t ω) :
    Continuous fun t ↦ stoppedProcess X τ t ω := by
  sorry

/-- Stopping preserves continuity of paths on an interval. -/
theorem continuousOn_stoppedProcess_Icc [LinearOrder ι] [Nonempty ι] [TopologicalSpace ι]
    [OrderTopology ι] [TopologicalSpace E] {X : ι → Ω → E} (τ : Ω → WithTop ι) {ω : Ω} {a b : ι}
    (hcont : ContinuousOn (X · ω) (Set.Icc a b)) :
    ContinuousOn (fun t ↦ stoppedProcess X τ t ω) (Set.Icc a b) := by
  sorry

/-- If processes `Y n` agree with `X` before the times `τ n`, the times tend to infinity, and
each `Y n` takes almost surely equal values at `a` and `b`, then so does `X`. -/
theorem ae_eq_of_forall_ae_eq_of_tendsto_nhds_top [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] {τ : ℕ → Ω → WithTop ι}
    (htop : ∀ᵐ ω ∂μ, Tendsto (τ · ω) atTop (𝓝 ⊤)) {X : ι → Ω → E} {Y : ℕ → ι → Ω → E}
    (hagree : ∀ n ω, ∀ t : ι, (t : WithTop ι) < τ n ω → Y n t ω = X t ω) {a b : ι}
    (heq : ∀ n, ∀ᵐ ω ∂μ, Y n a ω = Y n b ω) :
    ∀ᵐ ω ∂μ, X a ω = X b ω := by
  sorry

/-- **Reduction to uniformly bounded variation.**  If the stopped processes of `X` along a
sequence of times tending to infinity are martingales of uniformly bounded variation on `[a, b]`,
then `X a = X b` almost surely. -/
theorem ae_eq_of_tendsto_top_of_martingale_stoppedProcess
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
    [SecondCountableTopology ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [IsFiniteMeasure μ] {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} {τ : ℕ → Ω → WithTop ι}
    (htop : ∀ᵐ ω ∂μ, Tendsto (τ · ω) atTop (𝓝 ⊤))
    (hM : ∀ n, Martingale (stoppedProcess X (τ n)) 𝓕 μ) {a b : ι} (hab : a ≤ b)
    (hfv : ∀ n, ∃ C : ℝ≥0, ∀ᵐ ω ∂μ, eVariationOn (stoppedProcess X (τ n) · ω) (Set.Icc a b) ≤ C)
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (X · ω) (Set.Icc a b)) :
    ∀ᵐ ω ∂μ, X a ω = X b ω := by
  sorry

end

section

variable [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A stochastic process is a local martingale if it satisfies the martingale property locally. -/
def IsLocalMartingale (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (μ : Measure Ω) : Prop :=
  Locally (fun X ↦ Martingale X 𝓕 μ) 𝓕 X μ

/-- A stochastic process has locally finite variation if a sample path has locally finite variation
almost surely. -/
def IsLocalFiniteVar (X : ι → Ω → E) (μ : Measure Ω) : Prop :=
  ∀ᵐ ω ∂μ, LocallyBoundedVariationOn (X · ω) univ

/-- The stopped process of a local martingale is a local martingale. -/
theorem IsLocalMartingale.stoppedProcess_indicator [SecondCountableTopology ι]
    [MeasurableSpace ι] [BorelSpace ι] [PseudoMetrizableSpace ι] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] [IsFiniteMeasure μ]
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [Approximable 𝓕 μ] (hX : _root_.IsLocalMartingale X 𝓕 μ)
    (hcont : ∀ ω, Function.IsRightContinuous (X · ω)) {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime 𝓕 τ) :
    _root_.IsLocalMartingale (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ) 𝓕 μ := by
  sorry

/-- A bounded local martingale is a martingale. -/
theorem IsLocalMartingale.martingale_of_bounded [CompleteSpace E] [IsFiniteMeasure μ]
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hX : _root_.IsLocalMartingale X 𝓕 μ)
    (hadp : StronglyAdapted 𝓕 X) {C : ℝ} (hbdd : ∀ t ω, ‖X t ω‖ ≤ C) :
    Martingale X 𝓕 μ := by
  sorry

end

section

/-- **Kallenberg, Proposition 18.2.**  A continuous local martingale with locally finite
variation takes almost surely equal values at any two times. -/
theorem IsLocalMartingale.ae_eq_of_continuous_of_isLocalFiniteVar
    [ConditionallyCompleteLinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [DenselyOrdered ι] [MeasurableSpace ι] [PolishSpace ι]
    [BorelSpace ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [IsFiniteMeasure μ]
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [𝓕.IsComplete μ] [𝓕.IsRightContinuous]
    [Approximable 𝓕 μ] (hX : _root_.IsLocalMartingale X 𝓕 μ) (hfv : IsLocalFiniteVar X μ)
    (hadp : StronglyAdapted 𝓕 X) (hcont : ∀ ω, Continuous fun t ↦ X t ω) (a b : ι) :
    ∀ᵐ ω ∂μ, X a ω = X b ω := by
  sorry

/-- **Kallenberg, Proposition 18.2.**  A continuous local martingale with locally finite
variation is almost surely constant. -/
theorem IsLocalMartingale.ae_forall_eq_of_continuous_of_isLocalFiniteVar
    [ConditionallyCompleteLinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [DenselyOrdered ι] [MeasurableSpace ι] [PolishSpace ι]
    [BorelSpace ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [IsFiniteMeasure μ]
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [𝓕.IsComplete μ] [𝓕.IsRightContinuous]
    [Approximable 𝓕 μ] (hX : _root_.IsLocalMartingale X 𝓕 μ) (hfv : IsLocalFiniteVar X μ)
    (hadp : StronglyAdapted 𝓕 X) (hcont : ∀ ω, Continuous fun t ↦ X t ω) :
    ∀ᵐ ω ∂μ, ∀ a b, X a ω = X b ω := by
  sorry

end

/-! ### Generalization to `σ`-finite filtrations -/

section

theorem Martingale.indexComap_restrict [Preorder ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration μ 𝓕] (hX : Martingale X 𝓕 μ) {a : ι} {A : Set Ω}
    (hA : MeasurableSet[𝓕.seq a] A) :
    Martingale (X ∘ (Subtype.val : Iic a → ι)) (𝓕.indexComap (Subtype.mono_coe (Iic a)))
      (μ.restrict A) := by
  sorry

/-- A generalization of `Martingale.ae_eq_of_continuousOn_of_eVariationOn_le` to `σ`-finite
filtrations. -/
theorem Martingale.ae_eq_of_continuousOn_of_eVariationOn_le' [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] [SecondCountableTopology ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {X : ι → Ω → E}
    {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕] (hX : Martingale X 𝓕 μ) {C : ℝ≥0} {a b : ι}
    (hab : a ≤ b) (hcont : ∀ᵐ ω ∂μ, ContinuousOn (X · ω) (Icc a b))
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    ∀ᵐ ω ∂μ, X a ω = X b ω := by
  sorry

theorem ae_forall_eq_of_forall_ae_eq_of_continuous [TopologicalSpace ι] [SeparableSpace ι]
    [TopologicalSpace E] [T2Space E] {X : ι → Ω → E} (hcont : ∀ᵐ ω ∂μ, Continuous fun t ↦ X t ω)
    (hfixed : ∀ a b, ∀ᵐ ω ∂μ, X a ω = X b ω) :
    ∀ᵐ ω ∂μ, ∀ a b, X a ω = X b ω := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Eventually.of_forall fun _ a ↦ (hι.false a).elim
  · let d : ℕ → ι := TopologicalSpace.denseSeq ι
    have hd : DenseRange d := denseRange_denseSeq ι
    have h_dense : ∀ᵐ ω ∂μ, ∀ m n, X (d m) ω = X (d n) ω :=
      ae_all_iff.2 fun m ↦ ae_all_iff.2 fun n ↦ hfixed (d m) (d n)
    filter_upwards [hcont, h_dense] with ω hcontω h_denseω
    have h_path : (fun t ↦ X t ω) = fun _ ↦ X (d 0) ω :=
      hd.equalizer hcontω continuous_const <| funext fun n ↦ h_denseω n 0
    intro a b
    rw [congrFun h_path a, congrFun h_path b]

/-- A continuous martingale `X` of uniformly bounded variation is almost surely constant. -/
theorem Martingale.ae_forall_eq_of_continuous_of_eVariationOn_le
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [DenselyOrdered ι] [SecondCountableTopology ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration μ 𝓕] (hX : Martingale X 𝓕 μ) {C : ℝ≥0}
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) Set.univ ≤ C)
    (hcont : ∀ᵐ ω ∂μ, Continuous fun t ↦ X t ω) :
    ∀ᵐ ω ∂μ, ∀ a b, X a ω = X b ω := by
  sorry

end
