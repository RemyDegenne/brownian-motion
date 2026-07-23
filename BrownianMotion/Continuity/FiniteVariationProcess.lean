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

* `MeasureTheory.Martingale.integral_norm_sub_sq_eq_zero`: the squared increment of a
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

theorem norm_sub_sq_eq_sum_inner_partitionDiff [Preorder ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : ι → Ω → E) {a b : ι} (π : IccPartition ι a b) (ω : Ω) :
    ‖X b ω - X a ω‖ ^ 2 =
      ∑ i ∈ range π.card, ∑ j ∈ range π.card, ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ := by
  have hsum : X b ω - X a ω = ∑ i ∈ range π.card, partitionDiff X π i ω := by
    simpa using congrFun (sub_eq_sum_partitionDiff X π) ω
  rw [← real_inner_self_eq_norm_sq]
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
theorem ofReal_sum_norm_partitionDiff_sq_le_eVariationOn_mul_partitionOsc [LinearOrder ι]
    [SeminormedAddCommGroup E] (X : ι → Ω → E) {a b : ι}
    (π : IccPartition ι a b) (ω : Ω) :
    ENNReal.ofReal (∑ i ∈ range π.card, ‖partitionDiff X π i ω‖ ^ 2) ≤
      eVariationOn (X · ω) (Icc a b) * partitionOsc (X · ω) π := by
  calc
    ENNReal.ofReal (∑ i ∈ range π.card, ‖partitionDiff X π i ω‖ ^ 2)
      = ∑ i ∈ range π.card, edist (X (π.point (i + 1)) ω) (X (π.point i) ω) ^ 2 := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ sq_nonneg _]
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
theorem ofReal_sum_norm_partitionDiff_sq_le_eVariationOn_sq [LinearOrder ι]
    [SeminormedAddCommGroup E] (X : ι → Ω → E) {a b : ι}
    (π : IccPartition ι a b) (ω : Ω) :
    ENNReal.ofReal (∑ i ∈ range π.card, ‖partitionDiff X π i ω‖ ^ 2) ≤
      eVariationOn (X · ω) (Icc a b) ^ 2 :=
  calc
    _ ≤ eVariationOn (X · ω) (Icc a b) * partitionOsc (X · ω) π :=
        ofReal_sum_norm_partitionDiff_sq_le_eVariationOn_mul_partitionOsc X π ω
    _ ≤ eVariationOn (X · ω) (Icc a b) * eVariationOn (X · ω) (Icc a b) :=
        mul_le_mul_right (partitionOsc_le_eVariationOn X π ω) _
    _ = eVariationOn (X · ω) (Icc a b) ^ 2 := (sq _).symm

/-- The quadratic sum along a partition of a process of bounded variation is almost surely
bounded. -/
theorem ae_sum_norm_partitionDiff_sq_le_sq [LinearOrder ι] [SeminormedAddCommGroup E]
    {X : ι → Ω → E} {a b : ι} (π : IccPartition ι a b) {C : ℝ≥0}
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    ∀ᵐ ω ∂μ, ∑ i ∈ range π.card, ‖partitionDiff X π i ω‖ ^ 2 ≤ C ^ 2 := by
  filter_upwards [hfv] with ω hω
  rw [← NNReal.coe_pow C 2, ← ENNReal.ofReal_le_coe]
  exact (ofReal_sum_norm_partitionDiff_sq_le_eVariationOn_sq X π ω).trans (pow_le_pow_left' hω 2)

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

/-- The squared norm of a partition difference of a process of bounded variation is
integrable. -/
theorem integrable_norm_partitionDiff_sq [LinearOrder ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] [IsFiniteMeasure μ] {X : ι → Ω → E} {a b : ι}
    (π : IccPartition ι a b) (i : ℕ) {C : ℝ≥0} (hmeas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    Integrable (fun ω ↦ ‖partitionDiff X π i ω‖ ^ 2) μ :=
  (integrable_inner_partitionDiff π i i hmeas hfv).congr <|
    Eventually.of_forall fun _ ↦ real_inner_self_eq_norm_sq _

/-- The squared increment of a process of bounded variation is integrable. -/
theorem integrable_norm_sub_sq [LinearOrder ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] [IsFiniteMeasure μ] {X : ι → Ω → E} {a b : ι} (hab : a ≤ b) {C : ℝ≥0}
    (hmeas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    Integrable (fun ω ↦ ‖X b ω - X a ω‖ ^ 2) μ := by
  simpa [partitionDiff, IccPartition.trivial] using
    integrable_norm_partitionDiff_sq (IccPartition.trivial hab) 0 hmeas hfv

end


/-- The expected square norm of a centered martingale partition difference equals the expected
quadratic sum along a partition. -/
theorem MeasureTheory.Martingale.integral_norm_sub_sq_eq_integral_sum_norm_partitionDiff_sq
    [LinearOrder ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {X : ι → Ω → E}
    {𝓕 : Filtration ι mΩ} [IsFiniteMeasure μ] (hX : Martingale X 𝓕 μ)
    {a b : ι} (π : IccPartition ι a b) {C : ℝ≥0}
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    ∫ ω, ‖X b ω - X a ω‖ ^ 2 ∂μ =
      ∫ ω, ∑ i ∈ range π.card, ‖partitionDiff X π i ω‖ ^ 2 ∂μ := by
  let s := range π.card
  have hmeas : ∀ i, AEStronglyMeasurable (X i) μ := fun i ↦
    ((hX.stronglyMeasurable i).mono (𝓕.le i)).aestronglyMeasurable
  have hint : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω ↦ ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ) μ :=
    fun i _ j _ ↦ integrable_inner_partitionDiff π i j hmeas hfv
  calc
    ∫ ω, ‖X b ω - X a ω‖ ^ 2 ∂μ
        = ∫ ω, ∑ i ∈ s, ∑ j ∈ s,
            ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ ∂μ :=
        integral_congr_ae <| Eventually.of_forall fun ω ↦
          norm_sub_sq_eq_sum_inner_partitionDiff X π ω
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
    _ = ∑ i ∈ s, ∫ ω, ‖partitionDiff X π i ω‖ ^ 2 ∂μ := by
        simp_rw [real_inner_self_eq_norm_sq]
    _ = _ := (integral_finsetSum s fun i _ ↦
        integrable_norm_partitionDiff_sq π i hmeas hfv).symm

/-- For a continuous process of bounded variation, the quadratic sums along the partitions
subordinate to ever finer finite open covers tend to zero almost surely. -/
theorem ae_tendsto_sum_norm_partitionDiff_sq_nhds_zero [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] [SeminormedAddCommGroup E]
    {X : ι → Ω → E} {a b : ι} (hab : a ≤ b) {C : ℝ≥0}
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (X · ω) (Icc a b))
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun D : FiniteOpenCover ι (Set.Icc a b) ↦
      ∑ i ∈ range (D.iccPartition hab).card, ‖partitionDiff X (D.iccPartition hab) i ω‖ ^ 2)
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
  refine squeeze_zero (fun D ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
    (fun D ↦ ?_) htoReal
  have hle : ENNReal.ofReal
      (∑ i ∈ range (D.iccPartition hab).card, ‖partitionDiff X (D.iccPartition hab) i ω‖ ^ 2) ≤
      (C : ℝ≥0∞) * partitionOsc (X · ω) (D.iccPartition hab) :=
    (ofReal_sum_norm_partitionDiff_sq_le_eVariationOn_mul_partitionOsc X
      (D.iccPartition hab) ω).trans (mul_le_mul_left hfvω _)
  have hne : (C : ℝ≥0∞) * partitionOsc (X · ω) (D.iccPartition hab) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ne_top_of_le_ne_top ENNReal.coe_ne_top
        ((partitionOsc_le_eVariationOn X (D.iccPartition hab) ω).trans hfvω))
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hle

/-- The squared increment of a continuous martingale of uniformly bounded variation has zero
expectation. -/
theorem MeasureTheory.Martingale.integral_norm_sub_sq_eq_zero
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
    [SecondCountableTopology ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [IsFiniteMeasure μ] {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hX : Martingale X 𝓕 μ) {C : ℝ≥0}
    {a b : ι} (hab : a ≤ b) (hcont : ∀ᵐ ω ∂μ, ContinuousOn (X · ω) (Icc a b))
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    ∫ ω, ‖X b ω - X a ω‖ ^ 2 ∂μ = 0 := by
  have hmeas : ∀ i, AEStronglyMeasurable (X i) μ := fun i ↦
    ((hX.stronglyMeasurable i).mono (𝓕.le i)).aestronglyMeasurable
  set F : FiniteOpenCover ι (Set.Icc a b) → Ω → ℝ := fun D ω ↦
    ∑ i ∈ range (D.iccPartition hab).card, ‖partitionDiff X (D.iccPartition hab) i ω‖ ^ 2
    with hF
  have hF_meas : ∀ᶠ D in (atTop : Filter (FiniteOpenCover ι (Set.Icc a b))),
      AEStronglyMeasurable (F D) μ :=
    Eventually.of_forall fun D ↦
      (integrable_finsetSum _ fun i _ ↦
        integrable_norm_partitionDiff_sq (D.iccPartition hab) i hmeas hfv).aestronglyMeasurable
  have h_bound : ∀ᶠ D in (atTop : Filter (FiniteOpenCover ι (Set.Icc a b))),
      ∀ᵐ ω ∂μ, ‖F D ω‖ ≤ (C : ℝ) ^ 2 := by
    refine Eventually.of_forall fun D ↦ ?_
    filter_upwards [ae_sum_norm_partitionDiff_sq_le_sq (D.iccPartition hab) hfv] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)]
    exact hω
  have h_lim : ∀ᵐ ω ∂μ, Tendsto (fun D ↦ F D ω) atTop (𝓝 (0 : ℝ)) :=
    ae_tendsto_sum_norm_partitionDiff_sq_nhds_zero hab hcont hfv
  have htendsto : Tendsto (fun D ↦ ∫ ω, F D ω ∂μ) atTop (𝓝 0) := by
    simpa using tendsto_integral_filter_of_dominated_convergence (fun _ : Ω ↦ (C : ℝ) ^ 2)
      hF_meas h_bound (integrable_const _) h_lim
  have h_eq : ∀ D : FiniteOpenCover ι (Set.Icc a b),
      ∫ ω, ‖X b ω - X a ω‖ ^ 2 ∂μ = ∫ ω, F D ω ∂μ := fun D ↦
    hX.integral_norm_sub_sq_eq_integral_sum_norm_partitionDiff_sq (D.iccPartition hab) hfv
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
  have hmeas : ∀ i, AEStronglyMeasurable (X i) μ := fun i ↦
    ((hX.stronglyMeasurable i).mono (𝓕.le i)).aestronglyMeasurable
  have h_zero : (fun ω ↦ ‖X b ω - X a ω‖ ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (integrable_norm_sub_sq hab hmeas hfv)).1 (hX.integral_norm_sub_sq_eq_zero hab hcont hfv)
  filter_upwards [h_zero] with ω hω
  exact (sub_eq_zero.1 (norm_eq_zero.1 (sq_eq_zero_iff.1 hω))).symm

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
  simp [variationProcess, max_eq_left hta, variationOnFromTo.self]

theorem variationProcess_eq_toReal_eVariationOn_Icc [LinearOrder ι] [PseudoEMetricSpace E]
    (X : ι → Ω → E) {a t : ι} (hat : a ≤ t) (ω : Ω) :
    variationProcess X a t ω = (eVariationOn (X · ω) (Set.Icc a t)).toReal := by
  rw [variationProcess, max_eq_right hat, variationOnFromTo.eq_of_le (X · ω) Set.univ hat,
    Set.univ_inter]

theorem monotone_variationProcess [LinearOrder ι] [PseudoEMetricSpace E] {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (a : ι) :
    Monotone fun t ↦ variationProcess X a t ω := by
  intro s t hst
  have hmono := variationOnFromTo.monotoneOn (f := fun t ↦ X t ω) (s := Set.univ) (a := a)
    hX (Set.mem_univ a)
  exact hmono (Set.mem_univ _) (Set.mem_univ _) (max_le_max le_rfl hst)

/-- The variation process of a continuous path of locally bounded variation is left-continuous. -/
theorem continuousWithinAt_variationProcess_Iic [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [PseudoEMetricSpace E] {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (hcont : Continuous fun t ↦ X t ω)
    (a c : ι) :
    ContinuousWithinAt (fun t ↦ variationProcess X a t ω) (Set.Iic c) c := by
  rcases lt_or_ge c a with hca | hac
  · have hzero : (fun t ↦ variationProcess X a t ω) =ᶠ[𝓝[Set.Iic c] c] fun _ ↦ (0 : ℝ) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hca)] with y hy
      exact variationProcess_of_le X hy.le ω
    change Tendsto (fun t ↦ variationProcess X a t ω) (𝓝[Set.Iic c] c)
      (𝓝 (variationProcess X a c ω))
    rw [variationProcess_of_le X hca.le ω]
    exact Filter.Tendsto.congr' hzero.symm tendsto_const_nhds
  rcases hac.eq_or_lt with hac' | hac'
  · subst hac'
    have hzero : (fun t ↦ variationProcess X a t ω) =ᶠ[𝓝[Set.Iic a] a] fun _ ↦ (0 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact variationProcess_of_le X hy ω
    change Tendsto (fun t ↦ variationProcess X a t ω) (𝓝[Set.Iic a] a)
      (𝓝 (variationProcess X a a ω))
    rw [variationProcess_of_le X le_rfl ω]
    exact Filter.Tendsto.congr' hzero.symm tendsto_const_nhds
  · let f : ι → E := fun t ↦ X t ω
    let s : Set ι := Set.univ ∩ Set.Icc a c
    have hs_mem : s ∈ 𝓝[Set.Iic c] c := by
      refine mem_of_superset (inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hac'))
        self_mem_nhdsWithin) ?_
      rintro y ⟨hay, hyc⟩
      exact ⟨trivial, hay.le, hyc⟩
    have hf : BoundedVariationOn f s := hX a c trivial trivial
    have hfc : ContinuousWithinAt f (s ∩ Set.Iic c) c := hcont.continuousWithinAt
    have hsmall : Tendsto (fun y ↦ (eVariationOn f (s ∩ Set.Icc y c)).toReal)
        (𝓝[Set.Iic c] c) (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
        (hf.tendsto_eVariationOn_Icc_zero_left hfc)
      have hsmall_s : Tendsto (fun y ↦ (eVariationOn f (s ∩ Set.Icc y c)).toReal)
          (𝓝[s] c) (𝓝 0) := by
        simpa [Function.comp_def] using h
      exact hsmall_s.mono_left (nhdsWithin_le_of_mem hs_mem)
    have hrepr : (fun y ↦ variationProcess X a y ω) =ᶠ[𝓝[Set.Iic c] c]
        fun y ↦ variationProcess X a c ω - (eVariationOn f (s ∩ Set.Icc y c)).toReal := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hac')] with y hyc hay
      have hay' : a ≤ y := le_of_lt hay
      have hadd := variationOnFromTo.add (f := f) (s := Set.univ) hX
        (a := a) (b := y) (c := c) trivial trivial trivial
      have hset : Set.univ ∩ Set.Icc y c = s ∩ Set.Icc y c := by
        ext z
        simp only [s, Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_Icc]
        exact ⟨fun hz ↦ ⟨⟨hay'.trans hz.1, hz.2⟩, hz⟩, fun hz ↦ hz.2⟩
      have hyvar : variationOnFromTo f Set.univ y c =
          (eVariationOn f (s ∩ Set.Icc y c)).toReal := by
        rw [variationOnFromTo.eq_of_le f Set.univ hyc, hset]
      have hmax_y : max a y = y := max_eq_right hay'
      have hmax_c : max a c = c := max_eq_right hac'.le
      dsimp [variationProcess, f]
      rw [hmax_y, hmax_c]
      linarith
    exact Filter.Tendsto.congr' hrepr.symm (by simpa using tendsto_const_nhds.sub hsmall)

/-- The variation process of a continuous path of locally bounded variation is
right-continuous. -/
theorem continuousWithinAt_variationProcess_Ioi [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [PseudoEMetricSpace E] {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (hcont : Continuous fun t ↦ X t ω)
    (a c : ι) :
    ContinuousWithinAt (fun t ↦ variationProcess X a t ω) (Set.Ioi c) c := by
  rcases lt_or_ge c a with hca | hac
  · have hzero : (fun t ↦ variationProcess X a t ω) =ᶠ[𝓝[Set.Ioi c] c] fun _ ↦ (0 : ℝ) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hca)] with y hy
      exact variationProcess_of_le X hy.le ω
    change Tendsto (fun t ↦ variationProcess X a t ω) (𝓝[Set.Ioi c] c)
      (𝓝 (variationProcess X a c ω))
    rw [variationProcess_of_le X hca.le ω]
    exact Filter.Tendsto.congr' hzero.symm tendsto_const_nhds
  · by_cases hc : ∃ d, c < d
    · obtain ⟨d, hcd⟩ := hc
      let f : ι → E := fun t ↦ X t ω
      let s : Set ι := Set.univ ∩ Set.Icc c d
      have hs_mem : s ∈ 𝓝[Set.Ioi c] c := by
        refine mem_of_superset (Ioo_mem_nhdsGT hcd) ?_
        intro y hy
        exact ⟨trivial, hy.1.le, hy.2.le⟩
      have hf : BoundedVariationOn f s := hX c d trivial trivial
      have hfc : ContinuousWithinAt f (s ∩ Set.Ici c) c := hcont.continuousWithinAt
      have hsmall : Tendsto (fun y ↦ (eVariationOn f (s ∩ Set.Icc c y)).toReal)
          (𝓝[Set.Ioi c] c) (𝓝 0) := by
        have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
          (hf.tendsto_eVariationOn_Icc_zero_right c hfc)
        have hsmall_s : Tendsto (fun y ↦ (eVariationOn f (s ∩ Set.Icc c y)).toReal)
            (𝓝[s] c) (𝓝 0) := by
          simpa [Function.comp_def] using h
        exact hsmall_s.mono_left (nhdsWithin_le_of_mem hs_mem)
      have hrepr : (fun y ↦ variationProcess X a y ω) =ᶠ[𝓝[Set.Ioi c] c]
          fun y ↦ variationProcess X a c ω + (eVariationOn f (s ∩ Set.Icc c y)).toReal := by
        filter_upwards [self_mem_nhdsWithin, hs_mem] with y hcy hy
        have hle : c ≤ y := le_of_lt hcy
        have hyd : y ≤ d := hy.2.2
        have hadd := variationOnFromTo.add (f := f) (s := Set.univ) hX
          (a := a) (b := c) (c := y) trivial trivial trivial
        have hset : Set.univ ∩ Set.Icc c y = s ∩ Set.Icc c y := by
          ext z
          simp only [s, Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_Icc]
          exact ⟨fun hz ↦ ⟨⟨hz.1, hz.2.trans hyd⟩, hz⟩, fun hz ↦ hz.2⟩
        have hyvar : variationOnFromTo f Set.univ c y =
            (eVariationOn f (s ∩ Set.Icc c y)).toReal := by
          rw [variationOnFromTo.eq_of_le f Set.univ hle, hset]
        have hmax_y : max a y = y := max_eq_right (hac.trans hle)
        have hmax_c : max a c = c := max_eq_right hac
        dsimp [variationProcess, f]
        rw [hmax_y, hmax_c]
        linarith
      exact Filter.Tendsto.congr' hrepr.symm (by simpa using tendsto_const_nhds.add hsmall)
    · have hIoi : Set.Ioi c = ∅ := by
        ext y
        simp only [Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
        exact fun hcy ↦ hc ⟨y, hcy⟩
      rw [ContinuousWithinAt, hIoi, nhdsWithin_empty]
      exact tendsto_bot

/-- The variation process of a continuous path of locally bounded variation is continuous. -/
theorem continuous_variationProcess [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [PseudoEMetricSpace E] {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (hcont : Continuous fun t ↦ X t ω)
    (a : ι) :
    Continuous fun t ↦ variationProcess X a t ω := by
  rw [continuous_iff_continuousAt]
  intro c
  rw [← continuousWithinAt_univ, ← Set.Iic_union_Ioi (a := c)]
  exact (continuousWithinAt_variationProcess_Iic hX hcont a c).union
    (continuousWithinAt_variationProcess_Ioi hX hcont a c)

/-- There is a countable dense set containing a given point and every point that is isolated on
the left.  Partitions with points in such a set suffice to compute the variation of a continuous
function on an interval. -/
private lemma exists_countable_dense_mem_isolated [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (a : ι) :
    ∃ Q : Set ι, Q.Countable ∧ Dense Q ∧ a ∈ Q ∧ ∀ x : ι, 𝓝[<] x = ⊥ → x ∈ Q := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ι
  exact ⟨D ∪ {x | 𝓝[<] x = ⊥} ∪ {a},
    (hDc.union countable_setOf_isolated_left).union (Set.countable_singleton a),
    hDd.mono (Set.subset_union_left.trans Set.subset_union_left),
    Or.inr rfl, fun x hx ↦ Or.inl (Or.inr hx)⟩

/-- For a continuous function, the variation on `[a, c]` can be computed using only partition
points in a dense set containing `a` and all points that are isolated on the left: every
partition point can be approximated from the left inside its gap, which preserves
monotonicity. -/
private lemma eVariationOn_inter_Icc_of_dense [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [PseudoEMetricSpace E] {f : ι → E} (hf : Continuous f) {Q : Set ι}
    (hQd : Dense Q) (hQiso : ∀ x, 𝓝[<] x = ⊥ → x ∈ Q) {a : ι} (haQ : a ∈ Q) (c : ι) :
    eVariationOn f (Q ∩ Set.Icc a c) = eVariationOn f (Set.Icc a c) := by
  classical
  refine le_antisymm (eVariationOn.mono f Set.inter_subset_right) ?_
  have hdef : eVariationOn f (Set.Icc a c) =
      ⨆ p : ℕ × {u : ℕ → ι // Monotone u ∧ ∀ i, u i ∈ Set.Icc a c},
        ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) := rfl
  rw [hdef]
  refine iSup_le ?_
  rintro ⟨n, u, hu, hus⟩
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
  set ε : ℝ≥0∞ := δ / (2 * (n + 1)) with hεdef
  have hε0 : ε ≠ 0 := by
    refine ENNReal.div_ne_zero.2 ⟨by exact_mod_cast hδ.ne', ?_⟩
    finiteness
  -- a point of `Q` approximating `y` from the left within `(x, y]`
  have choice : ∀ x y : ι, x < y → ∃ w ∈ Q, w ∈ Set.Ioc x y ∧ edist (f w) (f y) ≤ ε := by
    intro x y hxy
    by_cases hiso : 𝓝[<] y = ⊥
    · exact ⟨y, hQiso y hiso, ⟨hxy, le_rfl⟩, by simp⟩
    haveI : (𝓝[<] y).NeBot := ⟨hiso⟩
    have hball : IsOpen {z | edist (f z) (f y) < ε} :=
      isOpen_Iio.preimage (hf.edist continuous_const)
    have hmem : Set.Ioo x y ∩ {z | edist (f z) (f y) < ε} ∈ 𝓝[<] y :=
      inter_mem (Ioo_mem_nhdsLT hxy) (mem_nhdsWithin_of_mem_nhds (hball.mem_nhds
        (by simpa [edist_self] using pos_iff_ne_zero.2 hε0)))
    obtain ⟨w, hwQ, hw⟩ := hQd.exists_mem_open (isOpen_Ioo.inter hball)
      (Filter.nonempty_of_mem hmem)
    exact ⟨w, hwQ, ⟨hw.1.1, hw.1.2.le⟩, hw.2.le⟩
  have choice₀ : ∃ w ∈ Q, w ∈ Set.Icc a (u 0) ∧ edist (f w) (f (u 0)) ≤ ε := by
    rcases (hus 0).1.eq_or_lt with heq | hlt
    · exact ⟨a, haQ, ⟨le_rfl, heq.le⟩, by simp [← heq]⟩
    · obtain ⟨w, hwQ, hw, hwd⟩ := choice a (u 0) hlt
      exact ⟨w, hwQ, ⟨hw.1.le, hw.2⟩, hwd⟩
  -- an approximating point for each partition point, chosen in the gap below its first
  -- occurrence so that the assignment is monotone
  have hex : ∀ m : ℕ, ∃ w : ι, (∀ j < m, u j < u m) → w ∈ Q ∧ w ∈ Set.Icc a c ∧ w ≤ u m ∧
      edist (f w) (f (u m)) ≤ ε ∧ ∀ j, u j < u m → u j < w := by
    intro m
    by_cases hm : ∀ j < m, u j < u m
    swap
    · exact ⟨a, fun hm' ↦ absurd hm' hm⟩
    cases m with
    | zero =>
      obtain ⟨w, hwQ, hwmem, hwd⟩ := choice₀
      exact ⟨w, fun _ ↦ ⟨hwQ, ⟨hwmem.1, hwmem.2.trans (hus 0).2⟩, hwmem.2, hwd,
        fun j hj ↦ absurd hj (not_lt.2 (hu (Nat.zero_le j)))⟩⟩
    | succ m =>
      obtain ⟨w, hwQ, hw, hwd⟩ := choice (u m) (u (m + 1)) (hm m m.lt_succ_self)
      refine ⟨w, fun _ ↦ ⟨hwQ, ⟨(hus m).1.trans hw.1.le, hw.2.trans (hus (m + 1)).2⟩, hw.2, hwd,
        fun j hj ↦ ?_⟩⟩
      have hjm : j ≤ m := by
        by_contra hjm
        exact absurd (hu (Nat.succ_le_of_lt (not_le.1 hjm))) (not_le.2 hj)
      exact (hu hjm).trans_lt hw.1
  choose W hW using hex
  have hrex : ∀ i : ℕ, ∃ j, u j = u i := fun i ↦ ⟨i, rfl⟩
  set r : ℕ → ℕ := fun i ↦ Nat.find (hrex i) with hrdef
  have hr_eq : ∀ i, u (r i) = u i := fun i ↦ Nat.find_spec (hrex i)
  have hr_lt : ∀ i, ∀ j < r i, u j < u (r i) := by
    intro i j hj
    refine lt_of_le_of_ne (hu hj.le) fun hjeq ↦ ?_
    exact absurd (Nat.find_min' (hrex i) (hjeq.trans (hr_eq i))) (not_le.2 hj)
  set q : ℕ → ι := fun i ↦ W (r i) with hqdef
  have hprops := fun i ↦ hW (r i) (hr_lt i)
  have hqd : ∀ i, edist (f (q i)) (f (u i)) ≤ ε := fun i ↦ by
    have := (hprops i).2.2.2.1
    rwa [hr_eq i] at this
  have hqmono : Monotone q := by
    intro i i' hii'
    rcases (hu hii').eq_or_lt with heq | hlt
    · have hr : r i = r i' := le_antisymm (Nat.find_min' (hrex i) ((hr_eq i').trans heq.symm))
        (Nat.find_min' (hrex i') ((hr_eq i).trans heq))
      simp [q, hr]
    · refine (((hprops i).2.2.1).trans_eq (hr_eq i)).trans ?_
      exact ((hprops i').2.2.2.2 i (by rw [hr_eq i']; exact hlt)).le
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))
      ≤ ∑ i ∈ Finset.range n, (edist (f (q (i + 1))) (f (q i)) + 2 * ε) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        calc edist (f (u (i + 1))) (f (u i))
            ≤ edist (f (u (i + 1))) (f (q (i + 1))) + edist (f (q (i + 1))) (f (q i)) +
              edist (f (q i)) (f (u i)) := edist_triangle4 _ _ _ _
          _ ≤ ε + edist (f (q (i + 1))) (f (q i)) + ε := by
              gcongr
              · rw [edist_comm]; exact hqd (i + 1)
              · exact hqd i
          _ = edist (f (q (i + 1))) (f (q i)) + 2 * ε := by ring
    _ = ∑ i ∈ Finset.range n, edist (f (q (i + 1))) (f (q i)) + n * (2 * ε) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ eVariationOn f (Q ∩ Set.Icc a c) + ↑δ := by
        refine add_le_add (eVariationOn.sum_le hqmono fun i ↦ ⟨(hprops i).1, (hprops i).2.1⟩) ?_
        calc (n : ℝ≥0∞) * (2 * ε) ≤ ((n : ℝ≥0∞) + 1) * (2 * ε) := by
              gcongr
              exact le_add_of_nonneg_right zero_le_one
          _ = 2 * ((n : ℝ≥0∞) + 1) * (δ / (2 * ((n : ℝ≥0∞) + 1))) := by rw [hεdef]; ring
          _ = δ := ENNReal.mul_div_cancel'
              (fun h ↦ absurd h (mul_ne_zero two_ne_zero (by simp)))
              (fun h ↦ absurd h (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
                (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩)))

/-- The clamped inclusion `ℕ → Fin (n + 1)` used to index partitions by tuples. -/
private def clampIdx (n i : ℕ) : Fin (n + 1) := ⟨min i n, Nat.lt_succ_of_le (min_le_right i n)⟩

@[simp]
private lemma clampIdx_val (n i : ℕ) : (clampIdx n i : ℕ) = min i n := rfl

/-- The variation of an adapted process over a countable set of times before `t` is
`𝓕 t`-measurable, as a countable supremum of measurable partial sums. -/
private lemma measurable_eVariationOn_of_countable [LinearOrder ι] [PseudoEMetricSpace E]
    {m' : MeasurableSpace Ω} {S : Set ι} (hS : S.Countable) {X : ι → Ω → E}
    (hX : ∀ s ∈ S, StronglyMeasurable[m'] (X s)) :
    Measurable[m'] fun ω ↦ eVariationOn (X · ω) S := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · have h0 : (fun ω ↦ eVariationOn (X · ω) ∅) = fun _ ↦ 0 :=
      funext fun ω ↦ eVariationOn.subsingleton _ Set.subsingleton_empty
    rw [h0]
    exact measurable_const
  obtain ⟨e, he⟩ := Set.Countable.exists_eq_range hS hSne
  have heS : ∀ k, e k ∈ S := fun k ↦ he ▸ Set.mem_range_self k
  have hkey : (fun ω ↦ eVariationOn (X · ω) S) = fun ω ↦
      ⨆ (n : ℕ) (σ : Fin (n + 1) → ℕ),
        if Monotone (fun i : ℕ ↦ e (σ (clampIdx n i))) then
          ∑ i ∈ Finset.range n,
            edist (X (e (σ (clampIdx n (i + 1)))) ω) (X (e (σ (clampIdx n i))) ω)
        else 0 := by
    funext ω
    refine le_antisymm ?_ (iSup_le fun n ↦ iSup_le fun σ ↦ ?_)
    · have hdef : eVariationOn (X · ω) S =
          ⨆ p : ℕ × {u : ℕ → ι // Monotone u ∧ ∀ i, u i ∈ S},
            ∑ i ∈ Finset.range p.1, edist (X (p.2.1 (i + 1)) ω) (X (p.2.1 i) ω) := rfl
      rw [hdef]
      refine iSup_le ?_
      rintro ⟨n, u, hu, hus⟩
      have hpre : ∀ i, ∃ k, e k = u i := fun i ↦ by rw [he] at hus; exact hus i
      choose κ hκ using hpre
      refine le_iSup_of_le n (le_iSup_of_le (fun i ↦ κ i) ?_)
      rw [if_pos]
      · refine le_of_eq (Finset.sum_congr rfl fun i hi ↦ ?_)
        have hin := Finset.mem_range.1 hi
        simp only [clampIdx_val, hκ]
        rw [min_eq_left (by omega), min_eq_left (by omega)]
      · intro i j hij
        simp only [clampIdx_val, hκ]
        exact hu (min_le_min hij le_rfl)
    · by_cases hmono : Monotone (fun i : ℕ ↦ e (σ (clampIdx n i)))
      · rw [if_pos hmono]
        exact eVariationOn.sum_le hmono fun i ↦ heS _
      · rw [if_neg hmono]
        exact zero_le
  rw [hkey]
  refine Measurable.iSup fun n ↦ Measurable.iSup fun σ ↦ ?_
  by_cases hmono : Monotone (fun i : ℕ ↦ e (σ (clampIdx n i)))
  · simp only [if_pos hmono]
    refine Finset.measurable_sum _ fun i _ ↦ ?_
    exact (continuous_edist.comp_stronglyMeasurable
      ((hX _ (heS _)).prodMk (hX _ (heS _)))).measurable
  · simp only [if_neg hmono]
    exact measurable_const

/-- The variation process of an adapted process with continuous paths is adapted. -/
theorem MeasureTheory.StronglyAdapted.variationProcess [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [PseudoEMetricSpace E]
    {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} (hX : StronglyAdapted 𝓕 X)
    (hcont : ∀ ω, Continuous fun t ↦ X t ω) (a : ι) :
    StronglyAdapted 𝓕 (variationProcess X a) := by
  obtain ⟨Q, hQc, hQd, haQ, hQiso⟩ := exists_countable_dense_mem_isolated a
  intro t
  rcases le_or_gt a t with hat | hta
  · have hform : _root_.variationProcess X a t = fun ω ↦
        (eVariationOn (X · ω) (Q ∩ Set.Icc a t)).toReal := funext fun ω ↦ by
      rw [variationProcess_eq_toReal_eVariationOn_Icc X hat ω,
        ← eVariationOn_inter_Icc_of_dense (hcont ω) hQd hQiso haQ t]
    rw [hform]
    exact (Measurable.ennreal_toReal (measurable_eVariationOn_of_countable
      (hQc.mono Set.inter_subset_left)
      fun s hs ↦ (hX s).mono (𝓕.mono hs.2.2))).stronglyMeasurable
  · have hform : _root_.variationProcess X a t = fun _ ↦ 0 :=
      funext fun ω ↦ variationProcess_of_le X hta.le ω
    rw [hform]
    exact stronglyMeasurable_const

/-- The variation process of an adapted process with continuous paths is progressively
measurable. -/
theorem isStronglyProgressive_variationProcess [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [MeasurableSpace ι]
    [BorelSpace ι] [PseudoMetrizableSpace ι] [PseudoEMetricSpace E] {𝓕 : Filtration ι mΩ}
    {X : ι → Ω → E} (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, Continuous fun t ↦ X t ω) (a : ι) :
    IsStronglyProgressive 𝓕 (variationProcess X a) := by
  classical
  obtain ⟨Q, hQc, hQd, haQ, hQiso⟩ := exists_countable_dense_mem_isolated a
  intro t
  rcases le_or_gt a t with hat | hta
  swap
  · have hzero : (fun p : Set.Iic t × Ω ↦ variationProcess X a p.1 p.2) = fun _ ↦ 0 :=
      funext fun p ↦ variationProcess_of_le X (p.1.2.trans hta.le) p.2
    rw [hzero]
    exact stronglyMeasurable_const
  have hSc : (Q ∩ Set.Icc a t).Countable := hQc.mono Set.inter_subset_left
  obtain ⟨e, he⟩ := Set.Countable.exists_eq_range hSc ⟨a, haQ, le_rfl, hat⟩
  have heS : ∀ k, e k ∈ Q ∩ Set.Icc a t := fun k ↦ he ▸ Set.mem_range_self k
  have hform : (fun p : Set.Iic t × Ω ↦ variationProcess X a p.1 p.2) = fun p ↦
      (eVariationOn (X · p.2) (Q ∩ Set.Icc a (max a ↑p.1))).toReal := by
    funext p
    rw [variationProcess, variationOnFromTo.eq_of_le _ _ (le_max_left a _), Set.univ_inter,
      eVariationOn_inter_Icc_of_dense (hcont p.2) hQd hQiso haQ (max a ↑p.1)]
  rw [hform]
  refine (Measurable.ennreal_toReal ?_).stronglyMeasurable
  have hkey : (fun p : Set.Iic t × Ω ↦ eVariationOn (X · p.2) (Q ∩ Set.Icc a (max a ↑p.1))) =
      fun p ↦ ⨆ (n : ℕ) (σ : Fin (n + 1) → ℕ),
        if Monotone (fun i : ℕ ↦ e (σ (clampIdx n i))) ∧
            (∀ k : ℕ, e (σ (clampIdx n k)) ≤ max a ↑p.1) then
          ∑ i ∈ Finset.range n,
            edist (X (e (σ (clampIdx n (i + 1)))) p.2) (X (e (σ (clampIdx n i))) p.2)
        else 0 := by
    funext p
    have hmax_le : max a ↑p.1 ≤ t := max_le hat p.1.2
    refine le_antisymm ?_ (iSup_le fun n ↦ iSup_le fun σ ↦ ?_)
    · have hdef : eVariationOn (X · p.2) (Q ∩ Set.Icc a (max a ↑p.1)) =
          ⨆ pt : ℕ × {u : ℕ → ι // Monotone u ∧ ∀ i, u i ∈ Q ∩ Set.Icc a (max a ↑p.1)},
            ∑ i ∈ Finset.range pt.1, edist (X (pt.2.1 (i + 1)) p.2) (X (pt.2.1 i) p.2) := rfl
      rw [hdef]
      refine iSup_le ?_
      rintro ⟨n, u, hu, hus⟩
      have hpre : ∀ i, ∃ k, e k = u i := fun i ↦ by
        have hmem : u i ∈ Q ∩ Set.Icc a t :=
          ⟨(hus i).1, (hus i).2.1, (hus i).2.2.trans hmax_le⟩
        rw [he] at hmem
        exact hmem
      choose κ hκ using hpre
      refine le_iSup_of_le n (le_iSup_of_le (fun i ↦ κ i) ?_)
      rw [if_pos]
      · refine le_of_eq (Finset.sum_congr rfl fun i hi ↦ ?_)
        have hin := Finset.mem_range.1 hi
        simp only [clampIdx_val, hκ]
        rw [min_eq_left (by omega), min_eq_left (by omega)]
      · constructor
        · intro i j hij
          simp only [clampIdx_val, hκ]
          exact hu (min_le_min hij le_rfl)
        · intro k
          simp only [clampIdx_val, hκ]
          exact (hus _).2.2
    · by_cases hcond : Monotone (fun i : ℕ ↦ e (σ (clampIdx n i))) ∧
          ∀ k : ℕ, e (σ (clampIdx n k)) ≤ max a ↑p.1
      · rw [if_pos hcond]
        exact eVariationOn.sum_le hcond.1 fun i ↦ ⟨(heS _).1, (heS _).2.1, hcond.2 i⟩
      · rw [if_neg hcond]
        exact zero_le
  rw [hkey]
  refine Measurable.iSup fun n ↦ Measurable.iSup fun σ ↦ ?_
  by_cases hmono : Monotone (fun i : ℕ ↦ e (σ (clampIdx n i)))
  swap
  · have h0 : (fun p : Set.Iic t × Ω ↦
        if Monotone (fun i : ℕ ↦ e (σ (clampIdx n i))) ∧
            (∀ k : ℕ, e (σ (clampIdx n k)) ≤ max a ↑p.1) then
          ∑ i ∈ Finset.range n,
            edist (X (e (σ (clampIdx n (i + 1)))) p.2) (X (e (σ (clampIdx n i))) p.2)
        else 0) = fun _ ↦ 0 := by
      funext p
      rw [if_neg fun h ↦ hmono h.1]
    rw [h0]
    exact measurable_const
  have hset : MeasurableSet[Subtype.instMeasurableSpace.prod (𝓕 t)]
      {p : Set.Iic t × Ω | ∀ k : ℕ, e (σ (clampIdx n k)) ≤ max a ↑p.1} := by
    have hrw : {p : Set.Iic t × Ω | ∀ k : ℕ, e (σ (clampIdx n k)) ≤ max a ↑p.1} =
        Prod.fst ⁻¹' ⋂ k : ℕ, {s : Set.Iic t | e (σ (clampIdx n k)) ≤ max a ↑s} := by
      ext p
      simp
    rw [hrw]
    refine measurable_fst (MeasurableSet.iInter fun k ↦ ?_)
    rcases le_or_gt (e (σ (clampIdx n k))) a with hka | hka
    · have huniv : {s : Set.Iic t | e (σ (clampIdx n k)) ≤ max a ↑s} = Set.univ :=
        Set.eq_univ_of_forall fun s ↦ hka.trans (le_max_left a _)
      rw [huniv]
      exact MeasurableSet.univ
    · have hIci : {s : Set.Iic t | e (σ (clampIdx n k)) ≤ max a ↑s} =
          Subtype.val ⁻¹' Set.Ici (e (σ (clampIdx n k))) := by
        ext s
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici, le_max_iff]
        exact ⟨fun h ↦ h.resolve_left (not_le.2 hka), Or.inr⟩
      rw [hIci]
      exact measurable_subtype_coe measurableSet_Ici
  have hsum : Measurable[𝓕 t] fun ω ↦ ∑ i ∈ Finset.range n,
      edist (X (e (σ (clampIdx n (i + 1)))) ω) (X (e (σ (clampIdx n i))) ω) := by
    refine Finset.measurable_sum _ fun i _ ↦ ?_
    have hmeas : ∀ k : ℕ, StronglyMeasurable[𝓕 t] (X (e (σ (clampIdx n k)))) := fun k ↦
      (hX _).mono (𝓕.mono (heS (σ (clampIdx n k))).2.2)
    exact (continuous_edist.comp_stronglyMeasurable ((hmeas _).prodMk (hmeas _))).measurable
  have hind : (fun p : Set.Iic t × Ω ↦
      if Monotone (fun i : ℕ ↦ e (σ (clampIdx n i))) ∧
          (∀ k : ℕ, e (σ (clampIdx n k)) ≤ max a ↑p.1) then
        ∑ i ∈ Finset.range n,
          edist (X (e (σ (clampIdx n (i + 1)))) p.2) (X (e (σ (clampIdx n i))) p.2)
      else 0) =
      {p : Set.Iic t × Ω | ∀ k : ℕ, e (σ (clampIdx n k)) ≤ max a ↑p.1}.indicator
        (fun p ↦ ∑ i ∈ Finset.range n,
          edist (X (e (σ (clampIdx n (i + 1)))) p.2) (X (e (σ (clampIdx n i))) p.2)) := by
    funext p
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hp : ∀ k : ℕ, e (σ (clampIdx n k)) ≤ max a ↑p.1
    · rw [if_pos ⟨hmono, hp⟩, if_pos hp]
    · rw [if_neg fun h ↦ hp h.2, if_neg hp]
  rw [hind]
  exact (hsum.comp measurable_snd).indicator hset

/-- The first time after `a` at which the variation of `X` measured from `a` reaches `r`. -/
noncomputable def variationHittingTime [ConditionallyCompleteLinearOrder ι]
    [PseudoEMetricSpace E] (X : ι → Ω → E) (a : ι) (r : ℝ) : Ω → WithTop ι :=
  hittingAfter (variationProcess X a) (Set.Ici r) a

theorem monotone_variationHittingTime [ConditionallyCompleteLinearOrder ι] [PseudoEMetricSpace E]
    (X : ι → Ω → E) (a : ι) (ω : Ω) : Monotone fun r ↦ variationHittingTime X a r ω := by
  intro r s hrs
  exact hittingAfter_anti (variationProcess X a) a (Set.Ici_subset_Ici.2 hrs) ω

/-- As long as the variation stays below `r`, the hitting time has not occurred. -/
theorem lt_variationHittingTime [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [PseudoEMetricSpace E] {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (hcont : Continuous fun t ↦ X t ω)
    {a t : ι} {r : ℝ} (hV : variationProcess X a t ω < r) :
    (t : WithTop ι) < variationHittingTime X a r ω := by
  have hmono : Monotone fun u ↦ variationProcess X a u ω := monotone_variationProcess hX a
  have hnot : ∀ j, j ≤ t → variationProcess X a j ω < r := fun j hjt ↦ (hmono hjt).trans_lt hV
  by_contra hle
  rw [not_lt] at hle
  by_cases hex : ∃ b, t < b
  · obtain ⟨b, htb⟩ := hex
    have hVcont : Continuous fun u ↦ variationProcess X a u ω :=
      continuous_variationProcess hX hcont a
    have hmem : (fun u ↦ variationProcess X a u ω) ⁻¹' Set.Iio r ∈ 𝓝 t :=
      hVcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds hV)
    obtain ⟨u, hu, hIco⟩ := exists_Ico_subset_of_mem_nhds' hmem htb
    have hlt : hittingAfter (variationProcess X a) (Set.Ici r) a ω < (u : WithTop ι) :=
      hle.trans_lt (WithTop.coe_lt_coe.2 hu.1)
    rw [hittingAfter_lt_iff] at hlt
    obtain ⟨j, ⟨-, hju⟩, hjs⟩ := hlt
    rcases le_or_gt j t with hjt | htj
    · exact absurd (Set.mem_Ici.1 hjs) (not_le.2 (hnot j hjt))
    · exact absurd (Set.mem_Ici.1 hjs) (not_le.2 (Set.mem_Iio.1 (hIco ⟨htj.le, hju⟩)))
  · have htop : hittingAfter (variationProcess X a) (Set.Ici r) a ω = ⊤ := by
      rw [hittingAfter_eq_top_iff]
      intro j _
      exact not_le.2 (hnot j (not_lt.1 fun h ↦ hex ⟨j, h⟩))
    rw [variationHittingTime, htop] at hle
    exact absurd hle (by simp)

/-- Under locally finite variation, the variation hitting times tend to infinity. -/
theorem ae_tendsto_variationHittingTime_nhds_top [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [PseudoEMetricSpace E] {X : ι → Ω → E}
    (hlfv : ∀ᵐ ω ∂μ, LocallyBoundedVariationOn (X · ω) Set.univ)
    (hcont : ∀ᵐ ω ∂μ, Continuous fun t ↦ X t ω) (a : ι) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ variationHittingTime X a n ω) atTop (𝓝 ⊤) := by
  filter_upwards [hlfv, hcont] with ω hXω hcontω
  rw [WithTop.tendsto_nhds_top_iff]
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (variationProcess X a t ω)
  filter_upwards [Ici_mem_atTop n] with m hm
  exact lt_variationHittingTime hXω hcontω (hn.trans_le (Nat.cast_le.2 hm))

/-- Hitting times of progressively measurable processes are stopping times, for a `σ`-finite
measure. -/
theorem isStoppingTime_hittingAfter_of_sigmaFinite [MeasurableSpace ι]
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [PolishSpace ι]
    [BorelSpace ι] {β : Type*} [TopologicalSpace β] [MeasurableSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [BorelSpace β] [SigmaFinite μ]
    {𝓕 : Filtration ι mΩ} [𝓕.IsComplete μ] [𝓕.IsRightContinuous] {Y : ι → Ω → β}
    (hY : IsStronglyProgressive 𝓕 Y) {s : Set β} (hs : MeasurableSet s) (n : ι) :
    IsStoppingTime 𝓕 (hittingAfter Y s n) := by
  obtain ⟨ν, hνfin, hμν, _⟩ := exists_isFiniteMeasure_absolutelyContinuous μ
  haveI : IsFiniteMeasure ν := hνfin
  haveI : 𝓕.IsComplete ν :=
    ⟨fun _ hA t ↦ Filtration.IsComplete.measurableSet_of_null (hμν hA) t⟩
  exact isStoppingTime_hittingAfter' ν hY hs n

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
    IsLocalizingSequence 𝓕 (fun n : ℕ ↦ variationHittingTime X a n) μ where
  isStoppingTime n := isStoppingTime_variationHittingTime (μ := μ) hX hcont a n
  mono := ae_of_all _ fun ω _ _ hnm ↦
    monotone_variationHittingTime X a ω (Nat.cast_le.2 hnm)
  tendsto_top := ae_tendsto_variationHittingTime_nhds_top hlfv (ae_of_all _ hcont) a

/-- The variation of the path stopped at the variation hitting time is bounded by the level at
which it was stopped. -/
theorem variationProcess_variationHittingTime_le [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] [PseudoEMetricSpace E]
    {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (hcont : Continuous fun t ↦ X t ω)
    {a c : ι} {r : ℝ} (hr : 0 ≤ r) (hτ : variationHittingTime X a r ω = c) :
    variationProcess X a c ω ≤ r := by
  rcases le_or_gt c a with hca | hac
  · rw [variationProcess_of_le X hca]
    exact hr
  by_contra hle
  have hlt : r < variationProcess X a c ω := not_le.mp hle
  have hpre : {t | r < variationProcess X a t ω} ∈ 𝓝[Set.Iic c] c :=
    continuousWithinAt_variationProcess_Iic hX hcont a c (isOpen_Ioi.mem_nhds hlt)
  obtain ⟨U, hU, hU_sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hpre
  obtain ⟨l, hl, hlU⟩ := exists_Ioc_subset_of_mem_nhds' hU hac
  obtain ⟨y, hly, hyc⟩ := exists_between hl.2
  have hy_hit : variationProcess X a y ω ∈ Set.Ici r :=
    Set.mem_Ici.mpr (le_of_lt (hU_sub ⟨hlU ⟨hly, hyc.le⟩, hyc.le⟩))
  have hτ_le : variationHittingTime X a r ω ≤ (y : WithTop ι) :=
    hittingAfter_le_of_mem (hl.1.trans hly.le) hy_hit
  rw [hτ] at hτ_le
  exact absurd (WithTop.coe_le_coe.1 hτ_le) (not_le.mpr hyc)

private theorem L5StoppedVar_stoppedProcess_eq_min [LinearOrder ι] [Nonempty ι]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {c : ι} {ω : Ω} (hτ : τ ω = c) (t : ι) :
    stoppedProcess X τ t ω = X (min t c) ω := by
  have h : stoppedProcess X τ t ω = X ((min (↑t) (τ ω)).untopA) ω := rfl
  rw [h, hτ, ← WithTop.coe_min]
  rfl

/-- If the stopping time `τ` occurs at `c` and the variation from `a` up to `c` is at most `C`,
then the variation of the stopped process on `[a, b]` is at most `C`. -/
theorem eVariationOn_stoppedProcess_Icc_le [LinearOrder ι] [Nonempty ι] [PseudoEMetricSpace E]
    {X : ι → Ω → E} {ω : Ω} (hX : LocallyBoundedVariationOn (X · ω) Set.univ)
    {τ : Ω → WithTop ι} {a b c : ι} (hτ : τ ω = c) {C : ℝ≥0}
    (hV : variationProcess X a c ω ≤ C) :
    eVariationOn (stoppedProcess X τ · ω) (Set.Icc a b) ≤ C := by
  have hfun : EqOn (fun t ↦ stoppedProcess X τ t ω) (fun t ↦ X (min t c) ω) (Set.Icc a b) :=
    fun t _ ↦ L5StoppedVar_stoppedProcess_eq_min hτ t
  rw [eVariationOn.congr hfun]
  rcases le_total c a with hca | hac
  · have hconst : eVariationOn (fun t ↦ X (min t c) ω) (Set.Icc a b) = 0 := by
      refine eVariationOn.constant_on ?_
      rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
      change X (min s c) ω = X (min t c) ω
      rw [min_eq_right (hca.trans hs.1), min_eq_right (hca.trans ht.1)]
    rw [hconst]
    exact bot_le
  · have hcomp : eVariationOn (fun t ↦ X (min t c) ω) (Set.Icc a b) ≤
        eVariationOn (X · ω) (Set.Icc a c) :=
      eVariationOn.comp_le_of_monotoneOn (X · ω) (fun t ↦ min t c)
        (fun _ _ _ _ h ↦ min_le_min h le_rfl)
        fun t ht ↦ ⟨le_min ht.1 hac, min_le_right t c⟩
    refine hcomp.trans ?_
    have hfin : BoundedVariationOn (X · ω) (Set.Icc a c) := by
      have h := hX a c trivial trivial
      rwa [Set.univ_inter] at h
    rw [← ENNReal.toReal_le_toReal hfin ENNReal.coe_ne_top, ENNReal.coe_toReal,
      ← variationProcess_eq_toReal_eVariationOn_Icc X hac ω]
    exact hV

/-- The process stopped at the variation hitting time of level `n` has variation at most `n`
on `[a, b]`. -/
theorem eVariationOn_stoppedProcess_variationHittingTime_le [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] [PseudoEMetricSpace E]
    {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) Set.univ) (hcont : Continuous fun t ↦ X t ω)
    (a b : ι) (n : ℕ) :
    eVariationOn (stoppedProcess X (variationHittingTime X a n) · ω) (Set.Icc a b) ≤ n := by
  haveI : Nonempty ι := ⟨a⟩
  by_cases htop : variationHittingTime X a (n : ℝ) ω = ⊤
  · have hfun : EqOn (fun t ↦ stoppedProcess X (variationHittingTime X a (n : ℝ)) t ω)
        (X · ω) (Set.Icc a b) := fun t _ ↦ stoppedProcess_eq_of_le (le_top.trans htop.ge)
    rw [eVariationOn.congr hfun]
    rcases le_or_gt a b with hab | hba
    · have hVlt : variationProcess X a b ω < n := by
        have h := hittingAfter_eq_top_iff.mp htop b hab
        simpa [not_le] using h
      have hfin : BoundedVariationOn (X · ω) (Set.Icc a b) := by
        have h := hX a b trivial trivial
        rwa [Set.univ_inter] at h
      rw [← ENNReal.toReal_le_toReal hfin (ENNReal.natCast_ne_top n), ENNReal.toReal_natCast,
        ← variationProcess_eq_toReal_eVariationOn_Icc X hab ω]
      exact hVlt.le
    · rw [Set.Icc_eq_empty hba.not_ge, eVariationOn.subsingleton _ Set.subsingleton_empty]
      exact bot_le
  · obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 htop
    have hVle : variationProcess X a c ω ≤ ((n : ℝ≥0) : ℝ) := by
      simpa using variationProcess_variationHittingTime_le hX hcont (Nat.cast_nonneg n) hc.symm
    have h := eVariationOn_stoppedProcess_Icc_le (b := b) hX hc.symm hVle
    simpa using h

/-- Stopping preserves continuity of paths. -/
theorem continuous_stoppedProcess [LinearOrder ι] [Nonempty ι] [TopologicalSpace ι]
    [OrderTopology ι] [TopologicalSpace E] {X : ι → Ω → E} (τ : Ω → WithTop ι) {ω : Ω}
    (hcont : Continuous fun t ↦ X t ω) :
    Continuous fun t ↦ stoppedProcess X τ t ω := by
  by_cases htop : τ ω = ⊤
  · have heq : (fun t ↦ stoppedProcess X τ t ω) = fun t ↦ X t ω := by
      funext t
      simp [stoppedProcess, htop]
    rw [heq]
    exact hcont
  · obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp htop
    have hcomp : Continuous fun t ↦ X (min t c) ω :=
      hcont.comp (continuous_id.min continuous_const)
    convert hcomp using 1
    funext t
    have hmin_eq : (min (↑t : WithTop ι) (↑c : WithTop ι)).untopA = min t c := by
      by_cases htc : t ≤ c
      · rw [min_eq_left htc, min_eq_left (WithTop.coe_le_coe.2 htc)]
        rfl
      · rw [min_eq_right (le_of_not_ge htc),
          min_eq_right (WithTop.coe_le_coe.2 (le_of_not_ge htc))]
        rfl
    simp [stoppedProcess, ← hc, hmin_eq]

/-- Stopping preserves continuity of paths on an interval. -/
theorem continuousOn_stoppedProcess_Icc [LinearOrder ι] [Nonempty ι] [TopologicalSpace ι]
    [OrderTopology ι] [TopologicalSpace E] {X : ι → Ω → E} (τ : Ω → WithTop ι) {ω : Ω} {a b : ι}
    (hcont : ContinuousOn (X · ω) (Set.Icc a b)) :
    ContinuousOn (fun t ↦ stoppedProcess X τ t ω) (Set.Icc a b) := by
  by_cases htop : τ ω = ⊤
  · refine hcont.congr fun t _ ↦ ?_
    simp [stoppedProcess, htop]
  · obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp htop
    have hval : ∀ t : ι, stoppedProcess X τ t ω = X (min t c) ω := by
      intro t
      have hmin_eq : (min (↑t : WithTop ι) (↑c : WithTop ι)).untopA = min t c := by
        by_cases htc : t ≤ c
        · rw [min_eq_left htc, min_eq_left (WithTop.coe_le_coe.2 htc)]
          rfl
        · rw [min_eq_right (le_of_not_ge htc),
            min_eq_right (WithTop.coe_le_coe.2 (le_of_not_ge htc))]
          rfl
      simp [stoppedProcess, ← hc, hmin_eq]
    by_cases hac : a ≤ c
    · have hmaps : Set.MapsTo (fun t ↦ min t c) (Set.Icc a b) (Set.Icc a b) :=
        fun t ht ↦ ⟨le_min ht.1 hac, (min_le_left t c).trans ht.2⟩
      exact (hcont.comp ((continuous_id.min continuous_const).continuousOn) hmaps).congr
        fun t _ ↦ hval t
    · refine (continuousOn_const (c := X c ω)).congr fun t ht ↦ ?_
      rw [hval t, min_eq_right ((not_le.1 hac).le.trans ht.1)]

/-- If processes `Y n` agree with `X` before the times `τ n`, the times tend to infinity, and
each `Y n` takes almost surely equal values at `a` and `b`, then so does `X`. -/
theorem ae_eq_of_forall_ae_eq_of_tendsto_nhds_top [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] {τ : ℕ → Ω → WithTop ι}
    (htop : ∀ᵐ ω ∂μ, Tendsto (τ · ω) atTop (𝓝 ⊤)) {X : ι → Ω → E} {Y : ℕ → ι → Ω → E}
    (hagree : ∀ n ω, ∀ t : ι, (t : WithTop ι) < τ n ω → Y n t ω = X t ω) {a b : ι}
    (heq : ∀ n, ∀ᵐ ω ∂μ, Y n a ω = Y n b ω) :
    ∀ᵐ ω ∂μ, X a ω = X b ω := by
  filter_upwards [htop, ae_all_iff.2 heq] with ω htopω heqω
  rw [WithTop.tendsto_nhds_top_iff] at htopω
  obtain ⟨n, hn⟩ := eventually_atTop.1 (htopω (max a b))
  have hmax : ((max a b : ι) : WithTop ι) < τ n ω := hn n le_rfl
  have ha : (a : WithTop ι) < τ n ω :=
    (WithTop.coe_le_coe.2 (le_max_left a b)).trans_lt hmax
  have hb : (b : WithTop ι) < τ n ω :=
    (WithTop.coe_le_coe.2 (le_max_right a b)).trans_lt hmax
  rw [← hagree n ω a ha, ← hagree n ω b hb]
  exact heqω n

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
  have : Nonempty ι := ⟨a⟩
  refine ae_eq_of_forall_ae_eq_of_tendsto_nhds_top (Y := fun n ↦ stoppedProcess X (τ n)) htop
    (fun n ω t ht ↦ stoppedProcess_eq_of_le ht.le) fun n ↦ ?_
  obtain ⟨C, hC⟩ := hfv n
  refine Martingale.ae_eq_of_continuousOn_of_eVariationOn_le (hM n) hab ?_ hC
  filter_upwards [hcont] with ω hω using continuousOn_stoppedProcess_Icc (τ n) hω

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
  have hstable : IsStable 𝓕 fun Y : ι → Ω → E ↦
      Martingale Y 𝓕 μ ∧ ∀ ω, Function.IsRightContinuous (Y · ω) := fun Y hY σ hσ ↦
    ⟨hY.1.stoppedProcess_indicator hY.2 hσ, isStable_rightContinuous Y hY.2 σ hσ⟩
  have hloc : Locally
      (fun Y ↦ Martingale Y 𝓕 μ ∧ ∀ ω, Function.IsRightContinuous (Y · ω)) 𝓕 X μ :=
    (locally_and_of_isStable isStable_rightContinuous hcont hX).mono fun Y hY ↦ ⟨hY.2, hY.1⟩
  exact (hstable.locally X hloc τ hτ).mono fun Y hY ↦ hY.1

/-- A bounded local martingale is a martingale. -/
theorem IsLocalMartingale.martingale_of_bounded [CompleteSpace E] [IsFiniteMeasure μ]
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hX : _root_.IsLocalMartingale X 𝓕 μ)
    (hadp : StronglyAdapted 𝓕 X) {C : ℝ} (hbdd : ∀ t ω, ‖X t ω‖ ≤ C) :
    Martingale X 𝓕 μ := by
  set σ : ℕ → Ω → WithTop ι := hX.localSeq with hσdef
  set M : ℕ → ι → Ω → E :=
    fun n ↦ stoppedProcess (fun i ↦ {ω | ⊥ < σ n ω}.indicator (X i)) (σ n) with hMdef
  have hM : ∀ n, Martingale (M n) 𝓕 μ := fun n ↦ hX.stoppedProcess_localSeq n
  have hMbdd : ∀ n t ω, ‖M n t ω‖ ≤ max C 0 := by
    intro n t ω
    by_cases hω : ω ∈ {ω' | ⊥ < σ n ω'}
    · have heq : M n t ω = X (min ↑t (σ n ω)).untopA ω := by
        simp only [hMdef, stoppedProcess]
        exact Set.indicator_of_mem hω _
      rw [heq]
      exact (hbdd _ ω).trans (le_max_left C 0)
    · have heq : M n t ω = 0 := by
        simp only [hMdef, stoppedProcess]
        exact Set.indicator_of_notMem hω _
      rw [heq, norm_zero]
      exact le_max_right C 0
  have hMeq : ∀ t : ι, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, M n t ω = X t ω := by
    intro t
    filter_upwards [hX.isLocalizingSequence_localSeq.tendsto_top] with ω hω
    rw [WithTop.tendsto_nhds_top_iff] at hω
    filter_upwards [hω t] with n hn
    have hMn : M n t ω = stoppedProcess (fun i ↦ {ω' | ⊥ < σ n ω'}.indicator (X i)) (σ n) t ω :=
      rfl
    rw [hMn, stoppedProcess_eq_of_le hn.le]
    exact Set.indicator_of_mem (show ω ∈ {ω' | ⊥ < σ n ω'} from bot_le.trans_lt hn) (X t)
  have hint : ∀ t : ι, Integrable (X t) μ := fun t ↦
    Integrable.of_bound ((hadp t).mono (𝓕.le t)).aestronglyMeasurable C
      (Eventually.of_forall fun ω ↦ hbdd t ω)
  refine ⟨hadp, fun i j hij ↦ ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le i) (hint j)
    (fun s _ _ ↦ (hint i).integrableOn) (fun s hs _ ↦ ?_)
    (hadp i).aestronglyMeasurable).symm
  suffices hlim : ∀ t : ι, Tendsto (fun n ↦ ∫ ω in s, M n t ω ∂μ) atTop (𝓝 (∫ ω in s, X t ω ∂μ))
    from tendsto_nhds_unique (hlim i) ((hlim j).congr fun n ↦ ((hM n).setIntegral_eq hij hs).symm)
  intro t
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ max C 0)
    (fun n ↦ (((hM n).stronglyMeasurable t).mono (𝓕.le t)).aestronglyMeasurable.restrict)
    (integrable_const _) (fun n ↦ Eventually.of_forall fun ω ↦ hMbdd n t ω) ?_
  refine ae_restrict_of_ae ((hMeq t).mono fun ω hω ↦ ?_)
  exact tendsto_const_nhds.congr' (hω.mono fun n hn ↦ hn.symm)

end

/-- A process with continuous paths taking almost surely equal values at any two fixed times is
almost surely constant. -/
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
  haveI : Nonempty ι := ⟨⊥⟩
  suffices key : ∀ u v : ι, u ≤ v → ∀ᵐ ω ∂μ, X u ω = X v ω by
    rcases le_total a b with hab | hba
    · exact key a b hab
    · filter_upwards [key b a hba] with ω hω using hω.symm
  intro u v huv
  set σ : ℕ → Ω → WithTop ι := hX.localSeq with hσdef
  set τ : ℕ → Ω → WithTop ι := fun n ↦ variationHittingTime X u n with hτdef
  have hτloc : IsLocalizingSequence 𝓕 τ μ :=
    isLocalizingSequence_variationHittingTime hadp hfv hcont u
  -- paths of indicator-stopped processes are continuous
  have hpath : ∀ (κ : Ω → WithTop ι) (ω : Ω), Continuous fun t ↦
      stoppedProcess (fun i ↦ {ω' | ⊥ < κ ω'}.indicator (X i)) κ t ω := by
    intro κ ω
    by_cases hω : ω ∈ {ω' | ⊥ < κ ω'}
    · have heq : (fun t ↦ stoppedProcess (fun i ↦ {ω' | ⊥ < κ ω'}.indicator (X i)) κ t ω) =
          fun t ↦ stoppedProcess X κ t ω := funext fun t ↦ by
        simp only [stoppedProcess]
        exact Set.indicator_of_mem hω _
      rw [heq]
      exact continuous_stoppedProcess κ (hcont ω)
    · have heq : (fun t ↦ stoppedProcess (fun i ↦ {ω' | ⊥ < κ ω'}.indicator (X i)) κ t ω) =
          fun _ ↦ 0 := funext fun t ↦ by
        simp only [stoppedProcess]
        exact Set.indicator_of_notMem hω _
      rw [heq]
      exact continuous_const
  -- the indicator-stopped process at `σ n ⊓ τ n` is a martingale
  have hMart : ∀ n : ℕ, Martingale
      (stoppedProcess (fun i ↦ {ω | ⊥ < min σ τ n ω}.indicator (X i)) (min σ τ n)) 𝓕 μ := by
    intro n
    have hM : Martingale (stoppedProcess (fun i ↦ {ω | ⊥ < σ n ω}.indicator (X i)) (σ n)) 𝓕 μ :=
      hX.stoppedProcess_localSeq n
    have hMcont : ∀ ω, Function.IsRightContinuous
        (stoppedProcess (fun i ↦ {ω' | ⊥ < σ n ω'}.indicator (X i)) (σ n) · ω) :=
      fun ω t ↦ (hpath (σ n) ω).continuousWithinAt
    have hcomm : stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator
          (stoppedProcess (fun i' ↦ {ω' | ⊥ < σ n ω'}.indicator (X i')) (σ n) i)) (τ n) =
        stoppedProcess (fun i ↦ {ω | ⊥ < min σ τ n ω}.indicator (X i)) (min σ τ n) := by
      funext i ω
      simp [stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess,
        Set.indicator_indicator, Set.setOf_and, lt_inf_iff, inf_comm, Pi.inf_apply]
    rw [← hcomm]
    exact hM.stoppedProcess_indicator hMcont (hτloc.isStoppingTime n)
  -- the stopped variation is bounded by the level of the hitting time
  have hvar : ∀ n : ℕ, ∀ᵐ ω ∂μ, eVariationOn
      (stoppedProcess (fun i ↦ {ω | ⊥ < min σ τ n ω}.indicator (X i)) (min σ τ n) · ω)
      (Set.Icc u v) ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
    intro n
    filter_upwards [hfv] with ω hω
    have hmin : min σ τ n ω = min (σ n ω) (τ n ω) := rfl
    by_cases hbot : ω ∈ {ω' | ⊥ < min σ τ n ω'}
    · have heq : (stoppedProcess (fun i ↦ {ω' | ⊥ < min σ τ n ω'}.indicator (X i))
            (min σ τ n) · ω) = (stoppedProcess X (min σ τ n) · ω) := funext fun t ↦ by
        simp only [stoppedProcess]
        exact Set.indicator_of_mem hbot _
      rw [heq]
      rcases eq_or_ne (min σ τ n ω) ⊤ with htop | hne
      · have hτtop : variationHittingTime X u (n : ℝ) ω = ⊤ := by
          rw [hmin, _root_.min_eq_top] at htop
          exact htop.2
        have hpatheq : (stoppedProcess X (min σ τ n) · ω) =
            (stoppedProcess X (variationHittingTime X u (n : ℝ)) · ω) := funext fun t ↦ by
          simp only [stoppedProcess]
          rw [htop, hτtop]
        rw [hpatheq]
        simpa using eVariationOn_stoppedProcess_variationHittingTime_le hω (hcont ω) u v n
      · obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 hne
        have hcτ : (c : WithTop ι) ≤ τ n ω := hc ▸ (hmin ▸ min_le_right (σ n ω) (τ n ω))
        have hVc : variationProcess X u c ω ≤ (n : ℝ) := by
          rcases le_or_gt u c with huc | hcu
          · by_contra hVn
            have hle : variationHittingTime X u (n : ℝ) ω ≤ (c : WithTop ι) :=
              hittingAfter_le_of_mem huc (le_of_lt (not_le.1 hVn))
            exact hVn (variationProcess_variationHittingTime_le hω (hcont ω)
              (Nat.cast_nonneg n) (le_antisymm hle hcτ))
          · rw [variationProcess_of_le X hcu.le ω]
            exact Nat.cast_nonneg n
        exact eVariationOn_stoppedProcess_Icc_le hω hc.symm
          (by simpa using hVc : variationProcess X u c ω ≤ ((n : ℝ≥0) : ℝ))
    · have heq : (stoppedProcess (fun i ↦ {ω' | ⊥ < min σ τ n ω'}.indicator (X i))
            (min σ τ n) · ω) = fun _ ↦ (0 : E) := funext fun t ↦ by
        simp only [stoppedProcess]
        exact Set.indicator_of_notMem hbot _
      rw [heq, eVariationOn.constant_on]
      · exact zero_le
      · rintro - ⟨s, -, rfl⟩ - ⟨s', -, rfl⟩
        rfl
  -- transfer along the localizing sequence
  refine ae_eq_of_forall_ae_eq_of_tendsto_nhds_top
    (Y := fun n ↦ stoppedProcess (fun i ↦ {ω | ⊥ < min σ τ n ω}.indicator (X i)) (min σ τ n))
    (hX.isLocalizingSequence_localSeq.min hτloc).tendsto_top (fun n ω t ht ↦ ?_) fun n ↦ ?_
  · rw [stoppedProcess_eq_of_le ht.le]
    exact Set.indicator_of_mem (show ω ∈ {ω' | ⊥ < min σ τ n ω'} from bot_le.trans_lt ht) (X t)
  · exact Martingale.ae_eq_of_continuousOn_of_eVariationOn_le (hMart n) huv
      (Eventually.of_forall fun ω ↦ (hpath (min σ τ n) ω).continuousOn) (hvar n)

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
    ∀ᵐ ω ∂μ, ∀ a b, X a ω = X b ω :=
  ae_forall_eq_of_forall_ae_eq_of_continuous (ae_of_all μ hcont) fun a b ↦
    hX.ae_eq_of_continuous_of_isLocalFiniteVar hfv hadp hcont a b

end

/-! ### Generalization to `σ`-finite filtrations -/

section

/-- A martingale reindexed along a monotone map with values above a fixed time `a` remains a
martingale for the measure restricted to any `𝓕 a`-measurable set. -/
theorem Martingale.indexComap_restrict {ι' : Type*} [Preorder ι] [Preorder ι']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {X : ι → Ω → E}
    {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕] (hX : Martingale X 𝓕 μ) {f : ι' → ι}
    (hf : Monotone f) {a : ι} (hfa : ∀ k, a ≤ f k) {A : Set Ω} (hA : MeasurableSet[𝓕 a] A) :
    Martingale (X ∘ f) (𝓕.indexComap hf) (μ.restrict A) := by
  have hAf : ∀ k, MeasurableSet[𝓕 (f k)] A := fun k ↦ 𝓕.mono (hfa k) A hA
  haveI : SigmaFiniteFiltration (μ.restrict A) (𝓕.indexComap hf) := by
    refine ⟨fun k ↦ ?_⟩
    change SigmaFinite ((μ.restrict A).trim (𝓕.le (f k)))
    rw [← restrict_trim (𝓕.le (f k)) μ (hAf k)]
    infer_instance
  refine ⟨hX.stronglyAdapted.indexComap hf, fun i j hij ↦ ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((𝓕.indexComap hf).le i)
    ((hX.integrable (f j)).mono_measure Measure.restrict_le_self)
    (fun s _ _ ↦ ((hX.integrable (f i)).mono_measure Measure.restrict_le_self).integrableOn)
    (fun s hs _ ↦ ?_) (hX.stronglyMeasurable (f i)).aestronglyMeasurable).symm
  have hsm : MeasurableSet s := (𝓕.indexComap hf).le i s hs
  calc
    ∫ ω in s, (X ∘ f) i ω ∂μ.restrict A = ∫ ω in s ∩ A, X (f i) ω ∂μ :=
      congrArg (fun ν : Measure Ω ↦ ∫ ω, X (f i) ω ∂ν) (Measure.restrict_restrict hsm)
    _ = ∫ ω in s ∩ A, X (f j) ω ∂μ := hX.setIntegral_eq (hf hij) (hs.inter (hAf i))
    _ = ∫ ω in s, (X ∘ f) j ω ∂μ.restrict A :=
      (congrArg (fun ν : Measure Ω ↦ ∫ ω, X (f j) ω ∂ν) (Measure.restrict_restrict hsm)).symm

/-- A generalization of `Martingale.ae_eq_of_continuousOn_of_eVariationOn_le` to `σ`-finite
filtrations. -/
theorem Martingale.ae_eq_of_continuousOn_of_eVariationOn_le' [ConditionallyCompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] [SecondCountableTopology ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {X : ι → Ω → E}
    {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕] (hX : Martingale X 𝓕 μ) {C : ℝ≥0} {a b : ι}
    (hab : a ≤ b) (hcont : ∀ᵐ ω ∂μ, ContinuousOn (X · ω) (Icc a b))
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) (Icc a b) ≤ C) :
    ∀ᵐ ω ∂μ, X a ω = X b ω := by
  set S : ℕ → Set Ω := spanningSets (μ.trim (𝓕.le a)) with hSdef
  have hSmeas : ∀ k, MeasurableSet[𝓕 a] (S k) := fun k ↦ measurableSet_spanningSets _ k
  have hres : ∀ k : ℕ, ∀ᵐ ω ∂μ.restrict (S k), X a ω = X b ω := by
    intro k
    haveI : IsFiniteMeasure (μ.restrict (S k)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ, ← trim_measurableSet_eq (𝓕.le a) (hSmeas k)]
      exact measure_spanningSets_lt_top _ k
    have hY : Martingale (X ∘ fun t ↦ max a t)
        (𝓕.indexComap fun _ _ h ↦ max_le_max le_rfl h) (μ.restrict (S k)) :=
      Martingale.indexComap_restrict hX _ (fun t ↦ le_max_left a t) (hSmeas k)
    have hkey := Martingale.ae_eq_of_continuousOn_of_eVariationOn_le hY hab
      (ae_restrict_of_ae (hcont.mono fun ω hω ↦
        hω.congr fun t ht ↦ by simp [max_eq_right ht.1]))
      (ae_restrict_of_ae (hfv.mono fun ω hω ↦ le_trans
        (le_of_eq (eVariationOn.eq_of_eqOn fun t ht ↦ by
          simp [max_eq_right ht.1])) hω))
    filter_upwards [hkey] with ω hω
    simpa [max_eq_right hab] using hω
  rw [ae_iff]
  have hbad : {ω | ¬X a ω = X b ω} ⊆ ⋃ k, {ω | ¬X a ω = X b ω} ∩ S k := by
    intro ω hω
    have hmem : ω ∈ ⋃ k, S k := by
      rw [hSdef, iUnion_spanningSets]
      trivial
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hmem
    exact Set.mem_iUnion.2 ⟨k, hω, hk⟩
  refine measure_mono_null hbad (measure_iUnion_null fun k ↦ ?_)
  have hk := hres k
  rw [ae_iff, Measure.restrict_apply' (𝓕.le a _ (hSmeas k))] at hk
  exact hk

/-- A continuous martingale `X` of uniformly bounded variation is almost surely constant. -/
theorem Martingale.ae_forall_eq_of_continuous_of_eVariationOn_le
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [DenselyOrdered ι] [SecondCountableTopology ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration μ 𝓕] (hX : Martingale X 𝓕 μ) {C : ℝ≥0}
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) Set.univ ≤ C)
    (hcont : ∀ᵐ ω ∂μ, Continuous fun t ↦ X t ω) :
    ∀ᵐ ω ∂μ, ∀ a b, X a ω = X b ω := by
  refine ae_forall_eq_of_forall_ae_eq_of_continuous hcont fun a b ↦ ?_
  have key : ∀ u v : ι, u ≤ v → ∀ᵐ ω ∂μ, X u ω = X v ω := fun u v huv ↦
    Martingale.ae_eq_of_continuousOn_of_eVariationOn_le' hX huv
      (hcont.mono fun ω hω ↦ hω.continuousOn)
      (hfv.mono fun ω hω ↦ (eVariationOn.mono _ (Set.subset_univ _)).trans hω)
  rcases le_total a b with hab | hba
  · exact key a b hab
  · filter_upwards [key b a hba] with ω hω using hω.symm

end
