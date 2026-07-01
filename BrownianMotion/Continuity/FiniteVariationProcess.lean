/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BrownianMotion.Auxiliary.ContinuousBilinForm
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Finite-Variation Processes

This file shows that a continuous local martingale of locally finite variation is almost surely
constant.
-/

@[expose] public section

open Filter MeasureTheory Finset Set
open scoped BigOperators NNReal ENNReal InnerProductSpace Topology

section -- Existence of an IccPartition with small partition differences

/-- A finite ordered partition of `[a, b]` in a ordered space. -/
structure IccPartition (ι : Type*) [Preorder ι] (a b : ι) where
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

def trivialIccPartition {ι} [Preorder ι] {a : ι} : IccPartition ι a a where
  card := 1
  point _ := a
  left_eq := rfl
  right_eq := rfl
  mono _ _ _ := refl _
  point_mem_Icc _ := ⟨refl _, refl _⟩

/-- If `a ≤ b ≤ c`, then a partition of `[a, b]` can be extended to a partition of `[a, c]`. -/
def extendIccPartition {ι} [Preorder ι] {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c)
    (π : IccPartition ι a b) : IccPartition ι a c where
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
    by_cases h : n ≤ π.card
    · simpa [h] using ⟨(π.point_mem_Icc n).1, (π.point_mem_Icc n).2.trans hbc⟩
    · simp [h, hab.trans hbc]

/-- If there exists a partition of `[a, x]` such that the differences of `f` on any two adjacent
points in this partition are small, then there exists a partition of `[a, y]` with the same
property if the difference of `f` on `y` and `x` is small. -/
theorem exists_IccPartition_edist_lt_aux {ι E} [Preorder ι] [PseudoEMetricSpace E]
    {a x y : ι} {f : ι → E} {ε : ℝ≥0∞} (hxy : x ≤ y) (hlast : edist (f y) (f x) < ε)
    (hR : ∃ π : IccPartition ι a x, ∀ n, edist (f (π.point (n + 1))) (f (π.point n)) < ε) :
    ∃ π : IccPartition ι a y, ∀ n, edist (f (π.point (n + 1))) (f (π.point n)) < ε := by
  obtain ⟨π, hπ⟩ := hR
  have hax : a ≤ x := by simpa [π.right_eq] using (π.point_mem_Icc π.card).1
  refine ⟨extendIccPartition hax hxy π, fun n => ?_⟩
  rcases lt_trichotomy n π.card with hn | hn | hn
  · simp [extendIccPartition, hn, hn.le, hπ n]
  · simp [hn, π.right_eq, extendIccPartition, hlast]
  · simp [extendIccPartition, hn.not_gt, hn.not_ge, zero_le.trans_lt hlast]

theorem preimage_mem_nhds_prod_of_mem_uniformity_aux {ι E} [TopologicalSpace ι]
    [UniformSpace E] {f : ι → E} (hc : Continuous f) {V : Set (E × E)}
    (hV : V ∈ uniformity E) (x : ι) :
    ∀ᶠ p in 𝓝 (x, x), (f p.1, f p.2) ∈ V :=
  ((hc.comp continuous_fst).prodMk (hc.comp continuous_snd)).continuousAt
    (nhds_le_uniformity (f x) hV)

theorem exists_mem_nhds_forall_mem_uniformity_aux {ι E} [TopologicalSpace ι]
    [UniformSpace E] {f : ι → E} (hc : Continuous f) {V : Set (E × E)}
    (hV : V ∈ uniformity E) (x : ι) :
    ∃ U ∈ 𝓝 x, ∀ᵉ (y ∈ U) (z ∈ U), (f y, f z) ∈ V := by
  have := preimage_mem_nhds_prod_of_mem_uniformity_aux hc hV x
  rw [nhds_prod_eq] at this
  obtain ⟨U, hU, W, hW, hUW⟩ := mem_prod_iff.1 this
  exact ⟨U ∩ W, inter_mem hU hW, fun y hy z hz => hUW (mk_mem_prod hy.1 hz.2)⟩

theorem exists_mem_nhds_forall_edist_lt_aux {ι E} [TopologicalSpace ι]
    [PseudoEMetricSpace E] {f : ι → E} (hc : Continuous f) {ε : ℝ≥0∞} (hε : 0 < ε)
    (x : ι) : ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ z ∈ U, edist (f y) (f z) < ε :=
  exists_mem_nhds_forall_mem_uniformity_aux hc (edist_mem_uniformity hε) x

/-- For any `a ≤ b`, there exists a partition of `[a, b]` such that the differences of `f` on any
two adjacent points in this partition are small. -/
theorem exists_IccPartition {ι E} [TopologicalSpace ι] [ConditionallyCompleteLinearOrder ι]
    [OrderTopology ι] [DenselyOrdered ι] {a b : ι} [PseudoEMetricSpace E] (hab : a ≤ b)
    {f : ι → E} (hc : Continuous f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ π : IccPartition ι a b, ∀ n, edist (f (π.point (n + 1))) (f (π.point n)) < ε := by
  let R : Set ι := {x | ∃ π : IccPartition ι a x,
    ∀ n, edist (f (π.point (n + 1))) (f (π.point n)) < ε}
  have haR : a ∈ R := ⟨trivialIccPartition, fun n => by simp [trivialIccPartition, hε]⟩
  have hR_step (x y) (hx : x ∈ closure R) (hy : y ∈ Ioi x) : (R ∩ Ioc x y).Nonempty := by
    obtain ⟨U, hU, hU_edist⟩ := exists_mem_nhds_forall_edist_lt_aux hc hε x
    obtain ⟨u, hxu, hxuU⟩ := exists_Ico_subset_of_mem_nhds' hU hy
    obtain ⟨w, hw⟩ := exists_between hxu.1
    have hxIio : Iio w ∈ 𝓝 x := (isOpen_gt' w).mem_nhds hw.1
    obtain ⟨z, hz, hzR⟩ := (mem_closure_iff_nhds.mp hx) (U ∩ Iio w) (inter_mem hU hxIio)
    refine ⟨w, ?_, hw.1, hw.2.le.trans hxu.2⟩
    exact exists_IccPartition_edist_lt_aux hz.2.le
      (hU_edist w (hxuU ⟨hw.1.le, hw.2⟩) z hz.1) hzR
  have hclosure_Icc : Icc a b ⊆ closure R := by
    refine (isClosed_closure.inter isClosed_Icc).Icc_subset_of_forall_exists_gt
      (subset_closure haR) fun x hx y hy => ?_
    exact (hR_step x y hx.1 hy).mono (Set.inter_subset_inter_left _ subset_closure)
  rcases eq_or_lt_of_le hab with hab | hab
  · simpa [hab, R] using haR
  · obtain ⟨U, hU, hU_edist⟩ := exists_mem_nhds_forall_edist_lt_aux hc hε b
    obtain ⟨l, hlb, hlU⟩ := exists_Ioc_subset_of_mem_nhds' hU hab
    obtain ⟨y, hyR, hy⟩ := hR_step l b (hclosure_Icc ⟨hlb.1, hlb.2.le⟩) hlb.2
    exact exists_IccPartition_edist_lt_aux hy.2 (hU_edist b (mem_of_mem_nhds hU) y (hlU hy)) hyR

end

section -- Continuous martingales of uniformly bounded variation are constant.

variable {ι Ω E : Type*}

theorem edist_le_variation [LinearOrder ι] [PseudoEMetricSpace E]
    (X : ι → Ω → E) {a b : ι} (ω : Ω) :
    edist (X a ω) (X b ω) ≤ eVariationOn (X · ω) Set.univ :=
  eVariationOn.edist_le _ trivial trivial

/-- The difference of a process of two adjancet points in a partition. -/
def partitionDiff [LinearOrder ι] [AddCommGroup E] (X : ι → Ω → E) {a b : ι}
    (π : IccPartition ι a b) (i : ℕ) : Ω → E :=
  X (π.point (i + 1)) - X (π.point i)

/-- This estimate is used in the application of dominated convergence. -/
theorem partitionDiff_le_variation [LinearOrder ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : ι → Ω → E) {a b : ι} (π : IccPartition ι a b)
    (i j : ℕ) (ω : Ω) :
    ENNReal.ofReal |⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ| ≤
      (eVariationOn (X · ω) Set.univ) ^ 2 := by
  have hinner : |⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ| ≤
      ‖partitionDiff X π i ω‖ * ‖partitionDiff X π j ω‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) (x := partitionDiff X π i ω)
        (y := partitionDiff X π j ω))
  have hi :
      ENNReal.ofReal ‖partitionDiff X π i ω‖ ≤ eVariationOn (fun x => X x ω) Set.univ := by
    simpa [partitionDiff, edist_eq_enorm_sub, ofReal_norm'] using
      (eVariationOn.edist_le (f := fun t => X t ω) (s := Set.univ)
        (x := π.point (i + 1)) (y := π.point i) trivial trivial)
  have hj :
      ENNReal.ofReal ‖partitionDiff X π j ω‖ ≤ eVariationOn (fun x => X x ω) Set.univ := by
    simpa [partitionDiff, edist_eq_enorm_sub, ofReal_norm'] using
      (eVariationOn.edist_le (f := fun t => X t ω) (s := Set.univ)
        (x := π.point (j + 1)) (y := π.point j) trivial trivial)
  calc
    ENNReal.ofReal |⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ|
        ≤ ENNReal.ofReal (‖partitionDiff X π i ω‖ * ‖partitionDiff X π j ω‖) :=
          ENNReal.ofReal_le_ofReal hinner
    _ = ENNReal.ofReal ‖partitionDiff X π i ω‖ *
          ENNReal.ofReal ‖partitionDiff X π j ω‖ := by
        rw [ENNReal.ofReal_mul (norm_nonneg (partitionDiff X π i ω))]
    _ ≤ eVariationOn (fun x => X x ω) Set.univ * eVariationOn (fun x => X x ω) Set.univ :=
          mul_le_mul hi hj bot_le bot_le
    _ = (eVariationOn (X · ω) Set.univ) ^ 2 := by ring

theorem process_sub_eq_sum_partitionDiff [LinearOrder ι] [OrderBot ι]
    [AddCommGroup E] (X : ι → Ω → E) {t : ι} (π : IccPartition ι ⊥ t) :
    X t - X ⊥ = ∑ i ∈ range π.card, partitionDiff X π i :=
  calc
    X t - X ⊥ = X (π.point π.card) - X (π.point 0) := by rw [π.right_eq, π.left_eq]
    _ = ∑ i ∈ range π.card, (X (π.point (i + 1)) - X (π.point i)) :=
      (sum_range_sub (fun i ↦ X (π.point i)) π.card).symm
    _ = ∑ i ∈ range π.card, partitionDiff X π i := by simp [partitionDiff]

theorem inner_process_sub_eq_sum_inner_partitionDiff [LinearOrder ι] [OrderBot ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (X : ι → Ω → E) {t : ι}
    (π : IccPartition ι ⊥ t) (ω : Ω) :
    ⟪X t ω - X ⊥ ω, X t ω - X ⊥ ω⟫_ℝ =
      ∑ i ∈ range π.card, ∑ j ∈ range π.card, ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ := by
  have hsum : X t ω - X ⊥ ω = ∑ i ∈ range π.card, partitionDiff X π i ω := by
    simpa using congrFun (process_sub_eq_sum_partitionDiff X π) ω
  simp_rw [hsum, sum_inner, inner_sum]

variable {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Pull-out property for conditional expectation with a Hilbert-space inner product. -/
theorem condExp_inner_of_stronglyMeasurable_left [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f g : Ω → E} (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (fun ω => ⟪f ω, g ω⟫_ℝ) μ) (hg : Integrable g μ) :
    μ[fun ω => ⟪f ω, g ω⟫_ℝ | m] =ᵐ[μ] fun ω => ⟪f ω, μ[g | m] ω⟫_ℝ :=
  condExp_bilin_of_aestronglyMeasurable_left (ContinuousBilinForm.inner E)
    hf.aestronglyMeasurable hfg hg

/-- Partition differences of a martingale along ordered partition points are orthogonal in
expectation. -/
theorem partitionDiff_orthogonal [LinearOrder ι] [OrderBot ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕]
    (hX : Martingale X 𝓕 μ) {t : ι} (π : IccPartition ι ⊥ t) (i j : ℕ) (hij : i < j) :
    ∫ ω, ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ ∂μ = 0 := by
  by_cases hfg :
    Integrable (fun ω => ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ) μ
  · have hle : π.point (i + 1) ≤ π.point j := π.mono (Nat.succ_le_of_lt hij)
    have hleft : StronglyMeasurable[𝓕 (π.point j)] (partitionDiff X π i) :=
      ((hX.stronglyMeasurable (π.point (i + 1))).mono (𝓕.mono hle)).sub
        ((hX.stronglyMeasurable (π.point i)).mono
          (𝓕.mono ((π.mono (Nat.le_succ i)).trans hle)))
    have hright_int : Integrable (partitionDiff X π j) μ :=
      (hX.integrable (π.point (j + 1))).sub (hX.integrable (π.point j))
    have hcond_right : μ[partitionDiff X π j | 𝓕 (π.point j)] =ᵐ[μ] 0 := by
      simpa [partitionDiff] using
        (condExp_sub (hX.integrable (π.point (j + 1))) (hX.integrable (π.point j))
          (𝓕 (π.point j))).trans
          ((hX.condExp_ae_eq (π.mono (Nat.le_succ j))).sub
            (hX.condExp_ae_eq le_rfl))
    have hcond_inner : μ[fun ω => ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ |
        𝓕 (π.point j)] =ᵐ[μ] 0 := by
      filter_upwards [condExp_inner_of_stronglyMeasurable_left hleft hfg hright_int,
        hcond_right] with ω hinner hright
      rw [hinner, hright]
      simp
    calc
      ∫ ω, ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ ∂μ
          = ∫ ω, μ[fun ω => ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ |
              𝓕 (π.point j)] ω ∂μ :=
            (integral_condExp (𝓕.le (π.point j))).symm
      _ = ∫ _ω, (0 : ℝ) ∂μ := integral_congr_ae hcond_inner
      _ = 0 := by simp
  · exact integral_undef hfg

/-- The expected square norm of a centered martingale partition difference equals the expected
quadratic sum along a partition. -/
theorem integral_inner_process_sub_eq_sum_integral_inner_partitionDiff [LinearOrder ι]
    [OrderBot ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : ι → Ω → E}
    {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕] (hX : Martingale X 𝓕 μ)
    {t : ι} (π : IccPartition ι ⊥ t)
    (hint : ∀ i ∈ range π.card, ∀ j ∈ range π.card,
      Integrable (fun ω => ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ) μ) :
    ∫ ω, ⟪X t ω - X ⊥ ω, X t ω - X ⊥ ω⟫_ℝ ∂μ =
      ∑ i ∈ range π.card,
        ∫ ω, ⟪partitionDiff X π i ω, partitionDiff X π i ω⟫_ℝ ∂μ := by
  let s := range π.card
  calc
    ∫ ω, ⟪X t ω - X ⊥ ω, X t ω - X ⊥ ω⟫_ℝ ∂μ
        = ∫ ω, ∑ i ∈ s, ∑ j ∈ s,
            ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ ∂μ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun ω => by
            simpa [s] using inner_process_sub_eq_sum_inner_partitionDiff X π ω
    _ = ∑ i ∈ s, ∫ ω, ∑ j ∈ s,
          ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ ∂μ :=
        integral_finsetSum s fun i hi => integrable_finsetSum s (hint i (by simpa [s] using hi))
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ ω,
          ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ ∂μ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_finsetSum s (hint i (by simpa [s] using hi))
    _ = ∑ i ∈ s, ∫ ω, ⟪partitionDiff X π i ω, partitionDiff X π i ω⟫_ℝ ∂μ := by
        apply Finset.sum_congr rfl
        intro i hi
        refine Finset.sum_eq_single i ?_ ?_
        · intro j hj hji
          rcases lt_or_gt_of_ne hji with hji_lt | hij_lt
          · calc
              ∫ ω, ⟪partitionDiff X π i ω, partitionDiff X π j ω⟫_ℝ ∂μ
                  = ∫ ω, ⟪partitionDiff X π j ω, partitionDiff X π i ω⟫_ℝ ∂μ := by
                    apply integral_congr_ae
                    exact Eventually.of_forall fun ω =>
                      (real_inner_comm (partitionDiff X π i ω) (partitionDiff X π j ω)).symm
              _ = 0 := partitionDiff_orthogonal hX π j i hji_lt
          · exact partitionDiff_orthogonal hX π i j hij_lt
        · intro hi_not
          exact (hi_not hi).elim
    _ = ∑ i ∈ range π.card, ∫ ω,
          ⟪partitionDiff X π i ω, partitionDiff X π i ω⟫_ℝ ∂μ := by simp [s]

/-- The quadratic sum along a finite ordered partition. -/
noncomputable def partitionQuadraticVariation [LinearOrder ι] [PseudoEMetricSpace E]
    (X : ι → Ω → E) {a b : ι} (π : IccPartition ι a b) : Ω → ℝ≥0∞ :=
  fun ω =>
    ∑ i ∈ Finset.range π.card, (edist (X (π.point (i + 1)) ω) (X (π.point i) ω)) ^ 2

/-- The largest size of a process partition difference along a finite ordered partition. -/
noncomputable def partitionOscillation [LinearOrder ι] [PseudoEMetricSpace E] (X : ι → Ω → E)
    {a b : ι} (π : IccPartition ι a b) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ i, edist (X (π.point (i + 1)) ω) (X (π.point i) ω)

/-- The centered square norm has zero expectation for a continuous finite-variation martingale. -/
theorem integral_inner_eq_zero [ConditionallyCompleteLinearOrder ι] [OrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure μ]
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕]
    (hX : Martingale X 𝓕 μ) {C : ℝ≥0}
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) Set.univ ≤ C)
    (hcont : ∀ᵐ ω ∂μ, Continuous fun t => X t ω) {t : ι} :
    ∫ ω, ⟪X t ω - X ⊥ ω, X t ω - X ⊥ ω⟫_ℝ ∂μ = 0 := by
  sorry

/-- A continuous finite-variation martingale is almost surely equal to its initial value. -/
theorem almost_surely_constant [ConditionallyCompleteLinearOrder ι] [OrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure μ]
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕]
    (hX : Martingale X 𝓕 μ) {C : ℝ≥0}
    (hfv : ∀ᵐ ω ∂μ, eVariationOn (X · ω) Set.univ ≤ C)
    (hcont : ∀ᵐ ω ∂μ, Continuous fun t => X t ω) {t : ι} :
    ∀ᵐ ω ∂μ, X t ω = X ⊥ ω := by
  sorry

#min_imports
