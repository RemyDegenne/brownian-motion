/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.Jensen
public import BrownianMotion.Auxiliary.Martingale
public import BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification

/-! # Càdlàg modification of martingales with values in a Banach space

We extend the construction of the càdlàg modification of a real quasimartingale (see the file
`BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification`) to martingales with values
in a Banach space `E`, which is not assumed to be separable.

## Main definitions

* `vectorRegularitySet T X d`: an event on which the path of `X` along the set of times `T` has
  left and right limits at all times before `d`. It is the analogue of `regularitySet` for a
  process with values in a Banach space.
* `vectorRightContModif X`: the right-continuous modification of `X`. It is strongly adapted if
  the filtration is right-continuous.
* `vectorCadlagModif X`: the càdlàg modification of `X`. It is strongly adapted if the filtration
  is right-continuous and complete.

Those two processes are `rightContModifOf R X` and `cadlagModifOf R X` for the regularity family
`R = vectorRegularitySet (regularityTimes ι) X` (see `isRegularityFamily_vectorRegularitySet`).
The properties of the modifications which do not depend on the way the regularity family is built
are proved in the file `CadlagModification`.

## Main statements

* `isCadlag_vectorCadlagModif`: the paths of `vectorCadlagModif X` are càdlàg.
* `Martingale.vectorRightContModif_ae_eq`, `Martingale.vectorCadlagModif_ae_eq`: for a martingale
  `X` with respect to a right-continuous filtration, these processes are modifications of `X`.
* `Martingale.exists_isCadlag_modification`: a martingale with values in a Banach space, with
  respect to a right-continuous and complete filtration, has a modification which is a martingale
  with càdlàg paths.

## Proof outline

As in the real case, the modification at time `t` is the right limit of the path of `X` along a
countable dense set of times `T`, on an event on which the paths along `T` have left and right
limits. That event has to be measurable and almost sure. There is no upcrossing inequality in a
Banach space, hence we reduce to the real case as follows.

* For all `e : E`, the process `‖X t - e‖` is a real submartingale, hence a real quasimartingale:
  almost surely, its paths along `T` have left and right limits.
* Almost surely, the path of `X` along `T ∩ Iic d` is totally bounded (`ae_totallyBounded_image`).
  Indeed, let `ξ` be a simple function close to `X d` in `L¹`. The martingale `μ[ξ | 𝓕 t]` takes
  values in the convex hull of the range of `ξ`, which is compact. By the maximal inequality for
  the real submartingale `‖μ[X d - ξ | 𝓕 t]‖`, with high probability the path of `X` before `d`
  stays uniformly close to that compact set.
* A function `x` with values in a compact set `K`, such that `‖x - e‖` converges for all `e` in a
  set whose closure contains `K`, converges (`exists_tendsto_of_tendsto_norm_sub`): it has a
  cluster point `y`, the limit of `‖x - e‖` is `‖y - e‖`, and this can be made arbitrarily small.

The two conditions above involve countably many random variables `X t` for `t ∈ T` (we use points
`e` in a countable set whose closure contains the values of the process, `denseValues T X`), hence
they define a measurable event.

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

section Pathwise

variable {α E : Type*} [NormedAddCommGroup E]

/-- If a function `x` takes values in a compact set `K` eventually along a filter `l`, and if the
distances `‖x a - e‖` converge along `l` for all `e` in a set `D` whose closure contains `K`,
then `x` converges along `l`. -/
lemma exists_tendsto_of_tendsto_norm_sub {l : Filter α} {x : α → E} {K D : Set E}
    (hK : IsCompact K) (hxK : ∀ᶠ a in l, x a ∈ K) (hD : K ⊆ closure D)
    (h : ∀ e ∈ D, ∃ c, Tendsto (fun a ↦ ‖x a - e‖) l (𝓝 c)) :
    ∃ y, Tendsto x l (𝓝 y) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact ⟨0, tendsto_bot⟩
  -- by compactness, `x` has a cluster point `y` along `l`
  obtain ⟨y, hyK, hy⟩ : ∃ y ∈ K, MapClusterPt y l x := hK (le_principal_iff.2 (mem_map.2 hxK))
  refine ⟨y, Metric.tendsto_nhds.2 fun ε hε ↦ ?_⟩
  -- take `e ∈ D` close to `y`: the limit of `‖x a - e‖` is `‖y - e‖`, which is small
  obtain ⟨e, heD, hye⟩ := Metric.mem_closure_iff.1 (hD hyK) (ε / 2) (half_pos hε)
  obtain ⟨c, hc⟩ := h e heD
  have hc_eq : ‖y - e‖ = c := by
    have h1 : MapClusterPt ‖y - e‖ l (fun a ↦ ‖x a - e‖) :=
      hy.continuousAt_comp (f := fun z ↦ ‖z - e‖) (by fun_prop)
    exact eq_of_nhds_neBot (ClusterPt.mono h1 hc)
  have hc_lt : c < ε / 2 := by rwa [← hc_eq, ← dist_eq_norm]
  filter_upwards [hc.eventually (gt_mem_nhds hc_lt)] with a ha
  calc dist (x a) y ≤ dist (x a) e + dist e y := dist_triangle _ _ _
  _ < ε / 2 + ε / 2 := by
    rw [dist_eq_norm, dist_comm e y]
    exact add_lt_add ha hye
  _ = ε := add_halves ε

end Pathwise

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [NormedAddCommGroup E]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → E} {T : Set ι}

section TotallyBounded

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- The conditional expectations of a simple function take values in a fixed compact set. -/
lemma exists_isCompact_condExp_mem [IsFiniteMeasure μ] (ξ : SimpleFunc Ω E) :
    ∃ K : Set E, IsCompact K ∧
      ∀ m : MeasurableSpace Ω, m ≤ mΩ → ∀ᵐ ω ∂μ, (μ[ξ | m]) ω ∈ K := by
  have hK : IsCompact (convexHull ℝ (Set.range ξ)) := ξ.finite_range.isCompact_convexHull ℝ
  have h_int : Integrable ξ μ := ξ.integrable_of_isFiniteMeasure
  have h_mem : ∀ᵐ ω ∂μ, ξ ω ∈ convexHull ℝ (Set.range ξ) :=
    ae_of_all _ fun ω ↦ subset_convexHull ℝ _ (Set.mem_range_self ω)
  exact ⟨convexHull ℝ (Set.range ξ), hK, fun m hm ↦
    (convex_convexHull ℝ _).condExp_mem hm h_int hK.isClosed h_mem⟩

variable [OrderBot ι]

/-- **Maximal inequality** for the norm of a martingale along a countable set of times. -/
lemma measure_exists_norm_gt_le [IsFiniteMeasure μ] {N : ι → Ω → E} (hN : Martingale N 𝓕 μ)
    (hT : T.Countable) (d : ι) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ∃ s ∈ T ∩ Set.Iic d, ε < ‖N s ω‖} ≤ ENNReal.ofReal (8 * (∫ ω, ‖N d ω‖ ∂μ) / ε) := by
  have hZ : Submartingale (fun t ω ↦ ‖N t ω‖) 𝓕 μ := hN.submartingale_norm
  have h := measure_exists_abs_gt_le hZ.isRealQuasimartingale hε hT (t := d)
  simp only [abs_norm] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have h_var : variationBound (fun t ω ↦ ‖N t ω‖) 𝓕 μ d
      ≤ ∫ ω, ‖N d ω‖ ∂μ - ∫ ω, ‖N ⊥ ω‖ ∂μ := by
    have : Nonempty (ElementaryPredictableSet 𝓕) := ⟨.empty 𝓕⟩
    exact ciSup_le fun S ↦ hZ.integral_elementaryPredictableSet_indicator_le S d
  have h_bot : ∫ ω, ‖N ⊥ ω‖ ∂μ ≤ ∫ ω, ‖N d ω‖ ∂μ := by
    simpa using hZ.setIntegral_le (bot_le : ⊥ ≤ d) MeasurableSet.univ
  have h_sub : ∫ ω, |‖N d ω‖ - ‖N ⊥ ω‖| ∂μ ≤ ∫ ω, ‖N d ω‖ ∂μ + ∫ ω, ‖N ⊥ ω‖ ∂μ := by
    rw [← integral_add (hZ.integrable d) (hZ.integrable ⊥)]
    refine integral_mono ((hZ.integrable d).sub (hZ.integrable ⊥)).abs
      ((hZ.integrable d).add (hZ.integrable ⊥)) fun ω ↦ ?_
    simp only [abs_le]
    constructor <;> linarith [norm_nonneg (N d ω), norm_nonneg (N ⊥ ω)]
  have h_nonneg : 0 ≤ ∫ ω, ‖N ⊥ ω‖ ∂μ := integral_nonneg fun _ ↦ norm_nonneg _
  exact div_le_div_of_nonneg_right (by linarith) hε.le

/-- Almost surely, the path of a martingale along a countable set of times which is bounded from
above is totally bounded. -/
lemma ae_totallyBounded_image [IsFiniteMeasure μ] (hX : Martingale X 𝓕 μ)
    (hT : T.Countable) (d : ι) :
    ∀ᵐ ω ∂μ, TotallyBounded ((X · ω) '' (T ∩ Set.Iic d)) := by
  -- it suffices to show that the path is a.s. at distance at most `1 / (k + 1)` of a compact set
  suffices h : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∃ K : Set E, IsCompact K ∧
      ∀ t ∈ T ∩ Set.Iic d, ∃ z ∈ K, ‖X t ω - z‖ ≤ 1 / (k + 1 : ℝ) by
    filter_upwards [ae_all_iff.2 h] with ω hω
    refine Metric.totallyBounded_iff.2 fun ε hε ↦ ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨K, hK, hKω⟩ := hω k
    obtain ⟨c, -, hc_fin, hKc⟩ := hK.finite_cover_balls (half_pos hε)
    refine ⟨c, hc_fin, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨z, hzK, hz⟩ := hKω t ht
    obtain ⟨y, hyc, hy⟩ : ∃ y ∈ c, z ∈ Metric.ball y (ε / 2) := by simpa using hKc hzK
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop]
    refine ⟨y, hyc, ?_⟩
    calc dist (X t ω) y ≤ dist (X t ω) z + dist z y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      rw [dist_eq_norm]
      exact add_lt_add (hz.trans_lt hk) hy
    _ = ε := add_halves ε
  intro k
  set ε : ℝ := 1 / (k + 1)
  have hε : 0 < ε := by positivity
  rw [ae_iff]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_) zero_le
  rw [zero_add]
  -- approximate `X d` in `L¹` by a simple function `ξ`
  have hδε : ENNReal.ofReal (δ * ε / 8) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  obtain ⟨ξ, hξ, -⟩ := (memLp_one_iff_integrable.2
    (hX.integrable d)).exists_simpleFunc_eLpNorm_sub_lt ENNReal.one_ne_top hδε
  have hξ_int : Integrable ξ μ := ξ.integrable_of_isFiniteMeasure
  -- the conditional expectations of `ξ` take values in a compact set `K`
  obtain ⟨K, hK, hKξ⟩ := exists_isCompact_condExp_mem (μ := μ) ξ
  -- the martingale `N t = μ[X d - ξ | 𝓕 t]` is uniformly small with high probability
  let N : ι → Ω → E := fun t ↦ μ[X d - ξ | 𝓕 t]
  have hN : Martingale N 𝓕 μ := martingale_condExp _ 𝓕 μ
  have h_ae : ∀ᵐ ω ∂μ, ∀ t ∈ T ∩ Set.Iic d,
      (μ[ξ | 𝓕 t]) ω ∈ K ∧ X t ω - (μ[ξ | 𝓕 t]) ω = N t ω := by
    rw [ae_ball_iff (hT.mono Set.inter_subset_left)]
    intro t ht
    have h1 : N t =ᵐ[μ] μ[X d | 𝓕 t] - μ[ξ | 𝓕 t] := condExp_sub (hX.integrable d) hξ_int _
    filter_upwards [hKξ (𝓕 t) (𝓕.le t), h1, hX.condExp_ae_eq ht.2] with ω h2 h3 h4
    refine ⟨h2, ?_⟩
    rw [h3, Pi.sub_apply, h4]
  have h_int : ∫ ω, ‖N d ω‖ ∂μ ≤ δ * ε / 8 := by
    refine (integral_norm_condExp_le _).trans ?_
    rw [integral_norm_eq_lintegral_enorm ((hX.integrable d).sub hξ_int).aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hξ.le
  calc μ {ω | ¬ ∃ K : Set E, IsCompact K ∧ ∀ t ∈ T ∩ Set.Iic d, ∃ z ∈ K, ‖X t ω - z‖ ≤ ε}
  _ ≤ μ ({ω | ∃ s ∈ T ∩ Set.Iic d, ε < ‖N s ω‖} ∪ {ω | ¬ ∀ t ∈ T ∩ Set.Iic d,
        (μ[ξ | 𝓕 t]) ω ∈ K ∧ X t ω - (μ[ξ | 𝓕 t]) ω = N t ω}) := by
    refine measure_mono fun ω hω ↦ ?_
    by_contra hω'
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt,
      not_not] at hω'
    refine hω ⟨K, hK, fun t ht ↦ ⟨_, (hω'.2 t ht).1, ?_⟩⟩
    rw [(hω'.2 t ht).2]
    exact hω'.1 t ht
  _ ≤ μ {ω | ∃ s ∈ T ∩ Set.Iic d, ε < ‖N s ω‖} := by
    refine (measure_union_le _ _).trans ?_
    rw [ae_iff.1 h_ae, add_zero]
  _ ≤ ENNReal.ofReal (8 * (∫ ω, ‖N d ω‖ ∂μ) / ε) := measure_exists_norm_gt_le hN hT d hε
  _ ≤ δ := by
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hε]
    linarith

end TotallyBounded

/-- The distance of a martingale to a fixed vector is a real quasimartingale. -/
lemma _root_.MeasureTheory.Martingale.isRealQuasimartingale_norm_sub [NormedSpace ℝ E]
    [CompleteSpace E] [OrderBot ι] [IsFiniteMeasure μ] (hX : Martingale X 𝓕 μ) (e : E) :
    IsRealQuasimartingale 𝓕 (fun t ω ↦ ‖X t ω - e‖) μ :=
  (hX.sub (martingale_const 𝓕 μ e)).submartingale_norm.isRealQuasimartingale

section RegularitySet

/-- A countable set whose closure contains the values of `X t` for all `t ∈ T`, if there is
such a set (which is the case if `T` is countable and `X` is strongly adapted). -/
noncomputable def denseValues (T : Set ι) (X : ι → Ω → E) : Set E :=
  open Classical in
  if h : TopologicalSpace.IsSeparable (⋃ t ∈ T, Set.range (X t)) then h.choose else ∅

omit [LinearOrder ι] in
lemma countable_denseValues : (denseValues T X).Countable := by
  unfold denseValues
  split_ifs with h
  · exact h.choose_spec.1
  · exact Set.countable_empty

omit [LinearOrder ι] in
lemma iUnion_range_subset_closure_denseValues (hT : T.Countable)
    (hX : ∀ t ∈ T, TopologicalSpace.IsSeparable (Set.range (X t))) :
    ⋃ t ∈ T, Set.range (X t) ⊆ closure (denseValues T X) := by
  have h : TopologicalSpace.IsSeparable (⋃ t ∈ T, Set.range (X t)) := by
    have := hT.to_subtype
    rw [Set.biUnion_eq_iUnion]
    exact .iUnion fun t ↦ hX t t.2
  simp only [denseValues, dif_pos h]
  exact h.choose_spec.2

/-- In this set, the path of the process along `T` before time `d` is totally bounded, and its
distance to any point `e` of the countable set `denseValues T X` is regular: `ω` belongs to the
`regularitySet` of the real process `‖X t - e‖`. We also require that the closure of
`denseValues T X` contains the values of `X` along `T`, which does not depend on `ω` and is true as
soon as `T` is countable and `X` is strongly adapted.

On this set, the path of the process along `T` has left and right limits at all times before `d`:
see `right_limit_of_mem_vectorRegularitySet` and `left_limit_of_mem_vectorRegularitySet`. -/
def vectorRegularitySet (T : Set ι) (X : ι → Ω → E) (d : ι) : Set Ω :=
  {ω | ⋃ t ∈ T, Set.range (X t) ⊆ closure (denseValues T X) ∧
    (∀ e ∈ denseValues T X, ω ∈ regularitySet T (fun t ω ↦ ‖X t ω - e‖) d) ∧
    TotallyBounded ((X · ω) '' (T ∩ Set.Iic d))}

lemma vectorRegularitySet_anti {d₁ d₂ : ι} (hd : d₁ ≤ d₂) :
    vectorRegularitySet T X d₂ ⊆ vectorRegularitySet T X d₁ :=
  fun _ hω ↦ ⟨hω.1, fun e he ↦ regularitySet_anti hd (hω.2.1 e he),
    hω.2.2.subset (Set.image_mono (Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.2 hd)))⟩

lemma measurableSet_totallyBounded_image (hX : StronglyAdapted 𝓕 X) (hT : T.Countable) (d : ι) :
    MeasurableSet[𝓕 d] {ω | TotallyBounded ((X · ω) '' (T ∩ Set.Iic d))} := by
  have h_eq : {ω | TotallyBounded ((X · ω) '' (T ∩ Set.Iic d))}
      = ⋂ k : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic d}, ⋂ t ∈ T ∩ Set.Iic d, ⋃ s ∈ F,
        {ω | dist (X t ω) (X s ω) < 1 / (k + 1 : ℝ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    refine ⟨fun h k ↦ ?_, fun h ↦ Metric.totallyBounded_iff.2 fun ε hε ↦ ?_⟩
    · obtain ⟨F, hF_sub, hF_fin, hF⟩ := Set.exists_subset_image_finite_and.1
        (Metric.finite_approx_of_totallyBounded h (1 / (k + 1 : ℝ)) (by positivity))
      refine ⟨hF_fin.toFinset, by simpa using hF_sub, fun t ht ↦ ?_⟩
      simpa using hF ⟨t, ht, rfl⟩
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨F, -, hFk⟩ := h k
      refine ⟨(X · ω) '' F, F.finite_toSet.image _, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨s, hs, hst⟩ := hFk t ht
      simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop]
      exact ⟨X s ω, ⟨s, hs, rfl⟩, hst.trans hk⟩
  rw [h_eq]
  refine MeasurableSet.iInter fun k ↦ MeasurableSet.biUnion
    (countable_setOf_finset_coe_subset (hT.mono Set.inter_subset_left)) fun F hF ↦
    MeasurableSet.biInter (hT.mono Set.inter_subset_left) fun t ht ↦
    Finset.measurableSet_biUnion _ fun s hs ↦ ?_
  have h1 : StronglyMeasurable[𝓕 d] (X t) := (hX t).mono (𝓕.mono ht.2)
  have h2 : StronglyMeasurable[𝓕 d] (X s) := (hX s).mono (𝓕.mono (hF hs).2)
  exact measurableSet_lt (h1.dist h2).measurable measurable_const

section OrderBot

variable [NormedSpace ℝ E] [CompleteSpace E] [OrderBot ι]

lemma measurableSet_vectorRegularitySet [IsFiniteMeasure μ] (hX : Martingale X 𝓕 μ)
    (hT : T.Countable) (d : ι) :
    MeasurableSet[𝓕 d] (vectorRegularitySet T X d) := by
  have h_eq : vectorRegularitySet T X d
      = {_ω | ⋃ t ∈ T, Set.range (X t) ⊆ closure (denseValues T X)}
        ∩ ((⋂ e ∈ denseValues T X, regularitySet T (fun t ω ↦ ‖X t ω - e‖) d)
        ∩ {ω | TotallyBounded ((X · ω) '' (T ∩ Set.Iic d))}) := by
    ext ω
    simp [vectorRegularitySet]
  rw [h_eq]
  refine (MeasurableSet.const _).inter (MeasurableSet.inter ?_ ?_)
  · exact MeasurableSet.biInter countable_denseValues fun e _ ↦
      measurableSet_regularitySet (hX.isRealQuasimartingale_norm_sub e) hT d
  · exact measurableSet_totallyBounded_image hX.stronglyAdapted hT d

lemma ae_mem_all_vectorRegularitySet [IsFiniteMeasure μ] (hX : Martingale X 𝓕 μ)
    {T' : Set ι} (hT : T.Countable) (hT' : T'.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T', ω ∈ vectorRegularitySet T X d := by
  have h1 : ∀ᵐ ω ∂μ, ∀ e ∈ denseValues T X, ∀ d ∈ T',
      ω ∈ regularitySet T (fun t ω ↦ ‖X t ω - e‖) d := by
    rw [ae_ball_iff countable_denseValues]
    exact fun e _ ↦ ae_mem_all_regularitySet (hX.isRealQuasimartingale_norm_sub e) hT hT'
  have h2 : ∀ᵐ ω ∂μ, ∀ d ∈ T', TotallyBounded ((X · ω) '' (T ∩ Set.Iic d)) := by
    rw [ae_ball_iff hT']
    exact fun d _ ↦ ae_totallyBounded_image hX hT d
  filter_upwards [h1, h2] with ω hω1 hω2 d hd
  exact ⟨iUnion_range_subset_closure_denseValues hT
    fun t _ ↦ (hX.stronglyAdapted t).isSeparable_range, fun e he ↦ hω1 e he d hd, hω2 d hd⟩

end OrderBot

/-- On `vectorRegularitySet T X d`, the path along `T` before `d` stays in a compact set, whose
points are limits of points of `denseValues T X`. -/
lemma exists_isCompact_of_mem_vectorRegularitySet [CompleteSpace E] {d : ι} {ω : Ω}
    (hω : ω ∈ vectorRegularitySet T X d) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ closure (denseValues T X) ∧
      ∀ s ∈ T ∩ Set.Iic d, X s ω ∈ K := by
  refine ⟨closure ((X · ω) '' (T ∩ Set.Iic d)), hω.2.2.closure.isCompact_of_isClosed
    isClosed_closure, closure_minimal ?_ isClosed_closure,
    fun s hs ↦ subset_closure ⟨s, hs, rfl⟩⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hω.1 (Set.mem_biUnion ht.1 (Set.mem_range_self ω))

variable [TopologicalSpace ι]

section Limits

variable [CompleteSpace E] [OrderTopology ι] {x d : ι} {ω : Ω}

lemma right_limit_of_mem_vectorRegularitySet (hxd : x < d)
    (hω : ω ∈ vectorRegularitySet T X d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 l) := by
  obtain ⟨K, hK, hKD, hXK⟩ := exists_isCompact_of_mem_vectorRegularitySet hω
  refine exists_tendsto_of_tendsto_norm_sub hK ?_ hKD
    fun e he ↦ right_limit_of_mem_regularitySet x d hxd (hω.2.1 e he)
  have hU : Set.Ioc x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x :=
    Filter.mem_of_superset (Ioo_inter_mem_nhdsWithin_inter_Ioi hxd) (by grind)
  filter_upwards [hU] with s hs using hXK s ⟨hs.2, hs.1.2⟩

lemma left_limit_of_mem_vectorRegularitySet (hxd : x ≤ d)
    (hω : ω ∈ vectorRegularitySet T X d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 l) := by
  obtain ⟨K, hK, hKD, hXK⟩ := exists_isCompact_of_mem_vectorRegularitySet hω
  refine exists_tendsto_of_tendsto_norm_sub hK ?_ hKD
    fun e he ↦ left_limit_of_mem_regularitySet x d hxd (hω.2.1 e he)
  filter_upwards [self_mem_nhdsWithin] with s hs using hXK s ⟨hs.1, hs.2.le.trans hxd⟩

/-- The events `vectorRegularitySet T X d` form a regularity family for the process `X`. -/
lemma isRegularityFamily_vectorRegularitySet :
    IsRegularityFamily T X (vectorRegularitySet T X) :=
  ⟨fun _ _ hd ↦ vectorRegularitySet_anti hd,
    fun _ _ _ hxd hω ↦ right_limit_of_mem_vectorRegularitySet hxd hω,
    fun _ _ _ hxd hω ↦ left_limit_of_mem_vectorRegularitySet hxd hω⟩

end Limits

end RegularitySet

/-! ## Right-continuous and càdlàg modifications

The modifications are the processes `rightContModifOf` and `cadlagModifOf` for the regularity family
`vectorRegularitySet (regularityTimes ι) X`. For a martingale `X` with values in a Banach space,
* `vectorRightContModif X` is right-continuous, and has left limits almost everywhere
* `vectorCadlagModif X` is càdlàg
* if the filtration is right-continuous, then `vectorRightContModif X` is strongly adapted and both
  processes are modifications of `X`
* if the filtration is right-continuous and complete, then `vectorCadlagModif X` is strongly
  adapted, hence a martingale.

-/

section Modification

variable [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]

/-- The right-continuous modification of a martingale with values in a Banach space, defined from
the right limits along the countable dense set `regularityTimes ι`. -/
noncomputable
def vectorRightContModif (X : ι → Ω → E) : ι → Ω → E :=
  rightContModifOf (vectorRegularitySet (regularityTimes ι) X) X

/-- The càdlàg modification of a martingale with values in a Banach space, defined from the right
limits along the countable dense set `regularityTimes ι`. -/
noncomputable
def vectorCadlagModif (X : ι → Ω → E) : ι → Ω → E :=
  cadlagModifOf (vectorRegularitySet (regularityTimes ι) X) X

variable [CompleteSpace E]

/-- The paths of `vectorRightContModif X` are right-continuous. -/
lemma continuousWithinAt_vectorRightContModif (x : ι) (ω : Ω) :
    ContinuousWithinAt (vectorRightContModif X · ω) (Set.Ioi x) x :=
  continuousWithinAt_rightContModifOf isRegularityFamily_vectorRegularitySet x ω

/-- The paths of `vectorCadlagModif X` are càdlàg. -/
theorem isCadlag_vectorCadlagModif (ω : Ω) : IsCadlag (vectorCadlagModif X · ω) :=
  isCadlag_cadlagModifOf isRegularityFamily_vectorRegularitySet ω

variable [NormedSpace ℝ E] [OrderBot ι] [IsFiniteMeasure μ]

/-- Almost surely, `ω` belongs to all the events used to define the modifications of a martingale
with values in a Banach space. -/
lemma _root_.MeasureTheory.Martingale.ae_mem_regularitySetRight_vectorRegularitySet
    (hX : Martingale X 𝓕 μ) :
    ∀ᵐ ω ∂μ, ∀ t, ω ∈ regularitySetRight (regularityTimes ι)
      (vectorRegularitySet (regularityTimes ι) X) t :=
  ae_mem_regularitySetRight
    (ae_mem_all_vectorRegularitySet hX countable_regularityTimes
      (countable_regularityTimes.union countable_setOfPred_isolated_right))
    fun _ ↦ dense_regularityTimes.exists_gt_of_not_isMax

lemma stronglyMeasurable_vectorRightContModif (hX : Martingale X 𝓕 μ) (t : ι) :
    StronglyMeasurable (vectorRightContModif X t) :=
  stronglyMeasurable_rightContModifOf isRegularityFamily_vectorRegularitySet hX.stronglyAdapted
    (measurableSet_vectorRegularitySet hX countable_regularityTimes) t

lemma stronglyAdapted_vectorRightContModif [𝓕.IsRightContinuous] (hX : Martingale X 𝓕 μ) :
    StronglyAdapted 𝓕 (vectorRightContModif X) :=
  stronglyAdapted_rightContModifOf isRegularityFamily_vectorRegularitySet hX.stronglyAdapted
    (measurableSet_vectorRegularitySet hX countable_regularityTimes)

/-- The right-continuous modification of a martingale with values in a Banach space, with respect
to a right-continuous filtration, is a modification. -/
theorem _root_.MeasureTheory.Martingale.vectorRightContModif_ae_eq [𝓕.IsRightContinuous]
    (hX : Martingale X 𝓕 μ) (t : ι) :
    vectorRightContModif X t =ᵐ[μ] X t :=
  hX.rightContModifOf_ae_eq hX.ae_mem_regularitySetRight_vectorRegularitySet
    isRegularityFamily_vectorRegularitySet
    (measurableSet_vectorRegularitySet hX countable_regularityTimes) t

lemma vectorCadlagModif_ae_eq_vectorRightContModif (hX : Martingale X 𝓕 μ) :
    ∀ᵐ ω ∂μ, ∀ t, vectorCadlagModif X t ω = vectorRightContModif X t ω :=
  cadlagModifOf_ae_eq_rightContModifOf hX.ae_mem_regularitySetRight_vectorRegularitySet

lemma stronglyMeasurable_vectorCadlagModif (hX : Martingale X 𝓕 μ) (t : ι) :
    StronglyMeasurable (vectorCadlagModif X t) :=
  stronglyMeasurable_cadlagModifOf isRegularityFamily_vectorRegularitySet hX.stronglyAdapted
    (measurableSet_vectorRegularitySet hX countable_regularityTimes) t

lemma stronglyAdapted_vectorCadlagModif [𝓕.IsRightContinuous] [𝓕.IsComplete μ]
    (hX : Martingale X 𝓕 μ) :
    StronglyAdapted 𝓕 (vectorCadlagModif X) :=
  stronglyAdapted_cadlagModifOf isRegularityFamily_vectorRegularitySet hX.stronglyAdapted
    (measurableSet_vectorRegularitySet hX countable_regularityTimes)
    hX.ae_mem_regularitySetRight_vectorRegularitySet

/-- The càdlàg modification of a martingale with values in a Banach space, with respect to a
right-continuous filtration, is a modification. -/
theorem _root_.MeasureTheory.Martingale.vectorCadlagModif_ae_eq [𝓕.IsRightContinuous]
    (hX : Martingale X 𝓕 μ) (t : ι) :
    vectorCadlagModif X t =ᵐ[μ] X t :=
  cadlagModifOf_ae_eq_of_rightContModifOf_ae_eq hX.ae_mem_regularitySetRight_vectorRegularitySet
    (hX.vectorRightContModif_ae_eq t)

/-- The càdlàg modification of a martingale with values in a Banach space, with respect to a
right-continuous and complete filtration, is a martingale. -/
theorem _root_.MeasureTheory.Martingale.martingale_vectorCadlagModif [𝓕.IsRightContinuous]
    [𝓕.IsComplete μ] (hX : Martingale X 𝓕 μ) :
    Martingale (vectorCadlagModif X) 𝓕 μ :=
  hX.congr (stronglyAdapted_vectorCadlagModif hX) fun t ↦ (hX.vectorCadlagModif_ae_eq t).symm

/-- A martingale with values in a Banach space, with respect to a right-continuous and complete
filtration, has a modification which is a martingale with càdlàg paths. -/
theorem _root_.MeasureTheory.Martingale.exists_isCadlag_modification [𝓕.IsRightContinuous]
    [𝓕.IsComplete μ] (hX : Martingale X 𝓕 μ) :
    ∃ Y : ι → Ω → E, Martingale Y 𝓕 μ ∧ (∀ ω, IsCadlag (Y · ω)) ∧ ∀ t, Y t =ᵐ[μ] X t :=
  ⟨vectorCadlagModif X, hX.martingale_vectorCadlagModif, isCadlag_vectorCadlagModif,
    hX.vectorCadlagModif_ae_eq⟩

end Modification

end ProbabilityTheory
