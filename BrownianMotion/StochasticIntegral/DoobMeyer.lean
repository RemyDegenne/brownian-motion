/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.ClassD
public import BrownianMotion.StochasticIntegral.Komlos
public import Mathlib.Topology.Order.LiminfLimsup

/-! # Doob-Meyer decomposition theorem

-/

@[expose] public section

open MeasureTheory Filter Order
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

namespace DoobMeyer

section DenseMesh

variable (ι) [LinearOrder ι] [OrderBot ι] [OrderTop ι] [TopologicalSpace ι]
  [SecondCountableTopology ι]

/-- The fixed countable dense set used instead of dyadics, with both endpoints adjoined. -/
noncomputable def denseSet : Set ι :=
  (TopologicalSpace.exists_countable_dense ι).choose ∪ ({⊥, ⊤} : Set ι)

lemma denseSet_countable : (denseSet ι).Countable := by
  have h_dense_countable := (TopologicalSpace.exists_countable_dense ι).choose_spec.1
  simpa [denseSet] using h_dense_countable.union (by simp : ({⊥, ⊤} : Set ι).Countable)

lemma denseSet_dense : Dense (denseSet ι) :=
  (TopologicalSpace.exists_countable_dense ι).choose_spec.2.mono (Set.subset_union_left)

/-- A choice of enumeration of the countable dense set used to construct finite meshes. -/
noncomputable def denseEnum : ℕ → ι :=
  have : Nonempty (denseSet ι) := ⟨⟨⊥, by simp [denseSet]⟩⟩
  Subtype.val ∘ (countable_iff_exists_surjective.mp (denseSet_countable ι)).choose

/-- The `n`-th finite mesh: the first `n` points of the dense enumeration, plus endpoints. -/
noncomputable def mesh (n : ℕ) : Finset ι :=
  insert ⊥ <| insert ⊤ <| (Finset.range n).image (denseEnum ι)

lemma bot_mem_mesh (n : ℕ) : (⊥ : ι) ∈ mesh ι n := by simp [mesh]

lemma top_mem_mesh (n : ℕ) : (⊤ : ι) ∈ mesh ι n := by simp [mesh]

instance (n : ℕ) : OrderBot (mesh ι n) where
  bot := ⟨⊥, bot_mem_mesh ι n⟩
  bot_le _ := bot_le

instance (n : ℕ) : OrderTop (mesh ι n) where
  top := ⟨⊤, top_mem_mesh ι n⟩
  le_top _ := le_top

noncomputable instance (n : ℕ) : LocallyFiniteOrder (mesh ι n) :=
  Fintype.toLocallyFiniteOrder

noncomputable instance (n : ℕ) : SuccOrder (mesh ι n) :=
  LinearLocallyFiniteOrder.succOrder (mesh ι n)

noncomputable instance (n : ℕ) : PredOrder (mesh ι n) :=
  LinearLocallyFiniteOrder.predOrder (mesh ι n)

end DenseMesh

section UniformIntegrability

variable {ι : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι]
  [LinearOrder ι] [OrderBot ι] [OrderTop ι] [SuccOrder ι]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The filtration obtained by restricting `𝓕` to a finite dense mesh. -/
def meshFiltration (𝓕 : Filtration ι mΩ) (n : ℕ) :
    Filtration (mesh ι n) mΩ :=
  𝓕.indexComap (Subtype.mono_coe (SetLike.coe (mesh ι n)))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Predictable part of a discrete process. -/
noncomputable def predictablePart [LocallyFiniteOrder ι] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω) :
    ι → Ω → E :=
  fun n ↦ ∑ i ∈ Finset.Iio n, P[S (succ i) - S i | 𝓕 i]

/-- Martingale part of a discrete process. -/
noncomputable def martingalePart [LocallyFiniteOrder ι] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω) :
    ι → Ω → E :=
  S - predictablePart S 𝓕 P

/-- Sequence of terminal values of the predictable part. -/
noncomputable def predictableSeq (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) :=
  predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⊤

/-- Sequence of terminal values of the martingale part. -/
noncomputable def martingaleSeq (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) :=
  martingalePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⊤

variable {S : ι → Ω → E} [LE E] {𝓕 : Filtration ι mΩ}

/-- The terminal values of the predictable parts are uniformly integrable. -/
lemma uniformIntegrable_terminal_predictablePart (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) :
    UniformIntegrable (predictableSeq S 𝓕 P) 1 P := by
  sorry

/-- As the terminal values of predictable parts are uniformly integrable, the terminal values of the
martingale parts are uniformly integrable. -/
lemma uniformIntegrable_terminal_martingalePart_of_predictablePart (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) :
    UniformIntegrable (martingaleSeq S 𝓕 P) 1 P := by
  sorry

/-- Show that the terminals values of some convex combinations of the martingale parts converge. -/
lemma exists_martingalPart_lim (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) :
    ∃ M : Ω → E, ∃ a : ℕ → StdSimplex ℝ ℕ,
      Tendsto (fun n ↦ eLpNorm ((a n).sum (fun m r ↦ r • martingaleSeq S 𝓕 P m) - M) 1 P)
      atTop (𝓝 0) := by
  sorry

end UniformIntegrability

-- We define the martingale part in the doob-meyer decomposition.
section MDef

variable {ι : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι]
  [LinearOrder ι] [OrderBot ι] [OrderTop ι] [SuccOrder ι]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {S : ι → Ω → E} [LE E] {𝓕 : Filtration ι mΩ}

/-- This is the martingalePart in the doob-meyer decomposition of a submartingale. -/
noncomputable def martingalePartLim (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) (i : ι) :=
  P[(exists_martingalPart_lim hs hc hd).choose | 𝓕 i]

lemma martingale_martingalePart (hs : Submartingale S 𝓕 P)
        (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) [SigmaFiniteFiltration P 𝓕] :
    Martingale (martingalePartLim hs hc hd) 𝓕 P :=
  martingale_condExp (exists_martingalPart_lim hs hc hd).choose 𝓕 P

/-- This is the weight associated with the martingale part. -/
noncomputable def weight (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) : ℕ → StdSimplex ℝ ℕ :=
  (exists_martingalPart_lim hs hc hd).choose_spec.choose

/-- The extension of the discrete martingale part `M^n`. -/
noncomputable def martingaleSeqStep (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    (n : ℕ) (i : ι) :=
  P[martingaleSeq S 𝓕 P n | 𝓕 i]

/-- The convexly averaged mesh step-extension `ℳ^n` of the martingale parts. -/
noncomputable def martingaleConvexStep (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) (n : ℕ) : ι → Ω → E :=
  (weight hs hc hd n).sum fun m r ↦ r • martingaleSeqStep S 𝓕 P m

end MDef

-- We define the predictable part in the doob-meyer decomposition.
section ADef

variable {ι : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι]
  [LinearOrder ι] [OrderBot ι] [OrderTop ι] [SuccOrder ι]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {S : ι → Ω → E} [LE E] {𝓕 : Filtration ι mΩ}

/-- The half-open mesh interval ending at `t`, with left endpoint the predecessor of `t` in the
finite mesh. -/
def meshPredIoc (n : ℕ) (t : mesh ι n) : Set ι :=
  Set.Ioc ((pred t : mesh ι n) : ι) (t : ι)

/-- The mesh step-extension of the discrete predictable part `A^n`. -/
noncomputable def predictableSeqStep (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    (n : ℕ) : ι → Ω → E :=
  fun t ↦ ∑ u : mesh ι n, (meshPredIoc n u).indicator
    (fun _ : ι ↦ predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P u) t

/-- The convexly averaged mesh step-extension `𝒜^n` of the predictable parts. -/
noncomputable def predictableConvexStep (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) (n : ℕ) : ι → Ω → E :=
  (weight hs hc hd n).sum fun m r ↦ r • predictableSeqStep S 𝓕 P m

/-- The predictable part in the Doob-Meyer decomposition, defined as `S - M`. -/
noncomputable def predictablePartLim (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) : ι → Ω → E :=
  S - martingalePartLim hs hc hd

/-- `L¹` norm convergence of `predictableConvexStep`. -/
lemma predictableConvexStep_eLpNorm_tendsto (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) (t : ι) :
    Tendsto (fun n ↦ eLpNorm
      (predictableConvexStep hs hc hd n t - predictablePartLim hs hc hd t) 1 P) atTop (𝓝 0) := by
  sorry

/-- Almost everywhere convergence of `predictableConvexStep`. -/
lemma predictableConvexStep_ae_tendsto (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) (t : ι) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ predictableConvexStep hs hc hd (φ n) t ω)
        atTop (𝓝 (predictablePartLim hs hc hd t ω)) := by
  sorry

end ADef

section MonotoneA

variable {ι : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι]
  [LinearOrder ι] [OrderBot ι] [OrderTop ι] [SuccOrder ι]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {S : ι → Ω → E} [LE E] {𝓕 : Filtration ι mΩ}

lemma predictableSeqStep_monotone_ae {X : ι → Ω → ℝ} (hs : Submartingale X 𝓕 P)
    (hc : ∀ ω, IsCadlag (X · ω)) (hd : ClassD X 𝓕 P) (n : ℕ) :
    ∀ᵐ ω ∂P, Monotone fun t ↦ predictableSeqStep X 𝓕 P n t ω := by
  sorry

lemma predictableConvexStep_monotone_ae {X : ι → Ω → ℝ} (hs : Submartingale X 𝓕 P)
    (hc : ∀ ω, IsCadlag (X · ω)) (hd : ClassD X 𝓕 P) (n : ℕ) :
    ∀ᵐ ω ∂P, Monotone fun t ↦ predictableConvexStep hs hc hd n t ω := by
  sorry

lemma predictablePartLim_monotone_ae {X : ι → Ω → ℝ} (hs : Submartingale X 𝓕 P)
    (hc : ∀ ω, IsCadlag (X · ω)) (hd : ClassD X 𝓕 P) :
    ∀ᵐ ω ∂P, Monotone fun t ↦ predictablePartLim hs hc hd t ω := by
  sorry

end MonotoneA

section LeftContinuousA

variable {ι : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι]
  [LinearOrder ι] [OrderBot ι] [OrderTop ι] [SuccOrder ι]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {S : ι → Ω → E} {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}

/-- The mesh step-extension of the discrete predictable part is left-continuous in time. -/
lemma predictableSeqStep_leftContinuous (n : ℕ) (ω : Ω) :
    ∀ t : ι, ContinuousWithinAt (fun s ↦ predictableSeqStep S 𝓕 P n s ω) (Set.Iio t) t := by
  sorry

/-- `predictableConvexStep` is left-continuous in time. -/
lemma predictableConvexStep_leftContinuous (n : ℕ) (hs : Submartingale X 𝓕 P)
    (hc : ∀ ω, IsCadlag (X · ω)) (hd : ClassD X 𝓕 P) (ω : Ω) :
    ∀ t : ι, ContinuousWithinAt (fun s ↦ predictableConvexStep hs hc hd n s ω) (Set.Iio t) t := by
  sorry

end LeftContinuousA

section Adapted

variable {ι : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι]
  [LinearOrder ι] [OrderBot ι] [OrderTop ι] [SuccOrder ι]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {S : ι → Ω → E} {𝓕 : Filtration ι mΩ}

omit [MeasurableSpace ι] [SuccOrder ι] in
private lemma stronglyMeasurable_predictablePart_mesh_le (n : ℕ) {u : mesh ι n} {t : ι}
    (hut : ((pred u : mesh ι n) : ι) ≤ t) :
    StronglyMeasurable[𝓕 t]
      (predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P u) := by
  simp only [predictablePart]
  refine Finset.stronglyMeasurable_sum _ fun i hi ↦ ?_
  have hiu : i < u := Finset.mem_Iio.mp hi
  have hi_pred : i ≤ (pred u : mesh ι n) := le_pred_of_lt hiu
  have hi_le_pred : (i : ι) ≤ ((pred u : mesh ι n) : ι) := hi_pred
  have hi_le_t : (i : ι) ≤ t := hi_le_pred.trans hut
  exact stronglyMeasurable_condExp.mono (by simpa [meshFiltration] using 𝓕.mono hi_le_t)

omit [MeasurableSpace ι] [SuccOrder ι] in
/-- The mesh step-extension of the discrete predictable part is strongly adapted. -/
lemma stronglyAdapted_predictableSeqStep (n : ℕ) :
    StronglyAdapted 𝓕 (predictableSeqStep S 𝓕 P n) := by
  intro t
  simp only [predictableSeqStep]
  refine Finset.stronglyMeasurable_sum _ fun u _hu ↦ ?_
  by_cases htu : t ∈ meshPredIoc (ι := ι) n u
  · rw [Set.indicator_of_mem htu]
    exact stronglyMeasurable_predictablePart_mesh_le (S := S) (𝓕 := 𝓕) (P := P) n htu.1.le
  · rw [Set.indicator_of_notMem htu]
    exact stronglyMeasurable_zero

/-- The convexly averaged mesh step-extension of the predictable parts is strongly adapted. -/
lemma stronglyAdapted_predictableConvexStep [LE E] (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) (n : ℕ) :
    StronglyAdapted 𝓕 (predictableConvexStep hs hc hd n) := by
  intro t
  simp only [predictableConvexStep, Pi.smul_apply, Finsupp.sum_apply']
  rw [Finsupp.sum]
  refine Finset.stronglyMeasurable_sum _ fun m _hm ↦ ?_
  exact (stronglyAdapted_predictableSeqStep (S := S) (𝓕 := 𝓕) (P := P) m t).const_smul _

end Adapted

lemma monotone_of_tendsto_atTop_of_monotone
    {α β : Type*} [Preorder α] [TopologicalSpace β] [Preorder β] [OrderClosedTopology β]
    {F : ℕ → α → β} {f : α → β}
    (hF : ∀ n, Monotone (F n))
    (hlim : ∀ x, Tendsto (fun n : ℕ ↦ F n x) atTop (𝓝 (f x))) :
    Monotone f := by
  intro x y hxy
  exact le_of_tendsto_of_tendsto (hlim x) (hlim y)
    (Eventually.of_forall fun n : ℕ ↦ hF n hxy)

section Limsup

private lemma mem_closure_dense_inter_Ioi
    {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    {D : Set α} (hD_dense : Dense D) {t : α} (ht : (Set.Ioi t).Nonempty) :
    t ∈ closure (D ∩ Set.Ioi t) := by
  have ht_closure : t ∈ closure (Set.Ioi t) := by
    rw [closure_Ioi' ht]
    simp
  have hsubset : Set.Ioi t ⊆ closure (Set.Ioi t ∩ D) :=
    hD_dense.open_subset_closure_inter isOpen_Ioi
  have hclosure_subset : closure (Set.Ioi t) ⊆ closure (closure (Set.Ioi t ∩ D)) :=
    closure_mono hsubset
  have : t ∈ closure (Set.Ioi t ∩ D) := by
    simpa only [closure_closure] using hclosure_subset ht_closure
  simpa [Set.inter_comm] using this

private lemma mem_closure_dense_inter_Iio
    {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    {D : Set α} (hD_dense : Dense D) {t : α} (ht : (Set.Iio t).Nonempty) :
    t ∈ closure (D ∩ Set.Iio t) := by
  have ht_closure : t ∈ closure (Set.Iio t) := by
    rw [closure_Iio' ht]
    simp
  have hsubset : Set.Iio t ⊆ closure (Set.Iio t ∩ D) :=
    hD_dense.open_subset_closure_inter isOpen_Iio
  have hclosure_subset : closure (Set.Iio t) ⊆ closure (closure (Set.Iio t ∩ D)) :=
    closure_mono hsubset
  have : t ∈ closure (Set.Iio t ∩ D) := by
    simpa only [closure_closure] using hclosure_subset ht_closure
  simpa [Set.inter_comm] using this

/-- Monotone convergence on a dense set controls the pointwise `limsup` everywhere.

This is the order-topological version of the first displayed assertion in the paper, with `[0, 1]`
replaced by a general linearly ordered index type with endpoints and `ℝ` replaced by a
conditionally complete linear order. -/
lemma limsup_le_of_monotone_of_tendsto_on_dense
    {α β : Type*} [LinearOrder α] [OrderBot α] [OrderTop α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
    [OrderTopology β] {D : Set α} {F : ℕ → α → β} {f : α → β}
    (hF_mono : ∀ n, Monotone (F n)) (hf_mono : Monotone f)
    (hf_right : Function.IsRightContinuous f) (hD_dense : Dense D) (hD_bot : (⊥ : α) ∈ D)
    (hD_top : (⊤ : α) ∈ D)
    (hD_lim : ∀ t ∈ D, Tendsto (fun n : ℕ ↦ F n t) atTop (𝓝 (f t))) (t : α) :
    limsup (fun n : ℕ ↦ F n t) atTop ≤ f t := by
  have _hf_mono : Monotone f := hf_mono
  by_cases ht_top : t = ⊤
  · subst t
    exact le_of_eq (hD_lim ⊤ hD_top).limsup_eq
  have ht_lt_top : t < ⊤ := lt_top_iff_ne_top.mpr ht_top
  have hFt_bddBelow : atTop.IsBoundedUnder (· ≥ ·) (fun n : ℕ ↦ F n t) :=
    ((hD_lim ⊥ hD_bot).isBoundedUnder_ge).mono_ge <|
      Eventually.of_forall fun n : ℕ ↦ hF_mono n bot_le
  have hFt_cobdd : atTop.IsCoboundedUnder (· ≤ ·) (fun n : ℕ ↦ F n t) :=
    hFt_bddBelow.isCoboundedUnder_le
  haveI : NeBot (𝓝[D ∩ Set.Ioi t] t) := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    exact mem_closure_dense_inter_Ioi hD_dense ⟨⊤, ht_lt_top⟩
  have hf_tendsto : Tendsto f (𝓝[D ∩ Set.Ioi t] t) (𝓝 (f t)) :=
    (hf_right t).mono_left (nhdsWithin_mono t Set.inter_subset_right)
  have hlimsup_le : ∀ᶠ s in 𝓝[D ∩ Set.Ioi t] t,
      limsup (fun n : ℕ ↦ F n t) atTop ≤ f s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hle : (fun n : ℕ ↦ F n t) ≤ᶠ[atTop] fun n : ℕ ↦ F n s :=
      Eventually.of_forall fun n : ℕ ↦ hF_mono n (le_of_lt hs.2)
    calc
      limsup (fun n : ℕ ↦ F n t) atTop
          ≤ limsup (fun n : ℕ ↦ F n s) atTop :=
            limsup_le_limsup hle hFt_cobdd (hD_lim s hs.1).isBoundedUnder_le
      _ = f s := (hD_lim s hs.1).limsup_eq
  exact ge_of_tendsto hf_tendsto hlimsup_le

/-- At continuity points of the limiting monotone function, convergence on the dense set upgrades to
pointwise convergence. -/
lemma tendsto_of_monotone_of_tendsto_on_dense_of_continuousAt
    {α β : Type*} [LinearOrder α] [OrderBot α] [OrderTop α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
    [OrderTopology β] {D : Set α} {F : ℕ → α → β} {f : α → β}
    (hF_mono : ∀ n, Monotone (F n)) (hf_mono : Monotone f)
    (hf_right : Function.IsRightContinuous f) (hD_dense : Dense D) (hD_bot : (⊥ : α) ∈ D)
    (hD_top : (⊤ : α) ∈ D)
    (hD_lim : ∀ t ∈ D, Tendsto (fun n : ℕ ↦ F n t) atTop (𝓝 (f t))) {t : α}
    (hf_cont : ContinuousAt f t) :
    Tendsto (fun n : ℕ ↦ F n t) atTop (𝓝 (f t)) := by
  by_cases ht_bot : t = ⊥
  · subst t
    exact hD_lim ⊥ hD_bot
  have hbot_lt : (⊥ : α) < t := bot_lt_iff_ne_bot.mpr ht_bot
  have hFt_bddBelow : atTop.IsBoundedUnder (· ≥ ·) (fun n : ℕ ↦ F n t) :=
    ((hD_lim ⊥ hD_bot).isBoundedUnder_ge).mono_ge <|
      Eventually.of_forall fun n : ℕ ↦ hF_mono n bot_le
  have hFt_bddAbove : atTop.IsBoundedUnder (· ≤ ·) (fun n : ℕ ↦ F n t) :=
    ((hD_lim ⊤ hD_top).isBoundedUnder_le).mono_le <|
      Eventually.of_forall fun n : ℕ ↦ hF_mono n le_top
  have hFt_cobdd_ge : atTop.IsCoboundedUnder (· ≥ ·) (fun n : ℕ ↦ F n t) :=
    hFt_bddAbove.isCoboundedUnder_ge
  haveI : NeBot (𝓝[D ∩ Set.Iio t] t) := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    exact mem_closure_dense_inter_Iio hD_dense ⟨⊥, hbot_lt⟩
  have hf_tendsto : Tendsto f (𝓝[D ∩ Set.Iio t] t) (𝓝 (f t)) :=
    hf_cont.tendsto.mono_left nhdsWithin_le_nhds
  have hliminf_ge : f t ≤ liminf (fun n : ℕ ↦ F n t) atTop := by
    have heventually : ∀ᶠ s in 𝓝[D ∩ Set.Iio t] t,
        f s ≤ liminf (fun n : ℕ ↦ F n t) atTop := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hle : (fun n : ℕ ↦ F n s) ≤ᶠ[atTop] fun n : ℕ ↦ F n t :=
        Eventually.of_forall fun n : ℕ ↦ hF_mono n (le_of_lt hs.2)
      calc
        f s = liminf (fun n : ℕ ↦ F n s) atTop := (hD_lim s hs.1).liminf_eq.symm
        _ ≤ liminf (fun n : ℕ ↦ F n t) atTop :=
          liminf_le_liminf hle (hD_lim s hs.1).isBoundedUnder_ge hFt_cobdd_ge
    exact le_of_tendsto hf_tendsto heventually
  have hlimsup_le : limsup (fun n : ℕ ↦ F n t) atTop ≤ f t :=
    limsup_le_of_monotone_of_tendsto_on_dense hF_mono hf_mono hf_right hD_dense hD_bot
      hD_top hD_lim t
  exact tendsto_of_le_liminf_of_limsup_le hliminf_ge hlimsup_le hFt_bddAbove hFt_bddBelow

end Limsup

end DoobMeyer

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
  [MeasurableSpace ι]

namespace IsLocalSubmartingale

theorem doob_meyer (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∃ (M A : ι → Ω → ℝ), X = M + A ∧ IsLocalMartingale M 𝓕 P ∧ (∀ ω, IsCadlag (M · ω)) ∧
      IsPredictable 𝓕 A ∧ (∀ ω, IsCadlag (A · ω)) ∧ (HasLocallyIntegrableSup A 𝓕 P)
      ∧ (∀ ω, Monotone (A · ω)) := by
  sorry

/-- The local martingale part of the Doob-Meyer decomposition of the local submartingale. -/
noncomputable
def martingalePart (X : ι → Ω → ℝ)
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ :=
  (hX.doob_meyer hX_cadlag).choose

/-- The predictable part of the Doob-Meyer decomposition of the local submartingale. -/
noncomputable
def predictablePart (X : ι → Ω → ℝ)
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose

lemma martingalePart_add_predictablePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    X = hX.martingalePart X hX_cadlag + hX.predictablePart X hX_cadlag :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.1

lemma isLocalMartingale_martingalePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    IsLocalMartingale (hX.martingalePart X hX_cadlag) 𝓕 P :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.1

lemma cadlag_martingalePart (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∀ ω, IsCadlag (hX.martingalePart X hX_cadlag · ω) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.1

lemma isPredictable_predictablePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    IsPredictable 𝓕 (hX.predictablePart X hX_cadlag) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.1

lemma cadlag_predictablePart (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∀ ω, IsCadlag (hX.predictablePart X hX_cadlag · ω) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.1

lemma hasLocallyIntegrableSup_predictablePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    HasLocallyIntegrableSup (hX.predictablePart X hX_cadlag) 𝓕 P :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.2.1

lemma monotone_predictablePart (hX : IsLocalSubmartingale X 𝓕 P)
    (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∀ ω, Monotone (hX.predictablePart X hX_cadlag · ω) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.2.2

end IsLocalSubmartingale

end ProbabilityTheory
