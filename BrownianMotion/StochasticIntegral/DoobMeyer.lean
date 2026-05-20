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

open MeasureTheory Filter Order ProbabilityTheory
open scoped NNReal ENNReal Topology

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

section MonotoneLim

/-- The limit of a collection of functions that is frequently monotone is monotone. -/
lemma monotone_of_frequently_monotone_of_tendsto {ι α β : Type*} [Preorder α] [TopologicalSpace β]
    [Preorder β] [OrderClosedTopology β] {l : Filter ι} [l.NeBot] {F : ι → α → β} {f : α → β}
    (hF : ∃ᶠ i in l, Monotone (F i)) (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Monotone f :=
  fun a b hab => le_of_tendsto_of_tendsto_of_frequently (hlim a) (hlim b)
    (hF.mono (fun _ hi => hi hab))

/-- The limit of a collection of functions that is frequently antitone is antitone. -/
lemma antitone_of_frequently_antitone_of_tendsto {ι α β : Type*} [Preorder α] [TopologicalSpace β]
    [Preorder β] [OrderClosedTopology β] {l : Filter ι} [l.NeBot] {F : ι → α → β} {f : α → β}
    (hF : ∃ᶠ i in l, Antitone (F i)) (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Antitone f :=
  monotone_of_frequently_monotone_of_tendsto (β := βᵒᵈ) hF hlim

/-- The limit of a collection of functions that is eventually monotone is monotone. -/
lemma monotone_of_eventually_monotone_of_tendsto {ι α β : Type*} [Preorder α] [TopologicalSpace β]
    [Preorder β] [OrderClosedTopology β] {l : Filter ι} [l.NeBot] {F : ι → α → β} {f : α → β}
    (hF : ∀ᶠ i in l, Monotone (F i)) (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Monotone f :=
  monotone_of_frequently_monotone_of_tendsto hF.frequently hlim

/-- The limit of a collection of functions that is eventually antitone is antitone. -/
lemma antitone_of_eventually_antitone_of_tendsto {ι α β : Type*} [Preorder α] [TopologicalSpace β]
    [Preorder β] [OrderClosedTopology β] {l : Filter ι} [l.NeBot] {F : ι → α → β} {f : α → β}
    (hF : ∀ᶠ i in l, Antitone (F i)) (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Antitone f :=
  monotone_of_eventually_monotone_of_tendsto (β := βᵒᵈ) hF hlim

/-- The limit of a collection of monotone functions is monotone. -/
lemma monotone_of_monotone_of_tendsto {ι α β : Type*} [Preorder α] [TopologicalSpace β]
    [Preorder β] [OrderClosedTopology β] {l : Filter ι} [l.NeBot] {F : ι → α → β} {f : α → β}
    (hF : ∀ i, Monotone (F i)) (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Monotone f :=
  monotone_of_eventually_monotone_of_tendsto (Eventually.of_forall hF) hlim

/-- The limit of a collection of antitone functions is antitone. -/
lemma antitone_of_antitone_of_tendsto {ι α β : Type*} [Preorder α] [TopologicalSpace β]
    [Preorder β] [OrderClosedTopology β] {l : Filter ι} [l.NeBot] {F : ι → α → β} {f : α → β}
    (hF : ∀ i, Antitone (F i)) (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Antitone f :=
  monotone_of_monotone_of_tendsto (β := βᵒᵈ) hF hlim

/-- This is an auxillary lemma used to prove `Dense.monotone_of_isRightContinuous`. It is saying
that if `D` is a dense set and `a, b` are two points such that `a < b`, then the comap of
`𝓝[Set.Ioi a] a` under the inclusion `D → α` is nontrivial. Note that `a < b` is necessary as
this is clearly not true if `a` is a top element. -/
lemma Dense.comap_val_nhdsWithin_Ioi_neBot {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [DenselyOrdered α] {D : Set α} (hD : Dense D) {a b : α} (hab : a < b) :
    ((𝓝[Set.Ioi a] a).comap ((↑) : D → α)).NeBot := by
  refine comap_neBot_iff.2 fun t ht => ?_
  obtain ⟨c, hc⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hab).1 ht
  obtain ⟨d, hd⟩ := hD.inter_open_nonempty (Set.Ioo a c) isOpen_Ioo (Set.nonempty_Ioo.2 hc.1.1)
  exact ⟨⟨d, hd.2⟩, hc.2 hd.1⟩

/-- This is the dual of `Dense.comap_val_nhdsWithin_Ioi_neBot`. -/
lemma Dense.comap_val_nhdsWithin_Iio_neBot {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [DenselyOrdered α] {D : Set α} (hD : Dense D) {a b : α} (hab : b < a) :
    ((𝓝[Set.Iio a] a).comap ((↑) : D → α)).NeBot := by
  refine comap_neBot_iff.2 fun t ht => ?_
  obtain ⟨c, hc⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hab).1 ht
  obtain ⟨d, hd⟩ := hD.inter_open_nonempty (Set.Ioo c a) isOpen_Ioo (Set.nonempty_Ioo.2 hc.1.2)
  exact ⟨⟨d, hd.2⟩, hc.2 hd.1⟩

/-- If `f` is monotone on a dense set `D` and is right continuous, then `f` is monotone. We prove
under the assumption that `α` has a top element `⊤` and `⊤ ∈ D`, which is a necessary assumption
because otherwise it is possible that `⊤` is an isolated point. This theorem should be also true
when `α` satisfies `NoTopOrder α`. -/
lemma Dense.monotone_of_isRightContinuous {α β : Type*} [LinearOrder α] [OrderTop α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [TopologicalSpace β]
    [Preorder β] [t : OrderClosedTopology β] {f : α → β} {D : Set α} (hD : Dense D) (htop : ⊤ ∈ D)
    (hm : Monotone (f ∘ (↑) : D → β)) (hf : f.IsRightContinuous) :
    Monotone f := by
  refine monotone_iff_forall_lt.2 fun a b hab => ?_
  by_cases! hbtop : b = ⊤
  · have : (comap ((↑) : D → α) (𝓝[>] a)).NeBot := hD.comap_val_nhdsWithin_Ioi_neBot hab
    rw [hbtop]
    refine (isClosed_Iic (a := f ⊤)).mem_of_tendsto (Tendsto.comp (hf a)
      (tendsto_comap (f := ((↑) : D → α)))) ?_
    rw [eventually_comap, eventually_nhdsWithin_iff]
    filter_upwards with z hz d rfl using hm (Subtype.mk_le_mk.2 le_top : d ≤ ⟨⊤, htop⟩)
  · -- This part should work when `α` satisfies `NoTopOrder α`.
    let I : D × D → α × α := Prod.map Subtype.val Subtype.val
    have : ((𝓝[Set.Ioi a ×ˢ Set.Ioi b] ⟨a, b⟩).comap I).NeBot := by
      simp only [nhdsWithin_prod_eq, comap_prodMap_prod, I]
      exact (hD.comap_val_nhdsWithin_Ioi_neBot hab).prod
        (hD.comap_val_nhdsWithin_Ioi_neBot hbtop.lt_top)
    have : ∀ᶠ (p : D × D) in (𝓝[Set.Ioi a ×ˢ Set.Ioi b] ⟨a, b⟩).comap I, p.1 ≤ p.2 := by
      rw [eventually_comap, eventually_nhdsWithin_iff]
      have := isOpen_lt_prod.mem_nhds_iff.2 (by simp [hab] : ⟨a, b⟩ ∈ {p : α × α | p.1 < p.2})
      filter_upwards [this] with p hlt _ a rfl using hlt.le
    exact t.isClosed_le'.mem_of_tendsto (Tendsto.comp ((hf a).prodMap (hf b)) tendsto_comap)
      (this.mono fun d hd => by simpa using hm hd)

/-- A helper lemma. -/
lemma Filter.IsCoboundedUnder.trans {ι α : Type*} {r : α → α → Prop} {l : Filter ι} [l.NeBot]
    [IsTrans α r] {u v : ι → α} (hle : ∀ᶠ i in l, r (u i) (v i)) (h : IsCoboundedUnder r l u) :
    IsCoboundedUnder r l v := by
  simp only [IsCoboundedUnder, IsCobounded, eventually_map] at *
  obtain ⟨b, hb⟩ := h
  refine ⟨b, fun a ha => hb a ?_⟩
  filter_upwards [ha, hle] with i hi huv using Trans.trans huv hi

/-- Convergence on a dense set of a collection of monotone function controls the `limsup` at a point
if `f` is right continuous at `a`. We prove this under the assumption that `α` has both a bottom
element and a top element. The bottom element is needed because otherwise `limsup` evaluated at the
bottome element may give a junk value to break the inequality. -/
lemma limsup_le_of_eventually_monotone_of_tendsto_on_dense {ι α β : Type*} [LinearOrder α]
    [BoundedOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {l : Filter ι}
    [l.NeBot] {D : Set α} {F : ι → α → β} {f : α → β} (hF : ∀ᶠ i in l, Monotone (F i))
    (hD : Dense D) (htop : ⊤ ∈ D) (hbot : ⊥ ∈ D) {a : α} (hfa : ContinuousWithinAt f (Set.Ioi a) a)
    (hlim : ∀ t ∈ D, Tendsto (fun i ↦ F i t) l (𝓝 (f t))) :
    limsup (F · a) l ≤ f a := by
  by_cases! ha : a = ⊤
  · rw [ha, (hlim ⊤ htop).limsup_eq]
  · have : (comap ((↑) : D → α) (𝓝[>] a)).NeBot := hD.comap_val_nhdsWithin_Ioi_neBot ha.lt_top
    refine (isClosed_Ici (a := limsup (F · a) l)).mem_of_tendsto (Tendsto.comp hfa
      (tendsto_comap (f := ((↑) : D → α)))) ?_
    rw [eventually_comap, eventually_nhdsWithin_iff]
    filter_upwards with z hz d rfl
    simp only [Function.comp_apply, Set.mem_Ici, ← (hlim d d.2).limsup_eq]
    refine limsup_le_limsup ?_ ?_ (hlim d d.2).isBoundedUnder_le
    · filter_upwards [hF] with i hi using hi hz.le
    · refine (hlim ⊥ hbot).isCoboundedUnder_le.trans ?_
      filter_upwards [hF] with i hi using hi bot_le

/-- This is the dual of `limsup_le_of_eventually_monotone_of_tendsto_on_dense`. -/
lemma le_liminf_of_eventually_monotone_of_tendsto_on_dense {ι α β : Type*} [LinearOrder α]
    [BoundedOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {l : Filter ι}
    [l.NeBot] {D : Set α} {F : ι → α → β} {f : α → β} (hF : ∀ᶠ i in l, Monotone (F i))
    (hD : Dense D) (htop : ⊤ ∈ D) (hbot : ⊥ ∈ D) {a : α} (hfa : ContinuousWithinAt f (Set.Iio a) a)
    (hlim : ∀ t ∈ D, Tendsto (fun i ↦ F i t) l (𝓝 (f t))) :
    f a ≤ liminf (F · a) l := by
  by_cases! ha : a = ⊥
  · rw [ha, (hlim ⊥ hbot).liminf_eq]
  · have : (comap ((↑) : D → α) (𝓝[<] a)).NeBot := hD.comap_val_nhdsWithin_Iio_neBot ha.bot_lt
    refine (isClosed_Iic (a := liminf (F · a) l)).mem_of_tendsto (Tendsto.comp hfa
      (tendsto_comap (f := ((↑) : D → α)))) ?_
    rw [eventually_comap, eventually_nhdsWithin_iff]
    filter_upwards with z hz d rfl
    simp only [Function.comp_apply, Set.mem_Iic, ← (hlim d d.2).liminf_eq]
    refine liminf_le_liminf ?_ (hlim d d.2).isBoundedUnder_ge ?_
    · filter_upwards [hF] with i hi using hi hz.le
    · refine (hlim ⊤ htop).isCoboundedUnder_ge.trans ?_
      filter_upwards [hF] with i hi using hi le_top

/-- We combine `limsup_le_of_eventually_monotone_of_tendsto_on_dense` and
`le_liminf_of_eventually_monotone_of_tendsto_on_dense` to prove that `F · a` converges to `f a`
if `f` is continuous at `a`. -/
lemma tendsto_of_eventually_monotone_of_tendsto_on_dense {ι α β : Type*} [LinearOrder α]
    [BoundedOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {l : Filter ι}
    [l.NeBot] {D : Set α} {F : ι → α → β} {f : α → β} (hF : ∀ᶠ i in l, Monotone (F i))
    (hD : Dense D) (htop : ⊤ ∈ D) (hbot : ⊥ ∈ D) (a : α) (hfa : ContinuousAt f a)
    (hlim : ∀ t ∈ D, Tendsto (fun i ↦ F i t) l (𝓝 (f t))) :
    Tendsto (F · a) l (𝓝 (f a)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ ?_ ?_
  · exact le_liminf_of_eventually_monotone_of_tendsto_on_dense hF hD htop hbot
      hfa.continuousWithinAt hlim
  · exact limsup_le_of_eventually_monotone_of_tendsto_on_dense hF hD htop hbot
      hfa.continuousWithinAt hlim
  · -- create an analogue of `Filter.IsCoboundedUnder.trans` for `IsBoundedUnder` to replace
    -- `isBoundedUnder_le.mono_le`
    refine (hlim ⊤ htop).isBoundedUnder_le.mono_le ?_
    filter_upwards [hF] with i hi using hi le_top
  · refine (hlim ⊥ hbot).isBoundedUnder_ge.mono_ge ?_
    filter_upwards [hF] with i hi using hi bot_le

end MonotoneLim

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
  [MeasurableSpace ι]

namespace ProbabilityTheory

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
