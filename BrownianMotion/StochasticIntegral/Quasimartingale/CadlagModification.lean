/-
Copyright (c) 2026 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rohit Manokaran, Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.ConvergenceInMeasure
public import BrownianMotion.Auxiliary.LeftLimWithin
public import BrownianMotion.Continuity.LimitModification
public import BrownianMotion.StochasticIntegral.Cadlag
public import BrownianMotion.StochasticIntegral.Predictable
public import BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality
public import BrownianMotion.StochasticIntegral.UniformIntegrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Cadlag modification of quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

/-- A dense set contains points above any point which is not maximal. -/
lemma Dense.exists_gt_of_not_isMax {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α]
    {s : Set α} (hs : Dense s) {a : α} (ha : ¬ IsMax a) :
    ∃ b ∈ s, a < b := by
  obtain ⟨y, hy⟩ := not_isMax_iff.1 ha
  obtain ⟨b, hbs, hb⟩ := hs.exists_between hy
  exact ⟨b, hbs, hb.1⟩

section UniformIntegrableAux

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Vitali**: if a uniformly integrable sequence converges almost everywhere, then its integrals
on any set converge to the integral of the limit. -/
lemma MeasureTheory.UniformIntegrable.tendsto_setIntegral [IsFiniteMeasure μ]
    {f : ℕ → Ω → E} {g : Ω → E} (hUI : UniformIntegrable f 1 μ)
    (hfg : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω))) (A : Set Ω) :
    Tendsto (fun n ↦ ∫ ω in A, f n ω ∂μ) atTop (𝓝 (∫ ω in A, g ω ∂μ)) := by
  have hg : MemLp g 1 μ := hUI.memLp_of_ae_tendsto hfg
  refine tendsto_setIntegral_of_L1' g hg.aestronglyMeasurable
    (.of_forall fun n ↦ memLp_one_iff_integrable.1 (hUI.memLp n)) ?_ A
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hUI.aestronglyMeasurable hg
    hUI.unifIntegrable hfg

/-- The integrals of the truncations `f ⊔ (-k)` of an integrable function `f` converge to the
integral of `f`. -/
lemma MeasureTheory.Integrable.tendsto_setIntegral_sup_neg_natCast {f : Ω → ℝ}
    (hf : Integrable f μ) (A : Set Ω) :
    Tendsto (fun k : ℕ ↦ ∫ ω in A, f ω ⊔ (-(k : ℝ)) ∂μ) atTop (𝓝 (∫ ω in A, f ω ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun ω ↦ |f ω|)
    (fun k ↦ (hf.aestronglyMeasurable.sup aestronglyMeasurable_const).restrict)
    hf.abs.restrict (fun k ↦ .of_forall fun ω ↦ ?_) (.of_forall fun ω ↦ ?_)
  · rw [Real.norm_eq_abs, abs_le]
    refine ⟨(neg_abs_le _).trans le_sup_left, sup_le (le_abs_self _) ?_⟩
    exact (neg_nonpos.2 (Nat.cast_nonneg k)).trans (abs_nonneg _)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈-f ω⌉₊] with k hk
    rw [eq_comm, sup_eq_left, neg_le]
    exact (Nat.le_ceil _).trans (mod_cast hk)

/-- A family of functions which is bounded from below by a constant and such that each function is
bounded from above by a conditional expectation of a fixed integrable function is uniformly
integrable. -/
lemma MeasureTheory.uniformIntegrable_of_le_condExp [IsFiniteMeasure μ] {κ : Type*}
    {f : κ → Ω → ℝ} {g : Ω → ℝ} {c : ℝ} {m : κ → MeasurableSpace Ω} (hm : ∀ i, m i ≤ mΩ)
    (hg : Integrable g μ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hcf : ∀ i, ∀ᵐ ω ∂μ, c ≤ f i ω) (hfg : ∀ i, f i ≤ᵐ[μ] μ[g | m i]) :
    UniformIntegrable f 1 μ := by
  have hUI : UniformIntegrable ((fun _ _ ↦ |c|) + fun i ω ↦ ‖(μ[g | m i]) ω‖) 1 μ :=
    (uniformIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const |c|)).add le_rfl
      (hg.uniformIntegrable_condExp hm).norm
  refine uniformIntegrable_of_dominated hUI hf fun i ↦ ⟨i, ?_⟩
  filter_upwards [hcf i, hfg i] with ω h1 h2
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (a := |c| + _) (by positivity), abs_le]
  constructor
  · linarith [neg_abs_le c, abs_nonneg ((μ[g | m i]) ω)]
  · linarith [le_abs_self ((μ[g | m i]) ω), abs_nonneg c]

/-- `L¹` bound for a submartingale on an interval. -/
lemma MeasureTheory.Submartingale.integral_abs_le {ι : Type*} [Preorder ι]
    {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕] [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : Submartingale X 𝓕 μ) {t s u : ι} (hts : t ≤ s) (hsu : s ≤ u) :
    ∫ ω, |X s ω| ∂μ ≤ 2 * ∫ ω, X u ω ⊔ 0 ∂μ - ∫ ω, X t ω ∂μ := by
  have hZ : Submartingale (fun s ω ↦ X s ω ⊔ 0) 𝓕 μ :=
    hX.sup (martingale_const 𝓕 μ 0).submartingale
  have h_eq : ∫ ω, |X s ω| ∂μ = 2 * ∫ ω, X s ω ⊔ 0 ∂μ - ∫ ω, X s ω ∂μ := by
    rw [← integral_const_mul, ← integral_sub ((hZ.integrable s).const_mul 2) (hX.integrable s)]
    congr with ω
    rcases le_total 0 (X s ω) with h | h
    · rw [abs_of_nonneg h, sup_of_le_left h]
      ring
    · rw [abs_of_nonpos h, sup_of_le_right h]
      ring
  have h1 := hZ.setIntegral_le hsu MeasurableSet.univ
  have h2 := hX.setIntegral_le hts MeasurableSet.univ
  simp only [Measure.restrict_univ] at h1 h2
  linarith

end UniformIntegrableAux

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section RegularitySet

/-- In this set, the process is bounded and has finitely many upcrossings (of any interval) in `T`
before time `d` -/
def regularitySet (T : Set ι) (X : ι → Ω → ℝ) (d : ι) : Set Ω :=
  {ω | (∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r) ∧
    (∃ M : ℕ, ∀ s ∈ T ∩ Set.Iic d, |X s ω| ≤ M + 1)}

/-- The set of `ω` that belong to some `regularitySet T X s`, for `s ∈ T` with `s > d` or for
`s ≥ d` a maximal element of `ι`.

If `d` is not maximal and `T` is cofinal among the non-maximal elements (e.g. if `T` is dense),
this is the set of `ω` that belong to `regularitySet T X s` for some `s ∈ T` with `s > d`
(see `regularitySetRight_eq_biUnion_gt`). If `d` is maximal, no such `s` exists and this is
`regularitySet T X d` (see `regularitySetRight_of_isMax`). -/
def regularitySetRight (T : Set ι) (X : ι → Ω → ℝ) (d : ι) : Set Ω :=
  ⋃ s ∈ (T ∩ Set.Ioi d) ∪ ({s | IsMax s} ∩ Set.Ici d), regularitySet T X s

lemma mem_regularitySetRight_iff {T : Set ι} {X : ι → Ω → ℝ} {d : ι} {ω : Ω} :
    ω ∈ regularitySetRight T X d
      ↔ ∃ s, ((s ∈ T ∧ d < s) ∨ (IsMax s ∧ d ≤ s)) ∧ ω ∈ regularitySet T X s := by
  simp [regularitySetRight]

lemma regularitySet_anti {T : Set ι} {X : ι → Ω → ℝ} {d₁ d₂ : ι} (hd : d₁ ≤ d₂) :
    regularitySet T X d₂ ⊆ regularitySet T X d₁ := by
  intro ω hω
  simp only [regularitySet, Set.mem_ofPred_eq] at hω ⊢
  constructor
  · intro q r hqr
    have hω' :=  hω.1 q r hqr
    refine fun h_mem ↦ hω' ?_
    exact infiniteAlt_mono'' hd h_mem
  · obtain ⟨M, hM⟩ := hω.2
    refine ⟨M, fun s hs ↦ ?_⟩
    specialize hM s (by grind)
    grind

lemma regularitySetRight_of_isMax {T : Set ι} {X : ι → Ω → ℝ} {d : ι} (hd : IsMax d) :
    regularitySetRight T X d = regularitySet T X d := by
  ext ω
  rw [mem_regularitySetRight_iff]
  refine ⟨fun ⟨s, hs, hω⟩ ↦ ?_, fun hω ↦ ⟨d, .inr ⟨hd, le_rfl⟩, hω⟩⟩
  rcases hs with ⟨-, hds⟩ | ⟨-, hds⟩
  · exact absurd hds hd.not_lt
  · exact regularitySet_anti hds hω

lemma regularitySetRight_eq_biUnion_lt
    {T : Set ι} {X : ι → Ω → ℝ} {d t : ι} (hT : ∃ u ∈ T, d < u ∧ u ≤ t) :
    regularitySetRight T X d = ⋃ d' ∈ T ∩ Set.Ioc d t, regularitySet T X d' := by
  ext ω
  simp only [mem_regularitySetRight_iff, Set.mem_inter_iff, Set.mem_iUnion, exists_prop,
    Set.mem_Ioc]
  obtain ⟨u, huT, hdu, hut⟩ := hT
  refine ⟨fun ⟨i, hi, hωi⟩ ↦ ?_, fun ⟨i, ⟨hiT, hdi, hit⟩, hωi⟩ ↦ ⟨i, .inl ⟨hiT, hdi⟩, hωi⟩⟩
  rcases hi with ⟨hiT, hdi⟩ | ⟨hi, hdi⟩
  · refine ⟨min i u, ?_, ?_⟩
    · grind
    · exact regularitySet_anti (by grind) hωi
  · exact ⟨u, ⟨huT, hdu, hut⟩, regularitySet_anti (hi.isTop u) hωi⟩

lemma regularitySetRight_eq_biUnion_gt
    {T : Set ι} {X : ι → Ω → ℝ} {d : ι} (hT : ∃ u ∈ T, d < u) :
    regularitySetRight T X d = ⋃ d' ∈ T ∩ Set.Ioi d, regularitySet T X d' := by
  ext ω
  simp only [mem_regularitySetRight_iff, Set.mem_inter_iff, Set.mem_iUnion, exists_prop,
    Set.mem_Ioi]
  obtain ⟨u, huT, hdu⟩ := hT
  refine ⟨fun ⟨i, hi, hωi⟩ ↦ ?_, fun ⟨i, hi, hωi⟩ ↦ ⟨i, .inl hi, hωi⟩⟩
  rcases hi with hi | ⟨hi, hdi⟩
  · exact ⟨i, hi, hωi⟩
  · exact ⟨u, ⟨huT, hdu⟩, regularitySet_anti (hi.isTop u) hωi⟩

lemma regularitySetRight_anti {T : Set ι} {X : ι → Ω → ℝ} {d₁ d₂ : ι} (hd : d₁ ≤ d₂) :
    regularitySetRight T X d₂ ⊆ regularitySetRight T X d₁ := by
  intro ω hω
  rw [mem_regularitySetRight_iff] at hω ⊢
  obtain ⟨s, hs, hω⟩ := hω
  exact ⟨s, hs.imp (fun h ↦ ⟨h.1, hd.trans_lt h.2⟩) (fun h ↦ ⟨h.1, hd.trans h.2⟩), hω⟩

/-- A linear order has at most one maximal element. -/
lemma countable_setOf_isMax : {s : ι | IsMax s}.Countable :=
  Set.Subsingleton.countable fun _ ha _ hb ↦ le_antisymm (hb.isTop _) (ha.isTop _)

variable [OrderBot ι]

lemma ae_mem_regularitySet [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) (hdT : d ∈ T) :
    ∀ᵐ ω ∂μ, ω ∈ regularitySet T X d := by
  filter_upwards [measure_all_infiniteAlt hX hT hT, ae_exists_bound'' hX hT d] with ω hω1 hω2
  exact ⟨fun q r hqr ↦ hω1 d hdT q r (mod_cast hqr), hω2⟩

lemma ae_mem_all_regularitySet [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T T' : Set ι} (hT : T.Countable) (hT' : T'.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T', ω ∈ regularitySet T X d := by
  filter_upwards [measure_all_infiniteAlt hX hT hT', ae_exists_bound hX hT hT'] with ω hω1 hω2 d hdT
  exact ⟨fun q r hqr ↦ hω1 d hdT q r (mod_cast hqr), hω2 d hdT⟩

/-- Almost surely, `ω` belongs to `regularitySet T X d` for all `d ∈ T` and all maximal `d`. -/
lemma ae_mem_all_regularitySet_union_isMax [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T ∪ {s | IsMax s}, ω ∈ regularitySet T X d :=
  ae_mem_all_regularitySet hX hT (hT.union countable_setOf_isMax)

lemma ae_mem_regularitySetRight [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (hTcof : ∀ x, ¬ IsMax x → ∃ s ∈ T, x < s) :
    ∀ᵐ ω ∂μ, ∀ d, ω ∈ regularitySetRight T X d := by
  filter_upwards [ae_mem_all_regularitySet_union_isMax hX hT] with ω hω d
  rw [mem_regularitySetRight_iff]
  by_cases hd : IsMax d
  · exact ⟨d, .inr ⟨hd, le_rfl⟩, hω d (.inr hd)⟩
  · obtain ⟨s, hs, hsd⟩ := hTcof d hd
    exact ⟨s, .inl ⟨hs, hsd⟩, hω s (.inl hs)⟩

lemma measurableSet_altSet (hX : IsRealQuasimartingale 𝓕 X μ)
    (d : ι) (F : Finset ι) (hF : ∀ i ∈ F, i ≤ d) {q r : ℚ} (_hqr : q < r) (m : ℕ) :
    MeasurableSet[𝓕 d] (altSet X F q r m) := by
  have hXmeas : ∀ s ∈ F, Measurable[𝓕 d] (X s) := fun s hs ↦
    (hX.adapted s).mono (𝓕.mono (hF s hs)) le_rfl
  have hset : altSet X F (q : ℝ) (r : ℝ) m
      = ⋃ g ∈ Fintype.piFinset (fun _ : Fin (2 * m) ↦ F),
          {ω | (∀ (i : Fin (2 * m)) (h : (i : ℕ) + 1 < 2 * m), g i < g ⟨(i : ℕ) + 1, h⟩)
            ∧ (∀ i : Fin m, X (g ⟨2 * (i : ℕ), by omega⟩) ω ≤ (q : ℝ))
            ∧ (∀ i : Fin m, (r : ℝ) ≤ X (g ⟨2 * (i : ℕ) + 1, by omega⟩) ω)} := by
    ext ω
    simp only [altSet, Set.mem_ofPred_eq, Set.mem_iUnion, Fintype.mem_piFinset, exists_prop]
    constructor
    · rintro ⟨c, hc1, hc2, hc3, hc4⟩
      exact ⟨fun i ↦ c (i : ℕ), fun i ↦ hc2 (i : ℕ) i.2,
        fun i h ↦ hc1 (i : ℕ) h, fun i ↦ hc3 (i : ℕ) i.2, fun i ↦ hc4 (i : ℕ) i.2⟩
    · rintro ⟨g, hgF, hg1, hg3, hg4⟩
      refine ⟨fun k ↦ if h : k < 2 * m then g ⟨k, h⟩ else ⊥, by grind, by grind, ?_, ?_⟩
      · intro i hi
        have h2i : 2 * i < 2 * m := by lia
        simp only [dif_pos h2i]
        exact hg3 ⟨i, hi⟩
      · intro i hi
        have h2i : 2 * i + 1 < 2 * m := by lia
        simp only [dif_pos h2i]
        exact hg4 ⟨i, hi⟩
  rw [hset]
  refine Finset.measurableSet_biUnion _ fun g hg ↦ ?_
  have hgF : ∀ i, g i ∈ F := Fintype.mem_piFinset.mp hg
  -- Split off the (measure-space independent) monotonicity condition, then recognise the event
  -- as a finite intersection of measurable half-lines `{X s ≤ q}` and `{r ≤ X s}`, `s ∈ F`.
  rw [Set.ofPred_and]
  refine (MeasurableSet.const _).inter ?_
  rw [Set.ofPred_and, Set.ofPred_forall, Set.ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i ↦ ?_) (MeasurableSet.iInter fun i ↦ ?_)
  · exact hXmeas _ (hgF ⟨2 * (i : ℕ), by lia⟩) measurableSet_Iic
  · exact hXmeas _ (hgF ⟨2 * (i : ℕ) + 1, by lia⟩) measurableSet_Ici

lemma measurableSet_infiniteAlt (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) {q r : ℚ} (hqr : q < r) :
    MeasurableSet[𝓕 d] (infiniteAlt T d X q r) := by
  unfold infiniteAlt
  refine MeasurableSet.iInter fun m ↦ MeasurableSet.biUnion ?_ fun F ↦ ?_
  · refine countable_setOf_finset_coe_subset ?_
    exact hT.mono (by grind)
  · intro hF
    refine measurableSet_altSet hX d F ?_ hqr m
    simp only [Set.subset_inter_iff, Set.mem_ofPred_eq] at hF
    intro i hi
    exact hF.2 hi

lemma measurableSet_regularitySet (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) :
    MeasurableSet[𝓕 d] (regularitySet T X d) := by
  suffices MeasurableSet[𝓕 d]
        ((⋂ (q : ℚ) (r : ℚ) (hqr : q < r), {ω | ω ∉ infiniteAlt T d X q r}) ∩
        (⋃ M : ℕ, ⋂ s ∈ T ∩ Set.Iic d, {ω | |X s ω| ≤ M + 1})) by
      convert this
      ext ω
      simp [regularitySet]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun p ↦ MeasurableSet.iInter fun q ↦ ?_
    by_cases hpq : p < q
    · simp only [hpq, Set.iInter_true]
      refine MeasurableSet.compl ?_
      exact measurableSet_infiniteAlt hX hT d hpq
    · simp [hpq]
  · refine MeasurableSet.iUnion fun M ↦ MeasurableSet.biInter (hT.mono (by grind)) fun s hs ↦ ?_
    refine measurableSet_le ?_ (by fun_prop)
    simp only [Set.mem_inter_iff, Set.mem_Iic] at hs
    refine Measurable.mono ?_ (𝓕.mono hs.2) le_rfl
    simp_rw [← Real.norm_eq_abs]
    exact (hX.stronglyAdapted s).norm.measurable

omit [OrderBot ι] in
/-- For a right-continuous filtration and a time `t` that is not maximal, a set that is
`𝓕 s`-measurable for every `s > t` is already `𝓕 t`-measurable, since `𝓕 t = ⨅ s > t, 𝓕 s`. -/
lemma measurableSet_of_forall_gt [DenselyOrdered ι] [𝓕.IsRightContinuous]
    {t : ι} (ht : ¬ IsMax t) {A : Set Ω}
    (h : ∀ s, t < s → MeasurableSet[𝓕 s] A) :
    MeasurableSet[𝓕 t] A := by
  have hrc : (𝓕 t : MeasurableSpace Ω) = ⨅ j > t, 𝓕 j := by
    have h1 := 𝓕.rightCont_eq_of_not_isMax ht
    rwa [Filtration.IsRightContinuous.eq] at h1
  rw [hrc, MeasurableSpace.measurableSet_iInf]
  intro j
  rw [MeasurableSpace.measurableSet_iInf]
  exact h j

lemma measurableSet_regularitySetRight [TopologicalSpace ι] [OrderClosedTopology ι]
    [DenselyOrdered ι] [𝓕.IsRightContinuous]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (hTd : Dense T) (d : ι) :
    MeasurableSet[𝓕 d] (regularitySetRight T X d) := by
  by_cases hd : IsMax d
  · rw [regularitySetRight_of_isMax hd]
    exact measurableSet_regularitySet hX hT d
  refine measurableSet_of_forall_gt hd fun s hs ↦ ?_
  rw [regularitySetRight_eq_biUnion_lt (t := s)]
  swap
  · obtain ⟨z, hz1, hz2, hz3⟩ := hTd.exists_between hs
    exact ⟨z, hz1, hz2, hz3.le⟩
  refine MeasurableSet.biUnion ?_ fun t ht ↦ ?_
  · exact hT.mono (by grind)
  · simp only [Set.mem_inter_iff, Set.mem_Ioc] at ht
    exact 𝓕.mono ht.2.2 _ (measurableSet_regularitySet hX hT t)

lemma measurableSet_regularitySetRight'
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) :
    MeasurableSet (regularitySetRight T X d) := by
  rw [regularitySetRight]
  refine MeasurableSet.biUnion ?_ fun t ht ↦ ?_
  · exact (hT.mono Set.inter_subset_left).union (countable_setOf_isMax.mono Set.inter_subset_left)
  · exact 𝓕.le _ _ (measurableSet_regularitySet hX hT t)

variable [TopologicalSpace ι] [OrderTopology ι]

omit [OrderBot ι] in
lemma right_limit_of_mem_regularitySet {T : Set ι}
    (x d : ι) {ω : Ω} (hxd : x < d) (hω : ω ∈ regularitySet T X d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 l) := by
  simp only [regularitySet, Set.mem_inter_iff, Set.mem_Iic, and_imp, Set.mem_ofPred_eq] at hω
  have h1 : ∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r := hω.1
  have h2 : ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
    convert hω.2
    simp
  obtain ⟨M, hM⟩ := h2
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩ hqr ⟨hfa, hfb⟩
    refine h1 p p' (mod_cast hqr) ?_
    exact mem_infiniteAlt_of_frequently_right hxd hfa hfb
  · refine ⟨((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Ioc x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x :=
      Filter.mem_of_superset (Ioo_inter_mem_nhdsWithin_inter_Ioi hxd) (by grind)
    filter_upwards [hU] with s' hs' using by grind
  · refine ⟨-((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Ioc x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x :=
      Filter.mem_of_superset (Ioo_inter_mem_nhdsWithin_inter_Ioi hxd) (by grind)
    filter_upwards [hU] with s' hs' using by grind

omit [OrderBot ι] in
lemma left_limit_of_mem_regularitySet {T : Set ι}
    (x d : ι) {ω : Ω} (hxle : x ≤ d) (hω : ω ∈ regularitySet T X d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 l) := by
  simp only [regularitySet, Set.mem_inter_iff, Set.mem_Iic, and_imp, Set.mem_ofPred_eq] at hω
  have h1 : ∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r := hω.1
  have h2 : ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
    convert hω.2
    simp
  obtain ⟨M, hM⟩ := h2
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩ hqr ⟨hfa, hfb⟩
    refine h1 p p' (mod_cast hqr) ?_
    exact mem_infiniteAlt_of_frequently_left hxle hfa hfb
  · refine ⟨(M : ℝ) + 1, ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Iio x ∩ T ∈ 𝓝[T ∩ Set.Iio x] x := by
      rw [Set.inter_comm]
      exact self_mem_nhdsWithin
    filter_upwards [hU] with s' hs' using by grind
  · refine ⟨-((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Iio x ∩ T ∈ 𝓝[T ∩ Set.Iio x] x := by
      rw [Set.inter_comm]
      exact self_mem_nhdsWithin
    filter_upwards [hU] with s' hs' using by grind

omit [OrderBot ι] in
lemma eventually_mem_regularitySetRight_of_mem {T : Set ι}
    {x : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) :
    ∀ᶠ y in 𝓝[>] x, ω ∈ regularitySetRight T X y := by
  obtain ⟨d, hd, hω'⟩ := mem_regularitySetRight_iff.1 hω
  rcases hd with ⟨hdT, hxd⟩ | ⟨hd, -⟩
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [eventually_lt_nhds hxd] with y hy hxy
    exact mem_regularitySetRight_iff.2 ⟨d, .inl ⟨hdT, hy⟩, hω'⟩
  · exact .of_forall fun y ↦ mem_regularitySetRight_iff.2 ⟨d, .inr ⟨hd, hd.isTop y⟩, hω'⟩

omit [OrderBot ι] in
lemma right_limit_of_mem_regularitySetRight {T : Set ι}
    {x y : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) (hyx : y ≤ x) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi y] y) (𝓝 l) := by
  by_cases hy : IsMax y
  · exact ⟨0, by simp [hy.Ioi_eq]⟩
  obtain ⟨d, hd, hω'⟩ := mem_regularitySetRight_iff.1 hω
  refine right_limit_of_mem_regularitySet y d ?_ hω'
  rcases hd with ⟨-, hxd⟩ | ⟨hd, hxd⟩
  · exact hyx.trans_lt hxd
  · exact lt_of_le_of_ne (hyx.trans hxd) fun h ↦ hy (h ▸ hd)

omit [OrderBot ι] in
lemma eventually_right_limit_of_mem_regularitySetRight' {T : Set ι}
    {x : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) :
    ∀ᶠ y in 𝓝[>] x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi y] y) (𝓝 l) := by
  filter_upwards [eventually_mem_regularitySetRight_of_mem hω] with y hy
  exact right_limit_of_mem_regularitySetRight hy le_rfl

omit [OrderBot ι] in
lemma left_limit_of_mem_regularitySetRight {T : Set ι}
    {x y : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) (hyx : y ≤ x) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio y] y) (𝓝 l) := by
  obtain ⟨d, hd, hω'⟩ := mem_regularitySetRight_iff.1 hω
  refine left_limit_of_mem_regularitySet y d ?_ hω'
  rcases hd with ⟨-, hxd⟩ | ⟨-, hxd⟩
  · exact hyx.trans hxd.le
  · exact hyx.trans hxd

omit [OrderBot ι] in
lemma eventually_left_limit_of_mem_regularitySetRight' {T : Set ι}
    {x : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) :
    ∀ᶠ y in 𝓝[>] x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio y] y) (𝓝 l) := by
  filter_upwards [eventually_mem_regularitySetRight_of_mem hω] with y hy
  exact left_limit_of_mem_regularitySetRight hy le_rfl

lemma ae_right_limit [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (hTcof : ∀ x, ¬ IsMax x → ∃ d ∈ T, x < d) :
    ∀ᵐ ω ∂μ, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 l) := by
  filter_upwards [ae_mem_regularitySetRight hX hT hTcof] with ω hω x
  exact right_limit_of_mem_regularitySetRight (hω x) le_rfl

lemma ae_left_limit [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (hTcof : ∀ x, ¬ IsMax x → ∃ d ∈ T, x ≤ d) :
    ∀ᵐ ω ∂μ, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 l) := by
  filter_upwards [ae_mem_all_regularitySet_union_isMax hX hT] with ω hω
  intro x
  by_cases hx : IsMax x
  · exact left_limit_of_mem_regularitySet x x le_rfl (hω x (.inr hx))
  · obtain ⟨d, hdT, hxle⟩ := hTcof x hx
    exact left_limit_of_mem_regularitySet x d hxle (hω d (.inl hdT))

end RegularitySet

-- Note that `ι` may have a maximal element `t`. Such a `t` is isolated on the right
-- (`𝓝[>] t = ⊥`), any function is right-continuous at `t` and `rightLimWithin f T t = f t`.
variable [TopologicalSpace ι] [OrderBot ι] [OrderTopology ι]
  --[FirstCountableTopology ι] -- required for ∀ t : ι, (𝓝[>] t).IsCountablyGenerated
  [DenselyOrdered ι] -- required for (𝓝[>] t).NeBot for all t : ι which are not maximal

/-! ### Pathwise regularization

For a fixed path `h : ι → ℝ` admitting one-sided limits along a dense set `T`, the right-limit
regularization `r` is right-continuous and inherits the left limits of `h`. -/

section PathRegularization

variable {T : Set ι} {h r : ι → ℝ} {x : ι}

omit [OrderBot ι] in
/-- The right-limit regularization inherits left limits of `h` along `T`. -/
lemma tendsto_rightLim_nhdsLT (hTd : Dense T)
    (hr : ∀ᶠ y in 𝓝[<] x, Tendsto h (𝓝[T ∩ Set.Ioi y] y) (𝓝 (r y))) {L : ℝ}
    (hL : Tendsto h (𝓝[T ∩ Set.Iio x] x) (𝓝 L)) :
    Tendsto r (𝓝[<] x) (𝓝 L) := by
  by_cases hex : ∃ u, u < x
  swap
  · have hempty : Set.Iio x = ∅ := Set.eq_empty_iff_forall_notMem.2
      (fun u hu ↦ hex ⟨u, hu⟩)
    rw [nhdsWithin, hempty, Filter.principal_empty, inf_bot_eq]
    exact tendsto_bot
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro C ⟨hCmem, hCclosed⟩
  have hev : ∀ᶠ s in 𝓝[<] x ⊓ 𝓟 T, h s ∈ C := by
    rw [nhdsWithin_inf_principal, Set.inter_comm]; exact hL.eventually hCmem
  obtain ⟨v, hvx, hv⟩ := (nhdsLT_basis_of_exists_lt hex).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  filter_upwards [Ioo_mem_nhdsLT hvx, hr] with y hy hr
  have hne := nhdsWithin_Ioi_inter_neBot_of_exists_gt hTd ⟨x, hy.2⟩
  rw [Set.inter_comm] at hne
  refine hCclosed.mem_of_tendsto hr ?_
  rw [Set.inter_comm, ← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT hy.2] with s hs hsT
  exact hv ⟨hy.1.trans hs.1, hs.2⟩ hsT

omit [OrderBot ι] in
/-- Along a strictly increasing sequence `u → x` from the left, the regularized values
`r (u k)` tend to the left limit of `h` at `x` along `T' ⊇ T`. -/
lemma tendsto_rightLim_comp_of_lt (hTd : Dense T) {T' : Set ι} (hTT' : T ⊆ T')
    (hr : ∀ y, Tendsto h (𝓝[T ∩ Set.Ioi y] y) (𝓝 (r y))) {u : ℕ → ι} {L : ℝ}
    (hux : ∀ k, u k < x) (hutend : Tendsto u atTop (𝓝 x))
    (hL : Tendsto h (𝓝[T' ∩ Set.Iio x] x) (𝓝 L)) :
    Tendsto (fun k ↦ r (u k)) atTop (𝓝 L) := by
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro C ⟨hCmem, hCclosed⟩
  have hev : ∀ᶠ s in 𝓝[<] x ⊓ 𝓟 T', h s ∈ C := by
    rw [nhdsWithin_inf_principal, Set.inter_comm]; exact hL.eventually hCmem
  obtain ⟨v, hvx, hv⟩ := (nhdsLT_basis_of_exists_lt ⟨u 0, hux 0⟩).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  have hevk : ∀ᶠ k in atTop, u k ∈ Set.Ioi v :=
    hutend (IsOpen.mem_nhds isOpen_Ioi hvx)
  filter_upwards [hevk] with k hk
  have hne := nhdsWithin_Ioi_inter_neBot_of_exists_gt hTd ⟨x, hux k⟩
  rw [Set.inter_comm] at hne
  refine hCclosed.mem_of_tendsto (hr (u k)) ?_
  rw [Set.inter_comm, ← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT (hux k)] with s hs hsT
  exact hv ⟨hk.trans hs.1, hs.2⟩ (hTT' hsT)

omit [OrderBot ι] in
/-- Along a strictly decreasing sequence `u → x` from the right, the regularized values
`r (u k)` tend to the right limit of `h` at `x` along `T' ⊇ T`. -/
lemma tendsto_rightLim_comp_of_gt (hTd : Dense T) {T' : Set ι} (hTT' : T ⊆ T')
    (hr : ∀ y, Tendsto h (𝓝[T ∩ Set.Ioi y] y) (𝓝 (r y))) {u : ℕ → ι} {L : ℝ}
    (hux : ∀ k, x < u k) (hutend : Tendsto u atTop (𝓝 x))
    (hL : Tendsto h (𝓝[T' ∩ Set.Ioi x] x) (𝓝 L)) :
    Tendsto (fun k ↦ r (u k)) atTop (𝓝 L) := by
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro C ⟨hCmem, hCclosed⟩
  have hev : ∀ᶠ s in 𝓝[>] x ⊓ 𝓟 T', h s ∈ C := by
    rw [nhdsWithin_inf_principal, Set.inter_comm]; exact hL.eventually hCmem
  obtain ⟨v, hvx, hv⟩ := (nhdsGT_basis_of_exists_gt ⟨u 0, hux 0⟩).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  have hevk : ∀ᶠ k in atTop, u k ∈ Set.Iio v :=
    hutend (IsOpen.mem_nhds isOpen_Iio hvx)
  filter_upwards [hevk] with k hk
  have hne := nhdsWithin_Ioi_inter_neBot_of_exists_gt hTd ⟨v, hk⟩
  rw [Set.inter_comm] at hne
  refine hCclosed.mem_of_tendsto (hr (u k)) ?_
  rw [Set.inter_comm, ← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT hk] with s hs hsT
  exact hv ⟨(hux k).trans hs.1, hs.2⟩ (hTT' hsT)

end PathRegularization

/-! ### Uncountable sets accumulate from the right -/

section Accumulation

omit [OrderBot ι] in
/-- Any uncountable set in a separable, densely-ordered, first-countable linear order admits a
strictly decreasing sequence of its elements converging to a point from the right. -/
lemma exists_seq_gt_tendsto_of_not_countable [TopologicalSpace.SeparableSpace ι]
    {A : Set ι} (hA : ¬ A.Countable) :
    ∃ (p : ι) (u : ℕ → ι), (∀ k, u k ∈ A) ∧ (∀ k, p < u k) ∧
      Tendsto u atTop (𝓝 p) := by
  have : SecondCountableTopology ι := .of_separableSpace_orderTopology _
  have h := countable_setOfPred_isolated_right_within (s := A)
  have hsub : ¬ A ⊆ {x | x ∈ A ∧ 𝓝[A ∩ Set.Ioi x] x = ⊥} := by
    intro hcon
    exact hA (h.mono hcon)
  rw [Set.not_subset] at hsub
  obtain ⟨p, hpA, hpiso⟩ := hsub
  simp only [Set.mem_ofPred_eq, not_and] at hpiso
  have : (𝓝[A ∩ Set.Ioi p] p).NeBot := ⟨hpiso hpA⟩
  obtain ⟨u, hu⟩ := exists_seq_tendsto (𝓝[A ∩ Set.Ioi p] p)
  simp only [tendsto_nhdsWithin_iff, Set.mem_inter_iff, Set.mem_Ioi, eventually_atTop] at hu
  obtain ⟨hu_tendsto, a, hu⟩ := hu
  refine ⟨p, fun k ↦ u (a + k), fun k ↦ (hu (a + k) (by grind)).1,
    fun k ↦ (hu (a + k) (by grind)).2, ?_⟩
  simp_rw [add_comm a]
  exact (tendsto_add_atTop_iff_nat a).mpr hu_tendsto

end Accumulation

open Function

omit [OrderBot ι] [DenselyOrdered ι] in
lemma tendsto_nhdsGT_rightLimWithin_of_mem_regularitySetRight
    {T : Set ι} {x : ι} {ω : Ω} (hmem : ω ∈ regularitySetRight T X x) :
    Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 (rightLimWithin (X · ω) T x)) := by
  have h := right_limit_of_mem_regularitySetRight hmem le_rfl
  rw [Set.inter_comm] at h ⊢
  exact tendsto_rightLimWithin_of_tendsto h

omit [OrderBot ι] [DenselyOrdered ι] in
lemma tendsto_nhdsLT_leftLimWithin_of_mem_regularitySetRight
    {T : Set ι} {x : ι} {ω : Ω} (hmem : ω ∈ regularitySetRight T X x) :
    Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 (leftLimWithin (X · ω) T x)) := by
  have h := left_limit_of_mem_regularitySetRight hmem le_rfl
  rw [Set.inter_comm] at h ⊢
  exact tendsto_leftLimWithin_of_tendsto h

omit [OrderBot ι] in
lemma rightContinuous_rightLimWithin_of_mem_regularitySetRight
    {T : Set ι} (hTd : Dense T) {x : ι}
    {ω : Ω} (hmem : ω ∈ regularitySetRight T X x) :
    ContinuousWithinAt (rightLimWithin (X · ω) T) (Set.Ici x) x := by
  refine continuousWithinAt_rightLimWithin_Ici_of_dense hTd ?_ ?_
  · have h := right_limit_of_mem_regularitySetRight hmem le_rfl
    rw [Set.inter_comm] at h
    exact tendsto_rightLimWithin_of_tendsto h
  · have h_ev_mem : ∀ᶠ y in 𝓝[>] x, ω ∈ regularitySetRight T X y :=
      eventually_mem_regularitySetRight_of_mem hmem
    filter_upwards [h_ev_mem] with y hy
    rw [Set.inter_comm]
    exact tendsto_nhdsGT_rightLimWithin_of_mem_regularitySetRight hy

omit [OrderBot ι] in
lemma measurableSet_tendsto_nhdsGT [FirstCountableTopology ι] [𝓕.IsRightContinuous]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) (t : ι) :
    MeasurableSet[𝓕 t] {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)} := by
  -- If `t` is maximal, the filter is trivial and the set is `univ`.
  by_cases ht : IsMax t
  · simp [ht.Ioi_eq]
  -- It suffices to prove `𝓕 s`-measurability for every `s > t`.
  refine measurableSet_of_forall_gt ht fun s hts ↦ ?_
  -- Along the countable set `S = (T ∩ Ioi t) ∩ Iio s` (all of whose points are `< s`), the limit
  -- along `𝓝[T ∩ Ioi t] t` is a limit along the countable index `↥S`.
  let S : Set ι := (T ∩ Set.Ioi t) ∩ Set.Iio s
  have hScount : S.Countable := hT.mono (Set.inter_subset_left.trans Set.inter_subset_left)
  have hSlt x (hx : x ∈ S) : x < s := by unfold S at hx; exact hx.2
  have hSmem : S ∈ 𝓝[T ∩ Set.Ioi t] t :=
    Filter.inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hts)))
  have : Countable S := hScount.to_subtype
  set l₀ : Filter S := Filter.comap ((↑) : S → ι) (𝓝[T ∩ Set.Ioi t] t) with hl₀
  have : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
  have hmap : Filter.map ((↑) : S → ι) l₀ = 𝓝[T ∩ Set.Ioi t] t :=
    Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact hSmem)
  have hset : {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)}
      = {ω | ∃ c, Tendsto (fun s' : S ↦ X s' ω) l₀ (𝓝 c)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    refine exists_congr fun c ↦ ?_
    rw [← hmap]
    exact tendsto_map'_iff
  rw [hset]
  have hf (s' : S) : Measurable[𝓕 s] (X s') := (hX s').mono (𝓕.mono (hSlt s' s'.2).le) le_rfl
  exact @MeasureTheory.measurableSet_exists_tendsto S ℝ Ω (𝓕 s) _ _ _ _ _ _ l₀ _ _ hf

omit [OrderBot ι] [OrderTopology ι] [DenselyOrdered ι] in
lemma measurableSet_tendsto_nhdsGT' [FirstCountableTopology ι]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) (t : ι) :
    MeasurableSet {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)} := by
  let S : Set ι := (T ∩ Set.Ioi t)
  have hScount : S.Countable := hT.mono (Set.inter_subset_left)
  have : Countable S := hScount.to_subtype
  set l₀ : Filter S := Filter.comap ((↑) : S → ι) (𝓝[T ∩ Set.Ioi t] t) with hl₀
  have : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
  have hmap : Filter.map ((↑) : S → ι) l₀ = 𝓝[T ∩ Set.Ioi t] t :=
    Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact self_mem_nhdsWithin)
  have hset : {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)}
      = {ω | ∃ c, Tendsto (fun s' : S ↦ X s' ω) l₀ (𝓝 c)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    refine exists_congr fun c ↦ ?_
    rw [← hmap]
    exact tendsto_map'_iff
  rw [hset]
  have hf (s' : S) : Measurable (X s') := (hX s').mono (𝓕.le _) le_rfl
  exact MeasureTheory.measurableSet_exists_tendsto hf

omit [OrderBot ι] [OrderTopology ι] [DenselyOrdered ι] in
lemma measurableSet_tendsto_nhdsLT [FirstCountableTopology ι]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) (t : ι) :
    MeasurableSet[𝓕 t] {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio t] t) (𝓝 l)} := by
  -- Every point of `S = T ∩ Iio t` is `< t`, so `X` there is already `𝓕 t`-measurable; the limit
  -- along `𝓝[T ∩ Iio t] t` is a limit along the countable index `↥S`.
  let S : Set ι := T ∩ Set.Iio t
  have hScount : S.Countable := hT.mono Set.inter_subset_left
  have hSlt x (hx : x ∈ S) : x < t := by unfold S at hx; exact hx.2
  have hSmem : S ∈ 𝓝[T ∩ Set.Iio t] t := self_mem_nhdsWithin
  haveI : Countable S := hScount.to_subtype
  set l₀ : Filter S := Filter.comap ((↑) : S → ι) (𝓝[T ∩ Set.Iio t] t) with hl₀
  haveI : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
  have hmap : Filter.map ((↑) : S → ι) l₀ = 𝓝[T ∩ Set.Iio t] t :=
    Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact hSmem)
  have hset : {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio t] t) (𝓝 l)}
      = {ω | ∃ c, Tendsto (fun s' : S ↦ X s' ω) l₀ (𝓝 c)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    refine exists_congr fun c ↦ ?_
    rw [← hmap]
    exact tendsto_map'_iff
  rw [hset]
  have hf (s' : S) : Measurable[𝓕 t] (X s') := (hX s').mono (𝓕.mono (hSlt s' s'.2).le) le_rfl
  exact @MeasureTheory.measurableSet_exists_tendsto S ℝ Ω (𝓕 t) _ _ _ _ _ _ l₀ _ _ hf

omit [OrderBot ι] [DenselyOrdered ι] in
lemma measurable_rightLimWithin [FirstCountableTopology ι]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) (t : ι) :
    Measurable (fun ω ↦ rightLimWithin (X · ω) T t) := by
  rcases (𝓝[T ∩ Set.Ioi t] t).eq_or_neBot with hlbot | hlne
  · -- If the right neighbourhood filter is trivial, the right limit is just `X t`.
    have heq : (fun ω ↦ rightLimWithin (X · ω) T t) = X t := by
      ext ω
      exact rightLimWithin_eq_of_eq_bot _ (by rw [Set.inter_comm]; exact hlbot)
    rw [heq]
    exact (hX t).mono (𝓕.le _) le_rfl
  · -- The set where the right limit exists is `𝓕 t`-measurable.
    have hAmeas : MeasurableSet {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)} :=
      measurableSet_tendsto_nhdsGT' hT hX t
    -- Off that set, the right limit equals `X t`.
    have hoffA ω (hω : ¬ (∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l))) :
        rightLimWithin (X · ω) T t = X t ω := by
      refine rightLimWithin_eq_of_not_tendsto _ ?_
      rw [Set.inter_comm]
      exact hω
    -- A measurable version of the right limit along the countable index `↥S`, `S ⊆ (t, s)`.
    set S : Set ι := (T ∩ Set.Ioi t) with hSdef
    have hScount : S.Countable := hT.mono (Set.inter_subset_left)
    have : Countable ↥S := hScount.to_subtype
    set l₀ : Filter ↥S := Filter.comap ((↑) : ↥S → ι) (𝓝[T ∩ Set.Ioi t] t) with hl₀
    have : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
    have hmap : Filter.map ((↑) : ↥S → ι) l₀ = 𝓝[T ∩ Set.Ioi t] t :=
      Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact self_mem_nhdsWithin)
    have : l₀.NeBot := by
      constructor
      intro h
      rw [h, Filter.map_bot] at hmap
      exact hlne.ne' hmap.symm
    -- The measurable candidate.
    have hf (s' : ↥S) : Measurable (fun ω => X ↑s' ω) :=
      (hX ↑s').mono (𝓕.le _) le_rfl
    have hgmeas : Measurable (fun ω => limUnder l₀ (fun s' : ↥S => X ↑s' ω)) :=
      @measurable_limUnder ↥S Ω ℝ mΩ _ _ _ _ _ l₀ _ _ _ hf
    -- On the set where the limit exists, the candidate is the right limit.
    have hgA (ω : Ω) (hω : ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)) :
        limUnder l₀ (fun s' : ↥S ↦ X ↑s' ω) = rightLimWithin (X · ω) T t := by
      rw [Set.inter_comm] at hω
      have htend := tendsto_rightLimWithin_of_tendsto hω
      rw [Set.inter_comm, ← hmap, tendsto_map'_iff] at htend
      exact htend.limUnder_eq
    -- Assemble via `piecewise`.
    classical
    have hpw : (fun ω ↦ rightLimWithin (X · ω) T t)
        = {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)}.piecewise
            (fun ω ↦ limUnder l₀ (fun s' : ↥S => X ↑s' ω)) (X t) := by
      funext ω
      simp only [Set.piecewise]
      split_ifs with hω
      · exact (hgA ω hω).symm
      · exact hoffA ω hω
    rw [hpw]
    refine Measurable.piecewise ?_ hgmeas ?_
    · exact hAmeas
    · exact (hX t).mono (𝓕.le _) le_rfl

omit [OrderBot ι] in
lemma adapted_rightLimWithin [FirstCountableTopology ι] [𝓕.IsRightContinuous]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) :
    Adapted 𝓕 (fun t ω ↦ rightLimWithin (X · ω) T t) := by
  classical
  intro t
  rcases (𝓝[T ∩ Set.Ioi t] t).eq_or_neBot with hlbot | hlne
  · -- If the right neighbourhood filter is trivial, the right limit is just `X t`.
    have heq : (fun ω ↦ rightLimWithin (X · ω) T t) = X t := by
      ext ω
      exact rightLimWithin_eq_of_eq_bot _ (by rw [Set.inter_comm]; exact hlbot)
    simp_rw [heq]
    exact (hX t)
  · -- The set where the right limit exists is `𝓕 t`-measurable.
    have hAmeas : MeasurableSet[𝓕 t] {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)} :=
      measurableSet_tendsto_nhdsGT hT hX t
    -- Off that set, the right limit equals `X t`.
    have hoffA ω (hω : ¬ (∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l))) :
        rightLimWithin (X · ω) T t = X t ω := by
      change Function.rightLimWithin (X · ω) T t = X t ω
      refine rightLimWithin_eq_of_not_tendsto _ ?_
      rw [Set.inter_comm]
      exact hω
    -- It suffices to show `𝓕 s`-measurability for every `s > t`.
    suffices key : ∀ s, t < s → Measurable[𝓕 s] (fun ω ↦ rightLimWithin (X · ω) T t) by
      -- `t` is not maximal since it is not isolated on the right
      have ht : ¬ IsMax t := fun ht ↦ hlne.ne (by simp [ht.Ioi_eq])
      intro B hB
      exact measurableSet_of_forall_gt ht fun s hts ↦ key s hts hB
    intro s hts
    -- A measurable version of the right limit along the countable index `↥S`, `S ⊆ (t, s)`.
    set S : Set ι := (T ∩ Set.Ioi t) ∩ Set.Iio s with hSdef
    have hScount : S.Countable := hT.mono (Set.inter_subset_left.trans Set.inter_subset_left)
    have hSlt : ∀ x ∈ S, x < s := by
      intro x hx; rw [hSdef] at hx; exact hx.2
    have hSmem : S ∈ 𝓝[T ∩ Set.Ioi t] t :=
      Filter.inter_mem self_mem_nhdsWithin
        (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hts)))
    have : Countable ↥S := hScount.to_subtype
    set l₀ : Filter ↥S := Filter.comap ((↑) : ↥S → ι) (𝓝[T ∩ Set.Ioi t] t) with hl₀
    have : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
    have hmap : Filter.map ((↑) : ↥S → ι) l₀ = 𝓝[T ∩ Set.Ioi t] t :=
      Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact hSmem)
    have : l₀.NeBot := by
      constructor
      intro h
      rw [h, Filter.map_bot] at hmap
      exact hlne.ne' hmap.symm
    -- The measurable candidate.
    have hf (s' : ↥S) : Measurable[𝓕 s] (fun ω => X ↑s' ω) :=
      (hX ↑s').mono (𝓕.mono (hSlt ↑s' s'.2).le) le_rfl
    have hgmeas : Measurable[𝓕 s] (fun ω ↦ limUnder l₀ (fun s' : ↥S ↦ X ↑s' ω)) :=
      @measurable_limUnder ↥S Ω ℝ (𝓕 s) _ _ _ _ _ l₀ _ _ _ hf
    -- On the set where the limit exists, the candidate is the right limit.
    have hgA ω (hω : ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)) :
        limUnder l₀ (fun s' : ↥S ↦ X ↑s' ω) = rightLimWithin (X · ω) T t := by
      rw [Set.inter_comm] at hω
      have htend := tendsto_rightLimWithin_of_tendsto hω
      rw [Set.inter_comm, ← hmap, tendsto_map'_iff] at htend
      exact htend.limUnder_eq
    -- Assemble via `piecewise`.
    have hpw : (fun ω ↦ rightLimWithin (X · ω) T t)
        = {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)}.piecewise
            (fun ω ↦ limUnder l₀ (fun s' : ↥S ↦ X ↑s' ω)) (X t) := by
      funext ω
      simp only [Set.piecewise]
      split_ifs with hω
      · exact (hgA ω hω).symm
      · exact hoffA ω hω
    rw [hpw]
    refine Measurable.piecewise ?_ hgmeas ?_
    · exact 𝓕.mono hts.le _ hAmeas
    · exact (hX t).mono (𝓕.mono hts.le) le_rfl

/-- The set of points where the right limit along a countable dense set `T` disagrees with `X` is
countable. -/
lemma countable_not_rightLimWithin_ae_eq [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hTc : T.Countable) (hTd : Dense T) :
    {t | ¬ (fun ω ↦ rightLimWithin (X · ω) T t) =ᵐ[μ] X t}.Countable := by
  -- every dense set is cofinal among non-maximal elements
  have hcof : ∀ T : Set ι, Dense T → ∀ x : ι, ¬ IsMax x → ∃ d ∈ T, x < d :=
    fun T hTd x hx ↦ hTd.exists_gt_of_not_isMax hx
  -- the right-limit value along `T`, by choice
  let R T' x ω : ℝ := Function.rightLimWithin (X · ω) T' x
  have hRspec T' x ω (h : ∃ l, Tendsto (X · ω) (𝓝[T' ∩ Set.Ioi x] x) (𝓝 l)) :
      Tendsto (X · ω) (𝓝[T' ∩ Set.Ioi x] x) (𝓝 (R T' x ω)) := by
    rw [Set.inter_comm] at h ⊢
    exact tendsto_rightLimWithin_of_tendsto h
  -- Stage 1: a.e. one-sided limits along D₀
  have hae₀ := ae_right_limit hX hTc (hcof T hTd)
  -- Stage 2: measurable versions of `R D₀ x`
  have hRm : ∀ x : ι, ∃ g : Ω → ℝ, Measurable g ∧ g =ᵐ[μ] R T x := by
    intro x
    -- if `x` is maximal, the right limit is `X x`
    by_cases hx : IsMax x
    · refine ⟨X x, hX.measurable x, ae_of_all _ fun ω ↦ ?_⟩
      exact (rightLimWithin_eq_of_isTop (f := (X · ω)) hx.isTop).symm
    have hne : (𝓝[T ∩ Set.Ioi x] x).NeBot := by
      rw [Set.inter_comm]
      exact nhdsWithin_Ioi_inter_neBot_of_exists_gt hTd (not_isMax_iff.1 hx)
    obtain ⟨v, hv⟩ := exists_seq_tendsto (𝓝[T ∩ Set.Ioi x] x)
    have haet : ∀ᵐ ω ∂μ, Tendsto (fun j ↦ X (v j) ω) atTop (𝓝 (R T x ω)) := by
      filter_upwards [hae₀] with ω hω
      exact (hRspec T x ω (hω x)).comp hv
    obtain ⟨g, hgmeas, hgae⟩ := measurable_limit_of_tendsto_metrizable_ae
      (f := fun j ↦ X (v j)) (L := atTop) (fun j ↦ (hX.measurable (v j)).aemeasurable)
      (by filter_upwards [haet] with ω hω using ⟨_, hω⟩)
    refine ⟨g, hgmeas, ?_⟩
    filter_upwards [haet, hgae] with ω h1 h2
    exact tendsto_nhds_unique h2 h1
  choose Rm hRmMeas hRmae using hRm
  -- Stage 3: the set of points where `R D₀ x` and `X x` disagree is countable
  let Sset : Set ι := {x | ¬ R T x =ᵐ[μ] X x}
  change Sset.Countable
  by_contra hSunc
  set Sn : ℕ → Set ι := fun n ↦
    {x | ENNReal.ofReal (1 / (n + 1)) < μ {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|}} with hSn
  have hSsub : Sset ⊆ ⋃ n, Sn n := by
    intro x hx
    have hxm : ¬ Rm x =ᵐ[μ] X x := fun hcon ↦ hx ((hRmae x).symm.trans hcon)
    have hpos : μ {ω | Rm x ω ≠ X x ω} ≠ 0 := hxm
    have hBmono : Monotone (fun n : ℕ ↦ {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|}) := by
      intro n n' hnn' ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hω
      have : (n : ℝ) ≤ (n' : ℝ) := mod_cast hnn'
      gcongr
    have hBunion : {ω | Rm x ω ≠ X x ω} = ⋃ n : ℕ, {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro hne
        have habs : 0 < |Rm x ω - X x ω| := abs_pos.2 (sub_ne_zero.2 hne)
        exact exists_nat_one_div_lt habs
      · rintro ⟨n, hn⟩ hcon
        rw [hcon, sub_self, abs_zero] at hn
        exact absurd hn (not_lt.2 (by positivity))
    have hexn : ∃ n₀ : ℕ, 0 < μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} := by
      by_contra! hcon
      simp only [nonpos_iff_eq_zero] at hcon
      refine hpos ?_
      rw [hBunion]
      refine le_antisymm ((measure_iUnion_le _).trans ?_) zero_le
      simp only [hcon, tsum_zero, Std.le_refl]
    obtain ⟨n₀, hn₀⟩ := hexn
    have hfin : μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} ≠ ⊤ := measure_ne_top μ _
    let ε : ℝ := (μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|}).toReal
    have hεpos : 0 < ε := ENNReal.toReal_pos hn₀.ne' hfin
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hεpos
    let n := max n₀ n₁
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    rw [hSn]
    have hsub2 : {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|}
        ⊆ {ω | 1 / ((n : ℝ) + 1) < |Rm x ω - X x ω|} :=
      hBmono (le_max_left n₀ n₁)
    calc ENNReal.ofReal (1 / (n + 1))
        ≤ ENNReal.ofReal (1 / (n₁ + 1)) := by
          refine ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by positivity) ?_)
          gcongr
          exact mod_cast le_max_right n₀ n₁
      _ < ENNReal.ofReal ε := ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.2 hn₁
      _ = μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} := by rw [ENNReal.ofReal_toReal hfin]
      _ ≤ μ {ω | 1 / ((n : ℝ) + 1) < |Rm x ω - X x ω|} := measure_mono hsub2
  have hexSn : ∃ n, ¬ (Sn n).Countable := by
    by_contra! hcon
    exact hSunc ((Set.countable_iUnion hcon).mono hSsub)
  obtain ⟨n, hSnunc⟩ := hexSn
  obtain ⟨p, u, huSn, hup, hutend⟩ := exists_seq_gt_tendsto_of_not_countable hSnunc
  set T' : Set ι := T ∪ (Set.range u ∪ {p}) with hT'
  have hT'c : T'.Countable :=
    hTc.union ((Set.countable_range u).union (Set.countable_singleton p))
  have hT'd : Dense T' := hTd.mono Set.subset_union_left
  have haediff : ∀ᵐ ω ∂μ, Tendsto (fun k ↦ Rm (u k) ω - X (u k) ω) atTop (𝓝 0) := by
    have hcnt : ∀ᵐ ω ∂μ, ∀ k, Rm (u k) ω = R T (u k) ω := ae_all_iff.2 fun k ↦ hRmae (u k)
    filter_upwards [hae₀, ae_right_limit hX hT'c (hcof T' hT'd), hcnt] with ω hω₀ hω' hkeq
    have hL' := hRspec T' p ω (hω' p)
    have hXu : Tendsto (fun k ↦ X (u k) ω) atTop (𝓝 (R T' p ω)) := by
      refine hL'.comp ?_
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hutend, Filter.Eventually.of_forall fun k ↦ by grind⟩
    have hRu : Tendsto (fun k ↦ R T (u k) ω) atTop (𝓝 (R T' p ω)) :=
      tendsto_rightLim_comp_of_gt hTd Set.subset_union_left
        (fun y ↦ hRspec T y ω (hω₀ y)) hup hutend hL'
    have hsub := hRu.sub hXu
    rw [sub_self] at hsub
    refine Tendsto.congr (fun k ↦ ?_) hsub
    rw [hkeq k]
  have htim : TendstoInMeasure μ (fun k ω ↦ Rm (u k) ω - X (u k) ω) atTop
      (fun _ ↦ (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae
      (fun k ↦ ((hRmMeas (u k)).sub (hX.measurable (u k))).aestronglyMeasurable) ?_
    filter_upwards [haediff] with ω hω using hω
  have hcontra := htim (ENNReal.ofReal (1 / (n + 1 : ℝ)))
    (by rw [ENNReal.ofReal_pos]; positivity)
  have hev : ∀ᶠ k in atTop,
      μ {ω | ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ edist (Rm (u k) ω - X (u k) ω) 0}
        < ENNReal.ofReal (1 / (n + 1)) := by
    refine hcontra.eventually_lt_const ?_
    positivity
  obtain ⟨k, hk⟩ := hev.exists
  have hmem := huSn k
  rw [hSn, Set.mem_ofPred_eq] at hmem
  have hsub3 : {ω | 1 / (n + 1 : ℝ) < |Rm (u k) ω - X (u k) ω|}
      ⊆ {ω | ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ edist (Rm (u k) ω - X (u k) ω) 0} := by
    intro ω hω
    rw [Set.mem_ofPred_eq] at hω ⊢
    rw [edist_dist, dist_zero_right, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal hω.le
  exact lt_irrefl _ ((hmem.trans_le (measure_mono hsub3)).trans hk)

/-! ## Right-continuous modification of a quasimartingale

For a real quasimartingale `X` we define a process `rightContModif X` with the following properties:
* `rightContModif X` is right-continuous
* `rightContModif X` has left limits almost everywhere
* for all `t` outside a countable set, `rightContModif X t =ᵐ[μ] X t`
* if `t` is a maximal element of `ι`, then `rightContModif X t =ᵐ[μ] X t`
* if `X` is right-continuous in probability, then `rightContModif X` is a modification of `X`.
* if the filtration is right-continuous, then `rightContModif X` is adapted.

Note that if `X` is not right-continuous in probability, we can still obtain a modification by
changing the value of `rightContModif X` on a countable set of times, with the drawback that the
right-continuity then holds only outside that countable set.

-/

/-- The right-continuous modification of a real quasimartingale along a countable dense set `T`. -/
noncomputable
def rightContModif [SecondCountableTopology ι] (X : ι → Ω → ℝ) (t : ι) (ω : Ω) : ℝ :=
  open Classical in
  if ω ∈ regularitySetRight (denseCountable ι) X t
    then rightLimWithin (X · ω) (denseCountable ι) t else 0

omit [DenselyOrdered ι] in
lemma measurable_rightContModif [SecondCountableTopology ι]
    (hX : IsRealQuasimartingale 𝓕 X μ) (t : ι) :
    Measurable (rightContModif X t) := by
  refine Measurable.ite (measurableSet_regularitySetRight' hX countable_denseCountable t) ?_
    (by fun_prop)
  exact measurable_rightLimWithin countable_denseCountable hX.stronglyAdapted.adapted t

omit [OrderBot ι] in
lemma tendsto_rightContModif_rightLimWithin [SecondCountableTopology ι] {x : ι} {ω : Ω}
    (hω : ω ∈ regularitySetRight (denseCountable ι) X x) :
    Tendsto (rightContModif X · ω) (𝓝[>] x) (𝓝 (rightLimWithin (X · ω) (denseCountable ι) x)) := by
  have h_mem : ∀ᶠ y in 𝓝[>] x, ω ∈ regularitySetRight (denseCountable ι) X y :=
    eventually_mem_regularitySetRight_of_mem hω
  classical
  rw [tendsto_congr' (f₂ := rightLimWithin (X · ω) (denseCountable ι))]
  swap; · filter_upwards [h_mem] with s' hs using by grind [rightContModif]
  suffices ContinuousWithinAt (rightLimWithin (X · ω) (denseCountable ι)) (Set.Ici x) x by
    rwa [← continuousWithinAt_Ioi_iff_Ici] at this
  exact rightContinuous_rightLimWithin_of_mem_regularitySetRight dense_denseCountable hω

omit [OrderBot ι] in
lemma tendsto_rightContModif_leftLimWithin [SecondCountableTopology ι] {x : ι} {ω : Ω}
    (hω : ω ∈ regularitySetRight (denseCountable ι) X x) :
    Tendsto (rightContModif X · ω) (𝓝[<] x) (𝓝 (leftLimWithin (X · ω) (denseCountable ι) x)) := by
  let R := fun t ω ↦ rightLimWithin (X · ω) (denseCountable ι) t
  have hRspec x ω (hω : ω ∈ regularitySetRight (denseCountable ι) X x) :
      Tendsto (X · ω) (𝓝[(denseCountable ι) ∩ Set.Ioi x] x) (𝓝 (R x ω)) :=
    tendsto_nhdsGT_rightLimWithin_of_mem_regularitySetRight hω
  let Lc x ω := leftLimWithin (X · ω) (denseCountable ι) x
  have hLspec x ω (h : ∃ l, Tendsto (fun s' ↦ X s' ω) (𝓝[(denseCountable ι) ∩ Set.Iio x] x) (𝓝 l)) :
      Tendsto (fun s' ↦ X s' ω) (𝓝[(denseCountable ι) ∩ Set.Iio x] x) (𝓝 (Lc x ω)) := by
    unfold Lc
    simp_rw [Set.inter_comm (denseCountable ι)] at h ⊢
    exact tendsto_leftLimWithin_of_tendsto h
  have h_mem y (hyx : y ≤ x) : ω ∈ regularitySetRight (denseCountable ι) X y :=
    regularitySetRight_anti hyx hω
  classical
  rw [tendsto_congr' (f₂ := (R · ω))]
  swap; · exact eventually_nhdsWithin_of_forall fun y hy ↦ by grind [rightContModif]
  unfold R
  refine tendsto_rightLim_nhdsLT dense_denseCountable ?_ (hLspec x ω ?_)
  · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
    exact hRspec y ω (h_mem y (by grind))
  · exact left_limit_of_mem_regularitySetRight (h_mem x le_rfl) le_rfl

omit [OrderBot ι] [OrderTopology ι] [DenselyOrdered ι] in
lemma rightContModif_eq_zero [SecondCountableTopology ι] {x : ι} {ω : Ω}
    (hω : ω ∉ regularitySetRight (denseCountable ι) X x) :
    (rightContModif  X · ω) =ᶠ[𝓝[>] x] 0 := by
  have h_all y (hy : x ≤ y) : ω ∉ regularitySetRight (denseCountable ι) X y :=
    fun hω' ↦ hω (regularitySetRight_anti hy hω')
  refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
  simp at hy ⊢
  grind [rightContModif]

omit [OrderBot ι] in
lemma continuousWithinAt_rightContModif [SecondCountableTopology ι] (x : ι) (ω : Ω) :
    ContinuousWithinAt (rightContModif X · ω) (Set.Ioi x) x := by
  by_cases hω : ω ∈ regularitySetRight (denseCountable ι) X x
  · have hYx : rightContModif X x ω = rightLimWithin (X · ω) (denseCountable ι) x := by
      simp only [rightContModif, if_pos hω]
    rw [ContinuousWithinAt, hYx]
    exact tendsto_rightContModif_rightLimWithin hω
  · refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (rightContModif_eq_zero hω) ?_
    · fun_prop
    · simp [rightContModif, hω]

lemma rightContModif_ae_eq_of_rightLimWithin_ae_eq [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) {t : ι}
    (ht : (fun ω ↦ rightLimWithin (X · ω) (denseCountable ι) t) =ᵐ[μ] X t) :
    rightContModif X t =ᵐ[μ] X t := by
  filter_upwards [ae_mem_regularitySetRight hX countable_denseCountable
    (fun _ ↦ dense_denseCountable.exists_gt_of_not_isMax), ht] with ω hω hωR
  simpa only [rightContModif, if_pos (hω _)]

/-- At a maximal time `t`, the right-continuous modification is a.e. equal to `X t`. -/
lemma rightContModif_ae_eq_of_isMax [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) {t : ι} (ht : IsMax t) :
    rightContModif X t =ᵐ[μ] X t :=
  rightContModif_ae_eq_of_rightLimWithin_ae_eq hX
    (ae_of_all _ fun _ ↦ rightLimWithin_eq_of_isTop ht.isTop)

/-- The set of points where the right modification of a real quasimartingale along
a countable dense set `T` disagrees with `X` is countable. -/
lemma countable_not_rightContModif_ae_eq [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    {t | ¬ rightContModif X t =ᵐ[μ] X t}.Countable := by
  refine (countable_not_rightLimWithin_ae_eq hX countable_denseCountable dense_denseCountable).mono
    fun t ht ↦ ?_
  exact fun hcon ↦ ht (rightContModif_ae_eq_of_rightLimWithin_ae_eq hX hcon)

lemma rightContModif_ae_eq_of_tendstoInMeasure [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    (t : ι) (hXRC : TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    rightContModif X t =ᵐ[μ] X t := by
  classical
  let Y := rightContModif X
  have hY_meas t : Measurable (Y t) := measurable_rightContModif hX t
  have hYCont x ω: ContinuousWithinAt (Y · ω) (Set.Ioi x) x :=
    continuousWithinAt_rightContModif x ω
  let T := denseCountable ι
  have hTc : T.Countable := countable_denseCountable
  have hTd : Dense T := dense_denseCountable
  have hX_cont x : ∀ᵐ ω ∂μ, Tendsto (X · ω) (𝓝[>] x ⊓ 𝓟 T) (𝓝 (Y x ω)) := by
    have hX_cont' x ω (hω : ω ∈ regularitySetRight T X x) :
        Tendsto (X · ω) (𝓝[>] x ⊓ 𝓟 T) (𝓝 (rightLimWithin (X · ω) T x)) := by
      rw [nhdsWithin_inf_principal, Set.inter_comm]
      exact tendsto_nhdsGT_rightLimWithin_of_mem_regularitySetRight hω
    have h1 := ae_mem_regularitySetRight hX hTc fun _ ↦ hTd.exists_gt_of_not_isMax
    filter_upwards [h1] with ω hω using by grind [rightContModif]
  -- if `t` is maximal, the right limit is `X t`
  by_cases ht : IsMax t
  · exact rightContModif_ae_eq_of_isMax hX ht
  have : (𝓝[Set.Ioi t ∩ T] t).NeBot :=
    nhdsWithin_Ioi_inter_neBot_of_exists_gt hTd (not_isMax_iff.1 ht)
  obtain ⟨w, hseq'⟩ := exists_seq_tendsto (𝓝[Set.Ioi t ∩ T] t)
  obtain hseq : Tendsto w atTop (𝓝[>] t) := by
    rw [tendsto_nhdsWithin_iff] at hseq' ⊢
    refine ⟨hseq'.1, ?_⟩
    filter_upwards [hseq'.2] with n hn using by grind
  refine tendstoInMeasure_ae_unique ?_ ?_ (f := Y ∘ w) (u := atTop)
  · refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
    · exact (hY_meas (w n)).aestronglyMeasurable
    · exact ae_of_all _ fun ω ↦ (hYCont t ω).tendsto.comp hseq
  suffices TendstoInMeasure μ (fun k ω ↦ Y (w k) ω - X (w k) ω) atTop 0 by
    have hX_tendsto := hXRC.comp hseq
    have h_eq : Y ∘ w = (fun k ω ↦ Y (w k) ω - X (w k) ω) + (X ∘ w) := by ext; simp
    rw [h_eq, ← zero_add (X t)]
    exact TendstoInMeasure.add this hX_tendsto
  refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
  · refine StronglyMeasurable.aestronglyMeasurable ?_
    exact (hY_meas (w n)).stronglyMeasurable.sub ((hX.stronglyAdapted (w n)).mono (𝓕.le _))
  filter_upwards [hX_cont t] with ω hX_cont
  simp only [Pi.zero_apply]
  have : 0 = Y t ω - Y t ω := by simp
  rw [this]
  refine Tendsto.sub ?_ ?_
  · exact (hYCont t ω).tendsto.comp hseq
  · refine hX_cont.comp ?_
    rwa [nhdsWithin_inf_principal]

lemma adapted_rightContModif [SecondCountableTopology ι] [𝓕.IsRightContinuous]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    Adapted 𝓕 (rightContModif X) := by
  refine fun i ↦ Measurable.ite
    (measurableSet_regularitySetRight hX countable_denseCountable dense_denseCountable i) ?_
    (by fun_prop)
  exact adapted_rightLimWithin countable_denseCountable hX.stronglyAdapted.adapted i

lemma stronglyAdapted_rightContModif [SecondCountableTopology ι] [𝓕.IsRightContinuous]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    StronglyAdapted 𝓕 (rightContModif X) :=
  (adapted_rightContModif hX).stronglyAdapted

/-! ## Càdlàg modification of a quasimartingale

For a real quasimartingale `X` we define a process `cadlagModif X` with the following properties:
* `cadlagModif X` is càdlàg
* for all `t` outside a countable set, `cadlagModif X t =ᵐ[μ] X t`
* if `t` is a maximal element of `ι`, then `cadlagModif X t =ᵐ[μ] X t`
* if `X` is right-continuous in probability, then `cadlagModif X` is a modification of `X`.
* if the filtration is right-continuous and complete, then `cadlagModif X` is adapted.

TODO: if `t ↦ μ[X t]` is right-continuous (in particular if `X` is a martingale),
then `cadlagModif X` is a modification of `X` without the assumption that `X`
is right-continuous in probability.

-/

/-- The càdlàg modification of a real quasimartingale along a countable dense set `T`. -/
noncomputable
def cadlagModif [SecondCountableTopology ι] (X : ι → Ω → ℝ) (t : ι) (ω : Ω) : ℝ :=
  open Classical in
  if ∀ t, ω ∈ regularitySetRight (denseCountable ι) X t then rightContModif X t ω else 0

lemma cadlagModif_ae_eq_rightContModif [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    ∀ᵐ ω ∂μ, ∀ t, cadlagModif X t ω = rightContModif X t ω := by
  filter_upwards [ae_mem_regularitySetRight hX countable_denseCountable
    (fun _ ↦ dense_denseCountable.exists_gt_of_not_isMax)] with ω hω
  simp [cadlagModif, if_pos hω]

lemma measurable_cadlagModif [SecondCountableTopology ι]
    (hX : IsRealQuasimartingale 𝓕 X μ) (t : ι) :
    Measurable (cadlagModif X t) := by
  refine Measurable.ite ?_ (measurable_rightContModif hX t) (by fun_prop)
  have : {a | ∀ (t : ι), a ∈ regularitySetRight (denseCountable ι) X t}
      = ⋂ t ∈ denseCountable ι ∪ {s | IsMax s}, regularitySetRight (denseCountable ι) X t := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun h t _ ↦ h t, fun h t ↦ ?_⟩
    by_cases ht : IsMax t
    · exact h t (.inr ht)
    obtain ⟨t', ht'T, htt'⟩ := dense_denseCountable.exists_gt_of_not_isMax ht
    exact regularitySetRight_anti htt'.le (h t' (.inl ht'T))
  rw [this]
  exact MeasurableSet.biInter (countable_denseCountable.union countable_setOf_isMax)
    fun t _ ↦ measurableSet_regularitySetRight' hX countable_denseCountable t

omit [OrderBot ι] in
lemma continuousWithinAt_cadlagModif [SecondCountableTopology ι] (x : ι) (ω : Ω) :
    ContinuousWithinAt (cadlagModif X · ω) (Set.Ioi x) x := by
  unfold cadlagModif
  split_ifs with hω
  · exact continuousWithinAt_rightContModif x ω
  · fun_prop

omit [OrderBot ι] in
lemma exists_tendsto_nhdsLT_cadlagModif [SecondCountableTopology ι] (x : ι) (ω : Ω) :
    ∃ l, Tendsto (cadlagModif X · ω) (𝓝[<] x) (𝓝 l) := by
  unfold cadlagModif
  split_ifs with hω
  · exact ⟨Function.leftLimWithin (X · ω) (denseCountable ι) x,
      tendsto_rightContModif_leftLimWithin (hω x)⟩
  · exact ⟨0, tendsto_const_nhds⟩

omit [OrderBot ι] in
theorem isCadlag_cadlagModif [SecondCountableTopology ι] (ω : Ω) :
    IsCadlag (cadlagModif X · ω) := by
  constructor
  · exact fun x ↦ continuousWithinAt_cadlagModif x ω
  · exact fun x ↦ exists_tendsto_nhdsLT_cadlagModif x ω

lemma cadlagModif_ae_eq_of_rightLimWithin_ae_eq [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) {t : ι}
    (ht : (fun ω ↦ rightLimWithin (X · ω) (denseCountable ι) t) =ᵐ[μ] X t) :
    cadlagModif X t =ᵐ[μ] X t := by
  filter_upwards [ae_mem_regularitySetRight hX countable_denseCountable
    (fun _ ↦ dense_denseCountable.exists_gt_of_not_isMax), ht] with ω hω hωR
  simpa only [cadlagModif, if_pos hω, rightContModif, if_pos (hω t)]

/-- At a maximal time `t`, the càdlàg modification is a.e. equal to `X t`. -/
lemma cadlagModif_ae_eq_of_isMax [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) {t : ι} (ht : IsMax t) :
    cadlagModif X t =ᵐ[μ] X t :=
  cadlagModif_ae_eq_of_rightLimWithin_ae_eq hX
    (ae_of_all _ fun _ ↦ rightLimWithin_eq_of_isTop ht.isTop)

/-- The set of points where the cadlag modification of a real quasimartingale along
a countable dense set `T` disagrees with `X` is countable. -/
lemma countable_not_cadlagModif_ae_eq [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    {t | ¬ cadlagModif X t =ᵐ[μ] X t}.Countable := by
  refine (countable_not_rightLimWithin_ae_eq hX countable_denseCountable dense_denseCountable).mono
    fun t ht ↦ ?_
  simp only [Set.mem_ofPred_eq] at ht ⊢
  refine fun h_contra ↦ ht ?_
  filter_upwards [cadlagModif_ae_eq_rightContModif hX,
    rightContModif_ae_eq_of_rightLimWithin_ae_eq hX h_contra] with ω hω hωc
  grind

lemma cadlagModif_ae_eq_of_tendstoInMeasure [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    (t : ι) (hXRC : TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    cadlagModif X t =ᵐ[μ] X t := by
  filter_upwards [cadlagModif_ae_eq_rightContModif hX,
    rightContModif_ae_eq_of_tendstoInMeasure hX t hXRC] with ω hω hωc
  grind

lemma adapted_cadlagModif [SecondCountableTopology ι] [𝓕.IsRightContinuous] [𝓕.IsComplete μ]
    [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    Adapted 𝓕 (cadlagModif X) := by
  refine fun i ↦ Measurable.ite ?_ (adapted_rightContModif hX i)
    (by fun_prop)
  rw [← MeasurableSet.compl_iff]
  refine Filtration.IsComplete.measurableSet_of_null ?_ i (μ := μ)
  have h := ae_mem_regularitySetRight hX countable_denseCountable
    fun _ ↦ dense_denseCountable.exists_gt_of_not_isMax
  rwa [ae_iff] at h

lemma stronglyAdapted_cadlagModif [SecondCountableTopology ι] [𝓕.IsRightContinuous] [𝓕.IsComplete μ]
    [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    StronglyAdapted 𝓕 (cadlagModif X) :=
  (adapted_cadlagModif hX).stronglyAdapted

lemma _root_.MeasureTheory.Martingale.integral_eq [SigmaFiniteFiltration μ 𝓕]
    (hX : Martingale X 𝓕 μ) (i j : ι) : ∫ ω, X i ω ∂μ = ∫ ω, X j ω ∂μ := by
  wlog hij : i ≤ j
  · exact (this hX j i (by grind)).symm
  conv_rhs => rw [← integral_condExp (𝓕.le i)]
  refine integral_congr_ae ?_
  filter_upwards [hX.2 i j hij] with _ heq using heq.symm

section Modification

variable [SecondCountableTopology ι] [IsFiniteMeasure μ]

/-- If `t` is not maximal, there is a sequence of times `w n ∈ (t, u]` tending to `t` along which
a quasimartingale `X` converges almost surely to `rightContModif X t`. -/
lemma exists_seq_tendsto_rightContModif (hX : IsRealQuasimartingale 𝓕 X μ) {t u : ι}
    (htu : t < u) :
    ∃ w : ℕ → ι, (∀ n, t < w n) ∧ (∀ n, w n ≤ u) ∧ Tendsto w atTop (𝓝[>] t) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (w n) ω) atTop (𝓝 (rightContModif X t ω)) := by
  let T := denseCountable ι
  have hTc : T.Countable := countable_denseCountable
  have hTd : Dense T := dense_denseCountable
  have : (𝓝[Set.Ioi t ∩ T] t).NeBot := nhdsWithin_Ioi_inter_neBot_of_exists_gt hTd ⟨u, htu⟩
  obtain ⟨w₀, hw₀⟩ := exists_seq_tendsto (𝓝[Set.Ioi t ∩ T] t)
  have h_ev : ∀ᶠ n in atTop, w₀ n ≤ u ∧ w₀ n ∈ Set.Ioi t ∩ T := by
    rw [tendsto_nhdsWithin_iff] at hw₀
    filter_upwards [hw₀.1.eventually (eventually_lt_nhds htu), hw₀.2] with n hn1 hn2
      using ⟨hn1.le, hn2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 h_ev
  have hw : Tendsto (fun n ↦ w₀ (n + N)) atTop (𝓝[T ∩ Set.Ioi t] t) := by
    rw [Set.inter_comm]
    exact (tendsto_add_atTop_iff_nat N).2 hw₀
  refine ⟨fun n ↦ w₀ (n + N), fun n ↦ (hN (n + N) (by lia)).2.1, fun n ↦ (hN (n + N) (by lia)).1,
    hw.mono_right (nhdsWithin_mono _ Set.inter_subset_right), ?_⟩
  filter_upwards [ae_mem_regularitySetRight hX hTc fun _ ↦ hTd.exists_gt_of_not_isMax] with ω hω
  have hYω : rightContModif X t ω = Function.rightLimWithin (X · ω) T t := by
    simp only [rightContModif, T, if_pos (hω t)]
  rw [hYω]
  exact (tendsto_nhdsGT_rightLimWithin_of_mem_regularitySetRight (hω t)).comp hw

/-- The right-continuous modification of a martingale with respect to a right-continuous
filtration is a modification. -/
theorem _root_.MeasureTheory.Martingale.rightContModif_ae_eq [𝓕.IsRightContinuous]
    (hX : Martingale X 𝓕 μ) (t : ι) :
    rightContModif X t =ᵐ[μ] X t := by
  have hXq : IsRealQuasimartingale 𝓕 X μ := hX.isRealQuasimartingale
  -- if `t` is maximal, the right limit is `X t`
  by_cases ht : IsMax t
  · exact rightContModif_ae_eq_of_isMax hXq ht
  -- a sequence `w n ∈ (t, u]` which tends to `t`, with `X (w n) → rightContModif X t` a.e.
  obtain ⟨u, htu⟩ := not_isMax_iff.1 ht
  obtain ⟨w, htw, hwu, -, h_tendsto⟩ := exists_seq_tendsto_rightContModif hXq htu
  -- the sequence `X (w n)` is uniformly integrable, hence converges in `L¹`
  have hUI : UniformIntegrable (fun n ↦ X (w n)) 1 μ := by
    rw [uniformIntegrable_congr_ae (g := fun n ↦ μ[X u | 𝓕 (w n)])
      fun n ↦ (hX.2 (w n) u (hwu n)).symm]
    exact (hX.integrable u).uniformIntegrable_condExp fun n ↦ 𝓕.le (w n)
  have hY_int : Integrable (rightContModif X t) μ := hUI.integrable_of_ae_tendsto h_tendsto
  -- `rightContModif X t` and `X t` are `𝓕 t`-measurable and have the same integrals on `𝓕 t`
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (𝓕.le t)
    (fun _ _ _ ↦ hY_int.integrableOn) (fun _ _ _ ↦ (hX.integrable t).integrableOn)
    (fun A hA _ ↦ ?_) (adapted_rightContModif hXq t).stronglyMeasurable.aestronglyMeasurable
    (hX.stronglyAdapted t).aestronglyMeasurable
  refine tendsto_nhds_unique (hUI.tendsto_setIntegral h_tendsto A) ?_
  simp_rw [← hX.setIntegral_eq (htw _).le hA]
  exact tendsto_const_nhds

/-- The càdlàg modification of a martingale with respect to a right-continuous filtration is a
modification. -/
theorem _root_.MeasureTheory.Martingale.cadlagModif_ae_eq [𝓕.IsRightContinuous]
    (hX : Martingale X 𝓕 μ) (t : ι) :
    cadlagModif X t =ᵐ[μ] X t := by
  filter_upwards [cadlagModif_ae_eq_rightContModif hX.isRealQuasimartingale,
    hX.rightContModif_ae_eq t] with ω hω hωc
  rw [hω t, hωc]

/-- The right-continuous modification of a submartingale with respect to a right-continuous
filtration is a modification at the times where the expectation is right-continuous. -/
theorem _root_.MeasureTheory.Submartingale.rightContModif_ae_eq [𝓕.IsRightContinuous]
    (hX : Submartingale X 𝓕 μ) (t : ι)
    (hXRC : Tendsto (fun s ↦ μ[X s]) (𝓝[>] t) (𝓝 (μ[X t]))) :
    rightContModif X t =ᵐ[μ] X t := by
  have hXq : IsRealQuasimartingale 𝓕 X μ := hX.isRealQuasimartingale
  -- if `t` is maximal, the right limit is `X t`
  by_cases ht : IsMax t
  · exact rightContModif_ae_eq_of_isMax hXq ht
  -- a sequence `w n ∈ (t, u]` which tends to `t`, with `X (w n) → Y := rightContModif X t` a.e.
  obtain ⟨u, htu⟩ := not_isMax_iff.1 ht
  obtain ⟨w, htw, hwu, hw, h_tendsto⟩ := exists_seq_tendsto_rightContModif hXq htu
  set Y := rightContModif X t
  -- `Y` is integrable, by Fatou's lemma
  have hY_int : Integrable Y μ := by
    refine memLp_one_iff_integrable.1 ⟨(measurable_rightContModif hXq t).aestronglyMeasurable, ?_⟩
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n ↦ (hX.integrable (w n)).aestronglyMeasurable) Y h_tendsto).trans_lt ?_
    have h_le n : eLpNorm (X (w n)) 1 μ
        ≤ ENNReal.ofReal (2 * ∫ ω, X u ω ⊔ 0 ∂μ - ∫ ω, X t ω ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm,
        ← ofReal_integral_norm_eq_lintegral_enorm (hX.integrable _)]
      exact ENNReal.ofReal_le_ofReal (hX.integral_abs_le (htw n).le (hwu n))
    refine (liminf_le_liminf (.of_forall h_le)).trans_lt ?_
    simp
  -- the truncated processes `X ⊔ c` are submartingales, uniformly integrable along `w`
  have hZ (c : ℝ) : Submartingale (fun s ω ↦ X s ω ⊔ c) 𝓕 μ :=
    hX.sup (martingale_const 𝓕 μ c).submartingale
  have hZ_UI (c : ℝ) : UniformIntegrable (fun n ω ↦ X (w n) ω ⊔ c) 1 μ :=
    uniformIntegrable_of_le_condExp (fun n ↦ 𝓕.le (w n)) ((hZ c).integrable u)
      (fun n ↦ ((hZ c).integrable (w n)).aestronglyMeasurable)
      (fun n ↦ .of_forall fun ω ↦ le_sup_right) (fun n ↦ (hZ c).2.1 (w n) u (hwu n))
  have hZ_lim (c : ℝ) (A : Set Ω) : Tendsto (fun n ↦ ∫ ω in A, X (w n) ω ⊔ c ∂μ) atTop
      (𝓝 (∫ ω in A, Y ω ⊔ c ∂μ)) := by
    refine (hZ_UI c).tendsto_setIntegral ?_ A
    filter_upwards [h_tendsto] with ω hω using hω.sup_nhds tendsto_const_nhds
  -- `∫_A X t ≤ ∫_A Y` for `A ∈ 𝓕 t`: true for the truncated processes, then let `c → -∞`
  have h_le (A : Set Ω) (hA : MeasurableSet[𝓕 t] A) :
      ∫ ω in A, X t ω ∂μ ≤ ∫ ω in A, Y ω ∂μ := by
    refine le_of_tendsto_of_tendsto' ((hX.integrable t).tendsto_setIntegral_sup_neg_natCast A)
      (hY_int.tendsto_setIntegral_sup_neg_natCast A) fun k ↦ ?_
    exact ge_of_tendsto' (hZ_lim _ A) fun n ↦ (hZ _).setIntegral_le (htw n).le hA
  -- `∫ Y ≤ ∫ X (w n₀)` for all `n₀`, by the same argument, hence `∫ Y ≤ ∫ X t`
  have h_ge : ∫ ω, Y ω ∂μ ≤ ∫ ω, X t ω ∂μ := by
    refine ge_of_tendsto' (hXRC.comp hw) fun n₀ ↦ ?_
    have h1 := hY_int.tendsto_setIntegral_sup_neg_natCast Set.univ
    have h2 := (hX.integrable (w n₀)).tendsto_setIntegral_sup_neg_natCast Set.univ
    simp only [Measure.restrict_univ] at h1 h2
    refine le_of_tendsto_of_tendsto' h1 h2 fun k ↦ ?_
    have h3 := hZ_lim (-(k : ℝ)) Set.univ
    simp only [Measure.restrict_univ] at h3
    have h_ev : ∀ᶠ n in atTop, w n < w n₀ :=
      (hw.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (htw n₀))
    refine le_of_tendsto h3 ?_
    filter_upwards [h_ev] with n hn
    simpa using (hZ (-(k : ℝ))).setIntegral_le hn.le MeasurableSet.univ
  -- `Y` and `X t` are `𝓕 t`-measurable and have the same integrals on `𝓕 t`
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (𝓕.le t)
    (fun _ _ _ ↦ hY_int.integrableOn) (fun _ _ _ ↦ (hX.integrable t).integrableOn)
    (fun A hA _ ↦ le_antisymm ?_ (h_le A hA))
    (adapted_rightContModif hXq t).stronglyMeasurable.aestronglyMeasurable
    (hX.stronglyAdapted t).aestronglyMeasurable
  have h1 := integral_add_compl (𝓕.le t A hA) hY_int
  have h2 := integral_add_compl (𝓕.le t A hA) (hX.integrable t)
  have h3 := h_le Aᶜ hA.compl
  linarith

/-- The càdlàg modification of a submartingale with respect to a right-continuous filtration is a
modification at the times where the expectation is right-continuous. -/
theorem _root_.MeasureTheory.Submartingale.cadlagModif_ae_eq [𝓕.IsRightContinuous]
    (hX : Submartingale X 𝓕 μ) (t : ι)
    (hXRC : Tendsto (fun s ↦ μ[X s]) (𝓝[>] t) (𝓝 (μ[X t]))) :
    cadlagModif X t =ᵐ[μ] X t := by
  filter_upwards [cadlagModif_ae_eq_rightContModif hX.isRealQuasimartingale,
    hX.rightContModif_ae_eq t hXRC] with ω hω hωc
  rw [hω t, hωc]

end Modification

end ProbabilityTheory
