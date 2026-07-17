/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# The variation process

## Main definitions

* `variationProcess`: the pathwise variation of `X` from a starting time `a`, as a process.

## Main results

* `variationProcess_nonneg`: for `a ≤ t` the variation process is nonnegative.
* `monotone_variationProcess`: the variation process of a path of locally bounded variation is
  monotone in time.
* `continuous_variationProcess`: the variation process of a continuous path of bounded variation is
  continuous.
* `MeasureTheory.StronglyAdapted.stronglyMeasurable_variationProcess`: for `a ≤ t`, the value of the
  variation process at time `t` is `𝓕 t`-measurable.

-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace ProbabilityTheory
open scoped ENNReal Topology

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω}

section Basic

variable [LinearOrder ι] [PseudoEMetricSpace E]

/-- The variation process of `X` from the starting time `a`: at time `t` and outcome `ω`, the signed
variation `variationOnFromTo (X · ω) univ a t` of the path `s ↦ X s ω`. For `a ≤ t` this is the
total variation of the path on `[a, t]`. -/
noncomputable def variationProcess (X : ι → Ω → E) (a : ι) : ι → Ω → ℝ :=
  fun t ω ↦ variationOnFromTo (X · ω) univ a t

theorem variationProcess_eq_toReal_eVariationOn_Icc (X : ι → Ω → E) {a t : ι} (hat : a ≤ t)
    (ω : Ω) : variationProcess X a t ω = (eVariationOn (X · ω) (Icc a t)).toReal := by
  simp [variationProcess, variationOnFromTo, univ_inter, hat]

theorem variationProcess_nonneg (X : ι → Ω → E) {a t : ι} (hat : a ≤ t) (ω : Ω) :
    0 ≤ variationProcess X a t ω :=
  variationOnFromTo.nonneg_of_le _ _ hat

theorem monotone_variationProcess {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) univ) (a : ι) :
    Monotone fun t ↦ variationProcess X a t ω := fun _ _ hst ↦
  variationOnFromTo.monotoneOn hX (mem_univ a) (mem_univ _) (mem_univ _) hst

end Basic

section Continuity

variable [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [PseudoEMetricSpace E] {X : ι → Ω → E} {ω : Ω} {c : ι}

/-- The variation process of a path of bounded variation that is continuous from the left at `c` is
left-continuous at `c`. -/
theorem continuousWithinAt_variationProcess_Iic
    (hX : BoundedVariationOn (X · ω) univ)
    (hcont : ContinuousWithinAt (fun t ↦ X t ω) (Iic c) c) (a : ι) :
    ContinuousWithinAt (fun t ↦ variationProcess X a t ω) (Iic c) c := by
  have hE : Tendsto (fun t ↦ eVariationOn (X · ω) (Icc t c)) (𝓝[Iic c] c) (𝓝 0) := by
    have h0 := hX.tendsto_eVariationOn_Icc_zero_left (x := c) (by simpa using hcont)
    rw [nhdsWithin_univ] at h0
    simpa [univ_inter] using h0.mono_left nhdsWithin_le_nhds
  have htend : Tendsto (fun t ↦ (eVariationOn (X · ω) (Icc t c)).toReal) (𝓝[Iic c] c) (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
  have hrepr : (fun t ↦ variationProcess X a t ω) =ᶠ[𝓝[Iic c] c]
      fun t ↦ variationProcess X a c ω - (eVariationOn (X · ω) (Icc t c)).toReal := by
    filter_upwards [self_mem_nhdsWithin] with t htc
    have hadd := variationOnFromTo.add (f := fun s ↦ X s ω) (s := univ)
      hX.locallyBoundedVariationOn (mem_univ a) (mem_univ c) (mem_univ t)
    have hge : variationOnFromTo (fun s ↦ X s ω) univ c t
        = -(eVariationOn (X · ω) (Icc t c)).toReal := by
      rw [variationOnFromTo.eq_of_ge _ _ htc, univ_inter]
    change variationOnFromTo (fun s ↦ X s ω) univ a t
      = variationOnFromTo (fun s ↦ X s ω) univ a c - (eVariationOn (X · ω) (Icc t c)).toReal
    rw [← hadd, hge]; ring
  change Tendsto (fun t ↦ variationProcess X a t ω) (𝓝[Iic c] c) (𝓝 (variationProcess X a c ω))
  refine Tendsto.congr' hrepr.symm ?_
  simpa using tendsto_const_nhds.sub htend

/-- The variation process of a path of bounded variation that is continuous from the right at `c` is
right-continuous at `c`. This is Mathlib's `continuousWithinAt_variationOnFromTo_Ici`, since
`variationProcess X a · ω = variationOnFromTo (X · ω) univ a`. -/
theorem continuousWithinAt_variationProcess_Ici
    (hX : BoundedVariationOn (X · ω) univ)
    (hcont : ContinuousWithinAt (fun t ↦ X t ω) (Ici c) c) (a : ι) :
    ContinuousWithinAt (fun t ↦ variationProcess X a t ω) (Ici c) c :=
  hX.continuousWithinAt_variationOnFromTo_Ici hcont

/-- The variation process of a continuous path of bounded variation is continuous. -/
theorem continuous_variationProcess (hX : BoundedVariationOn (X · ω) univ)
    (hcont : Continuous fun t ↦ X t ω) (a : ι) :
    Continuous fun t ↦ variationProcess X a t ω := by
  rw [continuous_iff_continuousAt]
  intro c
  rw [← continuousWithinAt_univ, ← Iic_union_Ici_of_le (le_refl c)]
  exact (continuousWithinAt_variationProcess_Iic hX hcont.continuousWithinAt a).union
    (continuousWithinAt_variationProcess_Ici hX hcont.continuousWithinAt a)

end Continuity

section Measurability

/-- There is a countable dense set containing a given point and every point that is isolated on
the left.  Partitions with points in such a set suffice to compute the variation of a continuous
function on an interval. -/
private lemma exists_countable_dense_mem_isolated [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (a : ι) :
    ∃ Q : Set ι, Q.Countable ∧ Dense Q ∧ a ∈ Q ∧ ∀ x : ι, 𝓝[<] x = ⊥ → x ∈ Q := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ι
  exact ⟨D ∪ {x | 𝓝[<] x = ⊥} ∪ {a},
    (hDc.union countable_setOf_isolated_left).union (countable_singleton a),
    hDd.mono (subset_union_left.trans subset_union_left),
    Or.inr rfl, fun x hx ↦ Or.inl (Or.inr hx)⟩

/-- For a continuous function, the variation on `[a, c]` can be computed using only partition
points in a dense set containing `a` and all points that are isolated on the left: every
partition point can be approximated from the left inside its gap, which preserves
monotonicity. -/
private lemma eVariationOn_inter_Icc_of_dense [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [PseudoEMetricSpace E] {f : ι → E} (hf : Continuous f) {Q : Set ι}
    (hQd : Dense Q) (hQiso : ∀ x, 𝓝[<] x = ⊥ → x ∈ Q) {a : ι} (haQ : a ∈ Q) (c : ι) :
    eVariationOn f (Q ∩ Icc a c) = eVariationOn f (Icc a c) := by
  classical
  refine le_antisymm (eVariationOn.mono f inter_subset_right) ?_
  have hdef : eVariationOn f (Icc a c) =
      ⨆ p : ℕ × {u : ℕ → ι // Monotone u ∧ ∀ i, u i ∈ Icc a c},
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
  have choice : ∀ x y : ι, x < y → ∃ w ∈ Q, w ∈ Ioc x y ∧ edist (f w) (f y) ≤ ε := by
    intro x y hxy
    by_cases hiso : 𝓝[<] y = ⊥
    · exact ⟨y, hQiso y hiso, ⟨hxy, le_rfl⟩, by simp⟩
    haveI : (𝓝[<] y).NeBot := ⟨hiso⟩
    have hball : IsOpen {z | edist (f z) (f y) < ε} :=
      isOpen_Iio.preimage (hf.edist continuous_const)
    have hmem : Ioo x y ∩ {z | edist (f z) (f y) < ε} ∈ 𝓝[<] y :=
      inter_mem (Ioo_mem_nhdsLT hxy) (mem_nhdsWithin_of_mem_nhds (hball.mem_nhds
        (by simpa [edist_self] using pos_iff_ne_zero.2 hε0)))
    obtain ⟨w, hwQ, hw⟩ := hQd.exists_mem_open (isOpen_Ioo.inter hball)
      (Filter.nonempty_of_mem hmem)
    exact ⟨w, hwQ, ⟨hw.1.1, hw.1.2.le⟩, hw.2.le⟩
  have choice₀ : ∃ w ∈ Q, w ∈ Icc a (u 0) ∧ edist (f w) (f (u 0)) ≤ ε := by
    rcases (hus 0).1.eq_or_lt with heq | hlt
    · exact ⟨a, haQ, ⟨le_rfl, heq.le⟩, by simp [← heq]⟩
    · obtain ⟨w, hwQ, hw, hwd⟩ := choice a (u 0) hlt
      exact ⟨w, hwQ, ⟨hw.1.le, hw.2⟩, hwd⟩
  -- an approximating point for each partition point, chosen in the gap below its first
  -- occurrence so that the assignment is monotone
  have hex : ∀ m : ℕ, ∃ w : ι, (∀ j < m, u j < u m) → w ∈ Q ∧ w ∈ Icc a c ∧ w ≤ u m ∧
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
    _ ≤ eVariationOn f (Q ∩ Icc a c) + ↑δ := by
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
      funext fun ω ↦ eVariationOn.subsingleton _ subsingleton_empty
    rw [h0]
    exact measurable_const
  obtain ⟨e, he⟩ := hS.exists_eq_range hSne
  have heS : ∀ k, e k ∈ S := fun k ↦ he ▸ mem_range_self k
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


/-- For `a ≤ t`, the value of the variation process at time `t` is `𝓕 t`-measurable. -/
theorem MeasureTheory.StronglyAdapted.stronglyMeasurable_variationProcess
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] [PseudoEMetricSpace E] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, Continuous fun t ↦ X t ω) {a t : ι} (hat : a ≤ t) :
    StronglyMeasurable[𝓕 t] (variationProcess X a t) := by
  obtain ⟨Q, hQc, hQd, haQ, hQiso⟩ := exists_countable_dense_mem_isolated a
  have hform : variationProcess X a t = fun ω ↦ (eVariationOn (X · ω) (Q ∩ Icc a t)).toReal :=
    funext fun ω ↦ by
      rw [variationProcess_eq_toReal_eVariationOn_Icc X hat ω,
        ← eVariationOn_inter_Icc_of_dense (hcont ω) hQd hQiso haQ t]
  rw [hform]
  exact (Measurable.ennreal_toReal (measurable_eVariationOn_of_countable
    (hQc.mono inter_subset_left)
    fun s hs ↦ (hX s).mono (𝓕.mono hs.2.2))).stronglyMeasurable

end Measurability
