/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BrownianMotion.Auxiliary.SeparableSpace
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
* `MeasureTheory.StronglyAdapted.measurable_variationProcess_of_continuous`,
  `..._of_continuousWithinAt_Ioi` and `..._of_continuousWithinAt_Iio`: for `a ≤ t`, the value at
  time `t` of the variation process of a strongly adapted process is `𝓕 t`-measurable.

## Measurability: two sets of assumptions

The variation over a set of times `s` is an uncountable supremum, so measurability is obtained by
computing it over a *countable* dense set of times instead. Which dense sets suffice depends on
the regularity of the paths, and we provide two independent results:

* the first assumes **continuity** of the paths together with **separability** of the time index
  (`eVariationOn_eq_comp_val_of_dense`, `measurable_eVariationOn_of_continuousWithinAt`);
* the second assumes only **right-continuity** of the paths, but requires the time index to be
  **second countable** (`eVariationOn_eq_comp_val_of_dense_Ioi`,
  `measurable_eVariationOn_of_continuousWithinAt_Ioi`), together with its left-continuous
  counterparts `eVariationOn_eq_comp_val_of_dense_Iio` and
  `measurable_eVariationOn_of_continuousWithinAt_Iio`, obtained by order duality.

Neither hypothesis implies the other as separability usually does not imply second countable
topology in an order topology.

## TODO

* There are several results in Mathlib about the continuity of the variation (e.g.
  `BoundedVariationOn.continuousWithinAt_variationOnFromTo_Ici`), and these should be generalized
  to functions of locally bounded variation.
* The left-continuous results are currently deduced from their right-continuous counterparts by
  hand, through `OrderDual`; the `to_dual` tactic should be able to produce them automatically.

-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω}

variable [LinearOrder ι] [PseudoEMetricSpace E]

/-- The variation process of `X` from the starting time `a`. -/
noncomputable def variationProcess (X : ι → Ω → E) (a : ι) : ι → Ω → ℝ :=
  fun t ω ↦ variationOnFromTo (X · ω) univ a t

/-- For `a ≤ t`, the variation process at time `t` is the total variation of the path on `Icc a t`,
converted to a real number. -/
theorem variationProcess_eq_toReal_eVariationOn_Icc (X : ι → Ω → E) {a t : ι} (hat : a ≤ t)
    (ω : Ω) : variationProcess X a t ω = (eVariationOn (X · ω) (Icc a t)).toReal := by
  simp [variationProcess, variationOnFromTo, univ_inter, hat]

/-- For `a ≤ t` the variation process is nonnegative. It can be negative for `t < a`, where it
takes the signed value `-(eVariationOn (X · ω) (Icc t a)).toReal`. -/
theorem variationProcess_nonneg (X : ι → Ω → E) {a t : ι} (hat : a ≤ t) (ω : Ω) :
    0 ≤ variationProcess X a t ω :=
  variationOnFromTo.nonneg_of_le _ _ hat

/-- The variation process of a path of locally bounded variation is monotone in time. Monotonicity
holds on all of `ι`, not just above the starting time `a`, since the variation is signed. -/
theorem monotone_variationProcess {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) univ) (a : ι) :
    Monotone fun t ↦ variationProcess X a t ω :=
  fun _ _ hst ↦ variationOnFromTo.monotoneOn hX (mem_univ a) (mem_univ _) (mem_univ _) hst

section Measurability

/-- The variation over `s`, reindexed as a supremum over monotone tuples `Fin (n + 1) → ι` with
values in `s`. Unlike the defining supremum over monotone sequences `ℕ → ι`, this index type is
countable whenever `s` is, which is what makes `measurable_eVariationOn_of_countable` go through. -/
theorem eVariationOn_eq_iSup_fin {s : Set ι} (X : ι → Ω → E) (ω : Ω) :
    eVariationOn (X · ω) s = ⨆ (n : ℕ) (p : {u : Fin (n + 1) → ι // Monotone u ∧ ∀ i, u i ∈ s}),
      ∑ i : Fin n, edist (X (p.1 i.succ) ω) (X (p.1 i.castSucc) ω) := by
  refine le_antisymm (iSup_le fun ⟨n, u, hu, hus⟩ ↦ ?_)
    (iSup_le fun n ↦ iSup_le fun ⟨p, hp, hps⟩ ↦ ?_)
  · let κ := fun n ↦ {u : Fin (n + 1) → ι // Monotone u ∧ ∀ i, u i ∈ s}
    let p : κ n := ⟨fun i : Fin (n + 1) ↦ u i, hu.comp Fin.val_strictMono.monotone, fun i ↦ hus i⟩
    have : ∑ i ∈ Finset.range n, edist (X (u (i + 1)) ω) (X (u i) ω) =
      ∑ i : Fin n, edist (X (p.1 i.succ) ω) (X (p.1 i.castSucc) ω) := by simp [Finset.sum_range, p]
    simpa [this] using le_iSup₂ (α := ℝ≥0∞) n p
  · let v : ℕ → ι := fun k ↦ p ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩
    have : ∑ i : Fin n, edist (X (p i.succ) ω) (X (p i.castSucc) ω) =
      ∑ i ∈ Finset.range n, edist (X (v (i + 1)) ω) (X (v i) ω) := by
      simp only [Finset.sum_range, Order.add_one_le_iff, Fin.is_lt, inf_of_le_left, Fin.is_le', v]
      congr
    rw [this]
    exact eVariationOn.sum_le (fun _ _ _ ↦ hp (by aesop)) fun i ↦ hps _

/-- The variation of a process over a countable set of times is measurable in `ω`. -/
theorem measurable_eVariationOn_of_countable {m : MeasurableSpace Ω} {s : Set ι}
    (hs : s.Countable) {X : ι → Ω → E} (hX : ∀ i ∈ s, StronglyMeasurable[m] (X i)) :
    Measurable[m] fun ω ↦ eVariationOn (X · ω) s := by
  simp only [eVariationOn_eq_iSup_fin]
  refine Measurable.iSup fun n ↦ ?_
  have : Countable {u : Fin (n + 1) → ι // Monotone u ∧ ∀ i, u i ∈ s} :=
    (countable_pi fun _ ↦ hs).mono fun _ hu ↦ hu.2
  refine Measurable.iSup fun p ↦ Finset.measurable_sum _ fun i _ ↦ ?_
  exact (continuous_edist.comp_stronglyMeasurable
    ((hX _ (p.2.2 i.succ)).prodMk (hX _ (p.2.2 i.castSucc)))).measurable

/-- Transfer of a partial sum to a subset: if every partition point `u i` with `i ≤ n` has an
approximant `q i ∈ t` within `ζ / (2 * (n + 1))`, chosen monotonically, then the partial sum of
`u` over `Finset.range n` is at most the variation over `t` plus `ζ`. This is the common endgame
of `eVariationOn_eq_comp_val_of_dense` and `eVariationOn_eq_comp_val_of_dense_Ioi`. -/
private lemma sum_le_eVariationOn_add {s : Set ι} {t : Set s} {f : ι → E} {n : ℕ} {u : ℕ → ι}
    {q : ℕ → s} {ζ : ℝ≥0} (hqmono : MonotoneOn (fun i ↦ ((q i : s) : ι)) (Iic n))
    (hqt : ∀ i ≤ n, ((q i : s) : ι) ∈ (↑t : Set ι))
    (hqd : ∀ i ≤ n, edist (f ((q i : s) : ι)) (f (u i)) ≤ ζ / (2 * (n + 1))) :
    ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ≤ eVariationOn f t + ζ := by
  set ε : ℝ≥0∞ := ζ / (2 * (n + 1)) with hεdef
  -- replace each partition point by its approximant, paying `2 * ε` per step
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))
      ≤ ∑ i ∈ Finset.range n, (edist (f ((q (i + 1) : s) : ι)) (f ((q i : s) : ι)) + 2 * ε) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hin := Finset.mem_range.1 hi
        calc edist (f (u (i + 1))) (f (u i))
            ≤ edist (f (u (i + 1))) (f ((q (i + 1) : s) : ι)) +
                edist (f ((q (i + 1) : s) : ι)) (f ((q i : s) : ι)) +
                edist (f ((q i : s) : ι)) (f (u i)) := edist_triangle4 _ _ _ _
          _ ≤ ε + edist (f ((q (i + 1) : s) : ι)) (f ((q i : s) : ι)) + ε := by
              gcongr
              · rw [edist_comm]
                exact hqd (i + 1) (by omega)
              · exact hqd i (by omega)
          _ = edist (f ((q (i + 1) : s) : ι)) (f ((q i : s) : ι)) + 2 * ε := by ring
    _ = ∑ i ∈ Finset.range n, edist (f ((q (i + 1) : s) : ι)) (f ((q i : s) : ι)) +
        n * (2 * ε) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- the total error `n * (2 * ε)` is at most `2 * (n + 1) * ε ≤ ζ`
    _ ≤ eVariationOn f ↑t + ↑ζ := by
        refine add_le_add (eVariationOn.sum_le_of_monotoneOn_Iic hqmono hqt) ?_
        calc (n : ℝ≥0∞) * (2 * ε) ≤ ((n : ℝ≥0∞) + 1) * (2 * ε) := by
              gcongr
              exact le_add_of_nonneg_right zero_le_one
          _ = 2 * ((n : ℝ≥0∞) + 1) * (↑ζ / (2 * ((n : ℝ≥0∞) + 1))) := by rw [hεdef]; ring
          _ ≤ ↑ζ := ENNReal.mul_div_le

variable [TopologicalSpace ι]

section Separable

/-- The variation of a function that is continuous within `s` at every point of `s` can be
computed using only points of a dense subset `t` of `s`.

Unlike the one-sided `eVariationOn_eq_comp_val_of_dense_Ioi` and `..._Iio`, no assumption on the
isolated points of `s` is needed: a point isolated in the subspace `↥s` is a singleton open set,
so density alone already puts it in `t`. -/
theorem eVariationOn_eq_comp_val_of_dense [OrderTopology ι] {s : Set ι} {t : Set s}
    (ht : Dense t) {f : ι → E} (hf : ∀ x ∈ s, ContinuousWithinAt f s x) :
    eVariationOn f s = eVariationOn f t := by
  refine le_antisymm ?_ (eVariationOn.mono f (Subtype.coe_image_subset s t))
  rw [eVariationOn.eVariationOn_eq_strictMonoOn]
  refine (iSup_le fun ⟨n, u, hum, hus⟩ ↦ (ENNReal.le_of_forall_pos_le_add fun ε hε het ↦ ?_))
  have hgc : Continuous fun x : s ↦ f x := continuousOn_iff_continuous_restrict.1 hf
  set δ : ℝ≥0∞ := ε / (2 * (n + 1))
  have hδ0 : 0 < δ := ENNReal.div_pos (ENNReal.coe_ne_zero.2 hε.ne') (by finiteness)
  have hball : ∀ y : s, IsOpen {z : s | edist (f (z : ι)) (f (y : ι)) < δ} := fun y ↦
    isOpen_Iio.preimage (hgc.edist continuous_const)
  have hballmem : ∀ y : s, {z : s | edist (f (z : ι)) (f (y : ι)) < δ} ∈ 𝓝 y := fun y ↦
    (hball y).mem_nhds (by simpa [edist_self] using hδ0)
  -- a point of `t` approximating `y` from the left, inside a prescribed open set `U ∋ y`
  have choiceL : ∀ y : s, (𝓝[<] y).NeBot → ∀ U : Set s, IsOpen U → y ∈ U →
      ∃ w : s, w ∈ t ∧ w ∈ U ∧ w < y ∧ edist (f (w : ι)) (f (y : ι)) ≤ δ := by
    intro y hy U hU hyU
    have hmem : U ∩ {z : s | edist (f (z : ι)) (f (y : ι)) < δ} ∩ Iio y ∈ 𝓝[<] y :=
      inter_mem (inter_mem (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hyU))
        (mem_nhdsWithin_of_mem_nhds (hballmem y))) self_mem_nhdsWithin
    obtain ⟨w, hwt, hw⟩ := ht.exists_mem_open ((hU.inter (hball y)).inter isOpen_Iio)
      (Filter.nonempty_of_mem hmem)
    exact ⟨w, hwt, hw.1.1, hw.2, hw.1.2.le⟩
  -- a point of `t` approximating `y` from the right, inside a prescribed open set `U ∋ y`
  have choiceR : ∀ y : s, (𝓝[>] y).NeBot → ∀ U : Set s, IsOpen U → y ∈ U →
      ∃ w : s, w ∈ t ∧ w ∈ U ∧ y < w ∧ edist (f (w : ι)) (f (y : ι)) ≤ δ := by
    intro y hy U hU hyU
    have hmem : U ∩ {z : s | edist (f (z : ι)) (f (y : ι)) < δ} ∩ Ioi y ∈ 𝓝[>] y :=
      inter_mem (inter_mem (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hyU))
        (mem_nhdsWithin_of_mem_nhds (hballmem y))) self_mem_nhdsWithin
    obtain ⟨w, hwt, hw⟩ := ht.exists_mem_open ((hU.inter (hball y)).inter isOpen_Ioi)
      (Filter.nonempty_of_mem hmem)
    exact ⟨w, hwt, hw.1.1, hw.2, hw.1.2.le⟩
  -- a point outside `t` is not isolated, since `{x}` would then be open and `t` is dense; hence
  -- it is approachable from the left or from the right
  have hnr : ∀ x : s, x ∉ t → ¬ (𝓝[<] x).NeBot → (𝓝[>] x).NeBot := fun x hxt hxl ↦
    ⟨fun hbot ↦ hxt (ht.mem_of_isOpen_singleton ((isOpen_singleton_iff_punctured_nhds x).2
      (by rw [← nhdsLT_sup_nhdsGT, not_neBot.1 hxl, hbot, sup_bot_eq])))⟩
  -- the clamped partition, lifted to the subspace `↥s`
  set uc : ℕ → ι := fun i ↦ u (min i n) with hucdef
  have hucs : ∀ i, uc i ∈ s := fun i ↦ hus _ (min_le_right i n)
  set v : ℕ → s := fun i ↦ ⟨uc i, hucs i⟩ with hvdef
  have hv_min : ∀ i, v (min i n) = v i := fun i ↦ by
    simp only [hvdef, hucdef, min_assoc, min_self]
  have hvlt : ∀ i j, min i n < min j n → v i < v j := fun i j h ↦
    hum (by simp) (by simp) h
  have hvmono : Monotone v := fun i j hij ↦
    hum.monotoneOn (by simp) (by simp) (min_le_min hij le_rfl)
  -- first pass: a left approximant for every point that lies in `t` or is left-approachable,
  -- chosen above the previous value; the remaining points keep their own value
  have hex1 : ∀ m : ℕ, ∃ w : s, m ≤ n → w ≤ v m ∧ (∀ k < m, v k < w) ∧
      ((v m ∈ t ∨ (𝓝[<] (v m)).NeBot) → w ∈ t ∧ edist (f (w : ι)) (f ((v m : s) : ι)) ≤ δ) := by
    intro m
    by_cases hm : m ≤ n
    swap
    · exact ⟨v 0, fun h ↦ absurd h hm⟩
    have hklt : ∀ k < m, v k < v m := fun k hk ↦ hvlt k m (by omega)
    by_cases hP : v m ∈ t ∨ (𝓝[<] (v m)).NeBot
    swap
    · exact ⟨v m, fun _ ↦ ⟨le_rfl, hklt, fun h ↦ absurd h hP⟩⟩
    by_cases hmt : v m ∈ t
    · exact ⟨v m, fun _ ↦ ⟨le_rfl, hklt, fun _ ↦ ⟨hmt, by simp⟩⟩⟩
    have hL : (𝓝[<] (v m)).NeBot := hP.resolve_left hmt
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · obtain ⟨w, hwt, -, hwlt, hwd⟩ := choiceL (v 0) hL univ isOpen_univ (mem_univ _)
      exact ⟨w, fun _ ↦ ⟨hwlt.le, fun k hk ↦ absurd hk (by omega), fun _ ↦ ⟨hwt, hwd⟩⟩⟩
    · obtain ⟨w, hwt, hwU, hwlt, hwd⟩ :=
        choiceL (v m) hL (Ioi (v (m - 1))) isOpen_Ioi (hklt (m - 1) (by omega))
      exact ⟨w, fun _ ↦ ⟨hwlt.le, fun k hk ↦ (hvmono (by omega : k ≤ m - 1)).trans_lt hwU,
        fun _ ↦ ⟨hwt, hwd⟩⟩⟩
  choose A hA using hex1
  -- second pass: the remaining points are right-approachable; approximate them from the right,
  -- below the left approximant of the next partition point
  have hex2 : ∀ m : ℕ, ∃ w : s, m ≤ n → w ∈ t ∧
      edist (f (w : ι)) (f ((v m : s) : ι)) ≤ δ ∧ A m ≤ w ∧ (m < n → w < A (m + 1)) := by
    intro m
    by_cases hm : m ≤ n
    swap
    · exact ⟨v 0, fun h ↦ absurd h hm⟩
    obtain ⟨hAle, -, hAP⟩ := hA m hm
    have hnext : ∀ h : m < n, v m < A (m + 1) := fun h ↦ (hA (m + 1) h).2.1 m m.lt_succ_self
    by_cases hP : v m ∈ t ∨ (𝓝[<] (v m)).NeBot
    · obtain ⟨hAt, hAd⟩ := hAP hP
      exact ⟨A m, fun _ ↦ ⟨hAt, hAd, le_rfl, fun h ↦ hAle.trans_lt (hnext h)⟩⟩
    · obtain ⟨hPt, hPl⟩ := not_or.1 hP
      have hR : (𝓝[>] (v m)).NeBot := hnr (v m) hPt hPl
      rcases eq_or_lt_of_le hm with heq | hmn
      · obtain ⟨w, hwt, -, hwgt, hwd⟩ := choiceR (v m) hR univ isOpen_univ (mem_univ _)
        exact ⟨w, fun _ ↦ ⟨hwt, hwd, hAle.trans hwgt.le, fun h ↦ absurd h (by omega)⟩⟩
      · obtain ⟨w, hwt, hwU, hwgt, hwd⟩ :=
          choiceR (v m) hR (Iio (A (m + 1))) isOpen_Iio (hnext hmn)
        exact ⟨w, fun _ ↦ ⟨hwt, hwd, hAle.trans hwgt.le, fun _ ↦ hwU⟩⟩
  choose D hD using hex2
  set q : ℕ → s := fun i ↦ D (min i n) with hqdef
  have hqp := fun i ↦ hD (min i n) (min_le_right i n)
  have hqt : ∀ i, ((q i : s) : ι) ∈ (↑t : Set ι) := fun i ↦ ⟨q i, (hqp i).1, rfl⟩
  have hqd : ∀ i ≤ n, edist (f ((q i : s) : ι)) (f (u i)) ≤ δ := fun i hi ↦ by
    have h := (hqp i).2.1
    rw [hv_min i] at h
    rwa [show ((v i : s) : ι) = u i from by simp [hvdef, hucdef, min_eq_left hi]] at h
  have hqmono : Monotone fun i ↦ ((q i : s) : ι) := by
    intro i i' hii'
    rcases (min_le_min hii' (le_refl n)).eq_or_lt with heq | hlt
    · simp only [hqdef, heq, le_refl]
    · have h1 : D (min i n) < A (min i n + 1) := (hqp i).2.2.2 (by omega)
      refine Subtype.coe_le_coe.2 (h1.le.trans (le_trans ?_ (hqp i').2.2.1))
      rcases eq_or_lt_of_le (by omega : min i n + 1 ≤ min i' n) with heq' | hlt'
      · exact le_of_eq (by rw [heq'])
      · exact ((hA _ (by omega)).1.trans_lt ((hA _ (min_le_right i' n)).2.1 _ hlt')).le
  exact sum_le_eVariationOn_add (hqmono.monotoneOn _) (fun i _ ↦ hqt i) hqd

/-- The variation of a process whose paths are continuous within `s` at every point of `s`, over
the times in a set `s`, is measurable. -/
theorem measurable_eVariationOn_of_continuousWithinAt [OrderTopology ι]
    [SeparableSpace ι] {m : MeasurableSpace Ω} {s : Set ι} {X : ι → Ω → E}
    (hX : ∀ i ∈ s, StronglyMeasurable[m] (X i))
    (hcont : ∀ ω, ∀ i ∈ s, ContinuousWithinAt (X · ω) s i) :
    Measurable[m] fun ω ↦ eVariationOn (X · ω) s := by
  obtain ⟨t, htc, ht⟩ := exists_countable_dense s
  simp only [fun ω ↦ eVariationOn_eq_comp_val_of_dense ht (hcont ω)]
  exact measurable_eVariationOn_of_countable (htc.image _) fun i hi ↦ hX i
    (Subtype.coe_image_subset s t hi)

/-- For `a ≤ t`, the value at time `t` of the variation process of a strongly adapted process with
continuous paths is `𝓕 t`-measurable. -/
theorem MeasureTheory.StronglyAdapted.measurable_variationProcess_of_continuous [OrderTopology ι]
    [SeparableSpace ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, Continuous (X · ω))
    {a t : ι} (hat : a ≤ t) : Measurable[𝓕 t] (variationProcess X a t) := by
  rw [funext fun ω ↦ variationProcess_eq_toReal_eVariationOn_Icc X hat ω]
  exact Measurable.ennreal_toReal <| measurable_eVariationOn_of_continuousWithinAt
    (fun i hi ↦ (hX i).mono (𝓕.mono hi.2)) fun ω i _ ↦ (hcont ω).continuousWithinAt

end Separable

section SecondCountableTopology

/-- The variation of a function that is right-continuous within `s` at every point of `s` can be
computed using only points of a dense subset `t` of `s`, provided `t` contains every point of `s`
that is isolated on the right. -/
theorem eVariationOn_eq_comp_val_of_dense_Ioi [OrderTopology ι] {s : Set ι} {t : Set s}
    (ht : Dense t) (hts : {x : s | 𝓝[>] x = ⊥} ⊆ t) {f : ι → E}
    (hf : ∀ x ∈ s, ContinuousWithinAt f (s ∩ Ioi x) x) :
    eVariationOn f s = eVariationOn f t := by
  refine le_antisymm ?_ (eVariationOn.mono f (Subtype.coe_image_subset s t))
  rw [eVariationOn.eVariationOn_eq_strictMonoOn]
  refine iSup_le fun ⟨n, u, hu, hus⟩ ↦ ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  set δ : ℝ≥0∞ := ε / (2 * (n + 1))
  have hδ0 : 0 < δ := ENNReal.div_pos (ENNReal.coe_ne_zero.2 hε.ne') (by finiteness)
  -- a point of `t` approximating `x ∈ s` from the right, inside a prescribed open set `U ∋ x`
  have choice : ∀ x ∈ s, ∀ U : Set ι, IsOpen U → x ∈ U →
      ∃ w : s, w ∈ t ∧ (w : ι) ∈ U ∧ x ≤ (w : ι) ∧ edist (f (w : ι)) (f x) ≤ δ := by
    intro x hx U hU hxU
    by_cases hiso : 𝓝[s ∩ Ioi x] x = ⊥
    · exact ⟨⟨x, hx⟩, hts (nhdsGT_subtype_eq_bot_iff.2 hiso), hxU, le_rfl, by simp⟩
    have : (𝓝[s ∩ Ioi x] x).NeBot := ⟨hiso⟩
    have hball : f ⁻¹' Metric.eball (f x) δ ∈ 𝓝[s ∩ Ioi x] x :=
      ContinuousWithinAt.preimage_mem_nhdsWithin (hf x hx)
        (Metric.eball_mem_nhds _ hδ0)
    rw [mem_nhdsWithin] at hball
    obtain ⟨V, hV, hxV, hVsub⟩ := hball
    have hO : IsOpen ((Subtype.val : s → ι) ⁻¹' (V ∩ U ∩ Ioi x)) :=
      ((hV.inter hU).inter isOpen_Ioi).preimage continuous_subtype_val
    have hOne : ((Subtype.val : s → ι) ⁻¹' (V ∩ U ∩ Ioi x)).Nonempty := by
      have hmem : (V ∩ U) ∩ (s ∩ Ioi x) ∈ 𝓝[s ∩ Ioi x] x :=
        inter_mem (mem_nhdsWithin_of_mem_nhds ((hV.inter hU).mem_nhds ⟨hxV, hxU⟩))
          self_mem_nhdsWithin
      obtain ⟨z, hz⟩ := Filter.nonempty_of_mem hmem
      exact ⟨⟨z, hz.2.1⟩, hz.1, hz.2.2⟩
    obtain ⟨w, hwt, hwO⟩ := Dense.exists_mem_open ht hO hOne
    have hwm : (w : ι) ∈ V ∩ U ∩ Ioi x := mem_preimage.1 hwO
    have hwb : edist (f (w : ι)) (f x) < δ :=
      Metric.mem_eball.1 (mem_preimage.1 (hVsub ⟨hwm.1.1, w.2, hwm.2⟩))
    exact ⟨w, hwt, hwm.1.2, (mem_Ioi.1 hwm.2).le, hwb.le⟩
  -- an approximant in `t` for each partition point, chosen below the next partition point
  have hex : ∀ m : ℕ, ∃ w : s, m ≤ n → w ∈ t ∧ u m ≤ (w : ι) ∧
      (m < n → (w : ι) < u (m + 1)) ∧ edist (f (w : ι)) (f (u m)) ≤ δ := by
    intro m
    by_cases hm : m ≤ n
    swap
    · exact ⟨⟨u 0, hus 0 (by simp)⟩, fun hm' ↦ absurd hm' hm⟩
    rcases hm.eq_or_lt with heq | hmn
    · obtain ⟨w, hwt, -, hwge, hwd⟩ := choice (u m) (hus m hm) univ isOpen_univ (mem_univ _)
      exact ⟨w, fun _ ↦ ⟨hwt, hwge, fun hj ↦ absurd hj (by omega), hwd⟩⟩
    · have hnext : u m < u (m + 1) := hu (by simp; omega) (by simp; omega) m.lt_succ_self
      obtain ⟨w, hwt, hwU, hwge, hwd⟩ :=
        choice (u m) (hus m hm) (Iio (u (m + 1))) isOpen_Iio (mem_Iio.2 hnext)
      exact ⟨w, fun _ ↦ ⟨hwt, hwge, fun _ ↦ mem_Iio.1 hwU, hwd⟩⟩
  choose q hq using hex
  refine sum_le_eVariationOn_add ?_ (fun i hi ↦ ⟨q i, (hq i hi).1, rfl⟩)
    (fun i hi ↦ (hq i hi).2.2.2)
  intro i hi i' hi' hii'
  rcases hii'.eq_or_lt with heq | hlt
  · rw [heq]
  · refine ((hq i hi).2.2.1 (by simp at hi'; omega)).le.trans (((hq i' hi').2.1).trans' ?_)
    exact hu.monotoneOn (by simp at hi' ⊢; omega) hi' (by omega)

/-- The variation of a process with right-continuous paths over the times in a set `s` is
measurable. -/
theorem measurable_eVariationOn_of_continuousWithinAt_Ioi [OrderTopology ι]
    [SecondCountableTopology ι] {m : MeasurableSpace Ω} {s : Set ι} {X : ι → Ω → E}
    (hX : ∀ i ∈ s, StronglyMeasurable[m] (X i))
    (hcont : ∀ ω, ∀ i ∈ s, ContinuousWithinAt (X · ω) (s ∩ Ioi i) i) :
    Measurable[m] fun ω ↦ eVariationOn (X · ω) s := by
  obtain ⟨t, ht, htc, hts⟩ : ∃ t : Set s, Dense t ∧ t.Countable ∧ {x : s | 𝓝[>] x = ⊥} ⊆ t := by
    obtain ⟨d, hdc, hdd⟩ := exists_countable_dense s
    have hsub : {x : s | 𝓝[>] x = ⊥} ⊆ Subtype.val ⁻¹' {x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥} :=
      fun x hx ↦ ⟨x.2, nhdsGT_subtype_eq_bot_iff.1 hx⟩
    have hisoc : {x : s | 𝓝[>] x = ⊥}.Countable :=
      ((countable_setOf_isolated_right_within (s := s)).preimage Subtype.val_injective).mono hsub
    exact ⟨d ∪ {x : s | 𝓝[>] x = ⊥}, hdd.mono subset_union_left, hdc.union hisoc,
      subset_union_right⟩
  simp only [fun ω ↦ eVariationOn_eq_comp_val_of_dense_Ioi ht hts (hcont ω)]
  exact measurable_eVariationOn_of_countable (htc.image _) fun i hi ↦ hX i
    (Subtype.coe_image_subset s t hi)

/-- For `a ≤ t`, the value at time `t` of the variation process of a strongly adapted process with
right-continuous paths is `𝓕 t`-measurable. -/
theorem MeasureTheory.StronglyAdapted.measurable_variationProcess_of_continuousWithinAt_Ioi
    [OrderTopology ι] [SecondCountableTopology ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, ∀ i, ContinuousWithinAt (X · ω) (Ioi i) i)
    {a t : ι} (hat : a ≤ t) : Measurable[𝓕 t] (variationProcess X a t) := by
  rw [funext fun ω ↦ variationProcess_eq_toReal_eVariationOn_Icc X hat ω]
  exact Measurable.ennreal_toReal <| measurable_eVariationOn_of_continuousWithinAt_Ioi
    (fun i hi ↦ (hX i).mono (𝓕.mono hi.2)) fun ω i _ ↦ (hcont ω i).mono inter_subset_right

/-- The variation of a function that is left-continuous within `s` at every point of `s` can be
computed using only points of a dense subset `t` of `s`, provided `t` contains every point of `s`
that is isolated on the left. -/
theorem eVariationOn_eq_comp_val_of_dense_Iio [OrderTopology ι] {s : Set ι} {t : Set s}
    (ht : Dense t) (hts : {x : s | 𝓝[<] x = ⊥} ⊆ t) {f : ι → E}
    (hf : ∀ x ∈ s, ContinuousWithinAt f (s ∩ Iio x) x) :
    eVariationOn f s = eVariationOn f ↑t := by
  rw [← eVariationOn.comp_ofDual, ← eVariationOn.comp_ofDual f t,
    eVariationOn_eq_comp_val_of_dense_Ioi (s := OrderDual.ofDual ⁻¹' s)
    (f := f ∘ OrderDual.ofDual) ht hts hf]
  congr

/-- The variation of a process with left-continuous paths over the times in a set `s` is
measurable. -/
theorem measurable_eVariationOn_of_continuousWithinAt_Iio [OrderTopology ι]
    [SecondCountableTopology ι] {m : MeasurableSpace Ω} {s : Set ι} {X : ι → Ω → E}
    (hX : ∀ i ∈ s, StronglyMeasurable[m] (X i))
    (hcont : ∀ ω, ∀ i ∈ s, ContinuousWithinAt (X · ω) (s ∩ Iio i) i) :
    Measurable[m] fun ω ↦ eVariationOn (X · ω) s := by
  have hdual : ∀ ω, eVariationOn (fun i ↦ X (OrderDual.ofDual i) ω) (OrderDual.ofDual ⁻¹' s)
    = eVariationOn (X · ω) s := fun ω ↦ eVariationOn.comp_ofDual (X · ω) s
  simpa [hdual] using measurable_eVariationOn_of_continuousWithinAt_Ioi
    (s := OrderDual.ofDual ⁻¹' s) (X := fun i ↦ X (OrderDual.ofDual i)) hX hcont

/-- For `a ≤ t`, the value at time `t` of the variation process of a strongly adapted process with
left-continuous paths is `𝓕 t`-measurable. -/
theorem MeasureTheory.StronglyAdapted.measurable_variationProcess_of_continuousWithinAt_Iio
    [OrderTopology ι] [SecondCountableTopology ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, ∀ i, ContinuousWithinAt (X · ω) (Iio i) i)
    {a t : ι} (hat : a ≤ t) : Measurable[𝓕 t] (variationProcess X a t) := by
  rw [funext fun ω ↦ variationProcess_eq_toReal_eVariationOn_Icc X hat ω]
  exact Measurable.ennreal_toReal <| measurable_eVariationOn_of_continuousWithinAt_Iio
    (fun i hi ↦ (hX i).mono (𝓕.mono hi.2)) fun ω i _ ↦ (hcont ω i).mono inter_subset_right

end SecondCountableTopology

end Measurability
