/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BrownianMotion.Auxiliary.EVariationOn
public import BrownianMotion.Auxiliary.SeparableSpace
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# The variation process

## Main definitions

* `variationProcess`: the pathwise variation of `X` from a starting time `a`, as a process.

## Main results

* `measurable_eVariationOn_of_countable`: the variation of a family of functions over a countable
  set of points is measurable in the parameter.
* `measurable_eVariationOn_of_continuousWithinAt`, `..._of_continuousWithinAt_Ioi` and
  `..._of_continuousWithinAt_Iio`: the variation of a family of functions over a set `s` is
  measurable in the parameter, assuming continuous, right-continuous and left-continuous functions
  respectively. The first result assumes separability of the domain, the other two require it to be
  second countable.
* `variationProcess_nonneg`: for `a ≤ t` the variation process is nonnegative.
* `monotone_variationProcess`: the variation process of a path of locally bounded variation is
  monotone in time.
* `MeasureTheory.StronglyAdapted.measurable_variationProcess_of_continuous`,
  `..._of_continuousWithinAt_Ioi` and `..._of_continuousWithinAt_Iio`: for `a ≤ t`, the value at
  time `t` of the variation process of a strongly adapted process is `𝓕 t`-measurable, assuming
  continuous, right-continuous and left-continuous paths respectively.

-/

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped Topology

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω}

variable [LinearOrder ι] [PseudoEMetricSpace E]

/-- The variation of a family of functions over a countable set of points is measurable in the
parameter. -/
lemma measurable_eVariationOn_of_countable {s : Set ι}
    (hs : s.Countable) {X : ι → Ω → E} (hX : ∀ i ∈ s, StronglyMeasurable[mΩ] (X i)) :
    Measurable[mΩ] fun ω ↦ eVariationOn (X · ω) s := by
  simp only [eVariationOn_eq_iSup_fin]
  refine Measurable.iSup fun n ↦ ?_
  have : Countable {u : Fin (n + 1) → ι // Monotone u ∧ ∀ i, u i ∈ s} :=
    (countable_pi fun _ ↦ hs).mono fun _ hu ↦ hu.2
  refine Measurable.iSup fun p ↦ Finset.measurable_sum _ fun i _ ↦ ?_
  exact (continuous_edist.comp_stronglyMeasurable
    ((hX _ (p.2.2 i.succ)).prodMk (hX _ (p.2.2 i.castSucc)))).measurable

/-- The variation process of `X` from the starting time `a`. -/
noncomputable def variationProcess (X : ι → Ω → E) (a : ι) : ι → Ω → ℝ :=
  fun t ω ↦ variationOnFromTo (X · ω) univ a t

/-- For `a ≤ t`, the variation process at time `t` is the total variation of the path on `Icc a t`,
converted to a real number. -/
lemma variationProcess_eq_toReal_eVariationOn_Icc (X : ι → Ω → E) {a t : ι} (hat : a ≤ t)
    (ω : Ω) : variationProcess X a t ω = (eVariationOn (X · ω) (Icc a t)).toReal := by
  simp [variationProcess, variationOnFromTo, hat]

/-- For `a ≤ t` the variation process is nonnegative. It can be negative for `t < a`, where it
takes the signed value `-(eVariationOn (X · ω) (Icc t a)).toReal`. -/
lemma variationProcess_nonneg (X : ι → Ω → E) {a t : ι} (hat : a ≤ t) (ω : Ω) :
    0 ≤ variationProcess X a t ω :=
  variationOnFromTo.nonneg_of_le _ _ hat

/-- The variation process of a path of locally bounded variation is monotone in time. Monotonicity
holds on all of `ι`, not just above the starting time `a`, since the variation is signed. -/
lemma monotone_variationProcess {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) univ) (a : ι) :
    Monotone fun t ↦ variationProcess X a t ω :=
  fun _ _ hst ↦ variationOnFromTo.monotoneOn hX (mem_univ a) (mem_univ _) (mem_univ _) hst

section Measurability

variable [TopologicalSpace ι]

section Separable

/-- The variation of a family of functions that are continuous within `s` at every point of `s`,
over the points of a set `s`, is measurable in the parameter. -/
lemma measurable_eVariationOn_of_continuousWithinAt [OrderTopology ι]
    [SeparableSpace ι] {s : Set ι} {X : ι → Ω → E}
    (hX : ∀ i ∈ s, StronglyMeasurable[mΩ] (X i)) (hcont : ∀ ω, ContinuousOn (X · ω) s) :
    Measurable[mΩ] fun ω ↦ eVariationOn (X · ω) s := by
  obtain ⟨t, htc, ht⟩ := exists_countable_dense s
  simp only [fun ω ↦ eVariationOn_eq_comp_val_of_dense ht (hcont ω)]
  exact measurable_eVariationOn_of_countable (htc.image _) fun i hi ↦ hX i
    (Subtype.coe_image_subset s t hi)

/-- For `a ≤ t`, the value at time `t` of the variation process of a strongly adapted process with
continuous paths is `𝓕 t`-measurable. -/
lemma MeasureTheory.StronglyAdapted.measurable_variationProcess_of_continuous [OrderTopology ι]
    [SeparableSpace ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) {a t : ι} (hcont : ∀ ω, ContinuousOn (X · ω) (Ici a))
    (hat : a ≤ t) :
    Measurable[𝓕 t] (variationProcess X a t) := by
  rw [funext fun ω ↦ variationProcess_eq_toReal_eVariationOn_Icc X hat ω]
  exact Measurable.ennreal_toReal <| measurable_eVariationOn_of_continuousWithinAt
    (fun i hi ↦ (hX i).mono (𝓕.mono hi.2)) fun ω ↦ (hcont ω).mono Icc_subset_Ici_self

/-- If the index set has a bottom element, then the variation process of a strongly adapted process
with continuous paths is adapted. -/
lemma MeasureTheory.StronglyAdapted.adapted_variationProcess_of_continuous [OrderTopology ι]
    [OrderBot ι] [SeparableSpace ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, Continuous (X · ω)) :
    Adapted 𝓕 (variationProcess X ⊥) :=
  fun _ => hX.measurable_variationProcess_of_continuous (by simpa) bot_le

end Separable

section SecondCountableTopology

/-- The variation of a family of right-continuous functions over the points of a set `s` is
measurable in the parameter. -/
lemma measurable_eVariationOn_of_continuousWithinAt_Ioi [OrderTopology ι]
    [SecondCountableTopology ι] {s : Set ι} {X : ι → Ω → E}
    (hX : ∀ i ∈ s, StronglyMeasurable[mΩ] (X i))
    (hcont : ∀ ω, ∀ i ∈ s, ContinuousWithinAt (X · ω) (s ∩ Ioi i) i) :
    Measurable[mΩ] fun ω ↦ eVariationOn (X · ω) s := by
  obtain ⟨t, ht, htc, hts⟩ : ∃ t : Set s, Dense t ∧ t.Countable ∧ {x : s | 𝓝[>] x = ⊥} ⊆ t := by
    obtain ⟨d, hdc, hdd⟩ := exists_countable_dense s
    refine ⟨d ∪ {x : s | 𝓝[>] x = ⊥}, hdd.mono subset_union_left, hdc.union ?_, subset_union_right⟩
    have hsub : {x : s | 𝓝[>] x = ⊥} ⊆ Subtype.val ⁻¹' {x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥} :=
      fun x hx ↦ ⟨x.2, (nhdsGT_subtype_eq_bot_iff x.2).1 hx⟩
    exact ((countable_setOfPred_isolated_right_within).preimage Subtype.val_injective).mono hsub
  simp only [fun ω ↦ eVariationOn_eq_comp_val_of_dense_Ioi ht hts (hcont ω)]
  exact measurable_eVariationOn_of_countable (htc.image _) fun i hi ↦ hX i
    (Subtype.coe_image_subset s t hi)

/-- The variation of a family of left-continuous functions over the points of a set `s` is
measurable in the parameter. -/
lemma measurable_eVariationOn_of_continuousWithinAt_Iio [OrderTopology ι]
    [SecondCountableTopology ι] {s : Set ι} {X : ι → Ω → E}
    (hX : ∀ i ∈ s, StronglyMeasurable[mΩ] (X i))
    (hcont : ∀ ω, ∀ i ∈ s, ContinuousWithinAt (X · ω) (s ∩ Iio i) i) :
    Measurable[mΩ] fun ω ↦ eVariationOn (X · ω) s := by
  have hdual : ∀ ω, eVariationOn (fun i ↦ X (OrderDual.ofDual i) ω) (OrderDual.ofDual ⁻¹' s)
    = eVariationOn (X · ω) s := fun ω ↦ eVariationOn.comp_ofDual (X · ω) s
  simpa [hdual] using measurable_eVariationOn_of_continuousWithinAt_Ioi
    (s := OrderDual.ofDual ⁻¹' s) (X := fun i ↦ X (OrderDual.ofDual i)) hX hcont

/-- For `a ≤ t`, the value at time `t` of the variation process of a strongly adapted process with
right-continuous paths is `𝓕 t`-measurable. -/
lemma MeasureTheory.StronglyAdapted.measurable_variationProcess_of_continuousWithinAt_Ioi
    [OrderTopology ι] [SecondCountableTopology ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, ∀ i, ContinuousWithinAt (X · ω) (Ioi i) i)
    {a t : ι} (hat : a ≤ t) :
    Measurable[𝓕 t] (variationProcess X a t) := by
  rw [funext fun ω ↦ variationProcess_eq_toReal_eVariationOn_Icc X hat ω]
  exact Measurable.ennreal_toReal <| measurable_eVariationOn_of_continuousWithinAt_Ioi
    (fun i hi ↦ (hX i).mono (𝓕.mono hi.2)) fun ω i _ ↦ (hcont ω i).mono inter_subset_right

/-- If the index set has a bottom element, then the variation process of a strongly adapted process
with right-continuous paths is adapted. -/
lemma MeasureTheory.StronglyAdapted.adapted_variationProcess_of_continuousWithinAt_Ioi
    [OrderTopology ι] [OrderBot ι] [SecondCountableTopology ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, ∀ i, ContinuousWithinAt (X · ω) (Ioi i) i) :
    Adapted 𝓕 (variationProcess X ⊥) :=
  fun _ => hX.measurable_variationProcess_of_continuousWithinAt_Ioi hcont bot_le

/-- For `a ≤ t`, the value at time `t` of the variation process of a strongly adapted process with
left-continuous paths is `𝓕 t`-measurable. -/
lemma MeasureTheory.StronglyAdapted.measurable_variationProcess_of_continuousWithinAt_Iio
    [OrderTopology ι] [SecondCountableTopology ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, ∀ i, ContinuousWithinAt (X · ω) (Iio i) i)
    {a t : ι} (hat : a ≤ t) :
    Measurable[𝓕 t] (variationProcess X a t) := by
  rw [funext fun ω ↦ variationProcess_eq_toReal_eVariationOn_Icc X hat ω]
  exact Measurable.ennreal_toReal <| measurable_eVariationOn_of_continuousWithinAt_Iio
    (fun i hi ↦ (hX i).mono (𝓕.mono hi.2)) fun ω i _ ↦ (hcont ω i).mono inter_subset_right

/-- If the index set has a bottom element, then the variation process of a strongly adapted process
with right-continuous paths is adapted. -/
lemma MeasureTheory.StronglyAdapted.adapted_variationProcess_of_continuousWithinAt_Iio
    [OrderTopology ι] [OrderBot ι] [SecondCountableTopology ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, ∀ i, ContinuousWithinAt (X · ω) (Iio i) i) :
    Adapted 𝓕 (variationProcess X ⊥) :=
  fun _ => hX.measurable_variationProcess_of_continuousWithinAt_Iio hcont bot_le

end SecondCountableTopology

end Measurability
