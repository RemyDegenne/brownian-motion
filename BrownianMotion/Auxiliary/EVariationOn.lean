/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Variation of a function over a countable or dense set of points

The variation of a function over a set is an uncountable supremum, so it is not measurable in a
parameter for free. This file provides tools to compute it over a countable set of points instead.
Measurability of the variation of a family of functions is deduced from these tools in the file
`BrownianMotion.StochasticIntegral.VariationProcess`.

## Main results

* `eVariationOn_eq_iSup_fin`: the variation over `s` as a supremum over monotone tuples with values
  in `s`.

Which dense sets suffice to compute the variation depends on the regularity of the function, and
this file provides two independent sets of assumptions:

1. the first assumes **continuity** of the function together with **separability** of the domain —
  `eVariationOn_eq_comp_val_of_dense`;
2. the second assumes only **right-continuity** of the function, but requires the domain to be
  **second countable** — `eVariationOn_eq_comp_val_of_dense_Ioi`, together with the left-continuous
  counterpart `eVariationOn_eq_comp_val_of_dense_Iio`.

-/

@[expose] public section

open Filter Set TopologicalSpace
open scoped ENNReal Topology

variable {ι Ω E : Type*}

variable [LinearOrder ι] [PseudoEMetricSpace E]

/-- The variation over `s`, reindexed as a supremum over monotone tuples `Fin (n + 1) → ι` with
values in `s`. -/
lemma eVariationOn_eq_iSup_fin {s : Set ι} (X : ι → E) :
    eVariationOn X s = ⨆ (n : ℕ) (p : {u : Fin (n + 1) → ι // Monotone u ∧ ∀ i, u i ∈ s}),
      ∑ i : Fin n, edist (X (p.1 i.succ)) (X (p.1 i.castSucc)) := by
  refine le_antisymm (iSup_le fun ⟨n, u, hu, hus⟩ ↦ ?_)
    (iSup_le fun n ↦ iSup_le fun ⟨p, hp, hps⟩ ↦ ?_)
  · let κ := fun n ↦ {u : Fin (n + 1) → ι // Monotone u ∧ ∀ i, u i ∈ s}
    let p : κ n := ⟨fun i : Fin (n + 1) ↦ u i, hu.comp Fin.val_strictMono.monotone, fun i ↦ hus i⟩
    have : ∑ i ∈ Finset.range n, edist (X (u (i + 1))) (X (u i)) =
      ∑ i : Fin n, edist (X (p.1 i.succ)) (X (p.1 i.castSucc)) := by simp [Finset.sum_range, p]
    simpa [this] using le_iSup₂ (α := ℝ≥0∞) n p
  · let v : ℕ → ι := fun k ↦ p ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩
    have : ∑ i : Fin n, edist (X (p i.succ)) (X (p i.castSucc)) =
      ∑ i ∈ Finset.range n, edist (X (v (i + 1))) (X (v i)) := by
      simp only [Finset.sum_range, Order.add_one_le_iff, Fin.is_lt, inf_of_le_left, Fin.is_le', v]
      congr
    rw [this]
    exact eVariationOn.sum_le (fun _ _ _ ↦ hp (by aesop)) fun i ↦ hps _

variable [TopologicalSpace ι]

section Separable

/-- The variation of a function that is continuous within `s` at every point of `s` can be
computed using only points of a dense subset `t` of `s`. -/
lemma eVariationOn_eq_comp_val_of_dense [OrderTopology ι] {s : Set ι} {t : Set s}
    (ht : Dense t) {f : ι → E} (hf : ContinuousOn f s) :
    eVariationOn f s = eVariationOn f t := by
  refine le_antisymm ?_ (eVariationOn.mono f (Subtype.coe_image_subset s t))
  simp only [eVariationOn.eVariationOn_eq_strictMonoOn, iSup_le_iff, Sigma.forall, Subtype.forall,
    mem_Iic, and_imp]
  refine fun n u hsu hus ↦ ?_
  -- The main idea of the proof is to express this finite sum as the limit along a product filter.
  let F := pi (fun i ↦ 𝓝[t] (u (min i n)))
  let g : (ℕ → ι) → ℝ≥0∞ := (fun a ↦ ∑ i ∈ Finset.range n, edist (f (a (i + 1))) (f (a i)))
  have heval ⦃i⦄ (hi : i ≤ n) : Tendsto (fun a : ℕ → ι ↦ a i) F (𝓝[t] (u i)) := by
    nth_rw 2 [← min_eq_left hi]
    exact tendsto_eval_pi _ i
  have htend : Tendsto g F (𝓝 (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))) := by
    suffices ∀ i ≤ n, Tendsto (fun a : ℕ → ι ↦ f (a i)) F (𝓝 (f (u i))) from
      tendsto_finsetSum _ fun i hi ↦ (this (i + 1) (Finset.mem_range.1 hi)).edist
        (this i (Finset.mem_range_le hi))
    refine fun i hi ↦ Tendsto.comp ?_ (heval hi)
    exact (hf (u i) (hus _ hi)).mono (Subtype.coe_image_subset s t)
  have (i : ℕ) : (𝓝[t] (u (min i n))).NeBot := by
    simpa [← mem_closure_iff_nhdsWithin_neBot, ← closure_image_closure continuous_subtype_val,
      ht.closure_eq] using subset_closure <| hus _ (min_le_right i n)
  refine le_of_tendsto htend ?_
  -- Eventually the approximants lie in `t` and stay strictly increasing along the partition.
  have hlt : ∀ᶠ c in F, StrictMonoOn c (Iic n) := by
    unfold StrictMonoOn
    refine (eventually_all_finite (finite_Iic n)).2 fun _ hi ↦
      (eventually_all_finite (finite_Iic n)).2 fun _ hj ↦ eventually_all.2 fun hij ↦ ?_
    refine Tendsto.eventually_lt ?_ ?_ (hsu hi hj hij)
    <;> exact tendsto_nhds_of_tendsto_nhdsWithin (heval (by assumption))
  have hmem : ∀ᶠ c in F, ∀ i ∈ Iic n, c i ∈ (t : Set ι) := (eventually_all_finite (finite_Iic n)).2
    fun i hi ↦ (tendsto_eval_pi _ i).eventually eventually_mem_nhdsWithin
  filter_upwards [hlt, hmem] with c hclt hcmem
  exact le_iSup_of_le ⟨n, c, hclt, hcmem⟩ le_rfl

end Separable

section SecondCountableTopology

/-- A point of a subset `s` is isolated on the right in the subspace `↥s` exactly when it is
isolated on the right within `s`. -/
lemma nhdsGT_subtype_eq_bot_iff {s : Set ι} {x : ι} (hx : x ∈ s) :
    𝓝[>] (⟨x, hx⟩ : s) = ⊥ ↔ 𝓝[s ∩ Ioi x] x = ⊥ := by
  have : ((↑) : s → ι) ⁻¹' Ioi x = Ioi ⟨x, hx⟩ := rfl
  rw [← this, nhdsWithin_subtype_eq_bot_iff, nhdsWithin, inf_assoc, inf_principal, inter_comm,
    ← nhdsWithin]

/-- The variation of a function that is right-continuous within `s` at every point of `s` can be
computed using only points of a dense subset `t` of `s`, provided `t` contains every point of `s`
that is isolated on the right. -/
lemma eVariationOn_eq_comp_val_of_dense_Ioi [OrderTopology ι] {s : Set ι} {t : Set s}
    (ht : Dense t) (hts : {x : s | 𝓝[>] x = ⊥} ⊆ t) {f : ι → E}
    (hf : ∀ x ∈ s, ContinuousWithinAt f (s ∩ Ioi x) x) :
    eVariationOn f s = eVariationOn f t := by
  refine le_antisymm ?_ (eVariationOn.mono f (Subtype.coe_image_subset s t))
  simp only [eVariationOn.eVariationOn_eq_strictMonoOn, iSup_le_iff, Sigma.forall, Subtype.forall,
    mem_Iic, and_imp]
  refine fun n u hsu hus ↦ ?_
  let F := pi (fun i ↦ 𝓝[t ∩ Ici (u (min i n))] (u (min i n)))
  let g : (ℕ → ι) → ℝ≥0∞ := (fun a ↦ ∑ i ∈ Finset.range n, edist (f (a (i + 1))) (f (a i)))
  have heval ⦃i⦄ (hi : i ≤ n) : Tendsto (fun a : ℕ → ι ↦ a i) F (𝓝[t ∩ Ici (u i)] (u i)) := by
    nth_rw 2 3 [← min_eq_left hi]
    exact tendsto_eval_pi _ i
  have htend : Tendsto g F (𝓝 (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))) := by
    suffices ∀ i ≤ n, Tendsto (fun a : ℕ → ι ↦ f (a i)) F (𝓝 (f (u i))) from
      tendsto_finsetSum _ fun i hi ↦ (this (i + 1) (Finset.mem_range.1 hi)).edist
        (this i (Finset.mem_range_le hi))
    refine fun i hi ↦ Tendsto.comp ?_ (heval hi)
    exact (continuousWithinAt_inter_Ioi_iff_Ici.1 (hf (u i) (hus _ hi))).mono
      (inter_subset_inter_left _ (Subtype.coe_image_subset s t))
  have (i : ℕ) : (𝓝[t ∩ Ici (u (min i n))] (u (min i n))).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    by_cases! hb : 𝓝[>] (⟨u (min i n), hus _ (min_le_right i n)⟩ : s) = ⊥
    · -- If `x` is isolated on the right within `s`, then `x ∈ t` by assumption, so `x ∈ t ∩ Ici x`.
      exact subset_closure ⟨mem_image_of_mem _ (hts hb), le_rfl⟩
    · -- Otherwise `𝓝[>] x ≠ ⊥`, so density of `t` gives points of `t` just to the right of `x`.
      refine mem_closure_iff.2 fun U hU hxU ↦ ?_
      have : (𝓝[s ∩ Ioi (u (min i n))] (u (min i n))).NeBot :=
        ⟨(nhdsGT_subtype_eq_bot_iff (hus _ (min_le_right i n))).not.1 hb.ne'⟩
      obtain ⟨z, hzU, hzs, hzx⟩ : (U ∩ (s ∩ Ioi (u (min i n)))).Nonempty :=
        nonempty_of_mem (inter_mem (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU))
          self_mem_nhdsWithin)
      obtain ⟨w, hwt, hwU, hwx⟩ := ht.exists_mem_open
        ((hU.inter isOpen_Ioi).preimage continuous_subtype_val) ⟨⟨z, hzs⟩, hzU, hzx⟩
      exact ⟨w, hwU, mem_image_of_mem _ hwt, hwx.le⟩
  refine le_of_tendsto htend ?_
  have hlt : ∀ᶠ c in F, StrictMonoOn c (Iic n) := by
    unfold StrictMonoOn
    refine (eventually_all_finite (finite_Iic n)).2 fun _ hi ↦
      (eventually_all_finite (finite_Iic n)).2 fun _ hj ↦ eventually_all.2 fun hij ↦ ?_
    refine Tendsto.eventually_lt ?_ ?_ (hsu hi hj hij)
    <;> exact tendsto_nhds_of_tendsto_nhdsWithin (heval (by assumption))
  have hmem : ∀ᶠ c in F, ∀ i ∈ Iic n, c i ∈ (t : Set ι) := (eventually_all_finite (finite_Iic n)).2
    fun i _ ↦ (tendsto_eval_pi _ i).eventually (eventually_mem_nhdsWithin.mono fun _ h ↦ h.1)
  filter_upwards [hlt, hmem] with c hclt hcmem
  exact le_iSup_of_le ⟨n, c, hclt, hcmem⟩ le_rfl

/-- The variation of a function that is left-continuous within `s` at every point of `s` can be
computed using only points of a dense subset `t` of `s`, provided `t` contains every point of `s`
that is isolated on the left. -/
lemma eVariationOn_eq_comp_val_of_dense_Iio [OrderTopology ι] {s : Set ι} {t : Set s}
    (ht : Dense t) (hts : {x : s | 𝓝[<] x = ⊥} ⊆ t) {f : ι → E}
    (hf : ∀ x ∈ s, ContinuousWithinAt f (s ∩ Iio x) x) :
    eVariationOn f s = eVariationOn f t := by
  rw [← eVariationOn.comp_ofDual, ← eVariationOn.comp_ofDual f t,
    eVariationOn_eq_comp_val_of_dense_Ioi (s := OrderDual.ofDual ⁻¹' s)
    (f := f ∘ OrderDual.ofDual) ht hts hf]
  congr

end SecondCountableTopology
