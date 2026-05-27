/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import BrownianMotion.StochasticIntegral.SimpleProcess
public import Mathlib.Probability.Process.Stopping

/-!
# Stochastic intervals

This file defines the **stochastic intervals** `[[σ,τ]]`, `[[σ,τ[[`, `]]σ,τ]]`,
`]]σ,τ[[` and the graph `[[σ]]` (blueprint `def:stochasticInterval`), and proves
that `]]σ,τ]]` is an `ElementaryPredictableSet` for bounded stopping times on `ℕ`
(blueprint `lem:elementaryPredictableSet_stochasticInterval`, issue
<https://github.com/RemyDegenne/brownian-motion/issues/440>).

For `σ, τ : Ω → T ∪ {∞}` (modelled as `Ω → WithTop ι`) over a time domain `ι`, a
stochastic interval is the subset of `ι × Ω` cut out by comparing the time
coordinate with `σ` and `τ`. Note these are subsets of `ι × Ω`, *not* of
`WithTop ι × Ω` — the time coordinate is a genuine time.

## Main definitions

* `stochasticIcc`, `stochasticIco`, `stochasticIoc`, `stochasticIoo` — the four
  stochastic intervals `[[σ,τ]]`, `[[σ,τ[[`, `]]σ,τ]]`, `]]σ,τ[[`.
* `stochasticGraph` — the graph `[[σ]] = {(t, ω) | t = σ ω}`.

## Main results

* `stochasticIoc.measurableSet_predictable` — for stopping times `σ, τ` on `ℕ`, the
  interval `]]σ,τ]]` is a predictable set. Via `eq_iUnion` it is a countable union of
  the predictable rectangles `(i, i+1] × {σ ≤ i < τ}`.
* `stochasticIoc.exists_elementaryPredictableSet` — for stopping times `σ, τ` with
  `τ` bounded by `n` on `ℕ`, the interval `]]σ,τ]]` is an `ElementaryPredictableSet`.
  It decomposes as the finite disjoint union `⋃_{i < n} (i, i+1] × {σ ≤ i < τ}`
  of predictable rectangles, which is exactly the data of an
  `ElementaryPredictableSet`. Only `τ` need be bounded (not `σ`).

`lem:predictable_stochasticInterval` is stated in the blueprint for an arbitrary time
domain; it is proved here for `ι = ℕ`. The general (continuous-time) case is separate.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Stochastic intervals (general time domain) -/

section Defs
variable [Preorder ι]

/-- The closed stochastic interval `[[σ, τ]] = {(t, ω) | σ ω ≤ t ≤ τ ω}`. -/
def stochasticIcc (σ τ : Ω → WithTop ι) : Set (ι × Ω) :=
  {p | σ p.2 ≤ (p.1 : WithTop ι) ∧ (p.1 : WithTop ι) ≤ τ p.2}

/-- The right-open stochastic interval `[[σ, τ[[ = {(t, ω) | σ ω ≤ t < τ ω}`. -/
def stochasticIco (σ τ : Ω → WithTop ι) : Set (ι × Ω) :=
  {p | σ p.2 ≤ (p.1 : WithTop ι) ∧ (p.1 : WithTop ι) < τ p.2}

/-- The left-open stochastic interval `]]σ, τ]] = {(t, ω) | σ ω < t ≤ τ ω}`. -/
def stochasticIoc (σ τ : Ω → WithTop ι) : Set (ι × Ω) :=
  {p | σ p.2 < (p.1 : WithTop ι) ∧ (p.1 : WithTop ι) ≤ τ p.2}

/-- The open stochastic interval `]]σ, τ[[ = {(t, ω) | σ ω < t < τ ω}`. -/
def stochasticIoo (σ τ : Ω → WithTop ι) : Set (ι × Ω) :=
  {p | σ p.2 < (p.1 : WithTop ι) ∧ (p.1 : WithTop ι) < τ p.2}

/-- The graph of a stopping time `[[σ]] = {(t, ω) | t = σ ω}`. -/
def stochasticGraph (σ : Ω → WithTop ι) : Set (ι × Ω) :=
  {p | (p.1 : WithTop ι) = σ p.2}

@[simp] lemma mem_stochasticIcc {σ τ : Ω → WithTop ι} {t : ι} {ω : Ω} :
    (t, ω) ∈ stochasticIcc σ τ ↔ σ ω ≤ (t : WithTop ι) ∧ (t : WithTop ι) ≤ τ ω := Iff.rfl

@[simp] lemma mem_stochasticIco {σ τ : Ω → WithTop ι} {t : ι} {ω : Ω} :
    (t, ω) ∈ stochasticIco σ τ ↔ σ ω ≤ (t : WithTop ι) ∧ (t : WithTop ι) < τ ω := Iff.rfl

@[simp] lemma mem_stochasticIoc {σ τ : Ω → WithTop ι} {t : ι} {ω : Ω} :
    (t, ω) ∈ stochasticIoc σ τ ↔ σ ω < (t : WithTop ι) ∧ (t : WithTop ι) ≤ τ ω := Iff.rfl

@[simp] lemma mem_stochasticIoo {σ τ : Ω → WithTop ι} {t : ι} {ω : Ω} :
    (t, ω) ∈ stochasticIoo σ τ ↔ σ ω < (t : WithTop ι) ∧ (t : WithTop ι) < τ ω := Iff.rfl

omit [Preorder ι] in
@[simp] lemma mem_stochasticGraph {σ : Ω → WithTop ι} {t : ι} {ω : Ω} :
    (t, ω) ∈ stochasticGraph σ ↔ (t : WithTop ι) = σ ω := Iff.rfl

end Defs

section
variable [PartialOrder ι]

/-- The graph is the diagonal stochastic interval, `[[σ]] = [[σ, σ]]`. -/
lemma stochasticGraph_eq (σ : Ω → WithTop ι) : stochasticGraph σ = stochasticIcc σ σ := by
  ext ⟨t, ω⟩
  exact ⟨fun h ↦ ⟨h.ge, h.le⟩, fun h ↦ h.2.antisymm h.1⟩

end

/-! ### `]]σ,τ]]` on `ℕ`: an elementary predictable set

The blueprint decomposition `]]σ,τ]] = ⋃ₖ (k-1, k] × {σ ≤ k-1 < τ}`. We index by
the *left* endpoint `i = k - 1`, so the building blocks are
`(i, i+1] × {σ ≤ i < τ}` for `i : ℕ`. -/

namespace stochasticIoc

variable {𝓕 : Filtration ℕ mΩ} {σ τ : Ω → WithTop ℕ}

/-- The slice `{ω | σ ω ≤ i < τ ω}` over the interval `(i, i+1]`. It is
`𝓕 i`-measurable for stopping times `σ, τ`: it is `{σ ≤ i} ∩ {τ ≤ i}ᶜ`. -/
lemma measurableSet_slice (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) (i : ℕ) :
    MeasurableSet[𝓕 i] {ω | σ ω ≤ (i : WithTop ℕ) ∧ (i : WithTop ℕ) < τ ω} := by
  have h2 : {ω | (i : WithTop ℕ) < τ ω} = {ω | τ ω ≤ (i : WithTop ℕ)}ᶜ := by
    ext ω; simp [not_le]
  have : {ω | σ ω ≤ (i : WithTop ℕ) ∧ (i : WithTop ℕ) < τ ω}
      = {ω | σ ω ≤ (i : WithTop ℕ)} ∩ {ω | τ ω ≤ (i : WithTop ℕ)}ᶜ := by
    rw [← h2]; rfl
  rw [this]
  exact (hσ.measurableSet_le i).inter (hτ.measurableSet_le i).compl

/-- `a < t ↔ a ≤ t - 1 ∧ t ≥ 1` in `WithTop ℕ` (the left-endpoint shift). -/
private lemma lt_coe_iff_le_coe_sub_one {a : WithTop ℕ} {t : ℕ} :
    a < (t : WithTop ℕ) ↔ a ≤ ((t - 1 : ℕ) : WithTop ℕ) ∧ 1 ≤ t := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe m => simp; omega

/-- `i < a ↔ i + 1 ≤ a` in `WithTop ℕ` (the right-endpoint shift). -/
private lemma coe_lt_iff_coe_succ_le {a : WithTop ℕ} {i : ℕ} :
    (i : WithTop ℕ) < a ↔ ((i + 1 : ℕ) : WithTop ℕ) ≤ a := by
  rw [Nat.cast_add_one]
  exact (ENat.add_one_le_iff (ENat.coe_ne_top i)).symm

/-- **Blueprint decomposition.** `]]σ,τ]] = ⋃ᵢ (i, i+1] × {σ ≤ i < τ}` as subsets
of `ℕ × Ω` — a purely arithmetic identity on `WithTop ℕ`, valid for any `σ, τ`. -/
lemma eq_iUnion (σ τ : Ω → WithTop ℕ) :
    stochasticIoc σ τ =
      ⋃ i : ℕ, Set.Ioc i (i + 1) ×ˢ {ω | σ ω ≤ (i : WithTop ℕ) ∧ (i : WithTop ℕ) < τ ω} := by
  ext ⟨t, ω⟩
  simp only [mem_stochasticIoc, mem_iUnion, Set.mem_prod, Set.mem_Ioc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hlt, hle⟩
    obtain ⟨hsub, ht1⟩ := lt_coe_iff_le_coe_sub_one.mp hlt
    refine ⟨t - 1, ⟨by omega, by omega⟩, hsub, ?_⟩
    exact lt_of_lt_of_le (by simp; omega) hle
  · rintro ⟨i, ⟨hi_lt, hi_le⟩, hσi, hiτ⟩
    have ht : t = i + 1 := by omega
    subst ht
    exact ⟨lt_of_le_of_lt hσi (Nat.cast_lt.mpr (by omega)),
      (coe_lt_iff_coe_succ_le).mp hiτ⟩

/-- **`]]σ,τ]]` is a predictable set** for `ℕ`-indexed stopping times (blueprint
`lem:predictable_stochasticInterval`, here for `ι = ℕ`). The decomposition `eq_iUnion`
exhibits it as a countable union of the predictable rectangles `(i, i+1] × {σ ≤ i < τ}`;
the general-time statement is a separate argument. -/
theorem measurableSet_predictable (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    MeasurableSet[𝓕.predictable] (stochasticIoc σ τ) := by
  rw [eq_iUnion]
  exact MeasurableSet.iUnion fun i ↦
    measurableSet_predictable_Ioc_prod i (i + 1) (measurableSet_slice hσ hτ i)

/-- For `τ` bounded by `n`, the slice `{σ ≤ i < τ}` is empty once `i ≥ n`
(`i < τ ω ≤ n`), so the decomposition `eq_iUnion` truncates to `i ∈ range n`. -/
private lemma slice_eq_empty_of_bound {n : ℕ} (hτn : ∀ ω, τ ω ≤ (n : WithTop ℕ))
    {i : ℕ} (hi : n ≤ i) : {ω | σ ω ≤ (i : WithTop ℕ) ∧ (i : WithTop ℕ) < τ ω} = ∅ := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _
  exact not_lt.mpr (le_trans (hτn ω) (by exact_mod_cast hi))

/-- **`]]σ,τ]]` is an elementary predictable set** for bounded stopping times on
`ℕ` (blueprint `lem:elementaryPredictableSet_stochasticInterval`). With `τ ≤ n`,
`]]σ,τ]] = ⋃_{i < n} (i, i+1] × {σ ≤ i < τ}` is a finite disjoint union of
predictable rectangles, which is exactly the data of an `ElementaryPredictableSet`. -/
theorem exists_elementaryPredictableSet (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ)
    {n : ℕ} (hτn : ∀ ω, τ ω ≤ (n : WithTop ℕ)) :
    ∃ S : ElementaryPredictableSet 𝓕, (S : Set (ℕ × Ω)) = stochasticIoc σ τ := by
  refine ⟨{
    setBot := ∅
    I := (Finset.range n).image (fun i ↦ (i, i + 1))
    set := fun p ↦ {ω | σ ω ≤ (p.1 : WithTop ℕ) ∧ (p.1 : WithTop ℕ) < τ ω}
    le_of_mem_I := ?_
    measurableSet_setBot := @MeasurableSet.empty _ (𝓕 ⊥)
    measurableSet_set := ?_
    pairwiseDisjoint := ?_ }, ?_⟩
  · intro p hp
    simp only [Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact Nat.le_succ i
  · intro p hp
    simp only [Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact measurableSet_slice hσ hτ i
  · intro p hp q hq hpq
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hp hq
    obtain ⟨i, _, rfl⟩ := hp
    obtain ⟨j, _, rfl⟩ := hq
    have hij : i ≠ j := fun h ↦ hpq (by rw [h])
    apply Set.disjoint_left.mpr
    rintro ⟨t, ω⟩ ht ht'
    simp only [Set.mem_prod, Set.mem_Ioc] at ht ht'
    omega
  · rw [ElementaryPredictableSet.toSet]
    simp only [Set.prod_empty, Set.empty_union]
    rw [Finset.set_biUnion_finset_image, eq_iUnion σ τ]
    ext ⟨t, ω⟩
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_prod, Set.mem_Ioc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, _, ht⟩
      exact ⟨i, ht⟩
    · rintro ⟨i, ht, hσi, hiτ⟩
      refine ⟨i, ?_, ht, hσi, hiτ⟩
      by_contra hin
      simp only [not_lt] at hin
      have := slice_eq_empty_of_bound (σ := σ) hτn hin
      rw [Set.eq_empty_iff_forall_notMem] at this
      exact this ω ⟨hσi, hiτ⟩

end stochasticIoc

end ProbabilityTheory
