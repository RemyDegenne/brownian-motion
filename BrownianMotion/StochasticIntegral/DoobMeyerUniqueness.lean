/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.DoleansMeasure
public import BrownianMotion.StochasticIntegral.DoobMeyer

/-! # Uniqueness of the Doob-Meyer decomposition

We prove that if `A` and `B` are predictable processes with monotone right-continuous paths such
that `A - B` is a martingale and `A ⊥ = B ⊥`, then `A` and `B` are indistinguishable. This gives
the uniqueness of the Doob-Meyer decomposition.

The proof does not use predictable stopping times. It uses the bounded function
`g x = x ^ 2 / (1 + x ^ 2)`, which satisfies the exact increment identity
`g y - g x = φ x y * (y - x)` with `φ x y = (x + y) / ((1 + x ^ 2) * (1 + y ^ 2))`.
* Summing the identity along the finite meshes of the time interval for `N = A - B` expresses
  `g (N ⊤) - g (N ⊥)` as the difference of the integrals of a step integrand against the
  Stieltjes measures of the paths of `A` and `B`.
* The step integrands converge pointwise to the bounded predictable process `φ (N₋) N`.
* The Doléans measures `H ↦ E[∫ H dA]` and `H ↦ E[∫ H dB]` agree on bounded predictable
  integrands, because `A - B` is a martingale.
Hence `E[g (N ⊤)] = E[g (N ⊥)] = 0`, so `N ⊤ = 0` almost surely, and `N = 0` by the martingale
property and right-continuity.

## Main statements

* `MeasureTheory.integral_integral_kernelOfRightContAdaptedMono_eq_of_martingale`: if `A - B` is a
  martingale, then `E[∫ H dA] = E[∫ H dB]` for every bounded predictable integrand `H`.
* `MeasureTheory.ae_eq_top_of_martingale_sub`: if `A` and `B` are predictable, integrable, with
  monotone right-continuous paths, equal at `⊥`, and `A - B` is a martingale, then `A ⊤ = B ⊤`
  almost surely.
* `MeasureTheory.indistinguishable_of_martingale_sub`: under the same hypotheses, `A` and `B` are
  indistinguishable.
* `MeasureTheory.doob_meyer_unique`, `MeasureTheory.doob_meyer_unique_of_integrable`: uniqueness
  of the Doob-Meyer decomposition.
-/

@[expose] public section

open MeasureTheory Filter Order ProbabilityTheory
open scoped NNReal ENNReal Topology

/-! ## Pathwise tools -/

namespace DoobMeyerUniqueness

/-! ### The functions `g` and `φ` -/

section Algebra

/-- The bounded function `g x = x² / (1 + x²)`, which vanishes only at `0`. -/
noncomputable def g (x : ℝ) : ℝ := x ^ 2 / (1 + x ^ 2)

/-- The increment ratio of `g`: `g y - g x = φ x y * (y - x)`. -/
noncomputable def φ (x y : ℝ) : ℝ := (x + y) / ((1 + x ^ 2) * (1 + y ^ 2))

lemma one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by positivity

/-- The exact increment identity for `g`. -/
lemma g_sub_g (x y : ℝ) : g y - g x = φ x y * (y - x) := by
  have hx := (one_add_sq_pos x).ne'
  have hy := (one_add_sq_pos y).ne'
  unfold g φ
  field_simp
  ring

/-- The increment ratio `φ` is bounded by `1`. -/
lemma abs_φ_le_one (x y : ℝ) : |φ x y| ≤ 1 := by
  have hpos : 0 < (1 + x ^ 2) * (1 + y ^ 2) := by positivity
  rw [φ, abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
  constructor
  · nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (x * y)]
  · nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (x * y)]

/-- The increment ratio `φ` is jointly continuous. -/
lemma continuous_uncurry_φ : Continuous (Function.uncurry φ) := by
  have : Function.uncurry φ
      = fun p : ℝ × ℝ ↦ (p.1 + p.2) / ((1 + p.1 ^ 2) * (1 + p.2 ^ 2)) := by
    ext ⟨x, y⟩; rfl
  rw [this]
  exact Continuous.div (by fun_prop) (by fun_prop) fun p ↦ by positivity

lemma continuous_φ_left (y : ℝ) : Continuous fun x ↦ φ x y :=
  continuous_uncurry_φ.comp (Continuous.prodMk_left y)

lemma continuous_φ_right (x : ℝ) : Continuous fun y ↦ φ x y :=
  continuous_uncurry_φ.comp (Continuous.prodMk_right x)

lemma measurable_uncurry_φ : Measurable (Function.uncurry φ) := continuous_uncurry_φ.measurable

lemma g_nonneg (x : ℝ) : 0 ≤ g x := by unfold g; positivity

lemma g_le_one (x : ℝ) : g x ≤ 1 := by
  rw [g, div_le_one (one_add_sq_pos x)]
  linarith

lemma g_lt_one (x : ℝ) : g x < 1 := by
  rw [g, div_lt_one (one_add_sq_pos x)]
  linarith

lemma abs_g_le_one (x : ℝ) : |g x| ≤ 1 := by
  rw [abs_of_nonneg (g_nonneg x)]
  exact g_le_one x

@[simp]
lemma g_zero : g 0 = 0 := by simp [g]

/-- The function `g` vanishes only at `0`. -/
@[simp]
lemma g_eq_zero_iff {x : ℝ} : g x = 0 ↔ x = 0 := by
  rw [g, div_eq_zero_iff]
  simp [(one_add_sq_pos x).ne']

lemma g_pos {x : ℝ} (hx : x ≠ 0) : 0 < g x :=
  lt_of_le_of_ne (g_nonneg x) (Ne.symm (g_eq_zero_iff.not.2 hx))

lemma continuous_g : Continuous g := by
  have : g = fun x : ℝ ↦ x ^ 2 / (1 + x ^ 2) := rfl
  rw [this]
  exact Continuous.div (by fun_prop) (by fun_prop) fun x ↦ (one_add_sq_pos x).ne'

lemma measurable_g : Measurable g := continuous_g.measurable

end Algebra

/-! ### Telescoping sums on a finite linear order -/

section Telescoping

/-- Telescoping sum over a finite linear order: the sum of the increments `h u - h (pred u)` is
`h ⊤ - h ⊥`. -/
lemma sum_sub_pred {α M : Type*} [LinearOrder α] [Fintype α] [OrderBot α] [OrderTop α]
    [SuccOrder α] [PredOrder α] [AddCommGroup M] (h : α → M) :
    ∑ u, (h u - h (pred u)) = h ⊤ - h ⊥ := by
  classical
  have h1 : ∑ u, h u = h ⊤ + ∑ u ∈ Finset.univ.erase ⊤, h u :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
  have h2 : ∑ u, h (pred u) = h ⊥ + ∑ u ∈ Finset.univ.erase ⊥, h (pred u) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⊥ : α)), pred_bot]
  have h3 : ∑ u ∈ Finset.univ.erase ⊥, h (pred u) = ∑ u ∈ Finset.univ.erase ⊤, h u := by
    refine Finset.sum_nbij' pred succ ?_ ?_ ?_ ?_ fun _ _ ↦ rfl
    · intro u hu
      have hu' : u ≠ ⊥ := Finset.ne_of_mem_erase hu
      exact Finset.mem_erase.2 ⟨((pred_lt_iff_ne_bot.2 hu').trans_le le_top).ne,
        Finset.mem_univ _⟩
    · intro u hu
      have hu' : u ≠ ⊤ := Finset.ne_of_mem_erase hu
      exact Finset.mem_erase.2 ⟨(bot_le.trans_lt (lt_succ_iff_ne_top.2 hu')).ne',
        Finset.mem_univ _⟩
    · intro u hu
      exact succ_pred_of_not_isMin (by simpa using Finset.ne_of_mem_erase hu)
    · intro u hu
      exact pred_succ_of_not_isMax (by simpa using Finset.ne_of_mem_erase hu)
  rw [Finset.sum_sub_distrib, h1, h2, h3]
  abel

end Telescoping

/-! ### Mesh cells -/

section MeshCell

variable {ι : Type*} [LinearOrder ι] [OrderBot ι] [OrderTop ι] [TopologicalSpace ι]
  [SecondCountableTopology ι] [OrderTopology ι] {n : ℕ} {s : ι}

/-- The telescoping identity for `g ∘ f` along the `n`-th mesh, for an arbitrary function `f`. -/
lemma g_top_sub_g_bot (n : ℕ) (f : ι → ℝ) :
    g (f ⊤) - g (f ⊥)
      = ∑ u : mesh ι n, φ (f (pred u : mesh ι n)) (f u) * (f u - f (pred u : mesh ι n)) := by
  simp_rw [← g_sub_g]
  exact (sum_sub_pred (fun u : mesh ι n ↦ g (f u))).symm

/-- The mesh cells `meshPredIoc n u` are pairwise disjoint. -/
lemma eq_of_mem_meshPredIoc {u v : mesh ι n} (hu : s ∈ meshPredIoc n u)
    (hv : s ∈ meshPredIoc n v) : u = v := by
  by_contra huv
  rcases lt_or_gt_of_ne huv with h | h
  · exact absurd (hu.2.trans (Subtype.coe_le_coe.2 (le_pred_of_lt h))) (not_le.2 hv.1)
  · exact absurd (hv.2.trans (Subtype.coe_le_coe.2 (le_pred_of_lt h))) (not_le.2 hu.1)

/-- The point `⊥` belongs to no mesh cell. -/
lemma bot_notMem_meshPredIoc (u : mesh ι n) : ⊥ ∉ meshPredIoc n u :=
  fun h ↦ absurd h.1 (not_lt.2 bot_le)

/-- Evaluation of a sum of indicators of mesh cells at a point of the cell `meshPredIoc n u`. -/
lemma sum_indicator_meshPredIoc_of_mem {M : Type*} [AddCommMonoid M] (c : mesh ι n → ι → M)
    {u : mesh ι n} (hs : s ∈ meshPredIoc n u) :
    ∑ v : mesh ι n, (meshPredIoc n v).indicator (c v) s = c u s := by
  rw [Finset.sum_eq_single_of_mem u (Finset.mem_univ _), Set.indicator_of_mem hs]
  exact fun v _ hvu ↦ Set.indicator_of_notMem (fun hv ↦ hvu (eq_of_mem_meshPredIoc hv hs)) _

/-- A sum of indicators of mesh cells vanishes at `⊥`. -/
lemma sum_indicator_meshPredIoc_bot {M : Type*} [AddCommMonoid M] (c : mesh ι n → ι → M) :
    ∑ v : mesh ι n, (meshPredIoc n v).indicator (c v) ⊥ = 0 :=
  Finset.sum_eq_zero fun v _ ↦ Set.indicator_of_notMem (bot_notMem_meshPredIoc v) _

/-- The smallest point of the `n`-th mesh which is greater than or equal to `s`. It is the right
endpoint of the mesh cell containing `s` (if `s ≠ ⊥`). -/
noncomputable def meshCell (n : ℕ) (s : ι) : mesh ι n :=
  (Finset.univ.filter fun u : mesh ι n ↦ s ≤ (u : ι)).min' ⟨⊤, by simp⟩

lemma le_meshCell (n : ℕ) (s : ι) : s ≤ (meshCell n s : ι) :=
  (Finset.mem_filter.1 (Finset.min'_mem _ (⟨⊤, by simp⟩ :
    (Finset.univ.filter fun u : mesh ι n ↦ s ≤ (u : ι)).Nonempty))).2

lemma meshCell_le {u : mesh ι n} (hu : s ≤ (u : ι)) : meshCell n s ≤ u :=
  Finset.min'_le _ u (Finset.mem_filter.2 ⟨Finset.mem_univ u, hu⟩)

lemma meshCell_ne_bot (n : ℕ) (hs : s ≠ ⊥) : meshCell n s ≠ ⊥ := by
  intro hc
  have h := le_meshCell n s
  rw [hc, bot_eq_bot] at h
  exact hs (le_bot_iff.1 h)

lemma pred_meshCell_lt (n : ℕ) (hs : s ≠ ⊥) : ((pred (meshCell n s) : mesh ι n) : ι) < s :=
  not_le.1 fun hcon ↦ absurd (meshCell_le hcon)
    (not_le.2 (pred_lt_iff_ne_bot.2 (meshCell_ne_bot n hs)))

/-- Every `s ≠ ⊥` belongs to the mesh cell with right endpoint `meshCell n s`. -/
lemma mem_meshPredIoc_meshCell (n : ℕ) (hs : s ≠ ⊥) : s ∈ meshPredIoc n (meshCell n s) :=
  ⟨pred_meshCell_lt n hs, le_meshCell n s⟩

/-- The mesh cell containing `s` is characterized by its right endpoint `meshCell n s`. -/
lemma meshCell_eq_of_mem {u : mesh ι n} (hs : s ∈ meshPredIoc n u) : meshCell n s = u :=
  eq_of_mem_meshPredIoc
    (mem_meshPredIoc_meshCell n fun h ↦ bot_notMem_meshPredIoc u (h ▸ hs)) hs

end MeshCell

/-! ### Step integrands -/

section StepInt

variable {ι : Type*} [LinearOrder ι] [OrderBot ι] [OrderTop ι] [TopologicalSpace ι]
  [SecondCountableTopology ι] [OrderTopology ι] {n : ℕ} {s : ι} {f : ι → ℝ}

/-- The step integrand associated to `f` along the `n`-th mesh: on the cell `(pred u, u]` it takes
the value `φ (f (pred u)) (f u)`. It vanishes at `⊥`. -/
noncomputable def stepInt (n : ℕ) (f : ι → ℝ) : ι → ℝ :=
  fun s ↦ ∑ u : mesh ι n,
    (meshPredIoc n u).indicator (fun _ ↦ φ (f (pred u : mesh ι n)) (f u)) s

/-- A variant of the step integrand `stepInt`, which is predictable if `f` is: on the cell
`(pred u, u]` it takes at `s` the value `φ (f (pred u)) (f s)`. It vanishes at `⊥`. -/
noncomputable def stepInt' (n : ℕ) (f : ι → ℝ) : ι → ℝ :=
  fun s ↦ ∑ u : mesh ι n,
    (meshPredIoc n u).indicator (fun _ ↦ φ (f (pred u : mesh ι n)) (f s)) s

/-- The step integrand `stepInt'` written with indicators of functions of the time variable, a
form which is convenient for measurability proofs. -/
lemma stepInt'_eq (n : ℕ) (f : ι → ℝ) :
    stepInt' n f = fun s ↦ ∑ u : mesh ι n,
      (meshPredIoc n u).indicator (fun r ↦ φ (f (pred u : mesh ι n)) (f r)) s := by
  ext s
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  by_cases h : s ∈ meshPredIoc n u
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]

/-- Value of `stepInt n f` on the mesh cell `meshPredIoc n u`. -/
lemma stepInt_of_mem {u : mesh ι n} (hs : s ∈ meshPredIoc n u) :
    stepInt n f s = φ (f (pred u : mesh ι n)) (f u) :=
  sum_indicator_meshPredIoc_of_mem (fun u _ ↦ φ (f (pred u : mesh ι n)) (f u)) hs

/-- Value of `stepInt' n f` on the mesh cell `meshPredIoc n u`. -/
lemma stepInt'_of_mem {u : mesh ι n} (hs : s ∈ meshPredIoc n u) :
    stepInt' n f s = φ (f (pred u : mesh ι n)) (f s) :=
  sum_indicator_meshPredIoc_of_mem (fun u _ ↦ φ (f (pred u : mesh ι n)) (f s)) hs

@[simp]
lemma stepInt_bot (n : ℕ) (f : ι → ℝ) : stepInt n f ⊥ = 0 :=
  sum_indicator_meshPredIoc_bot fun u _ ↦ φ (f (pred u : mesh ι n)) (f u)

@[simp]
lemma stepInt'_bot (n : ℕ) (f : ι → ℝ) : stepInt' n f ⊥ = 0 :=
  sum_indicator_meshPredIoc_bot fun u _ ↦ φ (f (pred u : mesh ι n)) (f ⊥)

/-- Value of `stepInt n f` at `s ≠ ⊥`, in terms of the mesh cell containing `s`. -/
lemma stepInt_of_ne_bot (n : ℕ) (f : ι → ℝ) (hs : s ≠ ⊥) :
    stepInt n f s = φ (f (pred (meshCell n s) : mesh ι n)) (f (meshCell n s)) :=
  stepInt_of_mem (mem_meshPredIoc_meshCell n hs)

/-- Value of `stepInt' n f` at `s ≠ ⊥`, in terms of the mesh cell containing `s`. -/
lemma stepInt'_of_ne_bot (n : ℕ) (f : ι → ℝ) (hs : s ≠ ⊥) :
    stepInt' n f s = φ (f (pred (meshCell n s) : mesh ι n)) (f s) :=
  stepInt'_of_mem (mem_meshPredIoc_meshCell n hs)

/-- The step integrand `stepInt n f` is bounded by `1`, for any function `f`. -/
lemma abs_stepInt_le_one (n : ℕ) (f : ι → ℝ) (s : ι) : |stepInt n f s| ≤ 1 := by
  rcases eq_or_ne s ⊥ with rfl | hs
  · simp
  · rw [stepInt_of_ne_bot n f hs]
    exact abs_φ_le_one _ _

/-- The step integrand `stepInt' n f` is bounded by `1`, for any function `f`. -/
lemma abs_stepInt'_le_one (n : ℕ) (f : ι → ℝ) (s : ι) : |stepInt' n f s| ≤ 1 := by
  rcases eq_or_ne s ⊥ with rfl | hs
  · simp
  · rw [stepInt'_of_ne_bot n f hs]
    exact abs_φ_le_one _ _

end StepInt

end DoobMeyerUniqueness

/-! ### Left limits of differences of monotone functions -/

section LeftLim

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] {a b : α → ℝ}

/-- The left limit of a difference of monotone functions is the difference of the left limits.
This holds at every point, also those which are isolated on their left. -/
lemma Monotone.leftLim_sub (ha : Monotone a) (hb : Monotone b) (t : α) :
    Function.leftLim (a - b) t = Function.leftLim a t - Function.leftLim b t := by
  rcases eq_or_neBot (𝓝[<] t) with h | h
  · simp [leftLim_eq_of_eq_bot _ h]
  · exact leftLim_eq_of_tendsto ((ha.tendsto_leftLim t).sub (hb.tendsto_leftLim t))

/-- A difference of monotone functions tends to its `leftLim` on the left, at every point. -/
lemma Monotone.tendsto_leftLim_sub (ha : Monotone a) (hb : Monotone b) (t : α) :
    Tendsto (a - b) (𝓝[<] t) (𝓝 (Function.leftLim (a - b) t)) :=
  tendsto_leftLim_of_tendsto ⟨_, (ha.tendsto_leftLim t).sub (hb.tendsto_leftLim t)⟩

end LeftLim

namespace DoobMeyerUniqueness

/-! ### Convergence of the step integrands -/

section Convergence

variable {ι : Type*} [LinearOrder ι] [OrderBot ι] [OrderTop ι] [TopologicalSpace ι]
  [SecondCountableTopology ι] [OrderTopology ι] [DenselyOrdered ι] {n : ℕ} {s : ι} {f : ι → ℝ}

/-- Between two points `a < b` of a densely ordered space, there is a point which belongs to all
meshes `mesh ι n` of large enough index. -/
lemma exists_forall_mem_mesh_of_lt {a b : ι} (hab : a < b) :
    ∃ d, a < d ∧ d < b ∧ ∃ k, ∀ n, k < n → d ∈ mesh ι n := by
  obtain ⟨c, hc₁, hc₂⟩ := exists_between hab
  obtain ⟨d, hd_mem, hd⟩ := (denseSet_dense ι).exists_mem_open isOpen_Ioo ⟨c, hc₁, hc₂⟩
  obtain ⟨k, hk⟩ := exists_denseEnum_eq ι hd_mem
  exact ⟨d, hd.1, hd.2, k, fun n hn ↦ hk ▸ denseEnum_mem_mesh ι hn⟩

/-- The right endpoints of the mesh cells containing `s` converge to `s` from the right. -/
lemma tendsto_meshCell (s : ι) :
    Tendsto (fun n ↦ ((meshCell n s : mesh ι n) : ι)) atTop (𝓝[≥] s) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun n ↦ ha.trans_le (le_meshCell n s),
    fun b hb ↦ ?_⟩, Eventually.of_forall fun n ↦ le_meshCell n s⟩
  obtain ⟨d, hd₁, hd₂, k, hk⟩ := exists_forall_mem_mesh_of_lt hb
  filter_upwards [eventually_gt_atTop k] with n hn
  have h : meshCell n s ≤ (⟨d, hk n hn⟩ : mesh ι n) := meshCell_le hd₁.le
  exact (Subtype.coe_le_coe.2 h).trans_lt hd₂

/-- The left endpoints of the mesh cells containing `s ≠ ⊥` converge to `s` from the left, while
being strictly less than `s`. -/
lemma tendsto_pred_meshCell (hs : s ≠ ⊥) :
    Tendsto (fun n ↦ ((pred (meshCell n s) : mesh ι n) : ι)) atTop (𝓝[<] s) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_order.2 ⟨fun a ha ↦ ?_,
    fun b hb ↦ Eventually.of_forall fun n ↦ (pred_meshCell_lt n hs).trans hb⟩,
    Eventually.of_forall fun n ↦ pred_meshCell_lt n hs⟩
  obtain ⟨d, hd₁, hd₂, k, hk⟩ := exists_forall_mem_mesh_of_lt ha
  filter_upwards [eventually_gt_atTop k] with n hn
  have h : (⟨d, hk n hn⟩ : mesh ι n) < meshCell n s :=
    Subtype.coe_lt_coe.1 (hd₂.trans_le (le_meshCell n s))
  exact hd₁.trans_le (Subtype.coe_le_coe.2 (le_pred_of_lt h))

/-- Pointwise convergence of the step integrands `stepInt n f` for a right-continuous function
with left limits. -/
lemma tendsto_stepInt (hf_rc : ContinuousWithinAt f (Set.Ioi s) s)
    (hf_ll : Tendsto f (𝓝[<] s) (𝓝 (f.leftLim s))) (hs : s ≠ ⊥) :
    Tendsto (fun n ↦ stepInt n f s) atTop (𝓝 (φ (f.leftLim s) (f s))) := by
  have h1 : Tendsto (fun n ↦ f ((pred (meshCell n s) : mesh ι n) : ι)) atTop
      (𝓝 (f.leftLim s)) := hf_ll.comp (tendsto_pred_meshCell hs)
  have h2 : Tendsto (fun n ↦ f ((meshCell n s : mesh ι n) : ι)) atTop (𝓝 (f s)) :=
    (continuousWithinAt_Ioi_iff_Ici.1 hf_rc).tendsto.comp (tendsto_meshCell s)
  refine ((continuous_uncurry_φ.tendsto (f.leftLim s, f s)).comp (h1.prodMk_nhds h2)).congr
    fun n ↦ ?_
  rw [stepInt_of_ne_bot n f hs]
  rfl

/-- Pointwise convergence of the step integrands `stepInt' n f` for a function with left
limits. -/
lemma tendsto_stepInt' (hf_ll : Tendsto f (𝓝[<] s) (𝓝 (f.leftLim s))) (hs : s ≠ ⊥) :
    Tendsto (fun n ↦ stepInt' n f s) atTop (𝓝 (φ (f.leftLim s) (f s))) := by
  have h1 : Tendsto (fun n ↦ f ((pred (meshCell n s) : mesh ι n) : ι)) atTop
      (𝓝 (f.leftLim s)) := hf_ll.comp (tendsto_pred_meshCell hs)
  refine (((continuous_φ_left (f s)).tendsto (f.leftLim s)).comp h1).congr fun n ↦ ?_
  rw [stepInt'_of_ne_bot n f hs]
  rfl

/-- Almost everywhere convergence of the step integrands `stepInt n f` for a right-continuous
function with left limits, with respect to a measure which does not charge `⊥`. -/
lemma ae_tendsto_stepInt {mι : MeasurableSpace ι} {μ : Measure ι} (hμ : μ {⊥} = 0)
    (hf_rc : ∀ t, ContinuousWithinAt f (Set.Ioi t) t)
    (hf_ll : ∀ t, Tendsto f (𝓝[<] t) (𝓝 (f.leftLim t))) :
    ∀ᵐ s ∂μ, Tendsto (fun n ↦ stepInt n f s) atTop (𝓝 (φ (f.leftLim s) (f s))) := by
  filter_upwards [compl_mem_ae_iff.2 hμ] with s hs
  exact tendsto_stepInt (hf_rc s) (hf_ll s) hs

/-- Almost everywhere convergence of the step integrands `stepInt' n f` for a function with left
limits, with respect to a measure which does not charge `⊥`. -/
lemma ae_tendsto_stepInt' {mι : MeasurableSpace ι} {μ : Measure ι} (hμ : μ {⊥} = 0)
    (hf_ll : ∀ t, Tendsto f (𝓝[<] t) (𝓝 (f.leftLim t))) :
    ∀ᵐ s ∂μ, Tendsto (fun n ↦ stepInt' n f s) atTop (𝓝 (φ (f.leftLim s) (f s))) := by
  filter_upwards [compl_mem_ae_iff.2 hμ] with s hs
  exact tendsto_stepInt' (hf_ll s) hs

end Convergence

/-! ### Measurability and integrals of the step integrands -/

section Integral

variable {ι : Type*} [LinearOrder ι] [OrderBot ι] [OrderTop ι] [TopologicalSpace ι]
  [SecondCountableTopology ι] [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι]
  {n : ℕ} {f : ι → ℝ} {μ : Measure ι}

lemma measurableSet_meshPredIoc (n : ℕ) (u : mesh ι n) : MeasurableSet (meshPredIoc n u) :=
  measurableSet_Ioc

/-- The step integrand `stepInt n f` is measurable, for any function `f`. -/
lemma measurable_stepInt (n : ℕ) (f : ι → ℝ) : Measurable (stepInt n f) :=
  Finset.measurable_sum _ fun u _ ↦ measurable_const.indicator (measurableSet_meshPredIoc n u)

/-- The step integrand `stepInt' n f` is measurable if `f` is measurable. -/
lemma measurable_stepInt' (n : ℕ) (hf : Measurable f) : Measurable (stepInt' n f) := by
  rw [stepInt'_eq]
  exact Finset.measurable_sum _ fun u _ ↦
    ((continuous_φ_right _).measurable.comp hf).indicator (measurableSet_meshPredIoc n u)

lemma integrable_stepInt [IsFiniteMeasure μ] (n : ℕ) (f : ι → ℝ) : Integrable (stepInt n f) μ :=
  Integrable.of_bound (measurable_stepInt n f).aestronglyMeasurable 1
    (ae_of_all _ fun s ↦ by simpa using abs_stepInt_le_one n f s)

lemma integrable_stepInt' [IsFiniteMeasure μ] (n : ℕ) (hf : Measurable f) :
    Integrable (stepInt' n f) μ :=
  Integrable.of_bound (measurable_stepInt' n hf).aestronglyMeasurable 1
    (ae_of_all _ fun s ↦ by simpa using abs_stepInt'_le_one n f s)

/-- Integral of the step integrand with respect to a measure which gives mass `a t - a s` to
the intervals `Ioc s t`: this is a Riemann-Stieltjes sum. -/
lemma integral_stepInt_of_measure_Ioc {a : ι → ℝ} (ha : Monotone a)
    (hμ : ∀ s t, μ (Set.Ioc s t) = ENNReal.ofReal (a t - a s)) (n : ℕ) (f : ι → ℝ) :
    ∫ s, stepInt n f s ∂μ
      = ∑ u : mesh ι n, φ (f (pred u : mesh ι n)) (f u) * (a u - a (pred u : mesh ι n)) := by
  have hμ_cell (u : mesh ι n) :
      μ (meshPredIoc n u) = ENNReal.ofReal (a u - a (pred u : mesh ι n)) := hμ _ _
  simp only [stepInt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [integral_indicator_const _ (measurableSet_meshPredIoc n u), smul_eq_mul, mul_comm,
      Measure.real, hμ_cell, ENNReal.toReal_ofReal]
    exact sub_nonneg.2 (ha (Subtype.coe_le_coe.2 (pred_le u)))
  · refine fun u _ ↦ (integrable_indicator_iff (measurableSet_meshPredIoc n u)).2
      (integrableOn_const ?_)
    rw [hμ_cell]
    exact ENNReal.ofReal_ne_top

/-- If `μ` and `ν` give mass `a t - a s` and `b t - b s` respectively to the intervals `Ioc s t`,
then the integrals of the step integrand of `a - b` against `μ` and `ν` differ by the increment
of `g ∘ (a - b)` between `⊥` and `⊤`. -/
lemma integral_stepInt_sub_of_measure_Ioc {ν : Measure ι} {a b : ι → ℝ} (ha : Monotone a)
    (hb : Monotone b) (hμ : ∀ s t, μ (Set.Ioc s t) = ENNReal.ofReal (a t - a s))
    (hν : ∀ s t, ν (Set.Ioc s t) = ENNReal.ofReal (b t - b s)) (n : ℕ) :
    ∫ s, stepInt n (fun t ↦ a t - b t) s ∂μ - ∫ s, stepInt n (fun t ↦ a t - b t) s ∂ν
      = g (a ⊤ - b ⊤) - g (a ⊥ - b ⊥) := by
  have key := g_top_sub_g_bot n fun t ↦ a t - b t
  beta_reduce at key
  rw [integral_stepInt_of_measure_Ioc ha hμ, integral_stepInt_of_measure_Ioc hb hν,
    ← Finset.sum_sub_distrib, key]
  exact Finset.sum_congr rfl fun u _ ↦ by ring

variable [DenselyOrdered ι] [CompactIccSpace ι]

omit [OrderTop ι] in
/-- The Stieltjes measure of a Stieltjes function on an order with a bottom element does not
charge `⊥`. -/
lemma _root_.StieltjesFunction.measure_singleton_bot (a : StieltjesFunction ι) :
    a.measure {⊥} = 0 := by
  rw [a.measure_singleton, leftLim_eq_of_isBot isBot_bot, sub_self, ENNReal.ofReal_zero]

/-- The Stieltjes measure of a Stieltjes function on a bounded order is finite. -/
instance _root_.StieltjesFunction.isFiniteMeasure_of_boundedOrder (a : StieltjesFunction ι) :
    IsFiniteMeasure a.measure :=
  ⟨by rw [← Set.Icc_bot_top, a.measure_Icc]; exact ENNReal.ofReal_lt_top⟩

/-- Integral of the step integrand with respect to a Stieltjes measure. -/
lemma integral_stepInt_stieltjes (a : StieltjesFunction ι) (n : ℕ) (f : ι → ℝ) :
    ∫ s, stepInt n f s ∂a.measure
      = ∑ u : mesh ι n, φ (f (pred u : mesh ι n)) (f u) * (a u - a (pred u : mesh ι n)) :=
  integral_stepInt_of_measure_Ioc a.mono a.measure_Ioc n f

/-- For two Stieltjes functions `a`, `b`, the integrals of the step integrand of `a - b` against
the Stieltjes measures of `a` and `b` differ by the increment of `g ∘ (a - b)` between `⊥`
and `⊤`. -/
lemma integral_stepInt_stieltjes_sub (a b : StieltjesFunction ι) (n : ℕ) :
    ∫ s, stepInt n (fun t ↦ a t - b t) s ∂a.measure
        - ∫ s, stepInt n (fun t ↦ a t - b t) s ∂b.measure
      = g (a ⊤ - b ⊤) - g (a ⊥ - b ⊥) :=
  integral_stepInt_sub_of_measure_Ioc a.mono b.mono a.measure_Ioc b.measure_Ioc n

end Integral

end DoobMeyerUniqueness

namespace MeasureTheory

end MeasureTheory

variable {ι Ω : Type*} [CompleteLinearOrder ι] [DenselyOrdered ι] [TopologicalSpace ι]
  [OrderTopology ι] [PolishSpace ι] [MeasurableSpace ι] [BorelSpace ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration ι mΩ}
  {A B : ι → Ω → ℝ}

namespace StieltjesFunction

section Integral

variable (hA : Adapted 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω))
  (hA_mono : ∀ ω, Monotone (A · ω)) {H : ι × Ω → ℝ} {C : ℝ}

/-- The integral of a jointly measurable function against the Stieltjes kernel of `A` is a
strongly measurable function of `ω`. -/
lemma stronglyMeasurable_integral_kernelOfRightContAdaptedMono (hH : Measurable H) :
    StronglyMeasurable
      fun ω ↦ ∫ s, H (s, ω) ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) :=
  MeasureTheory.StronglyMeasurable.integral_kernel_prod_left' hH.stronglyMeasurable

/-- The integral of a jointly measurable function against the Stieltjes kernel of `A` is a
measurable function of `ω`. -/
lemma measurable_integral_kernelOfRightContAdaptedMono (hH : Measurable H) :
    Measurable fun ω ↦ ∫ s, H (s, ω) ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) :=
  (stronglyMeasurable_integral_kernelOfRightContAdaptedMono hA hA_rc hA_mono hH).measurable

/-- The integral of a function bounded by `C` against the Stieltjes kernel of `A` is bounded by
`C * (A ⊤ ω - A ⊥ ω)`. -/
lemma abs_integral_kernelOfRightContAdaptedMono_le (hC : ∀ p, |H p| ≤ C) (ω : Ω) :
    |∫ s, H (s, ω) ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω)|
      ≤ C * (A ⊤ ω - A ⊥ ω) := by
  have h := norm_integral_le_of_norm_le_const
    (μ := kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) (f := fun s ↦ H (s, ω)) (C := C)
    (ae_of_all _ fun s ↦ hC (s, ω))
  rw [Real.norm_eq_abs] at h
  refine h.trans_eq ?_
  rw [Measure.real, kernelOfRightContAdaptedMono_univ,
    ENNReal.toReal_ofReal (sub_nonneg.2 (hA_mono ω bot_le))]

omit [IsFiniteMeasure P] in
/-- The integral of a bounded jointly measurable function against the Stieltjes kernel of `A` is
an integrable function of `ω`. -/
lemma integrable_integral_kernelOfRightContAdaptedMono (hH : Measurable H)
    (hC : ∀ p, |H p| ≤ C) (hA_top : Integrable (A ⊤) P) (hA_bot : Integrable (A ⊥) P) :
    Integrable
      (fun ω ↦ ∫ s, H (s, ω) ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω)) P := by
  refine Integrable.mono' ((hA_top.sub hA_bot).const_mul C)
    (stronglyMeasurable_integral_kernelOfRightContAdaptedMono hA hA_rc hA_mono
      hH).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_eq_abs]
  exact abs_integral_kernelOfRightContAdaptedMono_le hA hA_rc hA_mono hC ω

omit [IsFiniteMeasure P] in
/-- Dominated convergence for the Doléans measure: if `Hn n` are jointly measurable, uniformly
bounded, and converge pointwise to `H` away from `{⊥} × Ω`, then the iterated integrals against
the Stieltjes kernel of `A` and `P` converge. -/
lemma tendsto_integral_integral_kernelOfRightContAdaptedMono {Hn : ℕ → ι × Ω → ℝ}
    (hHn : ∀ n, Measurable (Hn n)) (hC : ∀ n p, |Hn n p| ≤ C)
    (h_tendsto : ∀ p : ι × Ω, p.1 ≠ ⊥ → Tendsto (fun n ↦ Hn n p) atTop (𝓝 (H p)))
    (hA_top : Integrable (A ⊤) P) (hA_bot : Integrable (A ⊥) P) :
    Tendsto
      (fun n ↦ ∫ ω, ∫ s, Hn n (s, ω) ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) ∂P)
      atTop (𝓝 (∫ ω, ∫ s, H (s, ω) ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω) ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun ω ↦ C * (A ⊤ ω - A ⊥ ω))
    (fun n ↦ (stronglyMeasurable_integral_kernelOfRightContAdaptedMono hA hA_rc hA_mono
      (hHn n)).aestronglyMeasurable) ((hA_top.sub hA_bot).const_mul C)
    (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_)
  · rw [Real.norm_eq_abs]
    exact abs_integral_kernelOfRightContAdaptedMono_le hA hA_rc hA_mono (hC n) ω
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ C)
    (fun n ↦ ((hHn n).comp measurable_prodMk_right).aestronglyMeasurable) (integrable_const C)
    (fun n ↦ ae_of_all _ fun s ↦ ?_) ?_
  · rw [Real.norm_eq_abs]
    exact hC n (s, ω)
  have h_ne : ∀ᵐ s ∂(kernelOfRightContAdaptedMono hA hA_rc hA_mono ω), s ≠ ⊥ := by
    rw [ae_iff]
    simp
  filter_upwards [h_ne] with s hs using h_tendsto (s, ω) hs

end Integral

end StieltjesFunction

namespace MeasureTheory

open StieltjesFunction

end MeasureTheory

/-! ## Uniqueness of the Doob-Meyer decomposition -/

/-- Two right-continuous functions which agree on a dense set containing `⊤` are equal. The
assumption `⊤ ∈ D` is necessary since right-continuity gives no information at `⊤`. -/
lemma Dense.eq_of_isRightContinuous {α β : Type*} [LinearOrder α] [OrderTop α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [TopologicalSpace β] [T2Space β]
    {f g : α → β} {D : Set α} (hD : Dense D) (htop : ⊤ ∈ D) (h : ∀ d ∈ D, f d = g d)
    (hf : IsRightContinuous f) (hg : IsRightContinuous g) :
    f = g := by
  ext a
  by_cases! ha : a = ⊤
  · rw [ha]
    exact h ⊤ htop
  · have : (comap ((↑) : D → α) (𝓝[>] a)).NeBot := hD.comap_val_nhdsWithin_Ioi_neBot
      (nhdsGT_neBot_of_exists_gt ⟨⊤, ha.lt_top⟩)
    have hf' := (hf a).tendsto.comp (tendsto_comap (f := ((↑) : D → α)))
    have hg' := (hg a).tendsto.comp (tendsto_comap (f := ((↑) : D → α)))
    exact tendsto_nhds_unique hf' (hg'.congr fun d ↦ (h d d.2).symm)

namespace DoobMeyerUniqueness

/-! ### The limit of the step integrands -/

section LimInt

variable {ι : Type*} [LinearOrder ι] [OrderBot ι] {s : ι} {f : ι → ℝ}

/-- The pointwise limit of the step integrands `stepInt n f` and `stepInt' n f`: it takes the value
`φ (f.leftLim s) (f s)` at `s ≠ ⊥`, and vanishes at `⊥`. -/
noncomputable def limInt (f : ι → ℝ) (s : ι) : ℝ :=
  if s = ⊥ then 0 else φ (f.leftLim s) (f s)

@[simp]
lemma limInt_bot (f : ι → ℝ) : limInt f ⊥ = 0 := if_pos rfl

lemma limInt_of_ne_bot (f : ι → ℝ) (hs : s ≠ ⊥) : limInt f s = φ (f.leftLim s) (f s) :=
  if_neg hs

/-- The limit integrand `limInt f` is bounded by `1`, for any function `f`. -/
lemma abs_limInt_le_one (f : ι → ℝ) (s : ι) : |limInt f s| ≤ 1 := by
  rcases eq_or_ne s ⊥ with rfl | hs
  · simp
  · rw [limInt_of_ne_bot f hs]
    exact abs_φ_le_one _ _

variable [OrderTop ι] [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
  [DenselyOrdered ι]

/-- The step integrands `stepInt n f` converge to `limInt f` at every `s ≠ ⊥`, for a
right-continuous function with left limits. -/
lemma tendsto_stepInt_limInt (hf_rc : ContinuousWithinAt f (Set.Ioi s) s)
    (hf_ll : Tendsto f (𝓝[<] s) (𝓝 (f.leftLim s))) (hs : s ≠ ⊥) :
    Tendsto (fun n ↦ stepInt n f s) atTop (𝓝 (limInt f s)) := by
  rw [limInt_of_ne_bot f hs]
  exact tendsto_stepInt hf_rc hf_ll hs

/-- The step integrands `stepInt' n f` converge to `limInt f` everywhere, for a function with
left limits. -/
lemma tendsto_stepInt'_limInt (hf_ll : Tendsto f (𝓝[<] s) (𝓝 (f.leftLim s))) :
    Tendsto (fun n ↦ stepInt' n f s) atTop (𝓝 (limInt f s)) := by
  rcases eq_or_ne s ⊥ with rfl | hs
  · simp
  · rw [limInt_of_ne_bot f hs]
    exact tendsto_stepInt' hf_ll hs

end LimInt

/-! ### Step integrands of the paths of a process -/

section Process

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] [OrderTop ι] [TopologicalSpace ι]
  [SecondCountableTopology ι] [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {N : ι → Ω → ℝ}

/-- The step integrand of the paths of a measurable process is jointly measurable. -/
lemma measurable_stepInt_path (n : ℕ) (hN : ∀ t, Measurable (N t)) :
    Measurable fun p : ι × Ω ↦ stepInt n (N · p.2) p.1 := by
  simp only [stepInt]
  refine Finset.measurable_sum _ fun u _ ↦ ?_
  have h_eq : (fun p : ι × Ω ↦ (meshPredIoc n u).indicator
        (fun _ ↦ φ (N (pred u : mesh ι n) p.2) (N u p.2)) p.1)
      = (meshPredIoc n u ×ˢ Set.univ).indicator
        fun p ↦ φ (N (pred u : mesh ι n) p.2) (N u p.2) := by
    ext p
    by_cases hp : p.1 ∈ meshPredIoc n u
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem
        (show p ∈ meshPredIoc n u ×ˢ Set.univ from ⟨hp, Set.mem_univ _⟩)]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem fun h ↦ hp h.1]
  rw [h_eq]
  exact (measurable_uncurry_φ.comp (((hN _).comp measurable_snd).prodMk
    ((hN _).comp measurable_snd))).indicator ((measurableSet_meshPredIoc n u).prod .univ)

/-- The step integrand `stepInt'` of the paths of a predictable process is predictable. -/
lemma stronglyMeasurable_predictable_stepInt'_path (n : ℕ) (hN : IsStronglyPredictable 𝓕 N) :
    StronglyMeasurable[𝓕.predictable] fun p : ι × Ω ↦ stepInt' n (N · p.2) p.1 := by
  have hN_ad : StronglyAdapted 𝓕 N := hN.stronglyAdapted
  simp only [stepInt']
  refine Finset.stronglyMeasurable_fun_sum _ fun u _ ↦ ?_
  have h_eq : (fun p : ι × Ω ↦ (meshPredIoc n u).indicator
        (fun _ ↦ φ (N (pred u : mesh ι n) p.2) (N p.1 p.2)) p.1)
      = (meshPredIoc n u ×ˢ Set.univ).indicator fun p ↦
        φ ((Set.Ioi ((pred u : mesh ι n) : ι) ×ˢ Set.univ).indicator
          (fun p : ι × Ω ↦ N (pred u : mesh ι n) p.2) p) (N p.1 p.2) := by
    ext p
    by_cases hp : p.1 ∈ meshPredIoc n u
    · have hp' : p ∈ Set.Ioi ((pred u : mesh ι n) : ι) ×ˢ (Set.univ : Set Ω) :=
        ⟨hp.1, Set.mem_univ _⟩
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem
        (show p ∈ meshPredIoc n u ×ˢ Set.univ from ⟨hp, Set.mem_univ _⟩),
        Set.indicator_of_mem hp']
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem fun h ↦ hp h.1]
  rw [h_eq]
  refine StronglyMeasurable.indicator ?_ (measurableSet_predictable_Ioc_prod _ _ .univ)
  exact continuous_uncurry_φ.comp_stronglyMeasurable
    ((stronglyMeasurable_predictable_indicator_Ioi (hN_ad _)).prodMk hN)

/-- The limit integrand of the paths of a predictable process with left limits is predictable. -/
lemma stronglyMeasurable_predictable_limInt_path [DenselyOrdered ι]
    (hN : IsStronglyPredictable 𝓕 N)
    (hN_ll : ∀ ω s, Tendsto (N · ω) (𝓝[<] s) (𝓝 ((N · ω).leftLim s))) :
    StronglyMeasurable[𝓕.predictable] fun p : ι × Ω ↦ limInt (N · p.2) p.1 :=
  stronglyMeasurable_of_tendsto atTop
    (fun n ↦ stronglyMeasurable_predictable_stepInt'_path n hN)
    (tendsto_pi_nhds.2 fun p ↦ tendsto_stepInt'_limInt (hN_ll p.2 p.1))

end Process

end DoobMeyerUniqueness

namespace MeasureTheory

open StieltjesFunction DoobMeyerUniqueness

section DoobMeyerUnique

/-- If `A` and `B` are predictable, integrable processes with monotone right-continuous paths, equal
at `⊥`, and such that `A - B` is a martingale, then `A ⊤ = B ⊤` almost surely. -/
theorem ae_eq_top_of_martingale_sub
    (hA : IsStronglyPredictable 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω))
    (hA_mono : ∀ ω, Monotone (A · ω)) (hA_int : ∀ t, Integrable (A t) P)
    (hB : IsStronglyPredictable 𝓕 B) (hB_rc : ∀ ω, IsRightContinuous (B · ω))
    (hB_mono : ∀ ω, Monotone (B · ω)) (hB_int : ∀ t, Integrable (B t) P)
    (h_bot : A ⊥ =ᵐ[P] B ⊥) (hAB : Martingale (A - B) 𝓕 P) :
    A ⊤ =ᵐ[P] B ⊤ := by
  have hA_ad : Adapted 𝓕 A := hA.stronglyAdapted.adapted
  have hB_ad : Adapted 𝓕 B := hB.stronglyAdapted.adapted
  have hN_meas (t : ι) : Measurable ((A - B) t) :=
    ((hA_ad t).sub (hB_ad t)).mono (𝓕.le t) le_rfl
  have hg_int (t : ι) : Integrable (fun ω ↦ g ((A - B) t ω)) P :=
    Integrable.of_bound (measurable_g.comp (hN_meas t)).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ by simpa using abs_g_le_one _)
  -- the step integrands `Hn` and their limit `H`
  let Hn (n : ℕ) (p : ι × Ω) : ℝ := stepInt n ((A - B) · p.2) p.1
  let H (p : ι × Ω) : ℝ := limInt ((A - B) · p.2) p.1
  have hHn_meas (n : ℕ) : Measurable (Hn n) := measurable_stepInt_path n hN_meas
  have hHn_bound (n : ℕ) (p : ι × Ω) : |Hn n p| ≤ 1 := abs_stepInt_le_one n _ _
  have hH_bound (p : ι × Ω) : |H p| ≤ 1 := abs_limInt_le_one _ _
  have hN_ll (ω : Ω) (s : ι) :
      Tendsto ((A - B) · ω) (𝓝[<] s) (𝓝 (((A - B) · ω).leftLim s)) :=
    (hA_mono ω).tendsto_leftLim_sub (hB_mono ω) s
  have hH_meas : StronglyMeasurable[𝓕.predictable] H :=
    stronglyMeasurable_predictable_limInt_path (hA.sub hB) hN_ll
  have h_tendsto (p : ι × Ω) (hp : p.1 ≠ ⊥) : Tendsto (fun n ↦ Hn n p) atTop (𝓝 (H p)) :=
    tendsto_stepInt_limInt ((hA_rc p.2 p.1).sub (hB_rc p.2 p.1)) (hN_ll p.2 p.1) hp
  -- the integrals of the step integrands give the increment of `g ∘ (A - B)`
  have h_path (n : ℕ) (ω : Ω) :
      ∫ s, Hn n (s, ω) ∂(kernelOfRightContAdaptedMono hA_ad hA_rc hA_mono ω)
          - ∫ s, Hn n (s, ω) ∂(kernelOfRightContAdaptedMono hB_ad hB_rc hB_mono ω)
        = g ((A - B) ⊤ ω) - g ((A - B) ⊥ ω) :=
    integral_stepInt_stieltjes_sub (rightContMono hA_rc hA_mono ω)
      (rightContMono hB_rc hB_mono ω) n
  have h_int_eq (n : ℕ) :
      ∫ ω, ∫ s, Hn n (s, ω) ∂(kernelOfRightContAdaptedMono hA_ad hA_rc hA_mono ω) ∂P
          - ∫ ω, ∫ s, Hn n (s, ω) ∂(kernelOfRightContAdaptedMono hB_ad hB_rc hB_mono ω) ∂P
        = ∫ ω, g ((A - B) ⊤ ω) ∂P - ∫ ω, g ((A - B) ⊥ ω) ∂P := by
    rw [← integral_sub
        (integrable_integral_kernelOfRightContAdaptedMono hA_ad hA_rc hA_mono (hHn_meas n)
          (hHn_bound n) (hA_int ⊤) (hA_int ⊥))
        (integrable_integral_kernelOfRightContAdaptedMono hB_ad hB_rc hB_mono (hHn_meas n)
          (hHn_bound n) (hB_int ⊤) (hB_int ⊥)),
      ← integral_sub (hg_int ⊤) (hg_int ⊥)]
    exact integral_congr_ae (ae_of_all _ (h_path n))
  -- pass to the limit, and use that the Doléans measures agree on predictable integrands
  have h_lim := (tendsto_integral_integral_kernelOfRightContAdaptedMono hA_ad hA_rc hA_mono
      hHn_meas hHn_bound h_tendsto (hA_int ⊤) (hA_int ⊥)).sub
    (tendsto_integral_integral_kernelOfRightContAdaptedMono hB_ad hB_rc hB_mono
      hHn_meas hHn_bound h_tendsto (hB_int ⊤) (hB_int ⊥))
  rw [integral_integral_kernelOfRightContAdaptedMono_eq_of_martingale hA_ad hA_rc hA_mono hB_ad
    hB_rc hB_mono hA_int hB_int hAB hH_meas hH_bound, sub_self] at h_lim
  simp_rw [h_int_eq] at h_lim
  have h_eq : ∫ ω, g ((A - B) ⊤ ω) ∂P - ∫ ω, g ((A - B) ⊥ ω) ∂P = 0 :=
    tendsto_nhds_unique tendsto_const_nhds h_lim
  have h_bot' : ∫ ω, g ((A - B) ⊥ ω) ∂P = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h_bot] with ω hω
    simp [hω]
  rw [h_bot', sub_zero, integral_eq_zero_iff_of_nonneg (fun ω ↦ g_nonneg _) (hg_int ⊤)] at h_eq
  filter_upwards [h_eq] with ω hω
  exact sub_eq_zero.1 (g_eq_zero_iff.1 hω)

/-- If `A` and `B` are predictable, integrable processes with monotone right-continuous paths, equal
at `⊥`, and such that `A - B` is a martingale, then `A` and `B` are indistinguishable. -/
theorem indistinguishable_of_martingale_sub
    (hA : IsStronglyPredictable 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω))
    (hA_mono : ∀ ω, Monotone (A · ω)) (hA_int : ∀ t, Integrable (A t) P)
    (hB : IsStronglyPredictable 𝓕 B) (hB_rc : ∀ ω, IsRightContinuous (B · ω))
    (hB_mono : ∀ ω, Monotone (B · ω)) (hB_int : ∀ t, Integrable (B t) P)
    (h_bot : A ⊥ =ᵐ[P] B ⊥) (hAB : Martingale (A - B) 𝓕 P) :
    ∀ᵐ ω ∂P, ∀ t, A t ω = B t ω := by
  have h_top : (A - B) ⊤ =ᵐ[P] 0 := by
    filter_upwards [ae_eq_top_of_martingale_sub hA hA_rc hA_mono hA_int hB hB_rc hB_mono hB_int
      h_bot hAB] with ω hω
    simp [hω]
  have h_ae (t : ι) : A t =ᵐ[P] B t := by
    have h1 : P[(A - B) ⊤ | 𝓕 t] =ᵐ[P] (A - B) t := hAB.condExp_ae_eq le_top
    have h2 : P[(A - B) ⊤ | 𝓕 t] =ᵐ[P] 0 := (condExp_congr_ae h_top).trans (by rw [condExp_zero])
    filter_upwards [h1, h2] with ω hω1 hω2
    exact sub_eq_zero.1 (hω1.symm.trans hω2)
  have h_dense : ∀ᵐ ω ∂P, ∀ t ∈ denseSet ι, A t ω = B t ω :=
    (ae_ball_iff (denseSet_countable ι)).2 fun t _ ↦ h_ae t
  filter_upwards [h_dense] with ω hω t
  exact congr_fun ((denseSet_dense ι).eq_of_isRightContinuous (top_mem_denseSet ι) hω
    (hA_rc ω) (hB_rc ω)) t

/-- **Uniqueness of the Doob-Meyer decomposition.** If `M + A = M' + A'` for two martingales `M`,
`M'` and two predictable, integrable processes `A`, `A'` with monotone right-continuous paths which
are almost surely equal at `⊥`, then `A` and `A'` are indistinguishable, as well as `M`
and `M'`. -/
theorem doob_meyer_unique {M M' A A' : ι → Ω → ℝ} (h : M + A = M' + A')
    (hM : Martingale M 𝓕 P) (hM' : Martingale M' 𝓕 P)
    (hA : IsStronglyPredictable 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω))
    (hA_mono : ∀ ω, Monotone (A · ω)) (hA_int : ∀ t, Integrable (A t) P)
    (hA' : IsStronglyPredictable 𝓕 A') (hA'_rc : ∀ ω, IsRightContinuous (A' · ω))
    (hA'_mono : ∀ ω, Monotone (A' · ω)) (hA'_int : ∀ t, Integrable (A' t) P)
    (h_bot : A ⊥ =ᵐ[P] A' ⊥) :
    (∀ᵐ ω ∂P, ∀ t, A t ω = A' t ω) ∧ (∀ᵐ ω ∂P, ∀ t, M t ω = M' t ω) := by
  have h_sub : A - A' = M' - M := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm]
    exact h
  have hA_eq : ∀ᵐ ω ∂P, ∀ t, A t ω = A' t ω :=
    indistinguishable_of_martingale_sub hA hA_rc hA_mono hA_int hA' hA'_rc hA'_mono hA'_int h_bot
      (h_sub ▸ hM'.sub hM)
  refine ⟨hA_eq, ?_⟩
  filter_upwards [hA_eq] with ω hω t
  have h_apply : M t ω + A t ω = M' t ω + A' t ω := congr_fun (congr_fun h t) ω
  rw [hω t] at h_apply
  exact add_right_cancel h_apply

/-- **Uniqueness of the Doob-Meyer decomposition.** If an integrable process `S` has two
decompositions `S = M + A = M' + A'` for two martingales `M`, `M'` and two predictable processes
`A`, `A'` with monotone right-continuous paths which are almost surely equal at `⊥`, then `A` and
`A'` are indistinguishable, as well as `M` and `M'`. -/
theorem doob_meyer_unique_of_integrable {S M M' A A' : ι → Ω → ℝ}
    (hS_int : ∀ t, Integrable (S t) P) (hS : S = M + A) (hS' : S = M' + A')
    (hM : Martingale M 𝓕 P) (hM' : Martingale M' 𝓕 P)
    (hA : IsStronglyPredictable 𝓕 A) (hA_rc : ∀ ω, IsRightContinuous (A · ω))
    (hA_mono : ∀ ω, Monotone (A · ω))
    (hA' : IsStronglyPredictable 𝓕 A') (hA'_rc : ∀ ω, IsRightContinuous (A' · ω))
    (hA'_mono : ∀ ω, Monotone (A' · ω)) (h_bot : A ⊥ =ᵐ[P] A' ⊥) :
    (∀ᵐ ω ∂P, ∀ t, A t ω = A' t ω) ∧ (∀ᵐ ω ∂P, ∀ t, M t ω = M' t ω) := by
  have hA_int (t : ι) : Integrable (A t) P := by
    have h_eq : A t = S t - M t := by simp [hS]
    rw [h_eq]
    exact (hS_int t).sub (hM.integrable t)
  have hA'_int (t : ι) : Integrable (A' t) P := by
    have h_eq : A' t = S t - M' t := by simp [hS']
    rw [h_eq]
    exact (hS_int t).sub (hM'.integrable t)
  exact doob_meyer_unique (hS.symm.trans hS') hM hM' hA hA_rc hA_mono hA_int hA' hA'_rc hA'_mono
    hA'_int h_bot

end DoobMeyerUnique

end MeasureTheory
