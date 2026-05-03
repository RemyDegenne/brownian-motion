/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Jonas Bayer
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
public import BrownianMotion.StochasticIntegral.ConvexWeights

/-!
# Komlos lemmas

-/

@[expose] public section

variable {E Ω : Type*} {mΩ : MeasurableSpace Ω}

open Filter MeasureTheory
open scoped Topology NNReal ENNReal

lemma komlos_convex (R : Type*) [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommMonoid E] [Module R E]
  {f : ℕ → E} {φ : E → ℝ} (hφ_nonneg : 0 ≤ φ)
  (hφ_bdd : ∃ M : ℝ, ∀ n, φ (f n) ≤ M) :
  ∃ g : ℕ → E, (∀ n, g n ∈ convexHull R (Set.range fun m ↦ f (n + m))) ∧
    ∀ δ > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
      2⁻¹ * φ (g n) + 2⁻¹ * φ (g m) - φ ((2 : R)⁻¹ • (g n + g m)) < δ := by
  obtain ⟨M, hM⟩ := hφ_bdd
  let r : ℕ → ℝ := fun n ↦ sInf (Set.image φ (convexHull R (Set.range (fun m ↦ f (n + m)))))
  have hr_nondec n : r n ≤ r (n + 1) := by
    apply_rules [csInf_le_csInf]
    · exact ⟨0, Set.forall_mem_image.2 fun x hx ↦ hφ_nonneg x⟩
    · exact ⟨_, ⟨ _, subset_convexHull R _ ⟨0, rfl⟩, rfl⟩⟩
    · refine Set.image_mono <| convexHull_min ?_ (convex_convexHull R _)
      rintro _ ⟨m, rfl⟩; exact subset_convexHull R _ ⟨m + 1, by simp [add_comm, add_left_comm]⟩
  obtain ⟨A, hA⟩ : ∃ A, Filter.Tendsto r Filter.atTop (nhds A) := by
    refine ⟨_, tendsto_atTop_ciSup (monotone_nat_of_le_succ hr_nondec) ?_⟩
    exact ⟨M, Set.forall_mem_range.mpr fun n ↦ csInf_le
      ⟨0, Set.forall_mem_image.mpr fun x hx ↦ hφ_nonneg x⟩
        (Set.mem_image_of_mem _ <| subset_convexHull R _
          <| Set.mem_range_self 0) |> le_trans <| by simpa using hM n⟩
  obtain ⟨g, hg⟩ :
      ∃ g : ℕ → E, (∀ n, g n ∈ convexHull R (Set.range (fun m ↦ f (n + m))))
          ∧ (∀ n, φ (g n) ≤ A + 1 / (n + 1)) := by
    have h_exists_g :
        ∀ n, ∃ g ∈ convexHull R (Set.range (fun m ↦ f (n + m))), φ g ≤ A + 1 / (n + 1) := by
      intro n
      have h_exists_g :
          ∃ g ∈ convexHull R (Set.range (fun m ↦ f (n + m))), φ g < A + 1 / (n + 1) := by
        have h_exists_g : r n < A + 1 / (n + 1) := by
          exact lt_add_of_le_of_pos (le_of_tendsto_of_tendsto tendsto_const_nhds hA
            (Filter.eventually_atTop.2 ⟨n, fun m hm ↦ by
              induction hm <;> [tauto; linarith [hr_nondec ‹_›]]⟩)) (by positivity)
        contrapose! h_exists_g
        exact le_csInf ⟨ _, Set.mem_image_of_mem _ <| subset_convexHull R _
          <| Set.mem_range_self 0 ⟩ fun x hx ↦ by
            rcases hx with ⟨ g, hg, rfl ⟩; exact h_exists_g g hg
      exact ⟨h_exists_g.choose, h_exists_g.choose_spec.1, le_of_lt h_exists_g.choose_spec.2⟩
    exact ⟨fun n ↦ Classical.choose (h_exists_g n),
      fun n ↦ Classical.choose_spec (h_exists_g n) |>.1,
        fun n ↦ Classical.choose_spec (h_exists_g n) |>.2⟩
  refine ⟨g, hg.1, fun δ δpos ↦ ?_⟩
  obtain ⟨ε, εpos, hε⟩ := exists_between (div_pos δpos zero_lt_four)
  obtain ⟨N, hN⟩ : ∃ N, r N ≥ A - ε ∧ 1 / (N + 1) ≤ ε := by
    rcases Metric.tendsto_atTop.mp hA ε εpos with ⟨N, hN⟩
    exact ⟨N + ⌈ε⁻¹⌉₊, by linarith [abs_lt.mp (hN (N + ⌈ε⁻¹⌉₊) (by grind))], by
      simpa using inv_le_of_inv_le₀ εpos (by linarith [Nat.le_ceil (ε⁻¹)])⟩
  refine ⟨N, fun n m hn hm ↦ ?_⟩
  have h_convex : φ ((1 / 2 : R) • (g n + g m)) ≥ A - ε := by
    have h_convex :
        (1 / 2 : R) • (g n + g m) ∈ convexHull R (Set.range (fun m ↦ f (N + m))) := by
      simp only [one_div, gt_iff_lt, ge_iff_le, tsub_le_iff_right, smul_add] at *
      refine convex_convexHull R _ ?_ ?_ ?_ ?_ ?_ <;> norm_num
      · refine convexHull_mono (Set.range_subset_iff.2 fun m ↦ ?_) (hg.1 n)
        exact ⟨m + (n - N), by grind⟩
      · refine convexHull_mono ?_ (hg.1 m)
        exact Set.range_subset_iff.2 fun k ↦ ⟨k + (m - N), by
          simp [show N + (k + (m - N)) = m + k by grind]⟩
      · positivity
      · positivity
    refine le_trans hN.1 ?_
    exact csInf_le ⟨0, Set.forall_mem_image.2 fun x hx ↦ hφ_nonneg _⟩ ⟨_, h_convex, rfl⟩
  norm_num at *
  linarith [hg.2 n, hg.2 m, inv_anti₀
    (by positivity) (by norm_cast; grind : (n : ℝ) + 1 ≥ N + 1), inv_anti₀
      (by positivity) (by norm_cast; grind : (m : ℝ) + 1 ≥ N + 1)]

set_option backward.isDefEq.respectTransparency false in
lemma komlos_norm [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : ℕ → E} (h_bdd : ∃ M : ℝ, ∀ n, ‖f n‖ ≤ M) :
    ∃ (g : ℕ → E), (∀ n, g n ∈ convexHull ℝ (Set.range fun m ↦ f (n + m))) ∧
      ∃ (x : E), Tendsto g atTop (𝓝 x) := by
  let φ : E → ℝ := fun f ↦ ‖f‖ ^ 2
  have φ_nonneg : 0 ≤ φ := fun f ↦ sq_nonneg ‖f‖
  have φ_bdd : ∃ M : ℝ, ∀ n, φ (f n) ≤ M := by
    rcases h_bdd with ⟨M, hM⟩
    exact ⟨M ^ 2, fun n ↦ pow_le_pow_left₀ (norm_nonneg _) (hM n) 2⟩
  rcases komlos_convex (R := ℝ) φ_nonneg φ_bdd with ⟨g, hg, h⟩
  use g
  have parallelogram_identity (x y : E) :
      2⁻¹ * ‖x‖ ^ 2 + 2⁻¹ * ‖y‖ ^ 2 - ‖(2 : ℝ)⁻¹ • (x + y)‖ ^ 2 = ‖y - x‖ ^ 2 / 4 := by
    have : (2 : ℝ)⁻¹ • (x + y) = (2 : ℝ)⁻¹ • (x + y) := by rfl
    rw [this, norm_smul_of_nonneg (by norm_num), mul_pow, add_comm x y]
    let para := parallelogram_law_with_norm ℝ y x
    linear_combination - para / 4
  have g_cauchy : CauchySeq g := by
    rw [Metric.cauchySeq_iff]
    intro δ δpos
    rcases h (δ ^ 2 / 4) (by positivity) with ⟨N, hn⟩
    use N
    intro m mgeN n ngeN
    specialize hn n m ngeN mgeN
    dsimp [φ] at hn
    rw [parallelogram_identity (g n) (g m)] at hn
    have : ‖g m - g n‖ ^ 2 < δ ^ 2 := by linarith
    rw [dist_eq_norm]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg (g m - g n)) (by positivity) (by norm_num)).mp this
  rcases CompleteSpace.complete g_cauchy with ⟨x, hx⟩
  tauto


lemma exists_stdSimplex_of_mem_convexHull {M ι : Type*} [AddCommGroup E] [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [Module M E] {s : ι → E} {x : E}
    (hx : x ∈ convexHull M (Set.range s)) :
    ∃ (w : StdSimplex M ι), x = w.sum (fun i wi ↦ wi • s i) := by
  classical
  rw [mem_convexHull_iff] at hx
  specialize hx {y | ∃ w : StdSimplex M ι, y = w.sum (fun i wi => wi • s i)} ?_ ?_
  · rintro _ ⟨i, rfl⟩
    use StdSimplex.single i
    simp
  · rintro x ⟨w₁, hw₁⟩ y ⟨w₂, hw₂⟩ a b ha hb hab
    use (StdSimplex.duple w₁ w₂ ha hb hab).join
    simp only [StdSimplex.join, StdSimplex.duple]
    repeat rw [Finsupp.sum_add_index (by simp) (fun _ _ _ _ ↦ Module.add_smul _ _ _)]
    have aux (c : M) (w : StdSimplex M ι) : c • (w.sum fun i wi ↦ wi • s i)
      = ((Finsupp.single w c).sum fun d r ↦ r • d.weights).sum fun i wi ↦ wi • s i := by
      simp only [zero_smul, Finsupp.sum_single_index]
      rw [Finsupp.sum_smul_index (by simp only [zero_smul, implies_true])]
      simp_rw [mul_smul, ← Finsupp.smul_sum]
    simp [aux, hw₁, hw₂]
  exact hx

section
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convex_combination_bounded {x : ℕ → E}
    {w : ℕ → StdSimplex ℝ ℕ} {M : ℝ} (hx : ∀ n, ‖x n‖ ≤ M) (n : ℕ) :
    ‖(w n).sum (fun i wi ↦ wi • x i)‖ ≤ M := by
  have h_sum : ‖(w n).sum (fun i wi => wi • x i)‖ ≤ ∑ i ∈ (w n).support, ((w n).weights i) * ‖x i‖
    := by
    convert norm_sum_le _ _
    simp [norm_smul, abs_of_nonneg ((w _).nonneg _)]
  refine le_trans h_sum (le_trans (Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (hx i) ((w n).nonneg i)) ?_)
  rw [← Finset.sum_mul _ _ _]
  have bound : (∑ i ∈ (w n).support, (w n).weights i) ≤ 1 := by
    rw [← (w n).total, Finsupp.sum]
  refine mul_le_of_le_one_left ?_ bound
  exact le_trans (norm_nonneg (x 0)) (hx 0)

/-- `komlosFormula x cw k n` is the convex combination of the stage-`k` vectors `x k m`,
weighted by `iteratedBindSimplex cw k n`. It is the sequence whose convergence is
established at each stage of the Komlós construction. -/
noncomputable def komlosFormula (x : ℕ → ℕ → E) (cw : ℕ → ℕ → StdSimplex ℝ ℕ) (k i n : ℕ) : E :=
  (StdSimplex.iteratedBind cw k n).sum (fun m cwm ↦ cwm • x i m)

lemma komlosFormula_congr (x : ℕ → ℕ → E) {cw1 : ℕ → ℕ → StdSimplex ℝ ℕ}
  {cw2 : ℕ → ℕ → StdSimplex ℝ ℕ} {k : ℕ} (h : ∀ k' ≤ k, cw1 k' = cw2 k') :
  komlosFormula x cw1 k = komlosFormula x cw2 k := by
  unfold komlosFormula; rw [StdSimplex.iteratedBind_congr]
  exact h

/--
We define the `convexTail` of a sequence `x` to be the set of sequences `y` with the property that
every `y n` can be written as a convex combination of elements `x k` with `k ≥ n`.
-/
def convexTail (x : ℕ → E) : Set (ℕ → E) :=
  { y | ∀ n, y n ∈ convexHull ℝ (Set.range (fun m ↦ x (n + m))) }

lemma exists_stdSimplex_of_mem_convexTail_reindexed {x g : ℕ → E} (hg : g ∈ convexTail x) (n : ℕ) :
  ∃ w : StdSimplex ℝ ℕ, g n = w.sum (fun i wi ↦ wi • x i) ∧ ∀ m < n, w.weights m = 0 := by
  obtain ⟨w₀, hw₀⟩ := exists_stdSimplex_of_mem_convexHull (hg n)
  let weights := Finsupp.embDomain ⟨fun i ↦ n + i, add_right_injective n⟩ w₀.weights
  have nonneg (i : ℕ) : 0 ≤ weights i := by
    unfold weights
    simp only [Finsupp.embDomain_apply, Function.Embedding.coeFn_mk]
    split_ifs
    · exact (w₀.nonneg _)
    · simp
  have zero_lt (m : ℕ) (hm : m < n) : weights m = 0 := by
    rw [Finsupp.embDomain_apply]
    split_ifs with h
    · exfalso
      rcases h with ⟨i, hi⟩
      have hnm : n ≤ m := by
        rw [← hi]
        exact Nat.le_add_right n i
      exact (Nat.not_le_of_lt hm hnm).elim
    · rfl
  use ⟨weights, nonneg, by grind [Finsupp.sum_embDomain]⟩
  refine ⟨?_, zero_lt⟩
  rw [Finsupp.sum_embDomain]
  simpa

variable [CompleteSpace E]

lemma komlos_base {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M) :
    ∃ (cw : ℕ → ℕ → StdSimplex ℝ ℕ), (∃ glim : E,
    Tendsto (komlosFormula x cw 0 0) atTop (𝓝 glim)) ∧ ∀ n, ∀ m < n, (cw 0 n).weights m = 0 := by
  obtain ⟨g, h_convex, lim, hlim⟩ := komlos_norm (hx 0)
  let cw (n : ℕ) := Classical.choose (exists_stdSimplex_of_mem_convexTail_reindexed h_convex n)
  use (fun k ↦ cw)
  have hg (n : ℕ) : g n = (cw n).weights.sum (fun m cwm ↦ cwm • x 0 m) := by
    exact (Classical.choose_spec (exists_stdSimplex_of_mem_convexTail_reindexed h_convex n)).1
  unfold komlosFormula
  constructor
  · use lim
    apply Tendsto.congr hg
    exact hlim
  · intro n
    exact (Classical.choose_spec (exists_stdSimplex_of_mem_convexTail_reindexed h_convex n)).2

open StdSimplex

lemma komlos_step {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M) (k : ℕ)
  (cw : ℕ → ℕ → StdSimplex ℝ ℕ) :
  ∃ (cw_new : ℕ → ℕ → StdSimplex ℝ ℕ),
    (∃ glim : E, Tendsto (komlosFormula x cw_new (k+1) (k+1)) atTop (𝓝 glim))
    ∧ (∀ i ≤ k, cw_new i = cw i) ∧ (∀ n, ∀ m < n, (cw_new (k+1) n).weights m = 0) := by
  let gtilde := fun n ↦ (iteratedBind cw k n).sum (fun m cwm ↦ cwm • (x (k+1) m))
  obtain ⟨M, hM⟩ := hx (k+1)
  have gtilde_bound : ∃ M, ∀ n, ‖gtilde n‖ ≤ M := ⟨M, convex_combination_bounded hM⟩
  obtain ⟨g_step, gstep_conv, glim, hglim⟩ := komlos_norm (gtilde_bound)
  obtain ⟨cw_step, ⟨hzero, g_step_eq_gtilde⟩⟩ : ∃ w : ℕ → StdSimplex ℝ ℕ,
    (∀ n, ∀ m < n, (w n).weights m = 0) ∧ ∀ n, g_step n = (w n).sum (fun i wi ↦ wi • gtilde i) := by
    let existence (n : ℕ) := exists_stdSimplex_of_mem_convexTail_reindexed gstep_conv n
    exact ⟨fun n ↦ Classical.choose (existence n), And.intro
      (fun n ↦ (Classical.choose_spec (existence n)).2)
      (fun n ↦ (Classical.choose_spec (existence n)).1)⟩
  let cw_new := Function.update cw (k+1) cw_step
  have g_step_eq (n : ℕ) : g_step n =
    (iteratedBind cw_new (k + 1) n).sum (fun m cwm ↦ cwm • x (k+1) m) := by
    have aux : (iteratedBind cw_new (k + 1) n)
      = (bind (cw_step n) (iteratedBind cw k)) := by
      unfold cw_new
      rw [iteratedBind, Function.update_self, iteratedBind_congr]
      grind
    rw [g_step_eq_gtilde n, aux, ← bind_sum_smul]
  use cw_new
  refine ⟨?_, by grind, ?_⟩
  · use glim; exact Tendsto.congr g_step_eq hglim
  · unfold cw_new
    simp only [Function.update_self]
    exact hzero

private noncomputable def komlosStage {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M)
    (stage : ℕ) :
    { w : ℕ → ℕ → StdSimplex ℝ ℕ // ∀ k ≤ stage, ∀ n, ∀ m < n, (w k n).weights m = 0 } :=
  match stage with
  | 0 => by
      use Classical.choose (komlos_base hx)
      intro k hk
      rw [show k=0 by grind]
      exact (Classical.choose_spec (komlos_base hx)).2
  | stage+1 => by
      let ⟨previous, hprevious⟩ := komlosStage hx stage
      let step := komlos_step hx stage previous
      use Classical.choose step
      intro k _
      let ⟨_, transfer, zero⟩ := Classical.choose_spec step
      by_cases hk: k=stage+1
      · rw [hk]
        exact zero
      · replace hk : k ≤ stage := by grind
        rw [transfer k hk]
        exact hprevious k hk

private lemma komlosStage_lim {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M) (k : ℕ) :
  (∃ glim : E, Tendsto (komlosFormula x (komlosStage hx k) k k) atTop (𝓝 glim)) := by
  induction k with
  | zero => exact (Classical.choose_spec (komlos_base hx)).1
  | succ k _ => exact Classical.choose_spec (komlos_step hx k (komlosStage hx k)) |>.1

private lemma komlosStage_congr_succ {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M)
    (k i : ℕ) (hi : i ≤ k) :
    (komlosStage hx k).val i = (komlosStage hx (k+1)).val i := by
  let aux := komlos_step hx k (komlosStage hx k)
  let ⟨_, aux2, _⟩ := Classical.choose_spec aux
  exact Eq.symm (aux2 i hi)

private lemma komlosStage_congr {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M)
    (i k : ℕ) (hi : i ≤ k) : (komlosStage hx i).val i = (komlosStage hx k).val i := by
  let n := k-i
  suffices (komlosStage hx i).val i = (komlosStage hx (i+n)).val i by
    rwa [show k = i + (k - i) by grind]
  induction n with
  | zero => rfl
  | succ n hn =>
  rw [← add_assoc, hn]
  apply komlosStage_congr_succ hx (i+n) i (by grind)

lemma komlos_convex_weights {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M) :
    ∃ (cw : ℕ → ℕ → StdSimplex ℝ ℕ),
    (∀ k : ℕ, ∃ glim : E, Tendsto (komlosFormula x cw k k) atTop (𝓝 glim))
    ∧ (∀ k n, ∀ m < n, (cw k n).weights m = 0) := by
  let cw (k : ℕ) : ℕ → StdSimplex ℝ ℕ := (komlosStage hx k).val k
  have transfer (k : ℕ) : komlosFormula x cw k = komlosFormula x (komlosStage hx k) k :=
    komlosFormula_congr x (fun i hi ↦ komlosStage_congr hx i k hi)
  use cw
  constructor
  · intro k; simp [transfer k, komlosStage_lim hx k]
  · intro k; exact (komlosStage hx k).prop k (le_refl k)

omit [CompleteSpace E] in
lemma TendstoUniformly_convexTail {x : ℕ → E} {xlim : E} (hx : Tendsto x atTop (𝓝 xlim)) :
  TendstoUniformly (fun (n : ℕ) (y : convexTail x) ↦ (y.val) n) (fun _ ↦ xlim) atTop := by
  intro u hu
  rcases Metric.mem_uniformity_dist.mp hu with ⟨ε, εpos, hεu⟩
  have hxε : ∀ᶠ n in atTop, dist (x n) xlim < ε := by
    simpa using hx (Metric.ball_mem_nhds _ εpos)
  rcases Filter.eventually_atTop.mp hxε with ⟨N, hN⟩
  refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn y
  apply hεu
  have htail : Set.range (fun m ↦ x (n + m)) ⊆ Metric.ball xlim ε := by
    rintro _ ⟨m, rfl⟩
    simpa using hN (n + m) (le_trans hn (Nat.le_add_right n m))
  have : dist xlim (y.1 n) < ε := by
    simpa [dist_comm] using (convexHull_min htail (convex_ball xlim ε)) (y.2 n)
  simpa only [gt_iff_lt] using this

omit [CompleteSpace E] in
lemma Tendsto_convexTail {x : ℕ → E} {xlim : E} (hx : Tendsto x atTop (𝓝 xlim)) :
    ∀ y ∈ convexTail x, Tendsto y atTop (𝓝 xlim) := by
  intro y hy
  exact TendstoUniformly.tendsto_at (TendstoUniformly_convexTail hx) ⟨y, hy⟩

lemma komlos_uniform_convergence
    {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M)
    (cw : ℕ → ℕ → StdSimplex ℝ ℕ) (lim : ℕ → E)
    (hcw: ∀ k : ℕ, Tendsto (komlosFormula x cw k k) atTop (𝓝 (lim k))) :
    ∀ i, TendstoUniformly (fun k ↦ komlosFormula x cw k i) lim atTop
    -- maybe too strong, the blueprint statement limits to k ≥ i
     := by
  intro i
  sorry

lemma komlos_convex_weights_diagonal
    {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M) :
    ∃ (η : ℕ → StdSimplex ℝ ℕ), (∀ n, ∀ m < n, (η n).weights m = 0) ∧ ∀ i : ℕ,
    ∃ glim : E, Tendsto (fun n ↦ (η n).sum (fun m ηm ↦ ηm • x i m)) atTop (𝓝 glim) := by sorry

lemma komlos_convergence_L2
    (f : ℕ → Ω → E) {P : Measure Ω} :
    let f' : ℕ → ℕ → Ω → E := fun i n ↦ Set.indicator {ω : Ω | ‖f n ω‖ ≤ i} (f n);
    ∃ cw : ℕ → StdSimplex ℝ ℕ, ∀ i : ℕ, ∃ lim : Ω → E,
    Tendsto (fun n ↦ eLpNorm (fun ω ↦ ((cw n).sum (fun i wi ↦ wi • f' i n)) ω - lim ω) 2 P)
      atTop (𝓝 0) := by sorry

theorem komlos_L1 [MeasurableSpace E] [BorelSpace E] {f : ℕ → Ω → E} {P : Measure Ω}
    (hf : UniformIntegrable f 1 P) :
    ∃ (g : ℕ → Ω → E) (glim : Ω → E), (∀ n, g n ∈ convexHull ℝ (Set.range fun m ↦ f (n + m))) ∧
      Tendsto (fun n ↦ eLpNorm (g n - glim) 1 P) atTop (𝓝 0) := by
  sorry

-- todo: check measurability hypothesis/conclusion
lemma komlos_ennreal (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable (X n))
    {P : Measure Ω} [IsProbabilityMeasure P] :
    ∃ (Y : ℕ → Ω → ℝ≥0∞) (Y_lim : Ω → ℝ≥0∞),
      (∀ n, Y n ∈ convexHull ℝ≥0∞ (Set.range fun m ↦ X (n + m))) ∧ Measurable Y_lim ∧
      ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (Y_lim ω)) :=
  sorry
