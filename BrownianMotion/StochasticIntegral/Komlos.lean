/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

import Mathlib.Probability.Notation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Lp.WithLp

/-!
# Komlos lemmas

-/
open Filter MeasureTheory Set Topology
open scoped Topology NNReal ENNReal BigOperators

variable {E Ω : Type*} {mΩ : MeasurableSpace Ω}

lemma komlos_convex [AddCommMonoid E] [Module ℝ≥0 E]
  {f : ℕ → E} {φ : E → ℝ} (hφ_nonneg : 0 ≤ φ)
  (hφ_bdd : ∃ M : ℝ, ∀ n, φ (f n) ≤ M) :
  ∃ g : ℕ → E, (∀ n, g n ∈ convexHull ℝ≥0 (Set.range fun m ↦ f (n + m))) ∧
    ∀ δ > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
      2⁻¹ * φ (g n) + 2⁻¹ * φ (g m) - φ ((2 : ℝ≥0)⁻¹ • (g n + g m)) < δ := by
  obtain ⟨M, hM⟩ := hφ_bdd
  let r : ℕ → ℝ := fun n ↦ sInf (Set.image φ (convexHull ℝ≥0 (Set.range (fun m ↦ f (n + m)))))
  have hr_nondec n : r n ≤ r (n + 1) := by
    apply_rules [csInf_le_csInf]
    · exact ⟨0, Set.forall_mem_image.2 fun x hx ↦ hφ_nonneg x⟩
    · exact ⟨_, ⟨ _, subset_convexHull ℝ≥0 _ ⟨0, rfl⟩, rfl⟩⟩
    · refine Set.image_mono <| convexHull_min ?_ (convex_convexHull ℝ≥0 _)
      rintro _ ⟨m, rfl⟩; exact subset_convexHull ℝ≥0 _ ⟨m + 1, by simp [add_comm, add_left_comm]⟩
  obtain ⟨A, hA⟩ : ∃ A, Filter.Tendsto r Filter.atTop (nhds A) := by
    refine ⟨_, tendsto_atTop_ciSup (monotone_nat_of_le_succ hr_nondec) ?_⟩
    exact ⟨M, Set.forall_mem_range.mpr fun n ↦ csInf_le
      ⟨0, Set.forall_mem_image.mpr fun x hx ↦ hφ_nonneg x⟩
        (Set.mem_image_of_mem _ <| subset_convexHull ℝ≥0 _
          <| Set.mem_range_self 0) |> le_trans <| by simpa using hM n⟩
  obtain ⟨g, hg⟩ :
      ∃ g : ℕ → E, (∀ n, g n ∈ convexHull ℝ≥0 (Set.range (fun m ↦ f (n + m))))
          ∧ (∀ n, φ (g n) ≤ A + 1 / (n + 1)) := by
    have h_exists_g :
        ∀ n, ∃ g ∈ convexHull ℝ≥0 (Set.range (fun m ↦ f (n + m))), φ g ≤ A + 1 / (n + 1) := by
      intro n
      have h_exists_g :
          ∃ g ∈ convexHull ℝ≥0 (Set.range (fun m ↦ f (n + m))), φ g < A + 1 / (n + 1) := by
        have h_exists_g : r n < A + 1 / (n + 1) := by
          exact lt_add_of_le_of_pos (le_of_tendsto_of_tendsto tendsto_const_nhds hA
            (Filter.eventually_atTop.2 ⟨n, fun m hm ↦ by
              induction hm <;> [tauto; linarith [hr_nondec ‹_›]]⟩)) (by positivity)
        contrapose! h_exists_g
        exact le_csInf ⟨ _, Set.mem_image_of_mem _ <| subset_convexHull ℝ≥0 _
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
  have h_convex : φ ((1 / 2 : ℝ≥0) • (g n + g m)) ≥ A - ε := by
    have h_convex :
        (1 / 2 : ℝ≥0) • (g n + g m) ∈ convexHull ℝ≥0 (Set.range (fun m ↦ f (N + m))) := by
      simp only [one_div, gt_iff_lt, ge_iff_le, tsub_le_iff_right, smul_add] at *
      refine convex_convexHull ℝ≥0 _ ?_ ?_ ?_ ?_ ?_ <;> norm_num
      · refine convexHull_mono (Set.range_subset_iff.2 fun m ↦ ?_) (hg.1 n)
        exact ⟨m + (n - N), by grind⟩
      · refine convexHull_mono ?_ (hg.1 m)
        exact Set.range_subset_iff.2 fun k ↦ ⟨k + (m - N), by
          simp [show N + (k + (m - N)) = m + k by grind]⟩
    refine le_trans hN.1 ?_
    exact csInf_le ⟨0, Set.forall_mem_image.2 fun x hx ↦ hφ_nonneg _⟩ ⟨_, h_convex, rfl⟩
  norm_num at *
  linarith [hg.2 n, hg.2 m, inv_anti₀
    (by positivity) (by norm_cast; grind : (n : ℝ) + 1 ≥ N + 1), inv_anti₀
      (by positivity) (by norm_cast; grind : (m : ℝ) + 1 ≥ N + 1)]

lemma komlos_norm [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : ℕ → E} (h_bdd : ∃ M : ℝ, ∀ n, ‖f n‖ ≤ M) :
    ∃ (g : ℕ → E) (x : E), (∀ n, g n ∈ convexHull ℝ≥0 (Set.range fun m ↦ f (n + m))) ∧
      Tendsto g atTop (𝓝 x) := by
  let φ : E → ℝ := fun f ↦ ‖f‖ ^ 2
  have φ_nonneg : 0 ≤ φ := fun f ↦ sq_nonneg ‖f‖
  have φ_bdd : ∃ M : ℝ, ∀ n, φ (f n) ≤ M := by
    rcases h_bdd with ⟨M, hM⟩
    exact ⟨M ^ 2, fun n ↦ pow_le_pow_left₀ (norm_nonneg _) (hM n) 2⟩
  rcases komlos_convex φ_nonneg φ_bdd with ⟨g, hg, h⟩
  use g
  have parallelogram_identity (x y : E) :
      2⁻¹ * ‖x‖ ^ 2 + 2⁻¹ * ‖y‖ ^ 2 - ‖(2 : ℝ≥0)⁻¹ • (x + y)‖ ^ 2 = ‖y - x‖ ^ 2 / 4 := by
    have : (2 : ℝ≥0)⁻¹ • (x + y) = (2 : ℝ)⁻¹ • (x + y) := by rfl
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
  exact ⟨x, hg, hx⟩

/-
## Part 0: Strict Convexity under Linear Equivalence

We need a quick transport lemma: strict convexity survives precomposition by a linear
equivalence. This lets us pass from `exp` to `exp ∘ (-)` in Part 1.
-/

namespace StrictConvexOn

variable {𝕜 : Type*} {E : Type*} {F : Type*} {β : Type*} [Semiring 𝕜]
  [PartialOrder 𝕜] [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid β]
  [PartialOrder β] [Module 𝕜 E] [Module 𝕜 F]
  [SMul 𝕜 β]

lemma LinearEquiv {f : F → β} {s : Set F} (hf : StrictConvexOn 𝕜 s f) (g : E ≃ₗ[𝕜] F) :
    StrictConvexOn  𝕜 (g ⁻¹' s) (f ∘ g) :=
  ⟨hf.1.linear_preimage _, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (g (a • x + b • y)) = f (a • g x + b • g y) := by rw [g.map_add, g.map_smul, g.map_smul]
      _ < a • f (g x) + b • f (g y) := hf.2 hx hy (g.injective.ne hxy) ha hb hab⟩

end StrictConvexOn

/-
## Part 1: The Reciprocal of the Real Exponential Function

We isolate analytic properties of `x ↦ exp (-x)` (a.k.a. `exp⁻¹`) that will be
needed later: strict convexity gives a midpoint gap inequality, and strict antitonicity
gives injectivity. These are the real-analytical inputs for the defect bounds.
-/

namespace Real

lemma exp_inv_le_one_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x.exp⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_exp hx)

lemma strictConvexOn_exp_neg : StrictConvexOn ℝ (Set.univ : Set ℝ) (fun x ↦ Real.exp (-x)) :=
  strictConvexOn_exp.LinearEquiv (LinearEquiv.neg ℝ)

lemma strictConvexOn_exp_inv : StrictConvexOn ℝ Set.univ rexp⁻¹ := by
  simp_rw [Pi.inv_def, ← Real.exp_neg]
  exact strictConvexOn_exp_neg

lemma exp_inv_midpoint_lt_avg {x y : ℝ} (hxy : x ≠ y) :
    (2⁻¹ * (x + y)).exp⁻¹ < 2⁻¹ * (x.exp⁻¹ + y.exp⁻¹) := by
  have := strictConvexOn_exp_inv.2 trivial trivial hxy one_half_pos one_half_pos (add_halves 1)
  simpa only [mul_add, one_div, smul_eq_mul] using this

lemma strictAnti_exp_inv : StrictAnti rexp⁻¹ := by
  intro x y hxy
  simp_rw [Pi.inv_apply]
  gcongr

lemma exp_inv_injective : Function.Injective rexp⁻¹ := strictAnti_exp_inv.injective

end Real

/-
## Part 2: Extension to Extended Non-Negative Reals

Our random variables are `ℝ≥0∞`-valued, so we extend `exp⁻¹` and `-log` to this setting.
We package `expInv : ℝ≥0∞ → ℝ` so that it lands in `[0,1]`, prove the same midpoint
inequality and strict antitone/injective/continuous properties, and build a closed
embedding `expInvIcc`. This will later let us move between convergence of `expInv ∘ f`
and convergence of `f` itself.
-/

namespace ENNReal

section ExponentialTransform

/-- ExponentialTransform -/
noncomputable
def expInv : ℝ≥0∞ → ℝ
  | ∞ => 0
  | (x : ℝ≥0) => (Real.exp x)⁻¹

@[simp] lemma expInv_top : expInv ⊤ = 0 := rfl

@[simp] lemma expInv_of_nnreal {x : ℝ≥0} : expInv x = (Real.exp x)⁻¹ := rfl

@[simp] lemma expInv_of_ne_top {x : ℝ≥0∞} (hy : x ≠ ⊤) : expInv x = (Real.exp x.toReal)⁻¹ := by
  lift x to NNReal using hy
  rw [coe_toReal]; rfl

lemma exp_coe_of_nonneg (x : Real) : (EReal.exp x).toReal = Real.exp x := by
  rw [EReal.exp_coe, ENNReal.toReal_ofReal_eq_iff]
  exact Real.exp_nonneg x

lemma expInv_eq_toReal_inv_exp {x : ℝ≥0∞} : x.expInv = (EReal.exp x)⁻¹.toReal:= by
  induction x with
  | top => rw [EReal.coe_ennreal_top, EReal.exp_top,inv_top,toReal_zero ]; rfl
  | coe x => rw [expInv_of_nnreal, toReal_inv, inv_inj, ← exp_coe_of_nonneg]; rfl

lemma expInv_def : expInv = fun x : ENNReal ↦ (EReal.exp x)⁻¹.toReal := by
  ext x
  rw [← expInv_eq_toReal_inv_exp]

lemma expInv_nonneg (x : ℝ≥0∞) : 0 ≤ x.expInv :=
  expInv_eq_toReal_inv_exp ▸ toReal_nonneg

lemma expInv_le_one (x : ℝ≥0∞) : x.expInv ≤ 1 := by
  induction x with
  | top => exact zero_le_one
  | coe x => exact Real.exp_inv_le_one_of_nonneg x.2

lemma expInv_abs_eq_self {x : ℝ≥0∞} : |x.expInv| = x.expInv := abs_of_nonneg (expInv_nonneg _)

lemma expInv_mem_Icc (x : ℝ≥0∞) : x.expInv ∈ Icc 0 1 := ⟨expInv_nonneg x, expInv_le_one x⟩

lemma strictAnti_exp_inv : StrictAnti expInv := by
  intro x y hxy
  lift x to NNReal using hxy.ne_top
  induction y with
  | top => exact inv_pos.2 (Real.exp_pos _)
  | coe y => exact Real.strictAnti_exp_inv (mod_cast hxy)

lemma expInv_injective : Function.Injective expInv :=  strictAnti_exp_inv.injective

lemma continuous_expInv : Continuous expInv := by
  rw [expInv_def, continuous_iff_continuousAt]
  intro x
  apply (continuousAt_toReal (by simp)).comp'
  exact (continuous_exp.comp' continuous_coe_ennreal_ereal).inv.continuousAt

lemma expInv_midpoint_lt_avg {x y : ℝ≥0∞} (h : x ≠ y) :
    expInv (2⁻¹ * (x + y)) < 2⁻¹ * (x.expInv + y.expInv) := by
  rw [← coe_inv_two]
  wlog hxy : x < y
  · rw [add_comm x.expInv, add_comm x]
    exact this h.symm <| lt_of_le_of_ne (not_lt.mp hxy) h.symm
  lift x to NNReal using hxy.ne_top
  induction y with
  | top => simpa using Real.exp_pos _
  | coe y =>
    exact Real.exp_inv_midpoint_lt_avg <| Subtype.coe_ne_coe.2 fun a ↦ h (congrArg ofNNReal a)

lemma expInv_midpoint_le_avg {x y : ℝ≥0∞} :
     expInv (2⁻¹ * (x + y)) ≤  2⁻¹ * (x.expInv + y.expInv) := by
  cases em (x = y) with
  | inl h => simp [h, ← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
  | inr h => exact (expInv_midpoint_lt_avg h).le

end ExponentialTransform

section LogarithmicTransform

/-- The inverse of expInv -/
noncomputable
def logNeg (x : ℝ) : ℝ≥0∞ := if x = 0 then ⊤ else ENNReal.ofReal (- Real.log x)

lemma expInv_logNeg_of_mem {y : ℝ} (hy : y ∈ Icc 0 1) : expInv (logNeg y) = y := by
  unfold logNeg
  split_ifs with h
  · subst h; rfl
  · rw [expInv_of_ne_top ofReal_ne_top, toReal_ofReal', max_eq_left]
    · rw [Real.exp_neg, InvolutiveInv.inv_inv, Real.exp_log <| hy.1.lt_of_ne' h]
    · rw [Right.nonneg_neg_iff, Real.log_nonpos_iff hy.1]
      exact hy.2

lemma measurable_logNeg : Measurable logNeg :=
  Measurable.ite measurableSet_eq measurable_const <| by measurability

end LogarithmicTransform

section Embedding

/-- Tranformation into the unit-interval -/
noncomputable
def expInvIcc (x : ℝ≥0∞) : Icc (0 : ℝ) 1 := ⟨expInv x, expInv_mem_Icc x⟩

lemma isClosedEmbedding_expInvIcc : IsClosedEmbedding expInvIcc := by
  have : Function.Injective expInvIcc := by
    intro x y hxy
    exact expInv_injective (congrArg Subtype.val hxy)
  exact (continuous_expInv.subtype_mk expInv_mem_Icc).isClosedEmbedding this

end Embedding

/-!
## Part 3: Convexity and Quantitative Defects

We quantify the strict convexity of `expInv` via a `defect` function measuring the midpoint gap.
The key estimate says: if `expInv x` and `expInv y` are separated, then the defect is uniformly
positive. This is the bridge from pointwise separation to an integral estimate in Part 4.
-/

/-- Gap function -/
noncomputable
def defect (x y : ℝ≥0∞) : ℝ :=  2⁻¹ *  (expInv x + expInv y) - expInv (2⁻¹ * (x + y))

lemma defect_nonneg (x y : ℝ≥0∞) : 0 ≤ defect x y :=
  sub_nonneg.mpr (expInv_midpoint_le_avg (x := x) (y := y))

lemma defect_pos_of_ne {x y : ℝ≥0∞} (hxy : x ≠ y) : 0 < defect x y :=
  sub_pos.mpr (expInv_midpoint_lt_avg hxy)

lemma continuous_defect_prod : Continuous (fun (p : ℝ≥0∞ × ℝ≥0∞) ↦ defect p.1 p.2) := by
  have h_avg : Continuous fun p : ℝ≥0∞ × ℝ≥0∞ => expInv p.1 + expInv p.2 :=
    (continuous_expInv.comp continuous_fst).add (continuous_expInv.comp continuous_snd)
  have h_mul : Continuous fun z : ℝ≥0∞ => 2⁻¹ * z :=
    ENNReal.continuous_const_mul (inv_ne_top.mpr (NeZero.ne 2))
  have h_mid : Continuous fun p : ℝ≥0∞ × ℝ≥0∞ =>  2⁻¹ * (p.1 + p.2) :=
    h_mul.comp (continuous_fst.add continuous_snd)
  exact (continuous_const.mul h_avg).sub <| continuous_expInv.comp h_mid

lemma quantitative_convexity (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : ℝ≥0∞, ε ≤ |expInv x - expInv y| → δ ≤ defect x y := by
  let K := {p : ℝ≥0∞ × ℝ≥0∞ | ε ≤ |expInv p.1 - expInv p.2|}
  have hK_closed : IsClosed K := by
    have h_phi_diff : Continuous fun p : ℝ≥0∞ × ℝ≥0∞ => |expInv p.1 - expInv p.2| :=
      ((continuous_expInv.comp continuous_fst).sub (continuous_expInv.comp continuous_snd)).abs
    exact isClosed_le continuous_const h_phi_diff
  by_cases h_nonempty : K.Nonempty
  · rcases h_nonempty with ⟨p₀, hp₀⟩
    rcases hK_closed.isCompact.exists_isMinOn ⟨p₀, hp₀⟩ continuous_defect_prod.continuousOn with
      ⟨⟨x₀, y₀⟩, hxy_mem, h_min⟩
    refine ⟨defect x₀ y₀, ?_, ?_⟩
    · have h_dist_pos : expInv x₀ ≠ expInv y₀ := by
        intro h_eq
        have h_le_zero : ε ≤ 0 := by simpa [K, h_eq] using hxy_mem
        exact lt_irrefl _ (lt_of_le_of_lt h_le_zero hε)
      exact defect_pos_of_ne fun h_eq => h_dist_pos (by rw [h_eq])
    · intro x y hxy
      simpa using (isMinOn_iff.1 h_min) ⟨x, y⟩ hxy
  · exact ⟨1, zero_lt_one, fun x y hxy ↦ (h_nonempty ⟨⟨x, y⟩, hxy⟩).elim⟩

/-- Inverse mapping properties.
Later we will know `expInv ∘ g_n → expInv g` and need to recover convergence of `g_n`.
This lemma uses the closed embedding from Part 2 to transfer convergence back to `ℝ≥0∞`. -/
lemma tendsto_of_expInv_tendsto {α : Type*} {l : Filter α} {f : α → ℝ≥0∞} {y : ℝ≥0∞}
    (h : Tendsto (expInv ∘ f) l (𝓝 (expInv y))) : Tendsto f l (𝓝 y) := by
  have hcoe : IsClosedEmbedding fun z : Icc (0 : ℝ) 1 => (z : ℝ) :=
    (isClosed_Icc : IsClosed (Icc (0 : ℝ) 1)).isClosedEmbedding_subtypeVal
  have hφ : Tendsto (expInvIcc ∘ f) l (𝓝 (expInvIcc y)) := by
    refine (hcoe.tendsto_nhds_iff).2 ?_
    simpa [Function.comp, expInvIcc] using h
  exact (isClosedEmbedding_expInvIcc.tendsto_nhds_iff).2 hφ

/-!
## Part 4: Measure-Theoretic Stuff

We lift the pointwise theory to random variables: measurability/integrability of `expInv`
and `defect`, and a definition of the expected defect `Defect_val`.
The  probabilistic estimate bounds the probability of large separation by this expected
defect; this used in the L1 Cauchy argument in Part 5.
-/

section MeasureTheory

variable (P : Measure Ω) [IsProbabilityMeasure P]

lemma measurable_expInv : Measurable expInv := continuous_expInv.measurable

lemma integrable_expInv_comp {f : Ω → ℝ≥0∞} (hf : Measurable f) : Integrable (expInv ∘ f) P := by
  refine ⟨((measurable_expInv.comp hf).aestronglyMeasurable), ?_⟩
  apply MeasureTheory.HasFiniteIntegral.of_bounded
  · filter_upwards with i
    simpa [Function.comp_apply, Real.norm_eq_abs, expInv_abs_eq_self] using expInv_le_one _

lemma integrable_defect {f g : Ω → ℝ≥0∞}
   (hf : Measurable f) (hg : Measurable g) : Integrable (fun ω ↦ defect (f ω) (g ω)) P := by
  have h_D_meas : Measurable (fun ω ↦ defect (f ω) (g ω)) := by
    refine Measurable.sub ?_ <| measurable_expInv.comp <| (hf.add hg).const_mul _
    exact measurable_const.mul ((measurable_expInv.comp hf).add (measurable_expInv.comp hg))
  use Measurable.aestronglyMeasurable h_D_meas
  apply HasFiniteIntegral.of_bounded
  change ∀ᵐ (a : Ω) ∂P, ‖defect (f a) (g a)‖ ≤ 1
  filter_upwards with ω
  rw [defect, Real.norm_eq_abs, abs_le]
  refine ⟨?_, ?_⟩
  · linarith [expInv_nonneg (f ω), expInv_nonneg (g ω), expInv_le_one (2⁻¹ * (f ω + g ω))]
  · linarith [expInv_le_one (f ω), expInv_le_one (g ω), expInv_nonneg (2⁻¹ * (f ω + g ω))]

/-- Gap value -/
noncomputable
def Defect_val (f g : Ω → ℝ≥0∞) := (∫ ω, (defect (f ω) (g ω)) ∂P)

lemma Defect_val_eq {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
   Defect_val P f g =  2⁻¹ * (∫ (ω : Ω), (f ω).expInv ∂P + ∫ (ω : Ω), (g ω).expInv ∂P) -
    ∫ (ω : Ω), (2⁻¹ * (f ω + g ω)).expInv ∂P := by
  have hfx : Integrable (fun ω ↦ (f ω).expInv) P := integrable_expInv_comp P hf
  have hgx : Integrable (fun a ↦ (g a).expInv) P := integrable_expInv_comp P hg
  have hmid : Integrable (fun ω ↦ expInv (2⁻¹ * (f ω + g ω))) P :=
    integrable_expInv_comp  _ <| (Measurable.add hf hg).const_mul 2⁻¹
  have hsum : Integrable (fun ω ↦ expInv (f ω) + expInv (g ω)) P := hfx.add hgx
  have hmul : Integrable (fun ω ↦ 2⁻¹ * (expInv (f ω) + expInv (g ω))) P := hsum.const_mul _
  dsimp [Defect_val, defect]
  rwa [integral_sub hmul hmid, integral_const_mul, integral_add hfx]

omit [IsProbabilityMeasure P] in
lemma defect_val_nonneg (f g : Ω → ℝ≥0∞) : 0 ≤ Defect_val P f g  := by
  apply integral_nonneg
  intro ω
  exact defect_nonneg (f ω) (g ω)

lemma prob_large_diff_le_defect (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (f g : Ω → ℝ≥0∞), Measurable f → Measurable g →
      P {ω | ε ≤ dist (f ω).expInv (g ω).expInv} ≤ ENNReal.ofReal (δ⁻¹ * (Defect_val P f g)) := by
  obtain ⟨δ, hδ_pos, hδ⟩ := quantitative_convexity ε hε
  use δ, hδ_pos
  intro f g hf hg
  let S := {ω | ε ≤ dist (f ω).expInv (g ω).expInv}
  let D := fun ω ↦ defect (f ω) (g ω)
  have hS_meas : MeasurableSet S := by
    apply measurableSet_le measurable_const
    exact (measurable_expInv.comp hf).dist (measurable_expInv.comp hg)
  have h_ineq_ptwise : ∀ ω, δ * (S.indicator (fun _ ↦ 1) ω) ≤ D ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [indicator_of_mem hω, mul_one]
      exact hδ (f ω) (g ω) hω
    · rw [indicator_of_notMem hω, mul_zero]
      exact defect_nonneg (f ω) (g ω)
  have h_integrable_indicator : Integrable (S.indicator (fun _ ↦ (1 : Real))) P :=
    (integrable_const 1).indicator hS_meas
  have h_integral_ineq : ∫ ω, δ * (S.indicator (fun _ ↦ 1) ω) ∂P ≤ ∫ ω, D ω ∂P :=
    integral_mono (h_integrable_indicator.const_mul δ) (integrable_defect _ hf hg) h_ineq_ptwise
  simp only [integral_const_mul, integral_indicator hS_meas, integral_const, MeasurableSet.univ,
    measureReal_restrict_apply, univ_inter, smul_eq_mul, mul_one] at h_integral_ineq
  rw [← Defect_val] at h_integral_ineq
  rw [le_ofReal_iff_toReal_le]
  · rwa [← div_eq_inv_mul, le_div_iff₀' hδ_pos]
  · exact measure_ne_top P _
  · exact mul_nonneg (inv_nonneg.mpr (le_of_lt hδ_pos)) <| defect_val_nonneg P _ _

lemma convexHull_real_subset_convexHull_ennreal (f : ℕ → Ω → ℝ≥0∞) (n : ℕ) :
    convexHull ℝ≥0 (Set.range (fun m => (f (n + m)))) ⊆
      convexHull ℝ≥0∞ (Set.range fun m => f (n + m)) := by
  intro i hg_mem
  rw [mem_convexHull_iff]
  intro S hS hS_conv
  exact (mem_convexHull_iff (𝕜 := ℝ≥0)).1 hg_mem _ hS (Convex.lift ℝ≥0 hS_conv)

end MeasureTheory

open ContinuousLinearMap PiLp WithLp


end ENNReal



open ENNReal
/-
## Part 5: Komlós Lemma for ENNReal

We combine the convex Komlós lemma with the defect bounds: first show `expInv ∘ g_n`
is Cauchy in L1, then extract a subsequence with a.e. convergence, and finally invert
`expInv` using `logNeg` to obtain a.e. convergence of `g_n` itself.
-/

lemma komlos_ennreal (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable (X n))
    {P : Measure Ω} [IsProbabilityMeasure P] :
    ∃ (Y : ℕ → Ω → ℝ≥0∞) (Y_lim : Ω → ℝ≥0∞),
      (∀ n, Y n ∈ convexHull ℝ≥0∞ (Set.range fun m ↦ X (n + m))) ∧ Measurable Y_lim ∧
      ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (Y_lim ω)) := by
  /-
  ### Step 1: Set up the `expInv` transform and basic bounds
  We move to the bounded transform `Z = expInv ∘ X` so that integrability and L1 estimates
  are straightforward, and we record uniform bounds that will be used repeatedly.
  -/
  letI : MeasureSpace Ω := { toMeasurableSpace := mΩ, volume := P }
  let Z : (Ω → ℝ≥0∞) → Ω → ℝ := fun X ω => (X ω).expInv
  let φ : (Ω → ℝ≥0∞) → ℝ := fun X => ∫ ω, Z X ω ∂P
  have hZ_le_one (X : Ω → ℝ≥0∞) (ω : Ω) : (Z X) ω ≤ 1 := expInv_le_one (X ω)
  have hZ_norm_le_one (X : Ω → ℝ≥0∞) : ∀ᵐ ω : Ω, ‖(X ω).expInv‖ ≤ 1 := by
    simp_rw [Real.norm_eq_abs, expInv_abs_eq_self]
    filter_upwards with ω using expInv_le_one _
  have hZ_integrable {W : Ω → ℝ≥0∞} (hX : Measurable W) : Integrable (Z W) :=
    ⟨(measurable_expInv.comp hX).aestronglyMeasurable, HasFiniteIntegral.of_bounded
      (hZ_norm_le_one _)⟩
  have hφ_le_one (n : ℕ) : φ (X n) ≤ 1 := by
    have hf_int : Integrable (Z (X n)) P := integrable_expInv_comp _ (hX n)
    have h_int := integral_mono (hf_int) (integrable_const _) (hZ_le_one _)
    have hconst : ∫ ω, (1 : ℝ) ∂P = 1 := by
      rw [integral_const 1, smul_eq_mul, mul_one, MeasureTheory.probReal_univ]
    simpa [φ,  Function.comp, hconst] using h_int
  have hφ_nonneg : 0 ≤ φ := by
    intro X
    apply integral_nonneg
    intro ω
    apply expInv_nonneg _
  have hφ_nonneg_X (X : Ω → ℝ≥0∞) : 0 ≤ φ X := hφ_nonneg X
  have hφ_bdd : ∃ M : ℝ, ∀ n, φ (X n) ≤ M := ⟨1, hφ_le_one⟩
  /-
  ### Step 2: Apply abstract Komlós with the defect functional
  We apply the convex Komlós lemma to the functional `φ` to obtain convex combinations `g n`
  with a Cauchy-type control in terms of the defect.
  -/
  have ⟨g, hg_convex, hg_cauchy_defect⟩ : ∃ g : ℕ → Ω → ℝ≥0∞,
    (∀ n, g n ∈ convexHull ℝ≥0∞ (Set.range fun m ↦ X (n + m))) ∧
    ∀ δ > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
       2⁻¹ *(φ (g n) + φ (g m)) - φ (fun ω ↦  2⁻¹ * (g n ω + g m ω)) < δ := by
    obtain ⟨g, hg_conv_rge0, hg_cauchy⟩ := komlos_convex (fun f ↦ hφ_nonneg f) hφ_bdd
    refine ⟨g, fun n ↦ convexHull_real_subset_convexHull_ennreal X n (hg_conv_rge0 n), ?_⟩
    intro δ δpos
    obtain ⟨N, hN⟩ := hg_cauchy δ δpos
    refine ⟨N, fun n m hn hm ↦ ?_⟩
    simp_rw [mul_add]
    convert hN n m hn hm with z
    simp only [Pi.smul_apply, Pi.add_apply, smul_add]
    congr
    · simp
    · simp
  have h_measurable_convex : Convex ℝ≥0∞ {h : Ω → ℝ≥0∞ | Measurable h} := by
    intro f hf g hg a b ha hb hab
    exact (measurable_const.mul hf).add (measurable_const.mul hg)
  have hg_meas (n : ℕ) : Measurable (g n) := by
    have h_range :  Set.range (fun m => X (n + m)) ⊆ {h : Ω → ℝ≥0∞ | Measurable h} :=
      range_subset_iff.mpr fun y ↦ hX (n + y)
    have hsubset : convexHull ℝ≥0∞ (Set.range fun m => X (n + m)) ⊆ {h : Ω → ℝ≥0∞ | Measurable h} :=
      convexHull_min h_range h_measurable_convex
    exact hsubset (hg_convex n)
  /-
  ### Step 3: Convert defect control into an L1 Cauchy estimate
  Using `prob_large_diff_le_defect`, we show `Z ∘ g n` is Cauchy in L1. This is the
  analytic heart of the argument: boundedness plus defect control yields L1 Cauchy.
  -/
  have h_exp_cauchy : ∀ η>0, ∃ N, ∀ n m, N ≤ n → N ≤ m → ∫ ω, |Z (g n) ω - Z (g m) ω| ∂P < η := by
    intro ε hε
    let δ' := 2⁻¹ * ε
    have hδ'_pos : 0 < δ' := by positivity
    obtain ⟨δ_defect, hδ_defect_pos, h_measure_bound⟩ := prob_large_diff_le_defect P δ' hδ'_pos
    let target_defect := (ε / 4) * δ_defect
    have h_target_defect_pos : 0 < target_defect := by
      rw [mul_pos_iff_of_pos_right hδ_defect_pos]
      positivity
    obtain ⟨N, hN_defect⟩ := hg_cauchy_defect target_defect h_target_defect_pos
    use N
    intro m n hm hn
    set Y := fun n ↦ expInv ∘ (g n)
    let S := {ω | δ' ≤ |Y m ω - Y n ω|}
    have hS_meas : MeasurableSet S := by
      apply measurableSet_le measurable_const
      exact (measurable_expInv.comp (hg_meas m)).dist (measurable_expInv.comp (hg_meas n))
    have h_abs_integrable : Integrable (fun ω ↦ |Y m ω - Y n ω|) P :=
      ((hZ_integrable  (hg_meas m)).sub (hZ_integrable  (hg_meas n))).abs
    have h_eval_constants :
        (∫ ω in S, 2 ∂P) + (∫ ω in Sᶜ, δ' ∂P) = 2 * (P S).toReal + δ' * (P Sᶜ).toReal := by
      simp [smul_eq_mul, smul_eq_mul, mul_comm]
      rfl
    have h_prob_compl_le_one : 2 * (P S).toReal + δ' * (P Sᶜ).toReal ≤ 2 * (P S).toReal + δ' := by
      have : (P Sᶜ).toReal ≤ 1 := (measureReal_def P Sᶜ).symm ▸ measureReal_le_one
      simpa only [add_le_add_iff_left, ge_iff_le] using ((mul_le_iff_le_one_right hδ'_pos).2 this)
    have h_measure_by_defect : 2 * (P S).toReal + δ'
        ≤ 2 * (δ_defect⁻¹ * (Defect_val P (g m) (g n))) + δ' := by
      have h_measure : (P S).toReal ≤ δ_defect⁻¹ * (Defect_val P (g m) (g n)) := by
        rw [← ENNReal.le_ofReal_iff_toReal_le (measure_ne_top P S)]
        · exact h_measure_bound (g m) (g n) (hg_meas m) (hg_meas n)
        · exact mul_nonneg (Right.inv_nonneg.mpr hδ_defect_pos.le) (defect_val_nonneg P (g m) (g n))
      simpa using mul_le_mul_of_nonneg_left h_measure zero_le_two
    have h_integral_bound : ∫ ω in S, |Y m ω - Y n ω| ∂P + ∫ ω in Sᶜ, |Y m ω - Y n ω| ∂P ≤
        ∫ ω in S, 2 ∂P + ∫ ω in Sᶜ, δ' ∂P := by
      have hY_le_one (k) (ω) : |Y k ω| ≤ 1 := by
        simpa only [Y, Function.comp, expInv_abs_eq_self] using (expInv_le_one _)
      have h_abs_le (ω : Ω) : |Y m ω - Y n ω| ≤ 2 := by
        rw [← one_add_one_eq_two]
        exact (abs_sub _ _ ).trans <| add_le_add (hY_le_one m ω) (hY_le_one n ω)
      have h_abs_le_delta {ω} (hω : ω ∈ Sᶜ) : |Y m ω - Y n ω| ≤ δ' := by
        have : ¬ δ' ≤ |Y m ω - Y n ω| := hω
        exact (lt_of_not_ge this).le
      have hone : (∫ ω in S, |Y m ω - Y n ω| ∂P) ≤ (∫ ω in S, 2 ∂P)  :=
        setIntegral_mono h_abs_integrable.integrableOn (integrable_const 2).integrableOn h_abs_le
      have htwo : (∫ ω in Sᶜ, |Y m ω - Y n ω| ∂P) ≤ (∫ ω in Sᶜ, δ' ∂P)  := by
        apply setIntegral_mono_on h_abs_integrable.integrableOn (integrable_const δ').integrableOn
        · rwa [@MeasurableSet.compl_iff]
        apply h_abs_le_delta
      exact add_le_add hone htwo
    have h_defect_lt_target_two :
        2 * (δ_defect⁻¹ * ((Defect_val P (g m) (g n)))) + δ' <
          2 * (δ_defect⁻¹ * target_defect) + δ' := by
      simpa [Defect_val_eq P (hg_meas m) (hg_meas n)] using
        mul_lt_mul_of_pos_left (hN_defect m n hm hn) <| Right.inv_pos.mpr hδ_defect_pos
    have h_dist_lt_ε : ∫ ω, |Y m ω - Y n ω| ∂P < ε := by
      calc
      ∫ ω, |Y m ω - Y n ω| ∂P =
          (∫ ω in S, |Y m ω - Y n ω| ∂P) + (∫ ω in Sᶜ, |Y m ω - Y n ω| ∂P) :=
            (integral_add_compl hS_meas h_abs_integrable).symm
      _ ≤ (∫ ω in S, 2 ∂P) + (∫ ω in Sᶜ, δ' ∂P) := h_integral_bound
      _ = 2 * (P S).toReal + δ' * (P Sᶜ).toReal := h_eval_constants
      _ ≤ 2 * (P S).toReal + δ' := h_prob_compl_le_one
      _ ≤ 2 * (δ_defect⁻¹ * (Defect_val P (g m) (g n))) + δ' := h_measure_by_defect
      _ < 2 * (δ_defect⁻¹ * target_defect) + δ' := h_defect_lt_target_two
      _ = ε :=  by field
    exact lt_of_le_of_lt (le_refl _) h_dist_lt_ε
  /-
  ### Step 4: Extract a subsequence with a.e. convergence in the `expInv` chart
  The L1 Cauchy property gives L1 convergence, hence convergence in measure. We then
  extract a subsequence converging almost surely pointwise in the `expInv` chart.
  -/
  have hZ_int (n : ℕ) : Integrable (Z (g n)) P := hZ_integrable (hg_meas n)
  let C : ℕ → Lp ℝ 1 P := fun n => (hZ_int n).toL1 (Z (g n))
  have hY_mem_L1' : CauchySeq C := by
    refine Metric.cauchySeq_iff'.2 <| fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := h_exp_cauchy ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm, ← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
    exact hN n N hn le_rfl
  obtain ⟨h, h_L1⟩  := cauchySeq_tendsto_of_complete hY_mem_L1'
  have h_step_mon : ∃ ns : ℕ → ℕ, StrictMono ns ∧
    ∀ᵐ ω ∂P, Tendsto (fun k => Z (g (ns k)) ω) atTop (𝓝 (h ω)) := by
    have h_in_measure : TendstoInMeasure P (fun n => C n) atTop h :=
       tendstoInMeasure_of_tendsto_Lp h_L1
    obtain ⟨ns, hns_mono, hns_tendsto⟩ := h_in_measure.exists_seq_tendsto_ae
    have hZR_eq_all : ∀ᵐ ω ∂P, ∀ n, C n ω = Z (g n) ω := by
      rw [ae_all_iff]
      intro n
      exact Integrable.coeFn_toL1 (hZ_integrable (hg_meas n))
    refine ⟨ns, hns_mono, ?_⟩
    filter_upwards [hZR_eq_all, hns_tendsto] with ω hω_eq hω_tend
    simpa [hω_eq] using hω_tend
  obtain ⟨ns, hns_mono, hns_tendsto⟩ := h_step_mon
  /-
  ### Step 5: Invert the transform and finish
  Use `logNeg` to recover an `ℝ≥0∞`-valued limit and transfer a.e. convergence back
  through `expInv`, yielding the Komlós limit for the convex averages.
  -/
  have h_step_lim : ∃ g_lim : Ω → ℝ≥0∞, Measurable g_lim ∧
      ∀ᵐ ω ∂P, Tendsto (fun k => g (ns k) ω) atTop (𝓝 (g_lim ω)) := by
    have h_range : ∀ᵐ ω ∂P, h ω ∈ Icc 0 1 := by
      filter_upwards [hns_tendsto] with ω hω_tend
      exact isClosed_Icc.mem_of_tendsto hω_tend (by filter_upwards with k using expInv_mem_Icc _)
    let g_lim0 : Ω → ℝ≥0∞ := fun ω => logNeg (h ω)
    have hg_lim0_aemeasurable : AEMeasurable g_lim0 P :=
      measurable_logNeg.comp_aemeasurable ((Lp.aestronglyMeasurable h).aemeasurable)
    have h_phi_eq : ∀ᵐ ω ∂P, expInv (g_lim0 ω) = h ω := by
      filter_upwards [h_range] with ω hω_range using expInv_logNeg_of_mem hω_range
    have hg_lim0_tendsto : ∀ᵐ ω ∂P, Tendsto (fun k => g (ns k) ω) atTop (𝓝 (g_lim0 ω)) := by
      filter_upwards [hns_tendsto, h_phi_eq] with ω hω_tend hω_eq
        using tendsto_of_expInv_tendsto (by rwa [hω_eq])
    have hg_lim_eq : hg_lim0_aemeasurable.mk g_lim0 =ᵐ[P] g_lim0 :=
      EventuallyEq.symm (AEMeasurable.ae_eq_mk hg_lim0_aemeasurable)
    refine ⟨hg_lim0_aemeasurable.mk g_lim0, hg_lim0_aemeasurable.measurable_mk, ?_⟩
    filter_upwards [hg_lim0_tendsto, hg_lim_eq] with ω hω_tend hω_eq
    rwa [hω_eq]
  obtain ⟨g_lim, mea_glim, tend_glim⟩ := h_step_lim
  refine ⟨g ∘ ns, g_lim, ?_, mea_glim, tend_glim⟩
  have h_ns_ge : ∀ n, n ≤ ns n := by
    refine Nat.rec (Nat.zero_le _) (fun n hn ↦ ?_)
    exact Nat.succ_le_of_lt (lt_of_le_of_lt hn (hns_mono (n.lt_succ_self)))
  intro N
  refine convexHull_mono (fun _ ↦ ?_) (hg_convex (ns N))
  simp only [mem_range, forall_exists_index]
  intro n nh
  use (ns N - N) + n
  rw [← Nat.add_sub_cancel' (h_ns_ge N)] at nh
  rwa [← add_assoc]
