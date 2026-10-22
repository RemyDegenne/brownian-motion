/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Martingale.Convergence

/-!
# Lévy's upward theorem in `L¹` for functions with values in a Banach space

Mathlib proves Lévy's upward theorem for real-valued functions: for a filtration `ℱ` indexed by
`ℕ` and an integrable function `g`, the conditional expectations `μ[g | ℱ n]` converge to
`μ[g | ⨆ n, ℱ n]` almost surely and in `L¹`. We extend the `L¹` convergence to functions with
values in a Banach space.

## Main statements

* `MeasureTheory.Integrable.tendsto_eLpNorm_condExp'`: if `g` is integrable and almost everywhere
  strongly measurable with respect to `⨆ n, ℱ n`, then `μ[g | ℱ n]` tends to `g` in `L¹`.
* `MeasureTheory.tendsto_eLpNorm_condExp'`: for any function `g`, `μ[g | ℱ n]` tends to
  `μ[g | ⨆ n, ℱ n]` in `L¹`.

These generalize `MeasureTheory.Integrable.tendsto_eLpNorm_condExp` and
`MeasureTheory.tendsto_eLpNorm_condExp`, which are about real-valued functions (and the first one
is about strongly measurable functions).

## Implementation notes

The set of functions `g` for which `μ[g | ℱ n]` tends to `g` in `L¹` is closed under addition and
under limits in `L¹`, and it contains the indicators `s.indicator fun _ ↦ c` of the sets `s` which
are measurable with respect to `⨆ n, ℱ n` by the real case. Hence it contains all integrable
functions which are almost everywhere strongly measurable with respect to `⨆ n, ℱ n`.

-/

public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {ℱ : Filtration ℕ mΩ} {g : Ω → E}

/-- If `μ[a j | ℱ n]` tends to `a j` in `L¹` as `n` tends to infinity for all `j`, and if `a j`
tends to `g` in `L¹` along a nontrivial filter, then `μ[g | ℱ n]` tends to `g` in `L¹`. -/
private lemma tendsto_eLpNorm_condExp_sub_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (hg : Integrable g μ) {a : ι → Ω → E} (ha_int : ∀ j, Integrable (a j) μ)
    (ha_lim : Tendsto (fun j ↦ eLpNorm (a j - g) 1 μ) l (𝓝 0))
    (ha : ∀ j, Tendsto (fun n ↦ eLpNorm (μ[a j | ℱ n] - a j) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (μ[g | ℱ n] - g) 1 μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by simp)
  obtain ⟨j, hj⟩ := (ha_lim.eventually_le_const hε3).exists
  obtain ⟨n₀, hn₀⟩ := ENNReal.tendsto_atTop_zero.1 (ha j) (ε / 3) hε3
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have h_eq : μ[g | ℱ n] - g =ᵐ[μ] μ[g - a j | ℱ n] + (μ[a j | ℱ n] - a j) + (a j - g) := by
    filter_upwards [condExp_sub hg (ha_int j) (ℱ n)] with ω hω
    simp only [Pi.sub_apply, Pi.add_apply, hω]
    abel
  rw [eLpNorm_congr_ae h_eq]
  calc eLpNorm (μ[g - a j | ℱ n] + (μ[a j | ℱ n] - a j) + (a j - g)) 1 μ
    _ ≤ eLpNorm (μ[g - a j | ℱ n]) 1 μ + eLpNorm (μ[a j | ℱ n] - a j) 1 μ
        + eLpNorm (a j - g) 1 μ :=
      (eLpNorm_add_le le_rfl).trans (add_le_add_left (eLpNorm_add_le le_rfl) _)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · exact (eLpNorm_condExp_le_eLpNorm _ le_rfl).trans ((eLpNorm_sub_comm ..).trans_le hj)
      · exact hn₀ n hn
    _ = ε := ENNReal.add_thirds ε

variable [IsFiniteMeasure μ]

/-- Lévy's upward theorem in `L¹` for the indicator of a set, which follows from the real case. -/
private lemma tendsto_eLpNorm_condExp_sub_indicator_const (c : E) {s : Set Ω}
    (hs : MeasurableSet[⨆ n, ℱ n] s) :
    Tendsto (fun n ↦ eLpNorm (μ[s.indicator (fun _ ↦ c) | ℱ n] - s.indicator (fun _ ↦ c)) 1 μ)
      atTop (𝓝 0) := by
  have hle : ⨆ n, ℱ n ≤ mΩ := iSup_le ℱ.le
  -- `u` is the real indicator of `s`, and `T` is the linear map `x ↦ x • c`
  let u : Ω → ℝ := s.indicator fun _ ↦ 1
  have hu_int : Integrable u μ := (integrable_const 1).indicator (hle s hs)
  have hu : Tendsto (fun n ↦ eLpNorm (μ[u | ℱ n] - u) 1 μ) atTop (𝓝 0) :=
    hu_int.tendsto_eLpNorm_condExp (stronglyMeasurable_const.indicator hs)
  let T : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ c
  have hT : T ∘ u = s.indicator fun _ ↦ c := by
    ext ω
    by_cases hω : ω ∈ s <;> simp [T, u, hω]
  have h_bound (n : ℕ) :
      eLpNorm (μ[s.indicator (fun _ ↦ c) | ℱ n] - s.indicator (fun _ ↦ c)) 1 μ
        ≤ ‖c‖₊ * eLpNorm (μ[u | ℱ n] - u) 1 μ := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
      (integrable_condExp.sub ((integrable_const c).indicator (hle s hs))).aestronglyMeasurable ?_ 1
    filter_upwards [T.comp_condExp_comm hu_int (m := ℱ n)] with ω hω
    rw [hT] at hω
    have h_eq : (μ[s.indicator (fun _ ↦ c) | ℱ n] - s.indicator fun _ ↦ c) ω
        = (μ[u | ℱ n] ω - u ω) • c := by
      rw [Pi.sub_apply, ← hω, ← congrFun hT ω, sub_smul]
      rfl
    rw [h_eq, enorm_smul, mul_comm, enorm_eq_nnnorm c, Pi.sub_apply]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) h_bound
  simpa using ENNReal.Tendsto.const_mul hu (.inr ENNReal.coe_ne_top)

/-- **Lévy's upward theorem**, `L¹` version, for a function with values in a Banach space: if `g`
is integrable and almost everywhere strongly measurable with respect to `⨆ n, ℱ n`, then the
conditional expectations `μ[g | ℱ n]` tend to `g` in `L¹`.

This generalizes `MeasureTheory.Integrable.tendsto_eLpNorm_condExp`, which is about real
functions which are strongly measurable with respect to `⨆ n, ℱ n`. -/
theorem Integrable.tendsto_eLpNorm_condExp' (hg : Integrable g μ)
    (hgmeas : AEStronglyMeasurable[⨆ n, ℱ n] g μ) :
    Tendsto (fun n ↦ eLpNorm (μ[g | ℱ n] - g) 1 μ) atTop (𝓝 0) := by
  refine MemLp.induction_stronglyMeasurable (iSup_le ℱ.le) ENNReal.one_ne_top
    (fun g ↦ Tendsto (fun n ↦ eLpNorm (μ[g | ℱ n] - g) 1 μ) atTop (𝓝 0)) ?_ ?_ ?_ ?_
    (memLp_one_iff_integrable.2 hg) hgmeas
  · exact fun c s hs _ ↦ tendsto_eLpNorm_condExp_sub_indicator_const c hs
  · intro f₁ f₂ _ hf₁ hf₂ _ _ hPf₁ hPf₂
    rw [memLp_one_iff_integrable] at hf₁ hf₂
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hPf₁.add hPf₂) (fun _ ↦ zero_le) fun n ↦ ?_
    have h_eq : μ[f₁ + f₂ | ℱ n] - (f₁ + f₂) =ᵐ[μ] (μ[f₁ | ℱ n] - f₁) + (μ[f₂ | ℱ n] - f₂) := by
      filter_upwards [condExp_add hf₁ hf₂ (ℱ n)] with ω hω
      simp only [Pi.sub_apply, Pi.add_apply, hω]
      abel
    rw [eLpNorm_congr_ae h_eq]
    exact eLpNorm_add_le le_rfl
  · refine IsSeqClosed.isClosed fun a f ha h_lim ↦ ?_
    have h_lim' : Tendsto (fun j ↦ (a j : Lp E 1 μ)) atTop (𝓝 (f : Lp E 1 μ)) :=
      (continuous_subtype_val.tendsto f).comp h_lim
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h_lim'
    exact tendsto_eLpNorm_condExp_sub_of_tendsto (L1.integrable_coeFn _)
      (fun j ↦ L1.integrable_coeFn _) h_lim' ha
  · intro f₁ f₂ hf _ hPf₁
    refine hPf₁.congr fun n ↦ eLpNorm_congr_ae ?_
    filter_upwards [condExp_congr_ae hf (m := ℱ n), hf] with ω hω hω'
    rw [Pi.sub_apply, Pi.sub_apply, hω, hω']

variable (ℱ) in
/-- **Lévy's upward theorem**, `L¹` version, for a function with values in a Banach space: the
conditional expectations `μ[g | ℱ n]` tend to `μ[g | ⨆ n, ℱ n]` in `L¹`.

This generalizes `MeasureTheory.tendsto_eLpNorm_condExp`, which is about real functions. -/
theorem tendsto_eLpNorm_condExp' (g : Ω → E) :
    Tendsto (fun n ↦ eLpNorm (μ[g | ℱ n] - μ[g | ⨆ n, ℱ n]) 1 μ) atTop (𝓝 0) := by
  have h : Tendsto (fun n ↦ eLpNorm (μ[μ[g | ⨆ n, ℱ n] | ℱ n] - μ[g | ⨆ n, ℱ n]) 1 μ) atTop
      (𝓝 0) :=
    integrable_condExp.tendsto_eLpNorm_condExp' stronglyMeasurable_condExp.aestronglyMeasurable
  refine h.congr fun n ↦ eLpNorm_congr_ae ?_
  have h_eq : μ[μ[g | ⨆ n, ℱ n] | ℱ n] =ᵐ[μ] μ[g | ℱ n] :=
    condExp_condExp_of_le (le_iSup _ n) (iSup_le ℱ.le)
  filter_upwards [h_eq] with ω hω
  rw [Pi.sub_apply, Pi.sub_apply, hω]

end MeasureTheory
