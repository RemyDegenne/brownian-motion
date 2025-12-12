import Mathlib.Probability.Process.Stopping

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

variable [Nonempty ι] [LinearOrder ι]

@[simp] lemma stoppedProcess_const {β : Type*} {u₀ : Ω → β} {τ : Ω → WithTop ι} :
    stoppedProcess (fun _ ↦ u₀) τ = fun _ ↦ u₀ := rfl

@[simp] lemma stoppedProcess_neg {β : Type*} [Neg β] {u : ι → Ω → β} {τ : Ω → WithTop ι} :
    stoppedProcess (-u) τ = -stoppedProcess u τ := rfl

@[simp] lemma stoppedProcess_add {β : Type*} [Add β] {u v : ι → Ω → β} {τ : Ω → WithTop ι} :
    stoppedProcess (u + v) τ = stoppedProcess u τ + stoppedProcess v τ := rfl

@[simp] lemma stoppedProcess_sub {β : Type*} [Sub β] {u v : ι → Ω → β} {τ : Ω → WithTop ι} :
    stoppedProcess (u - v) τ = stoppedProcess u τ - stoppedProcess v τ := rfl

@[simp] lemma stoppedProcess_const_smul {β : Type*} [SMul ℝ β] (c : ℝ) {u : ι → Ω → β}
    {τ : Ω → WithTop ι} : stoppedProcess (c • u) τ = c • stoppedProcess u τ := rfl

@[simp] lemma stoppedProcess_const_bot [OrderBot ι] {E} (X : ι → Ω → E) :
    stoppedProcess X (fun _ ↦ ⊥) = fun _ ↦ X ⊥ := by
  ext; simp [stoppedProcess, ← WithTop.coe_bot]

@[simp] lemma stoppedProcess_const_top {E} (X : ι → Ω → E) :
    stoppedProcess X (fun _ ↦ ⊤) = X := by ext; simp [stoppedProcess]

lemma stoppedProcess_indicator_comm {β : Type*} [Zero β] {u : ι → Ω → β}
    {τ : Ω → WithTop ι} {s : Set Ω} (i : ι) :
    stoppedProcess (fun i ↦ s.indicator (u i)) τ i
      = s.indicator (stoppedProcess u τ i) := by
  ext ω
  rw [Set.indicator]
  split_ifs with hω
  · rw [stoppedProcess, Set.indicator_of_mem hω, stoppedProcess]
  · rw [stoppedProcess, Set.indicator_of_notMem hω]

lemma stoppedProcess_indicator_comm' {β : Type*} [Zero β] {u : ι → Ω → β}
    {τ : Ω → WithTop ι} {s : Set Ω} :
    stoppedProcess (fun i ↦ s.indicator (u i)) τ
      = fun i ↦ s.indicator (stoppedProcess u τ i) := by
  ext i ω
  rw [stoppedProcess_indicator_comm]

theorem _root_.MeasureTheory.stoppedValue_stoppedProcess_apply
    {β : Type*} {ω : Ω} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} (hω : σ ω ≠ ⊤) :
    stoppedValue (stoppedProcess u τ) σ ω = stoppedValue u (fun ω ↦ min (σ ω) (τ ω)) ω := by
  simp only [stoppedValue_stoppedProcess, ne_eq, hω, not_false_eq_true, reduceIte]

@[simp]
theorem _root_.MeasureTheory.stoppedProcess_stoppedProcess
    {β : Type*} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (σ ⊓ τ) := by
  ext i ω
  rw [stoppedProcess, stoppedProcess, stoppedProcess]
  by_cases hτ : τ ω = ⊤
  · simp only [hτ, le_top, inf_of_le_left, WithTop.untopD_coe, Pi.inf_apply]
  by_cases hσ : σ ω = ⊤
  · simp only [hσ, le_top, inf_of_le_left, WithTop.untopD_coe, Pi.inf_apply, inf_of_le_right]
  by_cases hστ : σ ω ≤ τ ω
  · rw [min_eq_left, WithTop.untopA_eq_untop (lt_of_le_of_lt ((min_le_right _ _).trans hστ) <|
        WithTop.lt_top_iff_ne_top.2 hτ).ne, WithTop.coe_untop]
    · simp only [Pi.inf_apply, hστ, inf_of_le_left]
    · refine le_trans ?_ hστ
      rw [WithTop.untopA_eq_untop (lt_of_le_of_lt ((min_le_right _ _).trans hστ) <|
        WithTop.lt_top_iff_ne_top.2 hτ).ne, WithTop.coe_untop]
      exact min_le_right _ _
  · nth_rewrite 2 [WithTop.untopA_eq_untop ]
    · rw [WithTop.coe_untop, min_assoc]
      rfl
    · exact (lt_of_le_of_lt (min_le_right _ _) <| WithTop.lt_top_iff_ne_top.2 hσ).ne

theorem _root_.MeasureTheory.stoppedProcess_stoppedProcess'
    {β : Type*} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (fun ω ↦ min (σ ω) (τ ω)) := by
  simp; rfl

theorem _root_.MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
    {β : Type*} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} (h : σ ≤ τ) :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u σ := by
  rw [stoppedProcess_stoppedProcess, inf_of_le_left h]

theorem _root_.MeasureTheory.stoppedProcess_stoppedProcess_of_le_left
    {β : Type*} {u : ι → Ω → β} {τ σ : Ω → WithTop ι} (h : τ ≤ σ) :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u τ := by
  rw [stoppedProcess_stoppedProcess, inf_of_le_right h]

theorem _root_.MeasureTheory.stoppedProcess_eq_stoppedValue_apply
    {β : Type*} {u : ι → Ω → β} {τ : Ω → WithTop ι} (i : ι) (ω : Ω) :
    stoppedProcess u τ i ω = stoppedValue u (fun ω ↦ min i (τ ω)) ω := rfl

end MeasureTheory
