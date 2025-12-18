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

end MeasureTheory
