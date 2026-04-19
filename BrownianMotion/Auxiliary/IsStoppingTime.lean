module

public import Mathlib.Probability.Process.Stopping

@[expose] public section

namespace MeasureTheory

lemma stoppedProcess_min_eq_stoppedProcess {ι Ω E : Type*} [Nonempty ι] [LinearOrder ι]
    (X : ι → Ω → E) (τ : Ω → WithTop ι) {i j : ι} (hij : i ≤ j) :
    stoppedProcess X (fun ω ↦ min j (τ ω)) i = stoppedProcess X τ i := by
  simp [stoppedProcess_eq_stoppedValue, ← min_assoc, min_eq_left (WithTop.coe_le_coe.2 hij)]

end MeasureTheory
