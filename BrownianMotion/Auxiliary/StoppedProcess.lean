module

public import BrownianMotion.Auxiliary.Indistinguishable
public import BrownianMotion.StochasticIntegral.Cadlag
public import Mathlib.Probability.Process.Stopping

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Nonempty ι]
  {τ : Ω → WithTop ι} {ω : Ω} {t : ι} {X Y : ι → Ω → E}

section stoppedProcess

variable [LinearOrder ι]

@[simp]
lemma stoppedProcess_of_eq_top (s : ι) (hτ : τ ω = ⊤) :
    stoppedProcess X τ s ω = X s ω := by
  simp [stoppedProcess, hτ]

@[simp]
lemma stoppedProcess_of_eq_coe (s : ι) (hτ : τ ω = t) :
    stoppedProcess X τ s ω = X (min s t) ω := by
  obtain h | h := le_total s t <;> simp [stoppedProcess, hτ, h]

lemma stoppedProcess_congr (h : X ≡ᵐ[P] Y) :
    stoppedProcess X τ ≡ᵐ[P] stoppedProcess Y τ := by
  filter_upwards [h] with ω h t
  simp [stoppedProcess, h]

section Topology

variable [TopologicalSpace ι] [OrderTopology ι] [TopologicalSpace E]

/-- If a trajectory of a process is continuous, then the corresponding trajectory of the stopped
process is also continuous. -/
lemma _root_.Continuous.stoppedProcess {ω : Ω} (hX : Continuous (X · ω)) (τ : Ω → WithTop ι) :
    Continuous (stoppedProcess X τ · ω) := by
  cases h : τ ω with
  | top => simpa [h]
  | coe t =>
    simp only [h, WithTop.coe_inj, stoppedProcess_of_eq_coe]
    fun_prop

/-- If a trajectory of a process is right-continuous,
then the corresponding trajectory of the stopped process is also right-continuous. -/
lemma _root_.IsRightContinuous.stoppedProcess (hX : IsRightContinuous (X · ω)) (τ : Ω → WithTop ι) :
    IsRightContinuous (stoppedProcess X τ · ω) := by
  cases h : τ ω with
  | top => simpa [h]
  | coe t =>
    simp only [h, WithTop.coe_inj, stoppedProcess_of_eq_coe]
    intro s
    obtain hst | hts := lt_or_ge s t
    · exact hX (min s t) |>.comp (f := (min · t)) (by fun_prop) (by grind [Set.MapsTo])
    · exact (continuous_const (y := X t ω)).continuousWithinAt.congr (by grind) (by grind)

/-- If a trajectory of a process is càdlàg, then the corresponding trajectory of the stopped
process is also càdlàg. -/
lemma _root_.IsCadlag.stoppedProcess (hX : IsCadlag (X · ω)) (τ : Ω → WithTop ι) :
    IsCadlag (stoppedProcess X τ · ω) := by
  cases h : τ ω with
  | top => simpa [h]
  | coe t =>
    refine ⟨hX.right_continuous.stoppedProcess τ, fun s ↦ ?_⟩
    simp only [h, WithTop.coe_inj, stoppedProcess_of_eq_coe]
    obtain hst | hts := le_or_gt s t
    · obtain ⟨l, hl⟩ := hX.left_limit s
      exact ⟨l, hl.congr' (Set.EqOn.eventuallyEq_nhdsWithin fun s hs ↦ by grind)⟩
    · refine ⟨X t ω, tendsto_const_nhds.congr' ?_⟩
      rw [eventuallyEq_nhdsWithin_iff, eventually_nhds_iff]
      exact ⟨Set.Ioi t, by grind, isOpen_Ioi, by grind⟩

end Topology

end stoppedProcess

namespace stoppedValue

@[simp] lemma add [Add E] {u v : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (u + v) τ = stoppedValue u τ + stoppedValue v τ := rfl

@[simp] lemma neg [Neg E] {u : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (-u) τ = -stoppedValue u τ := rfl

@[simp] lemma sub [Sub E] {u v : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (u - v) τ = stoppedValue u τ - stoppedValue v τ := rfl

end stoppedValue

end MeasureTheory
