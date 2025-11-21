import Mathlib.Probability.Process.Adapted

open Filter TopologicalSpace Function
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} [TopologicalSpace ι] [TopologicalSpace E]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → ℝ} {τ : Ω → WithTop ι} {i : ι}

/-- A stochastic process is right continuous if each of its realizations is right continuous. -/
abbrev _root_.Function.RightContinuous [PartialOrder ι] (X : ι → Ω → E) :=
  ∀ ω a, ContinuousWithinAt (X · ω) (Set.Ioi a) a

variable [LinearOrder ι] [TopologicalSpace ι] [MetrizableSpace ι]
  [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι]
  [PseudoMetrizableSpace E] {X : ι → Ω → E}

lemma Adapted.progMeasurable_of_rightContinuous {𝓕 : Filtration ι mΩ}
    (h : Adapted 𝓕 X) (hu_cont : RightContinuous X) :
    ProgMeasurable 𝓕 X :=
  sorry

end MeasureTheory
