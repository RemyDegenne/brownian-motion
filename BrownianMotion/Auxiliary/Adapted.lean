import Mathlib.Probability.Process.Adapted

open Filter TopologicalSpace
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {ι Ω β : Type*} [TopologicalSpace ι] [TopologicalSpace β]

/-- A stochastic process is right continuous if each of its realizations is right continuous. -/
abbrev _root_.Function.RightContinuous [PartialOrder ι] (X : ι → Ω → β) :=
  ∀ ω a, ContinuousWithinAt (X · ω) (Set.Ioi a) a

variable [LinearOrder ι] [MetrizableSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι]
  [OpensMeasurableSpace ι] [PseudoMetrizableSpace β]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → β} {τ : Ω → WithTop ι} {n : ι}

lemma Adapted.progMeasurable_of_rightContinuous {𝓕 : Filtration ι mΩ}
    (h : Adapted 𝓕 X) (hu_cont : Function.RightContinuous X) :
    ProgMeasurable 𝓕 X :=
  sorry

end MeasureTheory
