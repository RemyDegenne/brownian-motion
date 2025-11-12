import Mathlib.Probability.Process.Adapted

open Filter TopologicalSpace
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {ι Ω β : Type*} [LinearOrder ι] [TopologicalSpace ι] [MetrizableSpace ι]
  [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι]
  [TopologicalSpace β] [PseudoMetrizableSpace β]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → β} {τ : Ω → WithTop ι} {n : ι}

lemma Adapted.progMeasurable_of_rightContinuous {𝓕 : Filtration ι mΩ}
    (h : Adapted 𝓕 X) (hu_cont : ∀ ω a, ContinuousWithinAt (X · ω) (Set.Ioi a) a) :
    ProgMeasurable 𝓕 X :=
  sorry

end MeasureTheory
