module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

variable {α β ι : Type*} {γ : ι → Type*} [Countable ι] [MeasurableSpace α] [MeasurableSpace β]
  [∀ n, MeasurableSpace (γ n)]

instance BorelSpace.sum [TopologicalSpace α] [TopologicalSpace β] [BorelSpace α] [BorelSpace β] :
    BorelSpace (α ⊕ β) := by
  constructor
  rw [Sum.instMeasurableSpace]
  refine le_antisymm ?_ ?_
  · sorry
  · refine MeasurableSpace.generateFrom_le fun t ht ↦ ?_
    simp only [isOpen_sum_iff, Set.mem_ofPred_eq] at ht
    rw [measurableSet_sum_iff]
    exact ⟨ht.1.measurableSet, ht.2.measurableSet⟩

instance BorelSpace.sigma [∀ n, TopologicalSpace (γ n)] [∀ n, BorelSpace (γ n)] :
    BorelSpace ((n : ι) × γ n) := by
  sorry

/-- A sum of two standard Borel spaces is standard Borel. -/
instance StandardBorelSpace.sum [StandardBorelSpace α] [StandardBorelSpace β] :
    StandardBorelSpace (α ⊕ β) :=
  letI := upgradeStandardBorel α
  letI := upgradeStandardBorel β
  inferInstance

/-- A sum of countably many standard Borel spaces is standard Borel. -/
instance StandardBorelSpace.sigma_countable [∀ n, StandardBorelSpace (γ n)] :
    StandardBorelSpace ((n : ι) × γ n) :=
  letI := fun n => upgradeStandardBorel (γ n)
  inferInstance
