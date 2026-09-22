module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

open Topology

variable {α β ι : Type*} {γ : ι → Type*} [Countable ι] [MeasurableSpace α] [MeasurableSpace β]
  [∀ n, MeasurableSpace (γ n)]

instance BorelSpace.sum [TopologicalSpace α] [TopologicalSpace β] [BorelSpace α] [BorelSpace β] :
    BorelSpace (α ⊕ β) := by
  refine ⟨le_antisymm ?_ ?_⟩
  · borelize (α ⊕ β)
    intro s hs
    obtain ⟨hl, hr⟩ := measurableSet_sum_iff.mp hs
    rw [← Set.image_preimage_inl_union_image_preimage_inr s]
    refine MeasurableSet.union ?_ ?_
    · exact IsOpenEmbedding.inl.measurableEmbedding.measurableSet_image' hl
    · exact IsOpenEmbedding.inr.measurableEmbedding.measurableSet_image' hr
  · refine MeasurableSpace.generateFrom_le fun t ht ↦ measurableSet_sum_iff.mpr ?_
    exact (isOpen_sum_iff.mp ht).imp IsOpen.measurableSet IsOpen.measurableSet

instance BorelSpace.sigma [∀ n, TopologicalSpace (γ n)] [∀ n, BorelSpace (γ n)] :
    BorelSpace ((n : ι) × γ n) := by
  refine ⟨le_antisymm ?_ ?_⟩
  · borelize ((n : ι) × γ n)
    intro s hs
    rw [← Set.iUnion_image_preimage_sigma_mk_eq_self s]
    refine MeasurableSet.iUnion fun n ↦ MeasurableEmbedding.measurableSet_image' ?_ ?_
    · exact IsOpenEmbedding.sigmaMk.measurableEmbedding
    · exact MeasurableSpace.measurableSet_iInf.mp hs n
  · refine MeasurableSpace.generateFrom_le fun t ht ↦ ?_
    exact MeasurableSpace.measurableSet_iInf.mpr fun n ↦ (isOpen_sigma_iff.mp ht n).measurableSet

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
