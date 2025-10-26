/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Adapted

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {E : Type*} [TopologicalSpace E]

section

variable [Preorder ι]

class RightContinuous (𝓕 : Filtration ι m) where
    IsRightContinuous (i : ι) := ⨅ j > i, 𝓕 j = 𝓕 i

class Filtration.UsualConditions [OrderBot ι] (𝓕 : Filtration ι m) (μ : Measure Ω := by volume_tac)
    extends RightContinuous 𝓕 where
    IsComplete ⦃s : Set Ω⦄ (hs : μ s = 0) : MeasurableSet[𝓕 ⊥] s

variable [OrderBot ι]

namespace Filtration

instance {𝓕 : Filtration ι m} {μ : Measure Ω} [u : UsualConditions 𝓕 μ] :
    @Measure.IsComplete Ω (𝓕 ⊥) (μ.trim <| 𝓕.le _) :=
  ⟨fun _ hs ↦ u.2 (measure_eq_zero_of_trim_eq_zero (Filtration.le 𝓕 ⊥) hs)⟩

lemma UsualConditions.measurableSet_of_null
    (𝓕 : Filtration ι m) {μ : Measure Ω} [u : UsualConditions 𝓕 μ] (s : Set Ω) (hs : μ s = 0) :
    MeasurableSet[𝓕 ⊥] s :=
  u.2 hs

def Predictable (𝓕 : Filtration ι m) : MeasurableSpace (ι × Ω) :=
    MeasurableSpace.generateFrom <|
      {s | ∃ A, MeasurableSet[𝓕 ⊥] A ∧ s = {⊥} ×ˢ A} ∪
      {s | ∃ i A, MeasurableSet[𝓕 i] A ∧ s = Set.Ioi i ×ˢ A}

-- Measurable or strongly measurable?
def IsPredictable (𝓕 : Filtration ι m) (u : ι → Ω → E) :=
    StronglyMeasurable[𝓕.Predictable] <| Function.uncurry u

example [MeasurableSpace E] (f : Ω → E) (hf : Measurable f) (s : Set Ω) :
    Measurable[Subtype.instMeasurableSpace] (fun (x : s) ↦ f x) := by
  exact hf.comp measurable_subtype_coe

end Filtration

end

namespace Filtration.IsPredictable

variable [LinearOrder ι] [OrderBot ι] [MeasurableSpace ι] [TopologicalSpace ι]
    [OpensMeasurableSpace ι] [OrderClosedTopology ι] [MeasurableSingletonClass ι]
    [MetrizableSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma progMeasurable {𝓕 : Filtration ι m} {u : ι → Ω → E} (h𝓕 : 𝓕.IsPredictable u) :
    ProgMeasurable 𝓕 u := by
  intro i
  refine Measurable.stronglyMeasurable ?_
  rw [IsPredictable, stronglyMeasurable_iff_measurable, measurable_iff_comap_le] at h𝓕
  rw [measurable_iff_comap_le, (by aesop : (fun (p : Set.Iic i × Ω) ↦ u (p.1) p.2)
      = Function.uncurry u ∘ (fun p ↦ (p.1, p.2))), ← MeasurableSpace.comap_comp]
  refine (MeasurableSpace.comap_mono h𝓕).trans ?_
  rw [Predictable, MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  rintro - ⟨-, (⟨s, hs, rfl⟩ | ⟨j, A, hA, rfl⟩), rfl⟩
  · rw [(by aesop : (fun (p : Set.Iic i × Ω) ↦ ((p.1 : ι), p.2)) ⁻¹' ({⊥} ×ˢ s) = {⊥} ×ˢ s)]
    · exact (measurableSet_singleton _).prod <| 𝓕.mono bot_le _ hs
  · by_cases hji : j ≤ i
    · rw [(_ : (fun (p : Set.Iic i × Ω) ↦ ((p.1 : ι), p.2)) ⁻¹' Set.Ioi j ×ˢ A
        = (Subtype.val ⁻¹' (Set.Ioc j i)) ×ˢ A)]
      · exact (measurable_subtype_coe measurableSet_Ioc).prod (𝓕.mono hji _ hA)
      · aesop
    · rw [(_ : (fun (p : Set.Iic i × Ω) ↦ ((p.1 : ι), p.2)) ⁻¹' Set.Ioi j ×ˢ A = ∅)]
      · simp only [MeasurableSet.empty]
      · ext p
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioi, Set.mem_empty_iff_false,
          iff_false, not_and]
        exact fun hj ↦ False.elim <| hji <| hj.le.trans p.1.2

lemma adapted {𝓕 : Filtration ι m} {u : ι → Ω → E} (h𝓕 : 𝓕.IsPredictable u) :
    Adapted 𝓕 u :=
  h𝓕.progMeasurable.adapted

lemma measurable_succ {𝓕 : Filtration ℕ m} {u : ℕ → Ω → E} (h𝓕 : 𝓕.IsPredictable u) (n : ℕ) :
    Measurable[𝓕 n] (u (n + 1)) := by
  sorry

end Filtration.IsPredictable

end MeasureTheory
