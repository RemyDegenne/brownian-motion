/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Martingale
import Mathlib.Probability.Martingale.OptionalStopping
import BrownianMotion.StochasticIntegral.Cadlag

/-! # Doob's Lᵖ inequality

-/

open MeasureTheory Filter Finset Set Function
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {ι α Ω E : Type*}

variable [TopologicalSpace ι] [hα : TopologicalSpace α] [ConditionallyCompleteLattice α]
  [ClosedIicTopology α] {f : ι → α}

theorem continuous_supremum_dense {S : Set ι} (hS : Dense S) (hf : Continuous f)
    (h : BddAbove (range f)) :
    ⨆ i, f i = ⨆ s : S, f s := by
  rw [← sSup_range, ← sSup_range]
  obtain (_ | _) := isEmpty_or_nonempty ι
  · simp [Set.range_eq_empty]
  have h₂ : Nonempty S := hS.nonempty.to_subtype
  refine (isLUB_csSup (range_nonempty f) h).unique ?_
  rw [← isLUB_iff_of_subset_of_subset_closure (image_subset_range f S)
    (hf.range_subset_closure_image_dense hS)]
  simpa [← Function.comp_def, range_comp] using
    isLUB_csSup (range_nonempty (fun x : S ↦ f x)) <| h.mono <| range_comp_subset_range ..

variable [PartialOrder ι]

theorem continuous_of_rightContinuous (hf_cont : RightContinuous f) :
    @Continuous ι α (TopologicalSpace.generateFrom {s : Set ι | ∃ (i j : ι), s = Set.Ico i j})
      hα f := by
  sorry

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} {s : Set ι}

/-- The restriction of a filtration to a subset is still a filtration. -/
def _root_.MeasureTheory.Filtration.subset (𝓕 : Filtration ι mΩ) :
    Filtration s mΩ where
  seq := 𝓕.seq ∘ Subtype.val
  mono' := fun _ _ h => 𝓕.mono' (Subtype.coe_le_coe.mpr h)
  le' := fun _ => 𝓕.le' _

/-- The restriction of a submartingale to a subset is still a submartingale. -/
def _root_.MeasureTheory.Submartingale.subset [LE E] (hsub : Submartingale X 𝓕 P) :
    Submartingale (X ∘ Subtype.val : s → Ω → E) 𝓕.subset P :=
  ⟨fun _ => hsub.1 _, fun _ _ h => hsub.2.1 _ _ h, fun _ => hsub.2.2 _⟩

variable [IsFiniteMeasure P] {Y : ι → Ω → ℝ}

theorem maximal_ineq_countable [Countable ι]
    (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω}, Y n ω ∂P) := by
  sorry

theorem maximal_ineq_norm_countable [Countable ι]
    (hsub : Martingale X 𝓕 P) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖}, ‖X n ω‖ ∂P) :=
  maximal_ineq_countable hsub.submartingale_norm (fun t ω => norm_nonneg (X t ω)) ε n

variable {β : Type*} {X : β → Ω → E} {Y : β → Ω → ℝ} [PartialOrder β] {𝓕 : Filtration β mΩ}
  [TopologicalSpace β] [SecondCountableTopology β]

theorem maximal_ineq (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) (n : β)
    (hY_cont : ∀ ω, RightContinuous (Y · ω)) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω}, Y n ω ∂P) := by
  obtain ⟨T, hT_countable, hT_dense⟩ := TopologicalSpace.exists_countable_dense (Iic n)
  let S := T ∪ {⟨n, le_rfl⟩}
  have hn : ⟨n, le_rfl⟩ ∈ S := by simp [S]
  have : Countable S := by
    rw [countable_coe_iff]
    exact Countable.union (Countable.mono (by simp) hT_countable) (by simp)
  have cont (ω : Ω) : @Continuous (Iic n) ℝ (TopologicalSpace.generateFrom {s | ∃ i j,
      s = Set.Ico i j}) inferInstance fun s ↦ Y (↑s) ω := by sorry
  have denseS : @Dense (Iic n) (TopologicalSpace.generateFrom
    {s : Set (Iic n) | ∃ i j, s = Set.Ico i j}) S := by sorry
  have (ω : Ω) : ⨆ i ≤ n, Y i ω
    = ⨆ s ≤ ⟨⟨n, le_rfl⟩, hn⟩, (Y ∘ Subtype.val ∘ Subtype.val: S → Ω → ℝ) s ω := by
    by_cases h: BddAbove (Set.range fun i : Iic n ↦ Y (↑i) ω)
    · calc
      _ = ⨆ s : Iic n, Y s ω := by
        have : Nonempty {i // i ≤ n} := Nonempty.intro ⟨n, le_rfl⟩
        have : Nonempty β := Nonempty.intro n
        exact ciSup_subtype' h (le_trans (Real.sSup_empty ▸ hnonneg n ω) (le_ciSup h ⟨n, le_rfl⟩))
      _ = ⨆ s : S, Y s ω := @continuous_supremum_dense (Iic n) ℝ (TopologicalSpace.generateFrom
        {s | ∃ i j, s = Set.Ico i j}) inferInstance inferInstance inferInstance (fun s ↦ Y (↑s) ω)
        S denseS (cont ω) h
      _ = ⨆ s : S, ⨆ (h : s ≤ ⟨⟨n, le_rfl⟩, hn⟩), Y s ω := by
        congr; ext x
        have : Nonempty (x ≤ ⟨⟨n, le_rfl⟩, hn⟩) := Nonempty.intro x.1.2
        exact ciSup_const.symm
      _ = ⨆ s : {z : S // z ≤ ⟨⟨n, le_rfl⟩, hn⟩}, Y s ω := by
        have : Nonempty {z : S // z ≤ ⟨⟨n, le_rfl⟩, hn⟩} := Nonempty.intro
          ⟨⟨⟨n, le_rfl⟩, hn⟩, le_rfl⟩
        have : Nonempty S := Nonempty.intro ⟨⟨n, le_rfl⟩, hn⟩
        refine ciSup_subtype' ?_ ?_
        · sorry
        · sorry
      _ = ⨆ s ≤ ⟨⟨n, le_rfl⟩, hn⟩, (Y ∘ Subtype.val ∘ Subtype.val: S → Ω → ℝ) s ω :=
        (cbiSup_eq_of_forall (ι := S) (fun s => s.1.2)).symm
    · sorry
  simpa [this] using maximal_ineq_countable (ι := S) hsub.subset.subset
    (fun _ _ => hnonneg _ _) ε ⟨⟨n, le_rfl⟩, hn⟩

-- ciSup_of_not_bddAbove

theorem maximal_ineq_norm (hsub : Martingale X 𝓕 P) (ε : ℝ≥0) (n : β)
    (hX_cont : ∀ ω, RightContinuous (X · ω)) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖}, ‖X n ω‖ ∂P) :=
  maximal_ineq hsub.submartingale_norm (fun t ω => norm_nonneg (X t ω)) ε n
    (fun ω a => (hX_cont ω a).norm)

end ProbabilityTheory
