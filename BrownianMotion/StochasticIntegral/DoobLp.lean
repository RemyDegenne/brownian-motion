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

open MeasureTheory Filter Topology TopologicalSpace Finset Set Function
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {ι α Ω E : Type*} [Preorder ι]

def lowerLimit (ι : Type*) [Preorder ι] : TopologicalSpace ι :=
  TopologicalSpace.generateFrom {s | ∃ i j, s = Set.Ico i j}

def WithLowerLimit (ι : Type*) := ι

instance : Preorder (WithLowerLimit ι) := ‹Preorder ι›
instance : TopologicalSpace (WithLowerLimit ι) := lowerLimit (WithLowerLimit ι)

theorem nhds_lowerLimit_eq (a : ι) :
    @nhds ι (TopologicalSpace.generateFrom {s | ∃ i j, s = Set.Ico i j}) a =
    ⨅ b > a, 𝓟 (Set.Ico a b) := by
  by_contra h_not_eq
  -- Since any interval [i, j) containing a must have i ≤ a and j > a, the infimum over all such
  -- intervals is the same as the infimum over the intervals [a, b) where b > a.
  have h_inf_eq : ⨅ (i : ι), ⨅ (j : ι), ⨅ (_ : i ≤ a ∧ a < j), 𝓟 (Set.Ico i j) =
    ⨅ (b : ι), ⨅ (_ : b > a), 𝓟 (Set.Ico a b) := by
    refine' le_antisymm _ _;
    · refine' le_iInf fun b => le_iInf fun hb => _;
      refine' le_trans ( iInf_le _ a ) _;
      refine' le_trans ( iInf_le _ b ) _;
      simp +decide [ hb ];
    · simp +decide [ iInf_le_iff ];
      intro i j hi hj b hb;
      exact Filter.mem_of_superset ( hb j hj ) ( Set.Ico_subset_Ico hi le_rfl );
  apply h_not_eq;
  rw [ ← h_inf_eq, TopologicalSpace.nhds_generateFrom ];
  refine' le_antisymm _ _;
  · refine' le_iInf fun i => le_iInf fun j => le_iInf fun hij => _;
    exact iInf₂_le _ ⟨ ⟨ hij.1, hij.2 ⟩, i, j, rfl ⟩;
  · refine' le_iInf₂ fun s hs => _;
    rcases hs with ⟨ has, ⟨ i, j, rfl ⟩ ⟩;
    refine' iInf_le_of_le i ( iInf_le_of_le j ( iInf_le_of_le ⟨ has.1, has.2 ⟩ le_rfl ) )

variable [TopologicalSpace ι] {f : ι → α} [hα : TopologicalSpace α]

theorem nhds_lowerLimit_eq_nhdsWithin_Ici (a : ι) :
    @nhds ι (TopologicalSpace.generateFrom {s | ∃ i j, s = Set.Ico i j}) a = 𝓝[≥] a := by
  sorry

variable {ι : Type*} [PartialOrder ι] [TopologicalSpace ι] {f : ι → α}

theorem continuous_of_rightContinuous (hf_cont : f.RightContinuous) :
    @Continuous ι α (TopologicalSpace.generateFrom {s : Set ι | ∃ (i j : ι), s = Set.Ico i j})
    hα f := by
  simp [RightContinuous, continuousWithinAt_Ioi_iff_Ici] at hf_cont
  simp_all [ContinuousWithinAt, continuous_iff_continuousAt, ContinuousAt,
    nhds_lowerLimit_eq_nhdsWithin_Ici]

variable {ι : Type*} [TopologicalSpace ι] {f : ι → α} [ConditionallyCompleteLattice α]
  [ClosedIicTopology α]

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
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖}, ‖X n ω‖ ∂P) := by
  sorry

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
  have cont (ω : Ω) : @Continuous (Iic n) ℝ (lowerLimit (Iic n)) inferInstance
    fun s ↦ ((Y · ω) ∘ (Subtype.val : Iic n → β)) s := by
    refine continuous_of_rightContinuous fun s ↦ ContinuousWithinAt.comp (t := univ) ?_ ?_ ?_
    · sorry
    · sorry
    · sorry
  have denseS : @Dense (Iic n) (TopologicalSpace.generateFrom
    {s : Set (Iic n) | ∃ i j, s = Set.Ico i j}) S := by sorry
  have (ω : Ω) : ⨆ i ≤ n, Y i ω
    = ⨆ s ≤ ⟨⟨n, le_rfl⟩, hn⟩, (Y ∘ Subtype.val ∘ Subtype.val: S → Ω → ℝ) s ω := by
    by_cases h : BddAbove (Set.range fun i : Iic n ↦ Y (↑i) ω)
    · calc
      _ = ⨆ s : Iic n, Y s ω := by
        have : Nonempty {i // i ≤ n} := Nonempty.intro ⟨n, le_rfl⟩
        have : Nonempty β := Nonempty.intro n
        exact ciSup_subtype' h (le_trans (Real.sSup_empty ▸ hnonneg n ω) (le_ciSup h ⟨n, le_rfl⟩))
      _ = ⨆ s : S, Y s ω := @continuous_supremum_dense ℝ inferInstance (Iic n)
        (TopologicalSpace.generateFrom {s | ∃ i j, s = Set.Ico i j}) (fun s ↦ Y (↑s) ω)
        inferInstance inferInstance S denseS (cont ω) h
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
