/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.Martingale
import Mathlib.Probability.Martingale.OptionalStopping

/-! # Doob's Lᵖ inequality

-/

open MeasureTheory Filter Finset
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
  {Y : ι → Ω → ℝ} [IsFiniteMeasure P]

section Countable

/-- Auxiliary lemma for `maximal_ineq_countable` where the index set is a Finset. -/
lemma maximal_ineq_finset (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) {n : ι}
    {J : Finset ι} (hJn : ∀ i ∈ J, i ≤ n) (hnJ : n ∈ J) :
    ε • P {ω | (ε : ℝ) ≤ J.sup' ⟨n, hnJ⟩ fun i ↦ Y i ω} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ J.sup' ⟨n, hnJ⟩ fun i ↦ Y i ω}, Y n ω ∂P) := by
  -- Convert to ℕ-indexed submartingale defined by (Y(j₁), ⋯, Y(jₘ), Y(n), Y(n), ⋯)
  -- where J = {j₁, ⋯, jₘ, n}, and j₁ < ⋯ < jₘ = n
  classical
  let toι (k : ℕ) : ι := if hn : k < #J then J.orderEmbOfFin rfl ⟨k, hn⟩ else n
  have toι_mono : Monotone toι := fun k l hkl ↦ by
    unfold toι
    split_ifs with hk hl hl
    exacts [(J.orderEmbOfFin rfl).monotone hkl, hJn _ (orderEmbOfFin_mem ..), by omega, le_refl _]
  have hcongr (ω : Ω) : J.sup' ⟨n, hnJ⟩ (fun i ↦ Y i ω) =
      (range (#J + 1)).sup' nonempty_range_add_one fun k ↦ Y (toι k) ω := by
    unfold toι
    apply le_antisymm
    · refine sup'_le _ _ fun i hi ↦ ?_
      refine le_sup'_of_le _ (b := ((J.orderIsoOfFin rfl).symm ⟨i, hi⟩ : ℕ)) ?_ ?_
      · simp
        omega
      · simp [orderEmbOfFin]
    · refine sup'_le _ _ fun k hk ↦ ?_
      apply le_sup' fun i ↦ Y i ω
      split_ifs
      exacts [orderEmbOfFin_mem .., hnJ]
  calc
    _ = ε • P {ω | (ε : ℝ) ≤ (range (#J + 1)).sup' nonempty_range_add_one fun k ↦ Y (toι k) ω} := by
      simp_rw [hcongr]
    _ ≤ ENNReal.ofReal
      (∫ ω in {ω | (ε : ℝ) ≤ (range (#J + 1)).sup' nonempty_range_add_one fun k ↦ Y (toι k) ω},
        Y n ω ∂P) := by
      convert maximal_ineq (hsub.indexComap toι_mono) (fun _ ↦ hnonneg _) #J
      simp [toι]
    _ = _ := by
      congr! with ω
      simp_rw [hcongr]

variable [Countable ι]

lemma _root_.Finset.measurable_sup'' {α : Type*} {m : MeasurableSpace α} {δ : Type*}
    [MeasurableSpace δ] [SemilatticeSup α] [MeasurableSup₂ α] {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {f : ι → δ → α} (hf : ∀ n ∈ s, Measurable (f n)) :
    Measurable (fun x => s.sup' hs fun k => f k x) := by
  convert Finset.measurable_sup' hs hf
  simp

#check Monotone.measure_iUnion
#check tendsto_setIntegral_of_monotone
/-- **Doob's maximal inequality** for a countable index set. -/
theorem maximal_ineq_countable (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω}, Y n ω ∂P) := by
  have : Nonempty ι := ⟨n⟩
  obtain ⟨f : ℕ → ι, hf⟩ := exists_surjective_nat ι
  let J (k : ℕ) : Finset ι := insert n ((range k).image f |>.filter (· ≤ n))
  have hJn (k) : ∀ i ∈ J k, i ≤ n := by simp [J]
  have hnJ (k) : n ∈ J k := by simp [J]
  have hJmono {k l : ℕ} (hkl : k ≤ l) : J k ⊆ J l := by
    unfold J
    gcongr
    exact image_mono _ (range_mono hkl)
  -- Monotone convergence works here but dominated convergence seems easier
  have htendsto (x : Ω → ℝ) (hx : Integrable x P) : Tendsto
      (fun k ↦ ∫ ω in {ω | (ε : ℝ) ≤ (J k).sup' ⟨n, hnJ k⟩ fun i ↦ Y i ω}, x ω ∂P) atTop
      (𝓝 <| ∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω}, x ω ∂P) := by
    convert tendsto_setIntegral_of_monotone _ _ hx.integrableOn
    · ext ω
      simp
      sorry
    · infer_instance
    · intro k
      apply measurableSet_le measurable_const
      apply Finset.measurable_sup'' ⟨n, hnJ k⟩ fun i _ ↦
        (hsub.stronglyMeasurable i).measurable.mono (𝓕.le _) (le_refl _)
    · intro k l hkl
      simpa using fun ω i hi h ↦ ⟨i, hJmono hkl hi, h⟩

theorem maximal_ineq_norm_countable [Countable ι] [IsFiniteMeasure P]
    (hsub : Martingale X 𝓕 P) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖}, ‖X n ω‖ ∂P) := by
  sorry

end Countable

variable [TopologicalSpace ι] [SecondCountableTopology ι]

theorem maximal_ineq (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω}, Y n ω ∂P) := by
  obtain ⟨T, hT_countable, hT_dense⟩ := TopologicalSpace.exists_countable_dense ι
  sorry

theorem maximal_ineq_norm (hsub : Martingale X 𝓕 P) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖}, ‖X n ω‖ ∂P) := by
  sorry

end ProbabilityTheory
