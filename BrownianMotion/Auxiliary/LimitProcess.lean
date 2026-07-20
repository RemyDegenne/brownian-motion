/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import BrownianMotion.Auxiliary.Indistinguishable
public import Mathlib.Probability.Process.Filtration

public section

open MeasureTheory Filter
open scoped Topology

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y Z : ι → Ω → E}
  [LinearOrder ι] [Nonempty ι] {𝓕 : Filtration ι mΩ}

section Basic

variable [TopologicalSpace E] [Zero E] [T2Space E]

lemma limitProcess_ae_eq {X : ι → Ω → E} {g : Ω → E}
    (mg : StronglyMeasurable[⨆ n, 𝓕 n] g) (hg : ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (g ω))) :
    𝓕.limitProcess X P =ᵐ[P] g := by
  have : ∃ g, StronglyMeasurable[⨆ n, 𝓕 n] g ∧ ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (g ω)) :=
    ⟨g, mg, hg⟩
  rw [Filtration.limitProcess, dif_pos this]
  filter_upwards [hg, this.choose_spec.2] with ω h1 h2 using tendsto_nhds_unique h2 h1

lemma limitProcess_congr {X Y : ι → Ω → E} (hXY : X ≡ᵐ[P] Y) :
    𝓕.limitProcess X P =ᵐ[P] 𝓕.limitProcess Y P := by
  rw [Filtration.limitProcess]
  split_ifs with h
  · symm
    apply limitProcess_ae_eq h.choose_spec.1
    filter_upwards [h.choose_spec.2, hXY] with ω h1 h2 using h1.congr h2
  rw [Filtration.limitProcess, dif_neg]
  contrapose h
  obtain ⟨g, hg1, hg2⟩ := h
  refine ⟨g, hg1, ?_⟩
  filter_upwards [hg2, hXY] with ω h1 h2 using h1.congr (fun t ↦ (h2 t).symm)

lemma limitProcess_const (c : E) :
    𝓕.limitProcess (fun _ _ ↦ c) P =ᵐ[P] (fun _ ↦ c) := by
  apply limitProcess_ae_eq stronglyMeasurable_const (by simp)

lemma limitProcess_zero :
    𝓕.limitProcess (0 : ι → Ω → E) P =ᵐ[P] 0 := limitProcess_const 0

end Basic

variable [NormedAddCommGroup E]

@[to_fun limitProcess_fun_smul]
lemma limitProcess_smul [NormedSpace ℝ E] (X : ι → Ω → E) (c : ℝ) :
    𝓕.limitProcess (c • X) P =ᵐ[P] c • 𝓕.limitProcess X P := by
  obtain rfl | hc := eq_or_ne c 0
  · simp [limitProcess_zero]
  nth_rw 2 [Filtration.limitProcess]
  split_ifs with h
  · apply limitProcess_ae_eq (h.choose_spec.1.const_smul c)
    filter_upwards [h.choose_spec.2] with ω h1 using h1.const_smul c
  rw [Filtration.limitProcess, dif_neg]
  · simp
  contrapose h
  obtain ⟨g, hg1, hg2⟩ := h
  refine ⟨c⁻¹ • g, hg1.const_smul _, ?_⟩
  filter_upwards [hg2] with ω h1
  convert h1.const_smul c⁻¹
  · simp [hc]
  · simp

@[to_fun limitProcess_fun_neg]
lemma limitProcess_neg (X : ι → Ω → E) :
    𝓕.limitProcess (-X) P =ᵐ[P] -𝓕.limitProcess X P := by
  nth_rw 2 [Filtration.limitProcess]
  split_ifs with h
  · apply limitProcess_ae_eq h.choose_spec.1.neg
    filter_upwards [h.choose_spec.2] with ω h1 using h1.neg
  rw [Filtration.limitProcess, dif_neg]
  · simp
  contrapose h
  obtain ⟨g, hg1, hg2⟩ := h
  refine ⟨-g, hg1.neg, ?_⟩
  filter_upwards [hg2] with ω h1
  simpa using h1.neg
