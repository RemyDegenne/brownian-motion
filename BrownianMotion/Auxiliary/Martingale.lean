/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Thomas Zhu
-/
module

public import BrownianMotion.Auxiliary.Filtration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.Probability.Martingale.Basic

/-!
# Properties of martingales and submartingales

This file contains auxiliary results about martingales and submartingales that are not yet in
Mathlib.

## Main statements

* `Martingale.indicator`, `Submartingale.indicator`: the product of a (sub)martingale with the
  indicator of a set that is measurable with respect to the first σ-algebra of the filtration is a
  (sub)martingale.
* `Martingale.indexComap`, `Submartingale.indexComap`: reindexing a (sub)martingale along a monotone
  map gives a (sub)martingale with respect to the filtration `Filtration.indexComap`.
* `Martingale.submartingale_convex_comp`: the composition of a martingale with a continuous convex
  function is a submartingale.
* `Martingale.submartingale_norm`: the norm of a martingale is a submartingale.
* `Submartingale.monotone_convex_comp`: the composition of a submartingale with a monotone
  continuous convex function is a submartingale.
* `Submartingale.norm_of_nonneg`: the norm of a nonnegative submartingale with values in a Banach
  lattice is a real submartingale.
* `Martingale.stoppedProcess_const`: a martingale stopped at a constant time is a martingale.
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω E : Type*} [Preorder ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

section Basic

/-- Each `X t` of a martingale `X` is strongly measurable with respect to the ambient σ-algebra. -/
lemma Martingale.stronglyMeasurable' (hX : Martingale X 𝓕 P) {t : ι} :
    StronglyMeasurable (X t) :=
  hX.stronglyMeasurable t |>.mono (𝓕.le t)

/-- The indicator of a `𝓕 ⊥`-measurable set times a martingale is a martingale. -/
lemma Martingale.indicator [CompleteSpace E] [OrderBot ι] {s : Set Ω}
    (hX : Martingale X 𝓕 P) (hs : MeasurableSet[𝓕 ⊥] s) :
    Martingale (fun t ↦ s.indicator (X t)) 𝓕 P :=
  ⟨fun i ↦ (hX.stronglyAdapted i).indicator (𝓕.mono bot_le _ hs), fun i j hij ↦
    (condExp_indicator (hX.integrable _) (𝓕.mono bot_le _ hs)).trans (hX.2 i j hij).indicator⟩

/-- The indicator of a `𝓕 ⊥`-measurable set times a submartingale is a submartingale. -/
lemma Submartingale.indicator [CompleteSpace E] [OrderBot ι] [Preorder E] {s : Set Ω}
    (hX : Submartingale X 𝓕 P) (hs : MeasurableSet[𝓕 ⊥] s) :
    Submartingale (fun t ↦ s.indicator (X t)) 𝓕 P := by
  refine ⟨fun i ↦ (hX.stronglyAdapted i).indicator (𝓕.mono bot_le _ hs), fun i j hij ↦ ?_,
    fun i ↦ (hX.integrable i).indicator (𝓕.le ⊥ _ hs)⟩
  filter_upwards [condExp_indicator (hX.integrable j) (𝓕.mono (bot_le : ⊥ ≤ i) _ hs),
    hX.2.1 i j hij] with ω h1 h2
  rw [h1]
  by_cases hω : ω ∈ s <;> simp [hω, h2]

/-- If `A - B` is a martingale, the increments of `A` and `B` up to `⊤` have the same integral on
every `𝓕 i`-measurable set. -/
lemma Martingale.setIntegral_sub_top_eq [OrderTop ι] [SigmaFiniteFiltration P 𝓕]
    {A B : ι → Ω → ℝ} (hA_int : ∀ t, Integrable (A t) P) (hB_int : ∀ t, Integrable (B t) P)
    (hAB : Martingale (A - B) 𝓕 P) (i : ι) {F : Set Ω} (hF : MeasurableSet[𝓕 i] F) :
    ∫ ω in F, (A ⊤ ω - A i ω) ∂P = ∫ ω in F, (B ⊤ ω - B i ω) ∂P := by
  have h := hAB.setIntegral_eq (le_top : i ≤ ⊤) hF
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hA_int i).integrableOn (hB_int i).integrableOn,
    integral_sub (hA_int ⊤).integrableOn (hB_int ⊤).integrableOn] at h
  rw [integral_sub (hA_int ⊤).integrableOn (hA_int i).integrableOn,
    integral_sub (hB_int ⊤).integrableOn (hB_int i).integrableOn]
  linarith

end Basic

section IndexComap

variable {ι' : Type*} [Preorder ι'] {f : ι' → ι}

/-- A martingale reindexed by a monotone map is a martingale for the reindexed filtration. -/
lemma Martingale.indexComap (hX : Martingale X 𝓕 P) (hf : Monotone f) :
    Martingale (X ∘ f) (𝓕.indexComap hf) P :=
  ⟨hX.stronglyAdapted.indexComap hf, fun _ _ hij ↦ hX.condExp_ae_eq (hf hij)⟩

/-- A submartingale reindexed by a monotone map is a submartingale for the reindexed filtration. -/
lemma Submartingale.indexComap [LE E] (hX : Submartingale X 𝓕 P) (hf : Monotone f) :
    Submartingale (X ∘ f) (𝓕.indexComap hf) P :=
  ⟨hX.stronglyAdapted.indexComap hf, fun _ _ hij ↦ hX.ae_le_condExp (hf hij),
    fun _ ↦ hX.integrable _⟩

end IndexComap

section ConvexComp

variable [CompleteSpace E] [SigmaFiniteFiltration P 𝓕] {φ : E → ℝ}

/-- The composition of a martingale with a continuous convex function is a submartingale. -/
lemma Martingale.submartingale_convex_comp (hX : Martingale X 𝓕 P)
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : Continuous φ)
    (hφ_int : ∀ t, Integrable (fun ω ↦ φ (X t ω)) P) :
    Submartingale (fun t ω ↦ φ (X t ω)) 𝓕 P := by
  refine ⟨fun i ↦ hφ_cont.comp_stronglyMeasurable (hX.stronglyAdapted i), fun i j hij ↦ ?_, hφ_int⟩
  calc
    _ =ᵐ[P] fun ω ↦ φ (P[X j | 𝓕 i] ω) := hX.condExp_ae_eq hij |>.fun_comp φ |>.symm
    _ ≤ᵐ[P] P[fun ω ↦ φ (X j ω) | 𝓕 i] :=
      hφ_cvx.map_condExp_le_univ (𝓕.le i) hφ_cont.lowerSemicontinuous (hX.integrable j) (hφ_int j)

/-- The norm of a martingale is a submartingale. -/
lemma Martingale.submartingale_norm (hX : Martingale X 𝓕 P) :
    Submartingale (fun t ω ↦ ‖X t ω‖) 𝓕 P :=
  hX.submartingale_convex_comp convexOn_univ_norm continuous_norm fun i ↦ (hX.integrable i).norm

/-- The composition of a submartingale with a monotone continuous convex function is a
submartingale. -/
lemma Submartingale.monotone_convex_comp [Preorder E] (hX : Submartingale X 𝓕 P)
    (hφ_mono : Monotone φ) (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : Continuous φ)
    (hφ_int : ∀ t, Integrable (fun ω ↦ φ (X t ω)) P) :
    Submartingale (fun t ω ↦ φ (X t ω)) 𝓕 P := by
  refine ⟨fun i ↦ hφ_cont.comp_stronglyMeasurable (hX.stronglyAdapted i), fun i j hij ↦ ?_, hφ_int⟩
  calc
    _ ≤ᵐ[P] fun ω ↦ φ (P[X j | 𝓕 i] ω) := (hX.ae_le_condExp hij).mono fun ω hω ↦ hφ_mono hω
    _ ≤ᵐ[P] P[fun ω ↦ φ (X j ω) | 𝓕 i] :=
      hφ_cvx.map_condExp_le_univ (𝓕.le i) hφ_cont.lowerSemicontinuous (hX.integrable j) (hφ_int j)

/-- The norm of a nonnegative submartingale with values in a Banach lattice is a real
submartingale. -/
lemma Submartingale.norm_of_nonneg [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
    (hX : Submartingale X 𝓕 P) (hX_nonneg : 0 ≤ X) :
    Submartingale (fun t ω ↦ ‖X t ω‖) 𝓕 P := by
  refine ⟨fun i ↦ (hX.stronglyAdapted i).norm, fun i j hij ↦ ?_, fun i ↦ (hX.integrable i).norm⟩
  calc (fun ω ↦ ‖X i ω‖)
    _ ≤ᵐ[P] fun ω ↦ ‖P[X j | 𝓕 i] ω‖ := (hX.ae_le_condExp hij).mono fun ω hω ↦ by
      refine norm_le_norm_of_abs_le_abs ?_
      rwa [abs_of_nonneg (hX_nonneg i ω), abs_of_nonneg ((hX_nonneg i ω).trans hω)]
    _ ≤ᵐ[P] P[fun ω ↦ ‖X j ω‖ | 𝓕 i] :=
      convexOn_univ_norm.map_condExp_le_univ (𝓕.le i) continuous_norm.lowerSemicontinuous
        (hX.integrable j) (hX.integrable j).norm

end ConvexComp

section LinearOrder

variable {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E}
  {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration P 𝓕]

/-- A martingale stopped at a constant time is a martingale. -/
lemma Martingale.stoppedProcess_const (hX : Martingale X 𝓕 P) (s : ι) :
    Martingale (stoppedProcess X fun _ ↦ (s : WithTop ι)) 𝓕 P := by
  have h_eq (i : ι) : stoppedProcess X (fun _ ↦ (s : WithTop ι)) i = X (min i s) := by
    ext ω
    simp only [stoppedProcess, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
  refine ⟨fun i ↦ h_eq i ▸ (hX.stronglyAdapted (min i s)).mono (𝓕.mono (min_le_left _ _)),
    fun i j hij ↦ ?_⟩
  rw [h_eq, h_eq]
  rcases le_total j s with hjs | hsj
  · simpa only [min_eq_left hjs, min_eq_left (hij.trans hjs)] using hX.2 i j hij
  rcases le_total i s with his | hsi
  · simpa only [min_eq_right hsj, min_eq_left his] using hX.2 i s his
  · simp only [min_eq_right hsj, min_eq_right hsi]
    exact (condExp_of_stronglyMeasurable (𝓕.le i) ((hX.stronglyAdapted s).mono (𝓕.mono hsi))
      (hX.integrable s)).eventuallyEq

end LinearOrder

end MeasureTheory
