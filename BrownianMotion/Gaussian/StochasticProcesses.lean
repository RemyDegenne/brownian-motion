import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.AEMeasurable

open MeasureTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : T → Ω → E}

lemma modification_of_indistinduishable (h : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) :
    ∀ t, X t =ᵐ[P] Y t := by
  intro t
  filter_upwards [h] with ω hω using hω t

variable [MeasurableSpace E]

lemma finite_distributions_eq {I : Finset T} (h : ∀ t, X t =ᵐ[P] Y t) :
    P.map (fun ω ↦ I.restrict (X · ω)) = P.map (fun ω ↦ I.restrict (Y · ω)) := by
  have h' : ∀ᵐ ω ∂P, ∀ (i : I), X i ω = Y i ω := by
    rw [MeasureTheory.ae_all_iff]
    exact fun i ↦ h i
  refine Measure.map_congr ?_
  filter_upwards [h'] with ω h using funext h

lemma isProjectiveMeasureFamily_map_restrict (hX : AEMeasurable (fun ω t ↦ X t ω) P) :
    IsProjectiveMeasureFamily (fun I ↦ P.map (fun ω ↦ I.restrict (X · ω))) := by
  intro I J hJI
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict₂ _).aemeasurable]
  · rfl
  · exact (Finset.measurable_restrict _).comp_aemeasurable hX

lemma isProjectiveLimit_map (hX : AEMeasurable (fun ω t ↦ X t ω) P) :
    IsProjectiveLimit (P.map (fun ω t ↦ X t ω)) (fun I ↦ P.map (fun ω ↦ I.restrict (X · ω))) := by
  rintro I
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict _).aemeasurable hX]
  rfl

lemma finite_distributions_eq_iff_same_law (hX : AEMeasurable (fun t ω ↦ X ω t) P)
    (hY : AEMeasurable (fun t ω ↦ Y ω t) P) [IsProbabilityMeasure P] :
    (∀ I : Finset T, P.map (fun ω ↦ I.restrict (X · ω)) = P.map (fun ω ↦ I.restrict (Y · ω)))
    ↔ P.map (fun ω t ↦ X t ω) = P.map (fun ω t ↦ Y t ω) := by
  refine ⟨fun h ↦ ?_, fun h I ↦ ?_⟩
  · have hX' := isProjectiveLimit_map hX
    simp_rw [h] at hX'
    exact hX'.unique (isProjectiveLimit_map hY)
  · have x : P.map (fun ω ↦ I.restrict (X · ω)) = (P.map (fun ω t ↦ X t ω)).map I.restrict := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
      rfl
    have y : P.map (fun ω ↦ I.restrict (Y · ω)) = (P.map (fun ω t ↦ Y t ω)).map I.restrict := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hY]
      rfl
    rw [x, y, h]

open TopologicalSpace in
omit [MeasurableSpace E] in
lemma indistinduishable_of_modification [TopologicalSpace E] [TopologicalSpace T]
    [SeparableSpace T] [T2Space E]
    (hX : ∀ᵐ ω ∂P, Continuous fun t ↦ X t ω) (hY : ∀ᵐ ω ∂P, Continuous fun t ↦ Y t ω)
    (h : ∀ t, X t =ᵐ[P] Y t) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  let ⟨D, D_countable, D_dense⟩ := ‹SeparableSpace T›
  have eq (ht : ∀ t ∈ D, X t =ᵐ[P] Y t) : ∀ᵐ ω ∂P, ∀ t ∈ D, X t ω = Y t ω :=
    (ae_ball_iff D_countable).mpr ht
  filter_upwards [hX, hY, eq (fun t ht ↦ h t)] with ω hX hY h t
  change (fun t ↦ X t ω) t = (fun t ↦ Y t ω) t
  rw [Continuous.ext_on D_dense hX hY h]
