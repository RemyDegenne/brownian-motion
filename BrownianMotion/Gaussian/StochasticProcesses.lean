import BrownianMotion.Auxiliary.MeasureTheory
import Mathlib.MeasureTheory.Constructions.Cylinders

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

lemma coincide_on_cylinders (hX : AEMeasurable (fun ω t ↦ X t ω) P)
    (hY : AEMeasurable (fun ω t ↦ Y t ω) P)
    (h : ∀ I : Finset T, P.map (fun ω ↦ I.restrict (X · ω)) = P.map (fun ω ↦ I.restrict (Y · ω)))
    (c : Set (T → E)) (hc : c ∈ measurableCylinders fun _ ↦ E) :
    P.map (fun ω t ↦ X t ω) c = P.map (fun ω t ↦ Y t ω) c := by
  rw [mem_measurableCylinders] at hc
  obtain ⟨s, S, hS, rfl⟩ := hc
  have hXtn : AEMeasurable (fun ω ↦ s.restrict (X · ω)) P :=
    aemeasurable_pi_lambda _ fun i ↦ hX.eval
  have hYtn : AEMeasurable (fun ω ↦ s.restrict (Y · ω)) P :=
    aemeasurable_pi_lambda _ fun i ↦ hY.eval
  have set1 : @MeasurableSet (T → E) MeasurableSpace.pi (s.restrict ⁻¹' S) :=
    Finset.measurable_restrict s hS
  have mappings_eq (XY : T → Ω → E) :
      (fun ω t ↦ XY t ω) ⁻¹' (s.restrict ⁻¹' S) = (fun ω ↦ s.restrict (XY · ω)) ⁻¹' S := by
    rw [← Set.preimage_comp]
    rfl
  have X_on_cyl : P.map (fun ω t ↦ X t ω) (s.restrict ⁻¹' S)
      = P.map (fun ω ↦ s.restrict (X · ω)) S := by
    rw [Measure.map_apply_of_aemeasurable hX set1, Measure.map_apply_of_aemeasurable hXtn hS,
      mappings_eq X]
  have Y_on_cyl : P.map (fun ω t ↦ Y t ω) (s.restrict ⁻¹' S)
      = P.map (fun ω ↦ s.restrict (Y · ω)) S := by
    rw [Measure.map_apply_of_aemeasurable hY set1, Measure.map_apply_of_aemeasurable hYtn hS,
      mappings_eq Y]
  rw [cylinder, X_on_cyl, Y_on_cyl, h]

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
