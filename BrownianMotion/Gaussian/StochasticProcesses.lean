import Mathlib

open MeasureTheory

variable {T Ω E ι : Type*} [Finite ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : T → Ω → E}

lemma modification_of_indistinduishable (h : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) :
    ∀ t, X t =ᵐ[P] Y t := by
  intro t
  filter_upwards [h] with ω hω using hω t

variable [MeasurableSpace E]

lemma finite_distributions_eq {t : ι → T} (h : ∀ t, X t =ᵐ[P] Y t) :
    P.map (fun ω i ↦ X (t i) ω) = P.map (fun ω i ↦ Y (t i) ω) := by
  have h' : ∀ᵐ ω ∂P, ∀ i, X (t i) ω = Y (t i) ω := by
    rw [MeasureTheory.ae_all_iff]
    exact fun i ↦ h (t i)
  refine Measure.map_congr ?_
  filter_upwards [h']
  simp_all only [Filter.eventually_all, implies_true, Set.mem_setOf_eq, Set.setOf_true,
    Filter.univ_mem]

theorem aemeasurable_proj {α δ : Type*} {X : δ → Type*} {mX : ∀ a, MeasurableSpace (X a)}
    [MeasurableSpace α] {μ : Measure α} {g : α → Π a, X a} (hg : AEMeasurable g μ) (a : δ) :
    AEMeasurable (fun x ↦ g x a) μ := by
  use fun x ↦ hg.mk g x a, hg.measurable_mk.eval
  exact hg.ae_eq_mk.mono fun _ h ↦ congrFun h _

lemma coincide_on_cylinders (hX : AEMeasurable (fun ω t ↦ X t ω) P)
    (hY : AEMeasurable (fun ω t ↦ Y t ω) P)
    (h : ∀ n (tn : Fin n → T), P.map (fun ω m ↦ X (tn m) ω) = P.map (fun ω m ↦ Y (tn m) ω))
    (c : Set (T → E)) (hc : c ∈ measurableCylinders fun _ ↦ E) :
    P.map (fun ω t ↦ X t ω) c = P.map (fun ω t ↦ Y t ω) c := by
  simp only [mem_measurableCylinders] at hc
  obtain ⟨s, ⟨S, ⟨hS, cyl⟩⟩⟩ := hc
  let ⟨tn, tn_bij⟩ := Fintype.truncFinBijection s |>.out
  let ⟨tninv, ⟨_, htninv⟩⟩ := Function.bijective_iff_has_inverse.mp tn_bij
  let h' := h (Fintype.card { x // x ∈ s }) (fun x ↦ tn x)
  let c' : Set (Fin (Fintype.card { x // x ∈ s }) → E) :=
    (fun cmap ↦ fun n ↦ s.restrict cmap (tn n)) '' c
  rw [Function.RightInverse, Function.LeftInverse] at htninv
  have hXtn : AEMeasurable (fun ω m ↦ X (↑(tn m)) ω) P :=
    aemeasurable_pi_lambda (fun ω m ↦ X (↑(tn m)) ω) fun m ↦ (aemeasurable_proj hX) ↑(tn m)
  have hYtn : AEMeasurable (fun ω m ↦ Y (↑(tn m)) ω) P :=
    aemeasurable_pi_lambda (fun ω m ↦ Y (↑(tn m)) ω) fun m ↦ (aemeasurable_proj hY) ↑(tn m)
  have set1 : @MeasurableSet (T → E) MeasurableSpace.pi (s.restrict ⁻¹' S) := by measurability
  have set2 : MeasurableSet ((fun s_1 ↦ s_1 ∘ tninv) ⁻¹' S) := by measurability
  have mappings_eq (XY : T → Ω → E) :
      (fun ω t ↦ XY t ω) ⁻¹' (s.restrict ⁻¹' S)
      = (fun ω m ↦ XY (↑(tn m)) ω) ⁻¹' ((fun s_1 ↦ s_1 ∘ tninv) ⁻¹' S) := by
    simp_rw [Set.preimage]
    unfold Function.comp
    simp only [Set.mem_setOf_eq, Set.mem_preimage, htninv]
    subst cyl
    simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Fin.univ_val_map, Fintype.card_coe,
      Finset.univ_eq_attach,Finset.attach_val, Subtype.forall]
    rfl
  have X_on_cyl : P.map (fun ω t ↦ X t ω) (s.restrict ⁻¹' S)
      = P.map (fun ω m ↦ X (↑(tn m)) ω) (S.preimage (fun s ↦ s ∘ tninv)) := by
    rw [Measure.map_apply_of_aemeasurable hX set1, Measure.map_apply_of_aemeasurable hXtn set2,
        mappings_eq X]
  have Y_on_cyl : P.map (fun ω t ↦ Y t ω) (s.restrict ⁻¹' S)
      = P.map (fun ω m ↦ Y (↑(tn m)) ω) (S.preimage (fun s ↦ s ∘ tninv)) := by
    rw [Measure.map_apply_of_aemeasurable hY set1, Measure.map_apply_of_aemeasurable hYtn set2,
        mappings_eq Y]
  rw [cyl, cylinder, X_on_cyl, Y_on_cyl, h]

lemma finite_distributions_eq_iff_same_law (hX : AEMeasurable (fun t ω ↦ X ω t) P)
    (hY : AEMeasurable (fun t ω ↦ Y ω t) P) [IsProbabilityMeasure P] :
    (∀ n, ∀ tn : Fin n → T, P.map (fun ω m ↦ X (tn m) ω) = P.map (fun ω m ↦ Y (tn m) ω))
    ↔ (P.map (fun ω t ↦ X t ω) = P.map (fun ω t ↦ Y t ω)) := by
  constructor
  · intro h
    apply Measure.ext
    let cyls : Set (Set (T → E)) := measurableCylinders (fun t : T ↦ E)
    have pX : IsProbabilityMeasure (Measure.map (fun ω t ↦ X t ω) P) := by
      apply isProbabilityMeasure_map hX
    have pY : IsProbabilityMeasure (Measure.map (fun ω t ↦ Y t ω) P) := by
      apply isProbabilityMeasure_map hY
    apply MeasurableSpace.induction_on_inter
      (C := fun S hS ↦ ((P.map (fun ω t ↦ X t ω)) S = (P.map (fun ω t ↦ Y t ω)) S))
      (h_eq := by rw [generateFrom_measurableCylinders])
      (h_inter := isPiSystem_measurableCylinders)
      (empty := by simp) (basic := coincide_on_cylinders hX hY h)
    · intro t ht hXY
      repeat rw [MeasureTheory.prob_compl_eq_one_sub ht]
      simp [hXY]
    · intro f disj hf map
      repeat rw [measure_iUnion disj hf]
      simp [map]
  · intro h n tn
    let proj := fun t : T → E ↦ (fun n0 ↦ t (tn n0))
    have x : P.map (fun ω m ↦ X (tn m) ω) = Measure.map proj (P.map (fun ω t ↦ X t ω)) := by
      rw [AEMeasurable.map_map_of_aemeasurable (f := fun ω t ↦ X t ω) (g := proj)]
      repeat measurability
    have y : P.map (fun ω m ↦ Y (tn m) ω) = Measure.map proj (P.map (fun ω t ↦ Y t ω)) := by
      rw [AEMeasurable.map_map_of_aemeasurable]
      repeat measurability
    rw [x, y, h]

open TopologicalSpace in
omit [MeasurableSpace E] in
lemma indistinduishable_of_modification [TopologicalSpace E] [TopologicalSpace T]
    [SeparableSpace T] [T2Space E]
    (hX : ∀ᵐ ω ∂P, Continuous fun t ↦ X t ω) (hY : ∀ᵐ ω ∂P, Continuous fun t ↦ Y t ω)
    (h : ∀ t, X t =ᵐ[P] Y t) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  let ⟨D, ⟨D_countable, D_dense⟩⟩ := ‹SeparableSpace T›
  have eq : (∀ t ∈ D, X t =ᵐ[P] Y t) → ∀ᵐ ω ∂P, ∀ t ∈ D, X t ω = Y t ω := by
    intro ht
    exact (ae_ball_iff D_countable).mpr ht
  filter_upwards [hX, hY, eq (fun t ht ↦ h t)] with ω hX hY h t
  show (fun t ↦ X t ω) t = (fun t ↦ Y t ω) t
  rw [Continuous.ext_on D_dense hX hY ?_]
  rw [Set.EqOn]
  exact h
