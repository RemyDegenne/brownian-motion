import Mathlib

open MeasureTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : T → Ω → E}

lemma modification_of_indistinduishable (h : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) :
    ∀ t, ∀ᵐ ω ∂P, X t ω = Y t ω := by
  intro t
  filter_upwards [h] with ω hω using hω t

variable [MeasurableSpace E]

lemma finite_distributions_eq {n : ℕ} {t : Fin n → T} (h : ∀ t, ∀ᵐ ω ∂P, X t ω = Y t ω) :
  Measure.map (fun ω m ↦ X (t m) ω) P = Measure.map (fun ω m ↦ Y (t m) ω) P := by
  have h': ∀ᵐ (ω : Ω) ∂P, ∀ (m : Fin n), X (t m) ω = Y (t m) ω := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    exact h (t i)
  refine Measure.map_congr ?_
  filter_upwards [h']
  simp_all only [Filter.eventually_all, implies_true, Set.mem_setOf_eq, Set.setOf_true,
    Filter.univ_mem]

lemma finite_distributions_eq_iff_same_law (hX : ∀ (t : T), Measurable (X t))
  (hY : ∀ (t : T), Measurable (Y t)) : (∀ n : ℕ, ∀ tn : Fin n → T,
  Measure.map (fun ω m ↦ X (tn m) ω) P = Measure.map (fun ω m ↦ Y (tn m) ω) P)
  ↔ (Measure.map (fun ω t ↦ X t ω) P = Measure.map (fun ω t ↦ Y t ω) P) := by
  constructor
  · sorry
  · intro h n tn
    let proj := fun t : T → E ↦ (fun n0 ↦ t (tn n0))
    have x: Measure.map (fun ω m ↦ X (tn m) ω) P
      = Measure.map proj (Measure.map (fun ω t ↦ X t ω) P) := by
      rw [Measure.map_map (f := fun ω t ↦ X t ω) (g := proj)]
      repeat measurability
    have y: Measure.map (fun ω m ↦ Y (tn m) ω) P
      = Measure.map proj (Measure.map (fun ω t ↦ Y t ω) P) := by
      rw [Measure.map_map]
      repeat measurability
    rw [x, y, h]

open TopologicalSpace in
lemma indistinduishable_of_modification [TopologicalSpace E] [TopologicalSpace T]
  [SeparableSpace T] [T2Space T] (hX: ∀ᵐ ω ∂P, Continuous fun t ↦ X t ω)
  (hY: ∀ᵐ ω ∂P, Continuous fun t ↦ Y t ω)
  (h : ∀ t, ∀ᵐ ω ∂P, X t ω = Y t ω) : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  let ⟨D, ⟨D_countable, D_dense⟩⟩ := ‹SeparableSpace T›
  have eq: (∀ t ∈ D, ∀ᵐ ω ∂P, X t ω = Y t ω) → ∀ᵐ ω ∂P, ∀ t ∈ D, X t ω = Y t ω := by
    intro ht
    sorry

  have h' : ∀ᵐ ω ∂P, ∀ t ∈ D, X t ω = Y t ω := by
    apply eq
    intro t ht
    exact h t

  have cont : ∀ᵐ ω ∂P, (∀ t ∈ D, X t ω = Y t ω) → (∀ t : T, X t ω = Y t ω) := by
    sorry

  sorry
