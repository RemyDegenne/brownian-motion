/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Debut.Basic

/-!
# Measurable section theorems
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {x y : Ω}

namespace MeasureTheory

instance : CompactIccSpace ℝ≥0 := by
  constructor
  intro a b
  sorry

lemma infClosed_insert_empty_Icc {ι : Type} [LinearOrder ι] :
    InfClosed (insert ∅ {t | ∃ a b : ι, Set.Icc a b = t}) := by
  intro s hs t ht
  cases hs with
  | inl hs => simp [hs]
  | inr hs =>
    cases ht with
    | inl ht => simp [ht]
    | inr ht =>
      obtain ⟨a₁, b₁, rfl⟩ := hs
      obtain ⟨a₂, b₂, rfl⟩ := ht
      refine Set.mem_insert_of_mem _ ?_
      simp only [Set.inf_eq_inter, Set.mem_setOf_eq]
      exact ⟨a₁ ⊔ a₂, b₁ ⊓ b₂, Set.Icc_inter_Icc.symm⟩

lemma isPavingAnalytic_measurableSet_swap {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {s : Set (𝓧 × Ω)}
    (hs : IsPavingAnalytic MeasurableSet s) :
    IsPavingAnalytic MeasurableSet (Prod.swap '' s) := by
  obtain ⟨𝓚, h𝓚, q, hq_empty, hq_compact, t, ht_mem, h_eq⟩ := hs
  refine ⟨𝓚, h𝓚, q, hq_empty, hq_compact, Prod.map Prod.swap id '' t, ?_, ?_⟩
  · rw [memProdSigmaDelta_iff] at ht_mem ⊢
    obtain ⟨A, K, hA, hK, rfl⟩ := ht_mem
    refine ⟨fun n m ↦ Prod.swap '' (A n m), K, fun n m ↦ ?_, hK, ?_⟩
    · change MeasurableSet (Prod.swap '' A n m)
      rw [Set.image_swap_eq_preimage_swap]
      exact MeasurableSet.preimage (hA n m) (by fun_prop)
    · rw [Set.image_iInter]
      swap; · exact Prod.swap_bijective.prodMap Function.bijective_id
      simp_rw [Set.image_iUnion]
      congr with n x
      simp
      grind
  · ext; simp; grind

lemma nullMeasurable_debut {s : Set (ℝ≥0 × Ω)} (hs : MeasurableSet s) (u : ℝ≥0) :
    NullMeasurable (debut s u) μ := by
  suffices ∀ (r : ℝ≥0), NullMeasurableSet {ω | debut s u ω < r} μ by
    -- todo: NullMeasurable version of measurable_of_Iio ? also deal with r not ⊤
    sorry
  intro r
  convert MeasurableSet.nullMeasurableSet_debut_lt (P := μ) hs u r
  convert instClosedIciTopology
  convert OrderTopology.to_orderClosedTopology
  exact NNReal.instOrderTopology

lemma todo' {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) (a : ℝ≥0∞)
    (ha : a < μ {ω | debut s 0 ω ≠ ⊤}) :
    ∃ τ : Ω → WithTop ℝ≥0, NullMeasurable τ μ ∧ (∀ ω, τ ω < ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      a ≤ μ {ω | τ ω ≠ ⊤} ∧ μ {ω | τ ω ≠ ⊤} ≤ μ {ω | debut s 0 ω ≠ ⊤} := by
  let I : Capacity (memFiniteUnion
      (memProd MeasurableSet (insert ∅ {t | ∃ a b, Set.Icc a b = t}))) :=
    μ.capacity.comp_fst MeasurableSet.empty (fun _ hs _ ht ↦  MeasurableSet.union hs ht) (by simp)
      (isCompactSystem_insert_empty_Icc ℝ≥0)
  have I_apply (t : Set (Ω × ℝ≥0)) : I t = μ {ω | ∃ u, (ω, u) ∈ t} := by
    rw [μ.capacity.comp_fst_apply, μ.capacity_apply]
    congr
    ext
    simp
  have I_apply_eq_debut (t : Set (Ω × ℝ≥0)) : I t = μ {ω | debut (Prod.swap '' t) 0 ω ≠ ⊤} := by
    rw [I_apply]
    congr with ω
    contrapose!
    have h_eq_iff := debut_eq_top_iff (E := Prod.swap '' t) (n := 0) (ω := ω)
    simp only [ge_iff_le, Set.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq,
      ↓existsAndEq, true_and, exists_eq_right] at h_eq_iff
    symm
    convert h_eq_iff using 2 with u
    exact ⟨fun hu _ ↦ hu, fun hu ↦ hu (zero_le u)⟩
  have I_apply_swap (t : Set (ℝ≥0 × Ω)) : I (Prod.swap '' t) = μ {ω | debut t 0 ω ≠ ⊤} := by
    rw [I_apply_eq_debut]
    congr! with ω
    ext
    simp
    grind
  have hs_capa : IsCapacitable I (Prod.swap '' s) := by
    apply IsPavingAnalytic.isCapacitable
    · refine memFiniteUnion_of_mem ?_
      exact ⟨∅, ∅, MeasurableSet.empty, by simp, by simp⟩
    · refine InfClosed.memFiniteUnion (InfClosed.memProd ?_ ?_)
      · exact fun _ hs _ ht ↦ MeasurableSet.inter hs ht
      · exact infClosed_insert_empty_Icc
    · exact supClosed_memFiniteUnion
    have hs' : IsPavingAnalytic MeasurableSet (Prod.swap '' s) :=
      isPavingAnalytic_measurableSet_swap hs
    rw [← isPavingAnalytic_memProd_measurableSet_Icc_iff] at hs'
    refine IsPavingAnalytic.mono ?_ hs'
    exact fun _ ↦ memFiniteUnion_of_mem
  choose B hB_mem hB_subset hB_le using hs_capa
  have hB_compact a ha ω : IsCompact {t | (ω , t) ∈ B a ha} := by
    sorry
  have ha' := ha
  rw [← I_apply_swap] at ha'
  refine ⟨debut (Prod.swap '' (B a ha')) 0, ?_, ?_, ?_, ?_⟩
  · refine nullMeasurable_debut ?_ _
    rw [Set.image_swap_eq_preimage_swap]
    refine MeasurableSet.preimage ?_ (by fun_prop)
    sorry -- use hB_mem
  · intro ω hω
    suffices (ω, (debut (Prod.swap '' B a ha') 0 ω).untopA) ∈ B a ha' by
      sorry -- use hB_subset
    -- use hB_compact
    -- see things like IsCompact.sInf_mem
    sorry
  · rw [← I_apply_swap]
    convert hB_le a ha'
    ext
    simp
    grind
  · rw [← I_apply_swap, ← I_apply_swap]
    refine I.mono ?_
    convert hB_subset a ha'
    ext
    simp
    grind

lemma todo'' {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) (a : ℝ≥0∞)
    (ha : a < μ {ω | debut s 0 ω ≠ ⊤}) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω < ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      a ≤ μ {ω | τ ω ≠ ⊤} ∧ μ {ω | τ ω ≠ ⊤} ≤ μ {ω | debut s 0 ω ≠ ⊤} := by
  obtain ⟨τ, hτ_null, hτ_mem, hτ_le, hτ_ge⟩ := todo' hs a ha
  let τ':= hτ_null.aemeasurable.mk
  let N := toMeasurable μ {ω | τ ω ≠ τ' ω}
  have hN_meas : MeasurableSet N := by simp [N]
  have hμN : μ N = 0 := by
    simp only [N]
    rw [measure_toMeasurable, ← ae_iff]
    exact hτ_null.aemeasurable.ae_eq_mk
  have h_not_mem ω (hω : ω ∉ N) : τ ω = τ' ω := by
    have : ω ∉ {ω | τ ω ≠ τ' ω} := fun h_subset ↦ hω (subset_toMeasurable _ _ h_subset)
    simpa
  classical
  let τ'' := fun ω ↦ if ω ∈ N then ⊤ else τ' ω
  refine ⟨τ'', ?_, ?_, ?_, ?_⟩
  · exact Measurable.ite hN_meas (by fun_prop) hτ_null.aemeasurable.measurable_mk
  · simp only [τ'']
    intro ω
    split_ifs with hω
    · simp
    · simp only [← h_not_mem ω hω]
      exact hτ_mem ω
  · simp only [ne_eq, ite_eq_left_iff, Classical.not_imp, τ'']
    refine hτ_le.trans_eq ?_
    calc μ {ω | τ ω ≠ ⊤}
    _ = μ {ω | ω ∉ N ∧ τ ω ≠ ⊤} := by
      symm
      refine Measure.measure_inter_eq_of_ae ?_
      simp only [imp_false, eventually_mem_set]
      change Nᶜ ∈ ae μ
      rwa [mem_ae_iff, compl_compl]
    _ = μ {ω | ω ∉ N ∧ τ' ω ≠ ⊤} := by
      congr with ω
      simp only [ne_eq, and_congr_right_iff]
      intro hω
      simp only [← h_not_mem ω hω]
  · refine le_trans (measure_mono fun ω ↦ ?_) hτ_ge
    simp only [ne_eq, ite_eq_left_iff, Classical.not_imp, Set.mem_setOf_eq, and_imp, τ'']
    intro h1 h2
    simpa [h_not_mem ω h1]

instance : MeasurableInf₂ (WithTop ℝ≥0) := sorry

variable (μ) in
noncomputable
def step {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s)
    (τn' : {τ : Ω → WithTop ℝ≥0 // Measurable τ}) :
    {τ : Ω → WithTop ℝ≥0 // Measurable τ ∧ (∀ ω, τ ω < ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      μ {ω | debut (s ∩ {(t, ω) | τn'.1 ω = ⊤}) 0 ω ≠ ⊤} / 2 ≤ μ {ω | τ ω ≠ ⊤} ∧
      μ {ω | τ ω ≠ ⊤} ≤ μ {ω | debut s 0 ω ≠ ⊤}} :=
  let τn := τn'.1
  have hτn_meas : Measurable τn := τn'.2
  let A := s ∩ {(t, ω) | τn ω = ⊤}
  have hA : IsPavingAnalytic MeasurableSet A := by
    refine IsPavingAnalytic.inter hs ?_
    have : {(t, ω) | τn ω = ⊤} = Prod.swap '' {ω | τn ω = ⊤} ×ˢ (Set.univ : Set ℝ≥0) := by ext; simp
    rw [this]
    refine isPavingAnalytic_measurableSet_swap ?_
    rw [← isPavingAnalytic_memProd_measurableSet_Icc_iff]
    refine isPavingAnalytic_of_memSigma_of_imp
      (p' := memProd MeasurableSet (insert ∅ {t | ∃ a b, Set.Icc a b = t})) ?_ ?_
    · obtain ⟨B, hB, h_eq⟩ := univ_memSigma_Icc (ι := ℝ≥0)
      rw [h_eq, Set.prod_iUnion]
      refine ⟨fun n ↦ {ω | τn ω = ⊤} ×ˢ B n, fun n ↦ ?_, rfl⟩
      refine ⟨{ω | τn ω = ⊤}, B n, ?_, ?_, rfl⟩
      · exact (measurableSet_singleton _).preimage hτn_meas
      · exact Set.mem_insert_of_mem _ (hB n)
    · intro x hx
      exact isPavingAnalytic_of_mem hx
  have hA_le : μ {ω | debut A 0 ω ≠ ⊤} ≤ μ {ω | debut s 0 ω ≠ ⊤} := by
    refine measure_mono fun ω ↦ ?_
    simp only [ne_eq, Set.mem_setOf_eq]
    refine fun hωA hωs ↦ hωA ?_
    rw [eq_top_iff, ← hωs]
    exact debut_anti _ (Set.inter_subset_left : A ⊆ s) ω
  let a := μ {ω | debut A 0 ω ≠ ⊤} / 2
  have ha : a < μ {ω | debut A 0 ω ≠ ⊤} := by
    refine ENNReal.half_lt_self ?_ (by simp)
    sorry
  let h := todo'' hA a ha
  ⟨h.choose, h.choose_spec.1, fun ω hω ↦ Set.inter_subset_left (h.choose_spec.2.1 ω hω),
    h.choose_spec.2.2.1, h.choose_spec.2.2.2.trans hA_le⟩

lemma step_mem {s : Set (ℝ≥0 × Ω)} {hs : IsPavingAnalytic MeasurableSet s}
    {τn : {τ : Ω → WithTop ℝ≥0 // Measurable τ}} {ω : Ω}
    (hω : (step μ hs τn).1 ω < ⊤) :
    (((step μ hs τn).1 ω).untopA, ω) ∈ s :=
  (step μ hs τn).2.2.1 ω hω

variable (μ) in
noncomputable
def someSeq {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) :
    ℕ → {τ : Ω → WithTop ℝ≥0 // Measurable τ}
| 0 => ⟨fun _ ↦ ⊤, measurable_const⟩
| n + 1 => ⟨(someSeq hs n).1 ⊓ (step μ hs (someSeq hs n)).1,
    (someSeq hs n).2.inf (step μ hs (someSeq hs n)).2.1⟩

lemma antitone_someSeq {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) :
    Antitone (someSeq μ hs) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  rw [← Subtype.coe_le_coe]
  exact inf_le_left

lemma todo {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω < ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      μ {ω | τ ω = ⊤} = μ {ω | debut s 0 ω = ⊤} := by
  refine ⟨fun ω ↦ ⨅ n, (someSeq μ hs n).1 ω, ?_, ?_, ?_⟩
  · exact Measurable.iInf fun n ↦ (someSeq μ hs n).2
  · intro ω hω
    sorry
  · sorry

lemma todo_meas' {s : Set (ℝ≥0 × Ω)} (hs : IsMeasurableAnalytic s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω < ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      μ {ω | τ ω = ⊤} = μ {ω | debut s 0 ω = ⊤} :=
  todo hs.isPavingAnalytic

lemma todo_meas {s : Set (ℝ≥0 × Ω)} (hs : MeasurableSet s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω < ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      μ {ω | τ ω = ⊤} = μ {ω | debut s 0 ω = ⊤} :=
  todo_meas' hs.isMeasurableAnalytic

end MeasureTheory
