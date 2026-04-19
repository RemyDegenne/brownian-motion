/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Debut.Basic

/-!
# Measurable section theorems
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {x y : Ω}

namespace MeasureTheory

instance : CompactIccSpace ℝ≥0 := by
  constructor
  intro a b
  sorry

instance : MeasurableInf₂ (WithTop ℝ≥0) := inferInstanceAs (MeasurableInf₂ ℝ≥0∞)

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

-- todo: swap could be any measurable embedding?
lemma isPavingAnalytic_swap {𝓧 : Type*} {s : Set (𝓧 × Ω)}
    {p : Set (Set (𝓧 × Ω))} (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic ((fun s ↦ Prod.swap '' s) '' p) (Prod.swap '' s) := by
  obtain ⟨𝓚, h𝓚, q, hq_empty, hq_compact, t, ht_mem, h_eq⟩ := hs
  refine ⟨𝓚, h𝓚, q, hq_empty, hq_compact, Prod.map Prod.swap id '' t, ?_, ?_⟩
  · rw [mem_prodSigmaDelta_iff] at ht_mem ⊢
    obtain ⟨A, hA, K, hK, rfl⟩ := ht_mem
    refine ⟨fun n m ↦ Prod.swap '' (A n m), fun n m ↦ ?_, K, hK, ?_⟩
    · simp only [Set.mem_image]
      exact ⟨A n m, hA n m, rfl⟩
    · rw [Set.image_iInter]
      swap; · exact Prod.swap_bijective.prodMap Function.bijective_id
      simp_rw [Set.image_iUnion]
      congr with n x
      simp
      grind
  · ext; simp; grind

lemma isPavingAnalytic_measurableSet_swap {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {s : Set (𝓧 × Ω)}
    (hs : IsPavingAnalytic MeasurableSet s) :
    IsPavingAnalytic MeasurableSet (Prod.swap '' s) := by
  convert isPavingAnalytic_swap hs
  ext s
  simp only [Set.mem_image]
  refine ⟨fun hs ↦ ⟨Prod.swap ⁻¹' s, MeasurableSet.preimage ?_ measurable_swap, ?_⟩,
    fun ⟨t, ht, ht_eq⟩ ↦ ?_⟩
  · exact hs
  · ext; simp; grind
  · rw [← ht_eq, Set.image_swap_eq_preimage_swap]
    refine MeasurableSet.preimage ?_ measurable_swap
    exact ht

/-- The début of a measurable set in `ℝ≥0 × Ω` is universally measurable: it is null-measurable
for any finite measure. -/
lemma nullMeasurable_debut {s : Set (ℝ≥0 × Ω)} (hs : MeasurableSet s) (u : ℝ≥0) :
    NullMeasurable (debut s u) μ := by
  suffices ∀ (r : ℝ≥0), NullMeasurableSet {ω | debut s u ω < r} μ by
    -- todo: NullMeasurable version of measurable_of_Iio ? also deal with r not ⊤
    sorry
  intro r
  exact MeasurableSet.nullMeasurableSet_debut_lt (P := μ) hs u r

lemma todo' {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) (a : ℝ≥0∞)
    (ha : a < μ {ω | debut s 0 ω ≠ ⊤}) :
    ∃ τ : Ω → WithTop ℝ≥0, NullMeasurable τ μ ∧ (∀ ω, τ ω < ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      a ≤ μ {ω | τ ω ≠ ⊤} ∧ μ {ω | τ ω ≠ ⊤} ≤ μ {ω | debut s 0 ω ≠ ⊤} := by
  let I : Capacity (supClosure
      (Set.image2 (· ×ˢ ·) MeasurableSet (insert ∅ {t | ∃ a b, Set.Icc a b = t}))) :=
    μ.capacity.comp_fst MeasurableSet.empty (fun _ hs _ ht ↦  MeasurableSet.union hs ht) (by simp)
      (isCompactSystem_insert_empty_Icc ℝ≥0)
  have I_apply (t : Set (Ω × ℝ≥0)) : I t = μ {ω | ∃ u, (ω, u) ∈ t} := by
    rw [μ.capacity.comp_fst_apply, μ.capacity_apply]; congr; ext; simp
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
    rw [I_apply_eq_debut]; congr! with ω; ext; simp; grind
  have hs_capa : IsCapacitable I (Prod.swap '' s) := by
    apply IsPavingAnalytic.isCapacitable
    · refine subset_supClosure ?_
      exact ⟨∅, MeasurableSet.empty, ∅, by simp, by simp⟩
    · refine InfClosed.supClosure (InfClosed.image2_prod ?_ ?_)
      · exact fun _ hs _ ht ↦ MeasurableSet.inter hs ht
      · exact infClosed_insert_empty_Icc
    · exact supClosed_supClosure
    have hs' : IsPavingAnalytic MeasurableSet (Prod.swap '' s) :=
      isPavingAnalytic_measurableSet_swap hs
    rw [← isPavingAnalytic_image2_prod_measurableSet_Icc_iff] at hs'
    exact IsPavingAnalytic.mono subset_supClosure hs'
  choose B hB_mem hB_subset hB_le using hs_capa
  have hB_compact a ha ω : IsCompact {t | (ω , t) ∈ B a ha} := by
    specialize hB_mem a ha
    obtain ⟨A, hA, hB_eq⟩ := hB_mem
    simp only [← hB_eq, Set.iInf_eq_iInter, Set.mem_iInter]
    suffices ∀ n, IsCompact {t | (ω, t) ∈ A n} by
      refine IsCompact.of_isClosed_subset (s := {t | (ω, t) ∈ A 0}) (this 0) ?_ fun x ↦ by grind
      suffices IsClosed (⋂ n, {t | (ω, t) ∈ A n}) by convert this; ext; simp
      exact isClosed_iInter fun n ↦ (this n).isClosed
    intro n
    specialize hA n
    rw [mem_supClosure_set_iff'] at hA
    choose t _ C hC hA_eq using hA
    simp only [hA_eq, Set.mem_iUnion, exists_prop]
    suffices IsCompact (⋃ i ∈ t, {u | (ω, u) ∈ C i}) by convert this; ext; simp
    refine Finset.isCompact_biUnion _ fun i hi ↦ ?_
    obtain ⟨D, hD, E, hE, hC_eq⟩ := hC i hi
    simp only [← hC_eq, Set.mem_prod]
    by_cases hωD : ω ∈ D
    · simp only [hωD, true_and, Set.setOf_mem_eq]
      cases hE with
      | inl hE => simp [hE]
      | inr hE =>
        obtain ⟨a, b, rfl⟩ := hE
        exact isCompact_Icc
    · simp [hωD]
  rw [← I_apply_swap] at ha
  refine ⟨debut (Prod.swap '' B a ha) 0, ?_, ?_, ?_, ?_⟩
  · refine nullMeasurable_debut ?_ _
    rw [Set.image_swap_eq_preimage_swap]
    refine MeasurableSet.preimage ?_ (by fun_prop)
    specialize hB_mem a ha
    refine MeasurableSet.of_mem_countableInfClosure' hB_mem fun s hs ↦ ?_
    refine MeasurableSet.of_mem_supClosure hs fun s hs ↦ ?_
    refine MeasurableSet.of_mem_image2_prod hs (fun _ ht ↦ ht) (fun t ht ↦ ?_)
    cases ht with
    | inl ht => simp [ht]
    | inr ht => obtain ⟨a, b, rfl⟩ := ht; exact measurableSet_Icc
  · intro ω hω
    suffices ((debut (Prod.swap '' B a ha) 0 ω).untopA, ω) ∈ Prod.swap '' B a ha by grind
    refine debut_mem_of_isClosed ?_ hω.ne
    convert (hB_compact a ha ω).isClosed with t
    simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq, ↓existsAndEq,
      true_and, exists_eq_right, and_iff_right_iff_imp]
    intro
    convert zero_le _
    exact NNReal.instCanonicallyOrderedAdd
  · specialize hB_le a ha
    rwa [I_apply_eq_debut] at hB_le
  · rw [← I_apply_swap, ← I_apply_swap]
    exact I.mono fun _ ↦ by simp; grind

-- same as the previous lemma but with a measurable section instead of a null-measurable one
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
    rw [← isPavingAnalytic_image2_prod_measurableSet_Icc_iff]
    refine isPavingAnalytic_of_mem_countableSupClosure_of_imp
      (p' := Set.image2 (· ×ˢ ·) MeasurableSet (insert ∅ {t | ∃ a b, Set.Icc a b = t})) ?_
      fun _ ↦ isPavingAnalytic_of_mem
    obtain ⟨B, hB, h_eq⟩ := univ_mem_countableSupClosure_Icc (ι := ℝ≥0)
    rw [← h_eq, Set.iSup_eq_iUnion, Set.prod_iUnion]
    refine ⟨fun n ↦ {ω | τn ω = ⊤} ×ˢ B n, fun n ↦ ?_, rfl⟩
    refine ⟨{ω | τn ω = ⊤}, ?_, B n, ?_, rfl⟩
    · exact (measurableSet_singleton _).preimage hτn_meas
    · exact Set.mem_insert_of_mem _ (hB n)
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

lemma someSeq_add_one_eq_of_ne_top {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s)
    {n : ℕ} {ω : Ω} (hω : (someSeq μ hs n).1 ω ≠ ⊤) :
    (someSeq μ hs (n + 1)).1 ω = (someSeq μ hs n).1 ω := by
  sorry

lemma someSeq_eq_of_ne_top_of_ge {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s)
    {n m : ℕ} {ω : Ω} (hω : (someSeq μ hs n).1 ω ≠ ⊤) (hm : n ≤ m) :
    (someSeq μ hs m).1 ω = (someSeq μ hs n).1 ω := by
  sorry

lemma someSeq_mem {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s)
    {n : ℕ} {ω : Ω} (hω : (someSeq μ hs n).1 ω ≠ ⊤) :
    (((someSeq μ hs n).1 ω).untopA, ω) ∈ s := by
  sorry

lemma todo {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω < ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      μ {ω | τ ω = ⊤} = μ {ω | debut s 0 ω = ⊤} := by
  refine ⟨fun ω ↦ ⨅ n, (someSeq μ hs n).1 ω, ?_, ?_, ?_⟩
  · exact Measurable.iInf fun n ↦ (someSeq μ hs n).2
  · intro ω hω
    simp only [iInf_lt_top] at hω
    simp only
    obtain ⟨n, hn⟩ := hω
    have : ⨅ n, (someSeq μ hs n).1 ω = (someSeq μ hs n).1 ω := by
      have h_eq m (hm : n ≤ m) := someSeq_eq_of_ne_top_of_ge hs hn.ne hm
      sorry
    rw [this]
    exact someSeq_mem hs hn.ne
  · simp only [iInf_eq_top]
    sorry

lemma todo_right {s : Set (Ω × ℝ≥0)} (hs : IsPavingAnalytic MeasurableSet s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω < ⊤ → (ω, (τ ω).untopA) ∈ s) ∧
      μ {ω | τ ω = ⊤} = μ {ω | debut (Prod.swap '' s) 0 ω = ⊤} := by
  obtain ⟨τ, hτ_meas, hτ_mem, hτ_eq⟩ := todo (μ := μ) (isPavingAnalytic_measurableSet_swap hs)
  exact ⟨τ, hτ_meas, fun ω hω ↦ by grind, by grind⟩

lemma todo_meas' {s : Set (ℝ≥0 × Ω)} (hs : IsMeasurableAnalytic s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω < ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      μ {ω | τ ω = ⊤} = μ {ω | debut s 0 ω = ⊤} :=
  todo hs.isPavingAnalytic

lemma todo_meas'_right {s : Set (Ω × ℝ≥0)} (hs : IsMeasurableAnalytic s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω < ⊤ → (ω, (τ ω).untopA) ∈ s) ∧
      μ {ω | τ ω = ⊤} = μ {ω | debut (Prod.swap '' s) 0 ω = ⊤} :=
  todo_right hs.isPavingAnalytic

lemma todo_meas {s : Set (ℝ≥0 × Ω)} (hs : MeasurableSet s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω < ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      μ {ω | τ ω = ⊤} = μ {ω | debut s 0 ω = ⊤} :=
  todo_meas' hs.isMeasurableAnalytic

lemma todo_meas_right {s : Set (Ω × ℝ≥0)} (hs : MeasurableSet s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω < ⊤ → (ω, (τ ω).untopA) ∈ s) ∧
      μ {ω | τ ω = ⊤} = μ {ω | debut (Prod.swap '' s) 0 ω = ⊤} :=
  todo_meas'_right hs.isMeasurableAnalytic

end MeasureTheory
