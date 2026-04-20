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

/-- The début of an analytic set in `ℝ≥0 × Ω` is universally measurable: it is null-measurable
for any finite measure. -/
lemma nullMeasurable_debut {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) (u : ℝ≥0) :
    NullMeasurable (debut s u) μ := by
  suffices ∀ (r : ℝ≥0), NullMeasurableSet {ω | debut s u ω < r} μ by
    sorry
  exact IsPavingAnalytic.nullMeasurableSet_debut_lt (P := μ) hs u

lemma todo' {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) (a : ℝ≥0∞)
    (ha : a < μ {ω | debut s 0 ω ≠ ⊤}) :
    ∃ τ : Ω → WithTop ℝ≥0, NullMeasurable τ μ ∧ (∀ ω, τ ω ≠ ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      a ≤ μ {ω | τ ω ≠ ⊤} ∧ debut s 0 ≤ τ := by
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
    refine isPavingAnalytic_of_mem ?_
    change MeasurableSet (Prod.swap ⁻¹' B a ha)
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
    refine debut_mem_of_isClosed ?_ hω
    convert (hB_compact a ha ω).isClosed with t
    simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq, ↓existsAndEq,
      true_and, exists_eq_right, and_iff_right_iff_imp]
    exact fun _ ↦ zero_le _
  · specialize hB_le a ha
    rwa [I_apply_eq_debut] at hB_le
  · refine debut_anti 0 ?_
    simp only [Set.le_eq_subset, Set.image_subset_iff]
    convert hB_subset _ _
    rw [Set.image_swap_eq_preimage_swap]

-- same as the previous lemma but with a measurable section instead of a null-measurable one
lemma todo'' {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) (a : ℝ≥0∞)
    (ha : a < μ {ω | debut s 0 ω ≠ ⊤}) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω ≠ ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      a ≤ μ {ω | τ ω ≠ ⊤} ∧ debut s 0 ≤ τ := by
  obtain ⟨τ, hτ_null, hτ_mem, hτ_le, hτ_ge⟩ := todo' hs a ha
  let τ' := hτ_null.aemeasurable.mk
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
    · simpa [← h_not_mem ω hω] using hτ_mem ω
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
  · intro ω
    by_cases hωN : ω ∈ N
    · simp [τ'', hωN]
    · simp only [hωN, ↓reduceIte, ← h_not_mem ω hωN, τ'']
      exact hτ_ge ω

lemma isPavingAnalytic_some_set {τ : Ω → WithTop ℝ≥0} (hτ_meas : Measurable τ) :
    IsPavingAnalytic MeasurableSet {((_, ω) : ℝ≥0 × Ω) | τ ω = ⊤} := by
  have : {(t, ω) | τ ω = ⊤} = Prod.swap '' {ω | τ ω = ⊤} ×ˢ (Set.univ : Set ℝ≥0) := by ext; simp
  rw [this]
  refine isPavingAnalytic_measurableSet_swap ?_
  rw [← isPavingAnalytic_image2_prod_measurableSet_Icc_iff]
  refine isPavingAnalytic_of_mem_countableSupClosure_of_imp
    (p' := Set.image2 (· ×ˢ ·) MeasurableSet (insert ∅ {t | ∃ a b, Set.Icc a b = t})) ?_
    fun _ ↦ isPavingAnalytic_of_mem
  obtain ⟨B, hB, h_eq⟩ := univ_mem_countableSupClosure_Icc (ι := ℝ≥0)
  rw [← h_eq, Set.iSup_eq_iUnion, Set.prod_iUnion]
  refine ⟨fun n ↦ {ω | τ ω = ⊤} ×ˢ B n, fun n ↦ ?_, rfl⟩
  refine ⟨{ω | τ ω = ⊤}, ?_, B n, ?_, rfl⟩
  · exact (measurableSet_singleton _).preimage hτ_meas
  · exact Set.mem_insert_of_mem _ (hB n)

omit [IsFiniteMeasure μ] in
lemma measure_debut_ne_top_mono {ι : Type*} [ConditionallyCompleteLinearOrder ι]
    {A B : Set (ι × Ω)} (hAB : A ⊆ B) (u : ι) :
    μ {ω | debut A u ω ≠ ⊤} ≤ μ {ω | debut B u ω ≠ ⊤} := by
  refine measure_mono fun ω ↦ ?_
  simp only [ne_eq, Set.mem_setOf_eq]
  refine fun hωA hωs ↦ hωA ?_
  rw [eq_top_iff, ← hωs]
  exact debut_anti _ hAB ω

variable (μ) in
noncomputable
def step {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s)
    (τn : {τ : Ω → WithTop ℝ≥0 // Measurable τ}) :
    {τ : Ω → WithTop ℝ≥0 // Measurable τ} :=
  let A := s ∩ {(t, ω) | τn.1 ω = ⊤}
  if h0 : μ {ω | debut A 0 ω ≠ ⊤} = 0 then ⟨fun _ ↦ ⊤, measurable_const⟩ else
    let h := todo'' (hs.inter (isPavingAnalytic_some_set τn.2)) (μ {ω | debut A 0 ω ≠ ⊤} / 2)
      (ENNReal.half_lt_self h0 (by simp))
    ⟨h.choose, h.choose_spec.1⟩

@[fun_prop]
lemma measurable_step {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s)
    (τn : {τ : Ω → WithTop ℝ≥0 // Measurable τ}) :
    Measurable (step μ hs τn).1 := by
  by_cases h0 : μ {ω | debut (s ∩ {(t, ω) | τn.1 ω = ⊤}) 0 ω ≠ ⊤} = 0
  · simp [h0, step]
  · simp only [step, ne_eq, h0, ↓reduceDIte, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact (todo'' (hs.inter (isPavingAnalytic_some_set τn.2))
      (μ {ω | debut (s ∩ {(t, ω) | τn.1 ω = ⊤}) 0 ω ≠ ⊤} / 2)
      (ENNReal.half_lt_self h0 (by simp))).choose_spec.1

lemma step_mem {s : Set (ℝ≥0 × Ω)} {hs : IsPavingAnalytic MeasurableSet s}
    {τn : {τ : Ω → WithTop ℝ≥0 // Measurable τ}} {ω : Ω}
    (hω : (step μ hs τn).1 ω ≠ ⊤) :
    (((step μ hs τn).1 ω).untopA, ω) ∈ s := by
  let A := s ∩ {(t, ω) | τn.1 ω = ⊤}
  have h_ne : μ {ω | debut A 0 ω ≠ ⊤} ≠ 0 := by
    by_contra! h0
    simp only [step, ne_eq, Set.mem_inter_iff, Set.mem_setOf_eq] at hω
    rw [dif_pos h0] at hω
    simp at hω
  have h_lt : μ {ω | debut A 0 ω ≠ ⊤} / 2 < μ {ω | debut A 0 ω ≠ ⊤} :=
    ENNReal.half_lt_self h_ne (by simp)
  rw [step, dif_neg h_ne] at hω ⊢
  exact Set.inter_subset_left
    ((todo'' (hs.inter (isPavingAnalytic_some_set τn.2)) (μ {ω | debut A 0 ω ≠ ⊤} / 2)
      h_lt).choose_spec.2.1 ω hω)

lemma measure_step_ne_top_ge {s : Set (ℝ≥0 × Ω)} {hs : IsPavingAnalytic MeasurableSet s}
    {τn : {τ : Ω → WithTop ℝ≥0 // Measurable τ}} :
    μ {ω | debut (s ∩ {(_, ω) | τn.1 ω = ⊤}) 0 ω ≠ ⊤} / 2 ≤ μ {ω | (step μ hs τn).1 ω ≠ ⊤} := by
  let A := s ∩ {(t, ω) | τn.1 ω = ⊤}
  by_cases h0 : μ {ω | debut A 0 ω ≠ ⊤} = 0
  · simp [A, h0]
  have h_lt : μ {ω | debut A 0 ω ≠ ⊤} / 2 < μ {ω | debut A 0 ω ≠ ⊤} :=
    ENNReal.half_lt_self h0 (by simp)
  rw [step, dif_neg h0]
  exact (todo'' (hs.inter (isPavingAnalytic_some_set τn.2)) (μ {ω | debut A 0 ω ≠ ⊤} / 2)
      h_lt).choose_spec.2.2.1

lemma debut_le_step {s : Set (ℝ≥0 × Ω)} {hs : IsPavingAnalytic MeasurableSet s}
    {τn : {τ : Ω → WithTop ℝ≥0 // Measurable τ}} {ω : Ω} :
    debut (s ∩ {(_, ω) | τn.1 ω = ⊤}) 0 ω ≤ (step μ hs τn).1 ω := by
  by_cases hω : (step μ hs τn).1 ω = ⊤
  · simp [hω]
  let A := s ∩ {(t, ω) | τn.1 ω = ⊤}
  have h_ne : μ {ω | debut A 0 ω ≠ ⊤} ≠ 0 := by
    by_contra! h0
    simp only [step, ne_eq, Set.mem_inter_iff, Set.mem_setOf_eq] at hω
    rw [dif_pos h0] at hω
    simp at hω
  have h_lt : μ {ω | debut A 0 ω ≠ ⊤} / 2 < μ {ω | debut A 0 ω ≠ ⊤} :=
    ENNReal.half_lt_self h_ne (by simp)
  rw [step, dif_neg h_ne]
  exact ((todo'' (hs.inter (isPavingAnalytic_some_set τn.2)) (μ {ω | debut A 0 ω ≠ ⊤} / 2)
      h_lt).choose_spec.2.2.2 ω)

lemma step_eq_top_of_ne_top {s : Set (ℝ≥0 × Ω)} {hs : IsPavingAnalytic MeasurableSet s}
    {τn : {τ : Ω → WithTop ℝ≥0 // Measurable τ}} {ω : Ω} (hω : τn.1 ω ≠ ⊤) :
    (step μ hs τn).1 ω = ⊤ := by
  refine le_antisymm le_top ?_
  refine le_trans ?_ debut_le_step
  simp only [top_le_iff]
  rw [debut_eq_top_iff]
  simp [hω]

variable (μ) in
noncomputable
def someSeq {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) :
    ℕ → {τ : Ω → WithTop ℝ≥0 // Measurable τ}
| 0 => ⟨fun _ ↦ ⊤, measurable_const⟩
| n + 1 => ⟨(someSeq hs n).1 ⊓ (step μ hs (someSeq hs n)).1,
    (someSeq hs n).2.inf (step μ hs (someSeq hs n)).2⟩

lemma someSeq_add_one {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) (n : ℕ) :
    (someSeq μ hs (n + 1)).1 = (someSeq μ hs n).1 ⊓ (step μ hs (someSeq μ hs n)).1 := rfl

@[fun_prop]
lemma measurable_someSeq {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) (n : ℕ) :
    Measurable (someSeq μ hs n).1 := by
  induction n with
  | zero => simp [someSeq]
  | succ n ih =>
    simp only [someSeq_add_one]
    exact ih.inf (measurable_step hs (someSeq μ hs n))

lemma antitone_someSeq {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) :
    Antitone (someSeq μ hs) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  rw [← Subtype.coe_le_coe]
  exact inf_le_left

lemma someSeq_add_one_eq_of_ne_top {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s)
    {n : ℕ} {ω : Ω} (hω : (someSeq μ hs n).1 ω ≠ ⊤) :
    (someSeq μ hs (n + 1)).1 ω = (someSeq μ hs n).1 ω := by
  rw [someSeq_add_one]
  simp [step_eq_top_of_ne_top hω]

lemma someSeq_eq_of_ne_top_of_ge {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s)
    {n m : ℕ} {ω : Ω} (hω : (someSeq μ hs n).1 ω ≠ ⊤) (hm : n ≤ m) :
    (someSeq μ hs m).1 ω = (someSeq μ hs n).1 ω := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hmn h_eq => rw [someSeq_add_one_eq_of_ne_top, h_eq]; rwa [h_eq]

lemma measure_someSeq_add_one_ne_top {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s)
    (n : ℕ) :
    μ {ω | (someSeq μ hs (n + 1)).1 ω ≠ ⊤} =
      μ {ω | (someSeq μ hs n).1 ω ≠ ⊤} + μ {ω | (step μ hs (someSeq μ hs n)).1 ω ≠ ⊤} := by
  rw [← measure_union]
  · congr 1
    ext ω
    rw [someSeq_add_one]
    simp only [Pi.inf_apply, ne_eq, inf_eq_top_iff, not_and]
    grind
  · rw [Set.disjoint_iff_inter_eq_empty]
    ext ω
    simp only [ne_eq, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_and, Decidable.not_not]
    exact step_eq_top_of_ne_top
  · exact ((measurableSet_singleton _).preimage (by fun_prop)).compl

lemma measure_someSeq_add_one_ne_top_ge {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s)
    (n : ℕ) :
    μ {ω | (someSeq μ hs n).1 ω ≠ ⊤} +
        μ {ω | debut s 0 ω ≠ ⊤ ∧ (someSeq μ hs n).1 ω = ⊤} / 2 ≤
      μ {ω | (someSeq μ hs (n + 1)).1 ω ≠ ⊤} := by
  rw [measure_someSeq_add_one_ne_top]
  gcongr
  convert measure_step_ne_top_ge with ω
  simp [debut_ne_top_iff]

lemma measure_inter_eq_zero {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) :
    μ {ω | debut s 0 ω ≠ ⊤ ∧ ⨅ n, (someSeq μ hs n).1 ω = ⊤} = 0 := by
  suffices μ {ω | ⨅ n, (someSeq μ hs n).1 ω ≠ ⊤} +
        μ {ω | debut s 0 ω ≠ ⊤ ∧ ⨅ n, (someSeq μ hs n).1 ω = ⊤} / 2 ≤
      μ {ω | ⨅ n, (someSeq μ hs n).1 ω ≠ ⊤} by
    conv_rhs at this => rw [← add_zero (μ {ω | ⨅ n, (someSeq μ hs n).1 ω ≠ ⊤})]
    rw [ENNReal.add_le_add_iff_left (by simp)] at this
    simpa using this
  have h_mono : Monotone fun n ↦ {ω | (someSeq μ hs n).1 ω ≠ ⊤} := by
    intro n m hnm
    simp only [Set.le_eq_subset, Set.setOf_subset_setOf]
    intro ω hω
    refine ne_of_lt (lt_of_le_of_lt ?_ (Ne.lt_top hω))
    exact antitone_someSeq hs hnm ω
  refine le_of_tendsto_of_tendsto ?_ ?_ (.of_forall (measure_someSeq_add_one_ne_top_ge hs (μ := μ)))
    (b := atTop)
  · refine Tendsto.add ?_ ?_
    · convert tendsto_measure_iUnion_atTop h_mono
      ext; simp
    · refine ENNReal.Tendsto.div_const ?_ (by simp)
      convert tendsto_measure_iInter_atTop ?_ ?_ ?_
      · ext ω
        simp only [ne_eq, iInf_eq_top, Set.mem_setOf_eq, Set.mem_iInter]
        exact ⟨fun ⟨hd, h_seq⟩ i ↦ ⟨hd, h_seq i⟩, fun h ↦ ⟨(h 0).1, fun i ↦ (h i).2⟩⟩
      · infer_instance
      · intro n
        change NullMeasurableSet ({ω | debut s 0 ω ≠ ⊤} ∩ {ω | (someSeq μ hs n).1 ω = ⊤}) μ
        refine NullMeasurableSet.inter ?_ ?_
        · exact (nullMeasurable_debut (μ := μ) hs 0 (measurableSet_singleton _)).compl
        · refine MeasurableSet.nullMeasurableSet ?_
          exact (measurableSet_singleton _).preimage (by fun_prop)
      · intro n m hnm
        simp only [ne_eq, Set.le_eq_subset, Set.setOf_subset_setOf, and_imp]
        intro ω hω h_top
        refine ⟨hω, ?_⟩
        refine le_antisymm le_top ?_
        rw [← h_top]
        exact antitone_someSeq hs hnm ω
      · exact ⟨0, by simp⟩
  · simp only [ne_eq, iInf_eq_top, not_forall]
    convert tendsto_measure_iUnion_atTop ?_
    · ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      refine ⟨fun ⟨n, hω⟩ ↦ ⟨n, ?_⟩, fun ⟨n, hω⟩ ↦ ⟨n + 1, hω⟩⟩
      refine ne_of_lt (lt_of_le_of_lt ?_ (Ne.lt_top hω))
      exact antitone_someSeq hs (by grind) ω
    · infer_instance
    · exact fun _ _ h ↦ h_mono (by grind)

lemma iInf_someSeq_ne_top_of_debut_ne_top_ae {s : Set (ℝ≥0 × Ω)}
    (hs : IsPavingAnalytic MeasurableSet s) :
    ∀ᵐ ω ∂μ, debut s 0 ω ≠ ⊤ → ⨅ n, (someSeq μ hs n).1 ω ≠ ⊤ := by
  rw [ae_iff]
  rw [← measure_inter_eq_zero hs (μ := μ)]
  congr with ω
  simp

lemma debut_le_someSeq {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) {ω : Ω} (n : ℕ) :
    debut s 0 ω ≤ (someSeq μ hs n).1 ω := by
  induction n with
  | zero => simp [someSeq]
  | succ n ih =>
    rw [someSeq_add_one]
    simp only [Pi.inf_apply, le_inf_iff, ih, true_and]
    refine le_trans ?_ debut_le_step
    exact debut_anti 0 Set.inter_subset_left ω

lemma debut_ne_top_of_iInf_someSeq_ne_top {s : Set (ℝ≥0 × Ω)}
    (hs : IsPavingAnalytic MeasurableSet s) {ω : Ω}
    (hω : ⨅ n, (someSeq μ hs n).1 ω ≠ ⊤) :
    debut s 0 ω ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt ?_ hω.lt_top)
  simp only [le_iInf_iff]
  exact debut_le_someSeq hs

lemma debut_ne_top_iff_ae {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) :
    ∀ᵐ ω ∂μ, debut s 0 ω ≠ ⊤ ↔ ⨅ n, (someSeq μ hs n).1 ω ≠ ⊤ := by
  filter_upwards [iInf_someSeq_ne_top_of_debut_ne_top_ae hs (μ := μ)] with ω hω using
    ⟨fun h_debut ↦ hω h_debut, fun h_iInf ↦ debut_ne_top_of_iInf_someSeq_ne_top hs h_iInf⟩

lemma someSeq_mem {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s)
    {n : ℕ} {ω : Ω} (hω : (someSeq μ hs n).1 ω ≠ ⊤) :
    (((someSeq μ hs n).1 ω).untopA, ω) ∈ s := by
  sorry

lemma todo {s : Set (ℝ≥0 × Ω)} (hs : IsPavingAnalytic MeasurableSet s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω ≠ ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      ∀ᵐ ω ∂μ, debut s 0 ω ≠ ⊤ ↔ τ ω ≠ ⊤ := by
  refine ⟨fun ω ↦ ⨅ n, (someSeq μ hs n).1 ω, ?_, ?_, ?_⟩
  · exact Measurable.iInf fun n ↦ (someSeq μ hs n).2
  · intro ω hω
    rw [← lt_top_iff_ne_top] at hω
    simp only [iInf_lt_top] at hω ⊢
    obtain ⟨n, hn⟩ := hω
    have : ⨅ n, (someSeq μ hs n).1 ω = (someSeq μ hs n).1 ω := by
      have h_eq m (hm : n ≤ m) := someSeq_eq_of_ne_top_of_ge hs hn.ne hm
      refine tendsto_nhds_unique (f := fun n ↦ (someSeq μ hs n).1 ω) (l := atTop) ?_ ?_
      · exact tendsto_atTop_iInf fun n m hnm ↦ antitone_someSeq hs hnm ω
      · refine tendsto_nhds_of_eventually_eq ?_
        simp only [eventually_atTop, ge_iff_le]
        exact ⟨n, h_eq⟩
    rw [this]
    exact someSeq_mem hs hn.ne
  · exact debut_ne_top_iff_ae hs

lemma todo_right {s : Set (Ω × ℝ≥0)} (hs : IsPavingAnalytic MeasurableSet s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω ≠ ⊤ → (ω, (τ ω).untopA) ∈ s) ∧
      ∀ᵐ ω ∂μ, debut (Prod.swap '' s) 0 ω ≠ ⊤ ↔ τ ω ≠ ⊤ := by
  obtain ⟨τ, hτ_meas, hτ_mem, hτ_eq⟩ := todo (μ := μ) (isPavingAnalytic_measurableSet_swap hs)
  exact ⟨τ, hτ_meas, fun ω hω ↦ by grind, by grind⟩

lemma todo_meas' {s : Set (ℝ≥0 × Ω)} (hs : IsMeasurableAnalytic s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω ≠ ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      ∀ᵐ ω ∂μ, debut s 0 ω ≠ ⊤ ↔ τ ω ≠ ⊤ :=
  todo hs.isPavingAnalytic

lemma todo_meas'_right {s : Set (Ω × ℝ≥0)} (hs : IsMeasurableAnalytic s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω ≠ ⊤ → (ω, (τ ω).untopA) ∈ s) ∧
      ∀ᵐ ω ∂μ, debut (Prod.swap '' s) 0 ω ≠ ⊤ ↔ τ ω ≠ ⊤ :=
  todo_right hs.isPavingAnalytic

lemma todo_meas {s : Set (ℝ≥0 × Ω)} (hs : MeasurableSet s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω ≠ ⊤ → ((τ ω).untopA, ω) ∈ s) ∧
      ∀ᵐ ω ∂μ, debut s 0 ω ≠ ⊤ ↔ τ ω ≠ ⊤ :=
  todo_meas' hs.isMeasurableAnalytic

lemma todo_meas_right {s : Set (Ω × ℝ≥0)} (hs : MeasurableSet s) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω ≠ ⊤ → (ω, (τ ω).untopA) ∈ s) ∧
      ∀ᵐ ω ∂μ, debut (Prod.swap '' s) 0 ω ≠ ⊤ ↔ τ ω ≠ ⊤ :=
  todo_meas'_right hs.isMeasurableAnalytic

end MeasureTheory
