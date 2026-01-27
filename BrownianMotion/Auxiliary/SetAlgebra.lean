/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.SetAlgebra

open MeasurableSpace Set

namespace MeasureTheory

variable {α : Type*}

/-
This file is ready to be upstreamed to Mathlilb almost as it is, just move the PiSystem section to
the Mathlib.MeasureTheory.PiSystem file, the rest can be put at the end of
Mathlib.MeasureTheory.SetAlgebra as it is.
Remember to update the docstrings of the Mathlib files accordingly.
-/

/-- A monotone class is a collection of subsets of a type `α` that is closed under countable
monotone union and countable antitone intersection.
-/
structure MonotoneClass (α : Type*) where
  /-- Predicate saying that a given set is contained in the Monotone Class. -/
  Has : Set α → Prop
  /-- A monotone class is closed under countable monotone union. -/
  has_iUnion : ∀ {A : ℕ → Set α}, (∀ n, Has (A n)) → Monotone A → Has (⋃ n, A n)
  /-- A monotone class is closed under countable antitone intersection. -/
  has_iInter : ∀ (B : ℕ → Set α), (∀ n, Has (B n)) → Antitone B → Has (⋂ n, B n)

namespace MonotoneClass

@[ext]
lemma ext : ∀ {C₁ C₂ : MonotoneClass α}, (∀ s : Set α, C₁.Has s ↔ C₂.Has s) → C₁ = C₂
  | ⟨s₁, _, _⟩, ⟨s₂, _, _⟩, h => by
    have : s₁ = s₂ := funext fun x => propext <| h x
    subst this
    rfl

variable (C : MonotoneClass α)

lemma has_iUnion' {β} [Nonempty β] [Countable β] [LinearOrder β]
    {A : β → Set α} (hC : ∀ i, C.Has (A i)) (h_mono : Monotone A) :
    C.Has (⋃ i, A i) := by
  have ⟨f, hf⟩ := exists_surjective_nat β
  have ⟨B, hB_mono, hB⟩ : ∃ i : ℕ → β, Monotone i ∧ ∀ b : β, ∃ n, b ≤ i n := by
    refine ⟨fun n ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one f,
      fun n m hnm ↦ Finset.sup'_le _ _ fun i hi ↦ Finset.le_sup' f (by grind), fun b ↦ ?_⟩
    obtain ⟨n, rfl⟩ := hf b
    exact ⟨n, Finset.le_sup' f (by grind)⟩
  have h_union_eq : ⋃ i, A i = ⋃ n, A (B n) := by
    ext x
    simp_rw [mem_iUnion]
    refine ⟨fun ⟨i, hi⟩ ↦ ?_, fun ⟨i, hi⟩ ↦ ⟨B i, hi⟩⟩
    obtain ⟨n, hn⟩ := hB i
    exact ⟨n, h_mono hn hi⟩
  exact h_union_eq ▸ C.has_iUnion (fun n ↦ hC _) (fun n m hnm ↦ h_mono (hB_mono hnm))

lemma has_iInter' {β} [Nonempty β] [Countable β] [LinearOrder β]
    {A : β → Set α} (hC : ∀ i, C.Has (A i)) (h_mono : Antitone A) :
    C.Has (⋂ i, A i) := by
  have ⟨f, hf⟩ := exists_surjective_nat β
  have ⟨B, hB_mono, hB⟩ : ∃ i : ℕ → β, Monotone i ∧ ∀ b : β, ∃ n, b ≤ i n := by
    refine ⟨fun n ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one f,
      fun n m hnm ↦ Finset.sup'_le _ _ fun i hi ↦ Finset.le_sup' f (by grind), fun b ↦ ?_⟩
    obtain ⟨n, rfl⟩ := hf b
    exact ⟨n, Finset.le_sup' f (by grind)⟩
  have h_inter_eq : ⋂ i, A i = ⋂ n, A (B n) := by
    ext x
    simp_rw [mem_iInter]
    refine ⟨fun hx n ↦ hx _, fun hx n ↦ ?_⟩
    obtain ⟨m, hm⟩ := hB n
    exact h_mono hm (hx m)
  exact h_inter_eq ▸ C.has_iInter _ (fun n ↦ hC _) (fun n m hnm ↦ h_mono (hB_mono hnm))

instance instLEMonotoneClass : LE (MonotoneClass α) where le C₁ C₂ := C₁.Has ≤ C₂.Has

lemma le_def {C₁ C₂ : MonotoneClass α} : C₁ ≤ C₂ ↔ C₁.Has ≤ C₂.Has := Iff.rfl

instance : PartialOrder (MonotoneClass α) :=
  { instLEMonotoneClass with
    le_refl := fun _ _ ↦ le_rfl
    le_trans := fun _ _ _ h₁ h₂ A hA ↦ h₂ A (h₁ A hA)
    le_antisymm := fun _ _ h₁ h₂ ↦ ext fun s ↦ ⟨h₁ s, h₂ s⟩ }

section PiSystem

-- TODO: put this in Mathlib.MeasureTheory.PiSystem perhaps, just after
-- `MeasurableSpace.DynkinSystem.has_diff`

variable {α : Type*} (d : DynkinSystem α)

lemma _root_.MeasurableSpace.DynkinSystem.has_iUnion_of_mono {α : Type*} (d : DynkinSystem α)
    {A : ℕ → Set α} (h_mono : Monotone A) (hA : ∀ (i : ℕ), d.Has (A i)) : d.Has (⋃ i, A i) := by
  have h_union : d.Has (⋃ n, (A (n + 1) \ A n)) := by
    refine d.has_iUnion (fun i j hij  ↦ ?_) (fun n ↦ d.has_diff (hA _) (hA _) (h_mono n.le_succ))
    cases lt_or_gt_of_ne hij <;> simp only [disjoint_left, mem_diff, not_and, not_not, and_imp]
    · exact fun x hx₁ _ _ ↦ h_mono (by grind) hx₁
    · exact fun x hx₁ hx₂ hx₃ ↦ (hx₂ (h_mono (by grind) hx₃)).elim
  have : ⋃ n, A n = A 0 ∪ ⋃ n, A (n + 1) \ A n := by
    ext x
    simp only [mem_iUnion, mem_union]
    refine ⟨fun ⟨w, h⟩ ↦ ?_, by grind⟩
    contrapose! h
    exact w.recOn h.1 (by grind)
  refine this ▸ d.has_union (hA 0) h_union ?_
  simp only [disjoint_left, mem_iUnion, mem_diff, not_exists, not_and, not_not]
  exact fun x hx n _ ↦ h_mono n.zero_le hx

lemma _root_.MeasurableSpace.DynkinSystem.has_iInter_of_anti {α : Type*} (d : DynkinSystem α)
    {B : ℕ → Set α} (h_anti : Antitone B) (hB : ∀ (i : ℕ), d.Has (B i)) : d.Has (⋂ i, B i) := by
  have h_sdiff : d.Has (⋃ n, (B n) \ (B (n + 1))) := by
    refine d.has_iUnion (fun i j hij  ↦ ?_) (fun n ↦ d.has_diff (hB n) (hB _) (h_anti n.le_succ))
    cases lt_or_gt_of_ne hij <;> simp only [disjoint_left, mem_diff, not_and, not_not, and_imp]
    · exact fun x hx₁ hx₂ hx₃ ↦ (hx₂ <| h_anti (by grind) hx₃).elim
    · exact fun _ h _ _ ↦ h_anti (by grind) h
  have : ⋂ n, B n = (( ⋃ n, (B n) \ (B (n + 1)) ) ∪ ( B 0 )ᶜ)ᶜ := by
    ext x
    refine ⟨by simp_all, ?_⟩
    simp only [compl_union, compl_iUnion, mem_inter_iff, mem_iInter, mem_compl_iff, mem_diff,
      not_and, not_not, and_imp]
    exact fun h h0 i ↦ Nat.recOn i h0 fun n ih ↦ h n ih
  rw [this, ← d.has_compl_iff, compl_compl]
  exact d.has_union h_sdiff (d.has_compl (hB 0)) (disjoint_left.mpr
    fun x hx₁ hx₂ ↦ hx₂ (h_anti (Nat.zero_le _) (mem_iUnion.mp hx₁).choose_spec.1))

end PiSystem

/-- Every Dynkin system forms a Monotone class. -/
def ofDynkinSystem (d : DynkinSystem α) : MonotoneClass α where
  Has := d.Has
  has_iUnion {_} hA h_mono := d.has_iUnion_of_mono h_mono hA
  has_iInter {_} hB h_anti := d.has_iInter_of_anti h_anti hB

lemma ofDynkinSystem_le_ofDynkinSystem_iff {d₁ d₂ : DynkinSystem α} :
    ofDynkinSystem d₁ ≤ ofDynkinSystem d₂ ↔ d₁ ≤ d₂ := Iff.rfl

/-- Every σ-algebra forms a Monotone class. -/
def ofMeasurableSpace (m : MeasurableSpace α) : MonotoneClass α :=
  ofDynkinSystem (MeasurableSpace.DynkinSystem.ofMeasurableSpace m)

lemma ofMeasurableSpace_le_ofMeasurableSpace_iff {m₁ m₂ : MeasurableSpace α} :
    ofMeasurableSpace m₁ ≤ ofMeasurableSpace m₂ ↔ m₁ ≤ m₂ := Iff.rfl

section Generate

/-- The least MonotoneClass containing a collection of basic sets.
  This inductive type gives the underlying collection of sets. -/
inductive GenerateHas (s : Set (Set α)) : Set α → Prop
  | basic : ∀ t ∈ s, GenerateHas s t
  | iUnion : ∀ {A : ℕ → Set α}, (∀ n, GenerateHas s (A n)) → Monotone A → GenerateHas s (⋃ n, A n)
  | iInter : ∀ {B : ℕ → Set α}, (∀ n, GenerateHas s (B n)) → Antitone B → GenerateHas s (⋂ n, B n)

/-- The least MonotoneClass containing a collection of basic sets. -/
def generate (s : Set (Set α)) : MonotoneClass α where
  Has := GenerateHas s
  has_iUnion {_} := GenerateHas.iUnion
  has_iInter {_} := GenerateHas.iInter

variable {s : Set (Set α)}

theorem generateHas_def : (generate s).Has = GenerateHas s := rfl

/- If `s` is an algebra of sets, then the monotone class generated by `s` is closed
under complements. -/
lemma generateHas_compl (hs : IsSetAlgebra s) {t : Set α} (ht : (generate s).Has t) :
    (generate s).Has tᶜ := by
  induction ht with
  | basic A hA => exact .basic _ (hs.compl_mem hA)
  | iUnion hA h_mono ih =>
    rw [compl_iUnion]
    exact .iInter ih (fun n m hnm ↦ compl_subset_compl.mpr (h_mono hnm))
  | iInter hB h_anti ih =>
    rw [compl_iInter]
    exact .iUnion ih (fun n m hnm ↦ compl_subset_compl.mpr (h_anti hnm))

/-- If `s` is an algebra of sets, then the monotone class generated by `s` is closed
under intersections. -/
lemma generateHas_inter (hs : IsSetAlgebra s) {t u : Set α}
    (ht : (generate s).Has t) (hu : (generate s).Has u) :
    (generate s).Has (t ∩ u) := by
  induction ht with
  | basic A hA =>
    induction hu with
    | basic B hB => exact .basic _ (hs.inter_mem hA hB)
    | iUnion hA h_mono ih =>
      rw [inter_iUnion]
      exact (generate s).has_iUnion ih (fun n m hnm ↦ inter_subset_inter le_rfl (h_mono hnm))
    | iInter hB h_anti ih =>
      rw [inter_iInter]
      exact .iInter ih (fun n m hnm ↦ inter_subset_inter le_rfl (h_anti hnm))
  | iUnion hA h_mono ih =>
    rw [iUnion_inter]
    exact (generate s).has_iUnion ih (fun n m hnm ↦ inter_subset_inter (h_mono hnm) le_rfl)
  | iInter hB h_anti ih =>
    rw [iInter_inter]
    exact .iInter ih (fun n m hnm ↦ inter_subset_inter (h_anti hnm) le_rfl)

/-- If `s` is an algebra of sets, then the monotone class it generates is an algebra of sets. -/
lemma isSetAlgebra_generateHas (hs : IsSetAlgebra s) : IsSetAlgebra (generate s).Has := by
  refine ⟨.basic _ hs.empty_mem, fun _ ↦ generateHas_compl hs, fun t₁ t₂ ht₁ ht₂ ↦ ?_⟩
  rw [union_eq_compl_compl_inter_compl t₁ t₂]
  exact generateHas_compl hs
    (generateHas_inter hs (generateHas_compl hs ht₁) (generateHas_compl hs ht₂))

/-- The monotone class generated by `s` is the smallest monotone class containing `s`. -/
lemma generate_le (h : ∀ t ∈ s, C.Has t) : generate s ≤ C :=
  fun _ ht ↦ ht.recOn h
    (fun _ h_mono hA ↦ C.has_iUnion hA h_mono) (fun _ h_anti hB ↦ C.has_iInter _ hB h_anti)

/-- If a set belongs to the monotone class generated by `s`, then it is measurable
for the σ-algebra generated by `s`. -/
lemma generate_has_subset_generate_measurable {S : Set α} (hS : (generate s).Has S) :
    MeasurableSet[generateFrom s] S :=
  generate_le (ofMeasurableSpace (generateFrom s)) (fun _ => measurableSet_generateFrom) S hS

end Generate

instance : Inhabited (MonotoneClass α) := ⟨generate univ⟩

/-- If a Monotone class is a set algebra, then it forms a `σ`-algebra. -/
def toMeasurableSpace (C : MonotoneClass α) (h : IsSetAlgebra C.Has) :
    MeasurableSpace α where
  MeasurableSet' := C.Has
  measurableSet_empty := h.empty_mem
  measurableSet_compl _ hs := h.compl_mem hs
  measurableSet_iUnion f hf := by
    rw [← biUnion_lt_eq_iUnion]
    refine C.has_iUnion (fun n ↦ ?_) ?_
    · induction n with
      | zero => simpa using h.empty_mem
      | succ n ih => exact biUnion_lt_succ _ _ ▸  h.union_mem ih (hf n)
    · exact fun n m hnm ↦ iUnion_subset fun i ↦ iUnion_subset fun hi ↦ subset_iUnion_of_subset i
        (subset_iUnion_of_subset (hi.trans_le hnm) (Subset.refl _))

lemma ofMeasurableSpace_toMeasurableSpace (h : IsSetAlgebra C.Has) :
    ofMeasurableSpace (C.toMeasurableSpace h) = C :=
  ext fun _ => Iff.rfl

/-- **Monotone Class theorem**:

Given a set algebra `s`. Then the monotone class generated by `s` is equal to the
σ-algebra generated by `s`.
-/
theorem generateFrom_eq {s : Set (Set α)} (hs : IsSetAlgebra s) :
    (generateFrom s).MeasurableSet' = (generate s).Has := by
  refine le_antisymm ?_ fun t ht ↦ ?_
  · change generateFrom s ≤ (generate s).toMeasurableSpace (isSetAlgebra_generateHas hs)
    exact generateFrom_le fun t ht ↦ .basic t ht
  · induction ht with
    | basic _ h => exact measurableSet_generateFrom h
    | iUnion _ _ ih => exact MeasurableSet.iUnion ih
    | iInter _ _ ih => exact MeasurableSet.iInter ih

end MonotoneClass

/--
Induction principle for measurable sets based on the Monotone Class theorem.
If `s` is a set algebra that generates the `σ`-algebra on `α`
and a predicate `C` defined on measurable sets is true

- on each set `t ∈ s`;
- on the union of monotone sequences of measurable sets that satisfy `C`;
- on the intersection of antitone sequences of measurable sets that satisfy `C`,

then it is true on all measurable sets in `α`.
-/
@[elab_as_elim]
theorem induction_on_monotone {m : MeasurableSpace α} {C : ∀ s : Set α, MeasurableSet s → Prop}
    {s : Set (Set α)} (h_eq : m = generateFrom s) (h_inter : IsSetAlgebra s)
    (basic : ∀ t (ht : t ∈ s), C t <| h_eq ▸ .basic t ht)
    (iUnion : ∀ (A : ℕ → Set α), (Monotone A) → ∀ (hfm : ∀ i, MeasurableSet (A i)),
      (∀ i, C (A i) (hfm i)) → C (⋃ i, A i) (.iUnion hfm))
    (iInter : ∀ (A : ℕ → Set α), (Antitone A) → ∀ (hfm : ∀ i, MeasurableSet (A i)),
      (∀ i, C (A i) (hfm i)) → C (⋂ i, A i) (.iInter hfm)) :
    ∀ t (ht : MeasurableSet t), C t ht := by
  have eq : ∀ t, MeasurableSet t ↔ MonotoneClass.GenerateHas s t := by
    have := h_eq ▸ MonotoneClass.generateFrom_eq h_inter
    exact fun t ↦ (Eq.to_iff (congrFun this t))
  simp_rw [eq]
  refine fun t ht ↦ ?_
  subst h_eq
  induction ht with
  | basic u hu => exact basic u hu
  | iUnion h_mono hA ih =>
    exact iUnion _ hA (fun i ↦ MonotoneClass.generate_has_subset_generate_measurable (h_mono i)) ih
  | iInter h_anti hA ih =>
    exact iInter _ hA (fun i ↦ MonotoneClass.generate_has_subset_generate_measurable (h_anti i)) ih

end MeasureTheory
