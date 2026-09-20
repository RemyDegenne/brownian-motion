/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.Algebra
public import BrownianMotion.StochasticIntegral.ClassD
public import BrownianMotion.StochasticIntegral.Komlos
public import BrownianMotion.StochasticIntegral.Predictable
public import BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification
public import Mathlib.Topology.Order.LiminfLimsup

import Mathlib.Order.CompleteLattice.Group
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Metrizable.Urysohn

/-! # Doob-Meyer decomposition theorem

-/

@[expose] public section

open MeasureTheory Filter Order ProbabilityTheory Convexity
open scoped NNReal ENNReal Topology

/-- An element of `WithTop α` other than `⊤` is at most the coercion of `⊤ : α`. -/
lemma WithTop.le_coe_top {α : Type*} [Preorder α] [OrderTop α] {x : WithTop α} (hx : x ≠ ⊤) :
    x ≤ ((⊤ : α) : WithTop α) := by
  lift x to α using hx
  exact mod_cast le_top

/-- A compact Hausdorff second-countable space is Polish: it is metrizable by Urysohn's
metrization theorem, and a compact metric space is complete. -/
lemma PolishSpace.of_compactSpace_of_secondCountableTopology {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [SecondCountableTopology X] : PolishSpace X := by
  letI := TopologicalSpace.metrizableSpaceMetric X
  infer_instance

/-- A linear order in which all the intervals `Iio t` are finite is countable. -/
lemma countable_of_linearOrder_of_locallyFiniteOrderBot (ι : Type*) [LinearOrder ι]
    [LocallyFiniteOrderBot ι] :
    Countable ι :=
  Function.Injective.countable (f := fun t : ι ↦ (Finset.Iio t).card)
    (StrictMono.injective fun _ _ h ↦ Finset.card_lt_card (Finset.Iio_ssubset_Iio h))

/-- If the section `{t | n ≤ t ∧ (t, ω) ∈ E}` of a set `E` is finite and nonempty, then the début
of `E` after `n` at `ω` belongs to that section. -/
lemma MeasureTheory.debut_mem_set_of_finite {ι Ω : Type*} [ConditionallyCompleteLinearOrder ι]
    {E : Set (ι × Ω)} {n : ι} {ω : Ω} (hfin : {t | n ≤ t ∧ (t, ω) ∈ E}.Finite)
    (h : ∃ t ≥ n, (t, ω) ∈ E) :
    ((debut E n ω).untopA, ω) ∈ E := by
  have hmem : sInf {t | n ≤ t ∧ (t, ω) ∈ E} ∈ {t | n ≤ t ∧ (t, ω) ∈ E} :=
    Set.Nonempty.csInf_mem h hfin
  simp only [debut_eq_ite, ge_iff_le, if_pos h, WithTop.untopD_coe]
  exact hmem.2

/-- Optional sampling for a stopping time with countable range bounded by `n`. This is
`Martingale.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range` without any topological
assumption on the index set. -/
lemma MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range'
    {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι] {m : MeasurableSpace Ω} {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ℱ : Filtration ι m}
    [SigmaFiniteFiltration μ ℱ] {τ : Ω → WithTop ι} {f : ι → Ω → E} {n : ι}
    (h : Martingale f ℱ μ) (hτ : IsStoppingTime ℱ τ) (hτ_le : ∀ x, τ x ≤ n)
    (h_countable_range : (Set.range τ).Countable)
    [SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le))] :
    stoppedValue f τ =ᵐ[μ] μ[f n | hτ.measurableSpace] := by
  have h_univ : Set.univ = ⋃ i ∈ Set.range τ, {x | τ x = i} := by
    ext1 x
    simp
  nth_rw 1 [← @Measure.restrict_univ Ω _ μ]
  rw [h_univ, ae_eq_restrict_biUnion_iff _ h_countable_range]
  intro i hi
  obtain ⟨ω, rfl⟩ := hi
  have h_top : τ ω ≠ ⊤ := fun h_eq ↦ by simpa [h_eq] using hτ_le ω
  obtain ⟨i, hi⟩ := WithTop.ne_top_iff_exists.1 h_top
  rw [← hi]
  have hin : i ≤ n := by
    have := hτ_le ω
    rw [← hi] at this
    exact mod_cast this
  have h_cond : μ[f n | hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] f i := by
    refine Filter.EventuallyEq.trans ?_ (ae_restrict_of_ae (h.condExp_ae_eq hin))
    refine condExp_ae_eq_restrict_of_measurableSpace_eq_on (hτ.measurableSpace_le_of_le hτ_le)
      (ℱ.le i) (hτ.measurableSet_eq_of_countable_range' h_countable_range i) fun t ↦ ?_
    rw [Set.inter_comm _ t, IsStoppingTime.measurableSet_inter_eq_iff]
  refine Filter.EventuallyEq.trans ?_ h_cond.symm
  rw [Filter.EventuallyEq, ae_restrict_iff'
    (ℱ.le _ _ (hτ.measurableSet_eq_of_countable_range h_countable_range i))]
  refine Filter.Eventually.of_forall fun x hx ↦ ?_
  rw [Set.mem_ofPred_eq] at hx
  simp [stoppedValue, hx]

section DenseMesh

/-- The fixed countable dense set used instead of dyadics, with both endpoints adjoined, as well as
the points that are isolated from the right or from the left. Those points are not limits of other
points from the corresponding side, hence the values of a process at these times are not controlled
by its values on a set which is merely dense. If `ι` is densely ordered, the only such points are
`⊥` and `⊤`. -/
noncomputable def denseSet (ι : Type*) [Preorder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] : Set ι :=
  (TopologicalSpace.exists_countable_dense ι).choose ∪ ({⊥, ⊤} : Set ι)
    ∪ {t | 𝓝[>] t = ⊥} ∪ {t | 𝓝[<] t = ⊥}

lemma denseSet_countable (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] :
    (denseSet ι).Countable :=
  (((TopologicalSpace.exists_countable_dense ι).choose_spec.1.union (by simp)).union
    countable_setOfPred_isolated_right).union countable_setOfPred_isolated_left

lemma denseSet_dense (ι : Type*) [Preorder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] : Dense (denseSet ι) :=
  (TopologicalSpace.exists_countable_dense ι).choose_spec.2.mono fun _ h ↦ .inl (.inl (.inl h))

lemma bot_mem_denseSet (ι : Type*) [Preorder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] : ⊥ ∈ denseSet ι := by simp [denseSet]

lemma top_mem_denseSet (ι : Type*) [Preorder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] : ⊤ ∈ denseSet ι := by simp [denseSet]

/-- The points that are isolated from the right belong to the dense set. -/
lemma mem_denseSet_of_nhdsGT_eq_bot {ι : Type*} [Preorder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] {t : ι} (ht : 𝓝[>] t = ⊥) :
    t ∈ denseSet ι := .inl (.inr ht)

/-- The points that are isolated from the left belong to the dense set. -/
lemma mem_denseSet_of_nhdsLT_eq_bot {ι : Type*} [Preorder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] {t : ι} (ht : 𝓝[<] t = ⊥) :
    t ∈ denseSet ι := .inr ht

/-- Between two times `a < b` there is a point `d` of the dense set with `a ≤ d < b`: a point of
the open interval `(a, b)` if that interval is nonempty, and `a` itself otherwise since `a` is
then isolated from the right. -/
lemma exists_mem_denseSet_Ico {ι : Type*} [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] {a b : ι} (hab : a < b) :
    ∃ d ∈ denseSet ι, a ≤ d ∧ d < b := by
  by_cases h : (Set.Ioo a b).Nonempty
  · obtain ⟨d, hd_mem, hd⟩ := (denseSet_dense ι).exists_mem_open isOpen_Ioo h
    exact ⟨d, hd_mem, hd.1.le, hd.2⟩
  · have hcov : a ⋖ b := ⟨hab, fun c hac hcb ↦ h ⟨c, hac, hcb⟩⟩
    exact ⟨a, mem_denseSet_of_nhdsGT_eq_bot hcov.nhdsGT, le_rfl, hab⟩

/-- A choice of enumeration of the countable dense set used to construct finite meshes. -/
noncomputable def denseEnum (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] : ℕ → ι :=
  have : Nonempty (denseSet ι) := ⟨⟨⊥, by simp [denseSet]⟩⟩
  Subtype.val ∘ (countable_iff_exists_surjective.mp (denseSet_countable ι)).choose

/-- Every element of the dense set is attained by the enumeration. -/
lemma exists_denseEnum_eq (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] {d : ι}
    (hd : d ∈ denseSet ι) :
    ∃ k, denseEnum ι k = d := by
  have : Nonempty (denseSet ι) := ⟨⟨⊥, by simp [denseSet]⟩⟩
  obtain ⟨k, hk⟩ :=
    (countable_iff_exists_surjective.mp (denseSet_countable ι)).choose_spec ⟨d, hd⟩
  exact ⟨k, congrArg Subtype.val hk⟩

/-- The `n`-th finite mesh: the first `n` points of the dense enumeration, plus endpoints. -/
noncomputable def mesh (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] (n : ℕ) : Finset ι :=
  insert ⊥ <| insert ⊤ <| (Finset.range n).image (denseEnum ι)

/-- The `k`-th point of the dense enumeration belongs to all meshes past `k`. -/
lemma denseEnum_mem_mesh (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] {k n : ℕ} (hkn : k < n) :
    denseEnum ι k ∈ mesh ι n := by
  simp only [mesh, Finset.mem_insert, Finset.mem_image]
  exact .inr <| .inr ⟨k, Finset.mem_range.2 hkn, rfl⟩

lemma bot_mem_mesh (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] (n : ℕ) :
    (⊥ : ι) ∈ mesh ι n := by simp [mesh]

lemma top_mem_mesh (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] (n : ℕ) :
    (⊤ : ι) ∈ mesh ι n := by simp [mesh]

instance (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] (n : ℕ) : OrderBot
    (mesh ι n) where
  bot := ⟨⊥, bot_mem_mesh ι n⟩
  bot_le _ := bot_le

instance (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] (n : ℕ) : OrderTop
    (mesh ι n) where
  top := ⟨⊤, top_mem_mesh ι n⟩
  le_top _ := le_top

@[simp]
lemma top_eq_top (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] (n : ℕ) : (⊤ : mesh ι n) =
    (⊤ : ι) := by rfl

@[simp]
lemma bot_eq_bot (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] (n : ℕ) : (⊥ : mesh ι n) =
    (⊥ : ι) := by rfl

noncomputable instance (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] (n : ℕ) : LocallyFiniteOrder
    (mesh ι n) :=
  Fintype.toLocallyFiniteOrder

noncomputable instance (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] (n : ℕ) : SuccOrder
    (mesh ι n) :=
  LinearLocallyFiniteOrder.succOrder (mesh ι n)

noncomputable instance (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] (n : ℕ) : PredOrder
    (mesh ι n) :=
  LinearLocallyFiniteOrder.predOrder (mesh ι n)

noncomputable instance (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] (n : ℕ) : CompleteLinearOrder
    (mesh ι n) :=
  Fintype.toCompleteLinearOrder (mesh ι n)

end DenseMesh

section Estimate

/-- The filtration obtained by restricting `𝓕` to a finite dense mesh. -/
def meshFiltration {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [LinearOrder ι]
    [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ι mΩ)
    (n : ℕ) :
    Filtration (mesh ι n) mΩ :=
  𝓕.indexComap (Subtype.mono_coe (· ∈ (mesh ι n)))

instance sigmaFiniteFiltration_meshFiltration {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration P 𝓕]
    (n : ℕ) : SigmaFiniteFiltration P (meshFiltration 𝓕 n) := by
  unfold meshFiltration
  infer_instance

/-- Predictable part of a discrete process. -/
noncomputable def predictablePart {ι Ω E : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    ι → Ω → E :=
  fun n ↦ ∑ i ∈ Finset.Iio n, P[S (succ i) - S i | 𝓕 i]

/-- The predictable part is additive for integrable processes. -/
lemma predictablePart_add {ι Ω E : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {P : Measure Ω} {S₁ S₂ : ι → Ω → E} (𝓕 : Filtration ι mΩ)
    (hS₁ : ∀ t, Integrable (S₁ t) P) (hS₂ : ∀ t, Integrable (S₂ t) P) (t : ι) :
    predictablePart (S₁ + S₂) 𝓕 P t =ᵐ[P] predictablePart S₁ 𝓕 P t + predictablePart S₂ 𝓕 P t := by
  simp only [_root_.predictablePart, ← Finset.sum_add_distrib]
  refine eventuallyEq_sum fun i _ => ?_
  rw [show (S₁ + S₂) (succ i) - (S₁ + S₂) i =
    (S₁ (succ i) - S₁ i) + (S₂ (succ i) - S₂ i) by simp; abel]
  exact condExp_add ((hS₁ (succ i)).sub (hS₁ i)) ((hS₂ (succ i)).sub (hS₂ i)) (𝓕 i)

/-- The predictable part of a martingale is zero at every time. -/
lemma predictablePart_eq_zero_of_martingale {ι Ω E : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {P : Measure Ω} {S : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hS : Martingale S 𝓕 P)
    (t : ι) :
    predictablePart S 𝓕 P t =ᵐ[P] 0 := by
  rw [_root_.predictablePart, ← Finset.sum_const_zero]
  refine eventuallyEq_sum fun i _ => ?_
  grw [condExp_sub (hS.integrable (succ i)) (hS.integrable i) (𝓕 i),
    (hS.condExp_ae_eq (le_succ i)).sub (hS.condExp_ae_eq le_rfl), sub_self]

@[simp]
lemma predictablePart_bot {ι Ω E : Type*} [Preorder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    predictablePart S 𝓕 P ⊥ = 0 := by
  simp [_root_.predictablePart]

/-- The predictable part at a fixed point of a discrete mesh is integrable. -/
lemma integrable_predictablePart {ι Ω E : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    (t : ι) :
    Integrable (predictablePart S 𝓕 P t) P := by
  simp only [_root_.predictablePart]
  exact integrable_finsetSum' (Finset.Iio t) fun _ _ => integrable_condExp

/-- The predictable part of a discrete submartingale is monotone a.e. -/
lemma MeasureTheory.Submartingale.monotone_predictablePart_ae {ι Ω E : Type*} [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [SuccOrder ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [PartialOrder E]
    [IsOrderedAddMonoid E] {S : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hs : Submartingale S 𝓕 P) :
    ∀ᵐ ω ∂P, Monotone (_root_.predictablePart S 𝓕 P · ω) := by
  have : Countable ι := countable_of_linearOrder_of_locallyFiniteOrderBot ι
  have hnonneg : ∀ᵐ ω ∂P, ∀ i : ι, 0 ≤ P[S (succ i) - S i | 𝓕 i] ω :=
    ae_all_iff.2 fun i ↦ hs.condExp_sub_nonneg (le_succ i)
  filter_upwards [hnonneg] with ω hω a b hab
  simp only [_root_.predictablePart, Finset.sum_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iio_subset_Iio hab) fun i _ _ ↦ hω i

/-- The predictable part of a discrete submartingale is nonnegative a.e. -/
lemma MeasureTheory.Submartingale.predictablePart_nonneg' {ι Ω E : Type*} [LinearOrder ι]
    [LocallyFiniteOrder ι] [OrderBot ι] [SuccOrder ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [PartialOrder E]
    [IsOrderedAddMonoid E] {S : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hs : Submartingale S 𝓕 P) :
    ∀ᵐ ω ∂P, ∀ n, 0 ≤ _root_.predictablePart S 𝓕 P n ω := by
  filter_upwards [hs.monotone_predictablePart_ae] with ω hω n
  simpa [predictablePart_bot] using hω bot_le

/-- Martingale part of a discrete process. -/
noncomputable def martingalePart {ι Ω E : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    ι → Ω → E :=
  S - predictablePart S 𝓕 P

/-- The martingale part is additive for integrable processes. -/
lemma martingalePart_add {ι Ω E : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {P : Measure Ω} {S₁ S₂ : ι → Ω → E} {𝓕 : Filtration ι mΩ}
    (hS₁ : ∀ t, Integrable (S₁ t) P) (hS₂ : ∀ t, Integrable (S₂ t) P) (t : ι) :
    martingalePart (S₁ + S₂) 𝓕 P t =ᵐ[P] martingalePart S₁ 𝓕 P t + martingalePart S₂ 𝓕 P t := by
  filter_upwards [predictablePart_add 𝓕 hS₁ hS₂ t] with ω hω
  simp [_root_.martingalePart, hω]
  abel

/-- The martingale part of a martingale is the martingale itself. -/
lemma martingalePart_eq_self_of_martingale {ι Ω E : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {P : Measure Ω} {S : ι → Ω → E} {𝓕 : Filtration ι mΩ}
    (hS : Martingale S 𝓕 P) (t : ι) :
    martingalePart S 𝓕 P t =ᵐ[P] S t := by
  filter_upwards [predictablePart_eq_zero_of_martingale hS t] with ω hω
  simp [_root_.martingalePart, hω]

/-- The predictable part of a process is strongly adapted. -/
lemma stronglyAdapted_predictablePart {ι Ω E : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    StronglyAdapted 𝓕 (predictablePart S 𝓕 P) :=
  fun _ => Finset.stronglyMeasurable_sum _ fun _ hi =>
    stronglyMeasurable_condExp.mono (𝓕.mono (Finset.mem_Iio.1 hi).le)

/-- The predictable part at `succ j` is the predictable part at `j` plus the conditional
expectation of the increment. -/
lemma predictablePart_succ_of_not_isMax {ι Ω E : Type*} [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) {j : ι}
    (hj : ¬ IsMax j) :
    predictablePart S 𝓕 P (succ j) = predictablePart S 𝓕 P j + P[S (succ j) - S j | 𝓕 j] := by
  simp only [_root_.predictablePart]
  rw [Finset.Iio_succ_eq_Iic_of_not_isMax hj, ← Finset.Iio_insert,
    Finset.sum_insert Finset.notMem_Iio_self, add_comm]

/-- The martingale part of an adapted integrable process is a martingale. -/
lemma martingale_martingalePart {ι Ω E : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {S : ι → Ω → E} {𝓕 : Filtration ι mΩ} {P : Measure Ω}
    [SigmaFiniteFiltration P 𝓕] (hS_adapted : StronglyAdapted 𝓕 S)
    (hS_int : ∀ t, Integrable (S t) P) :
    Martingale (martingalePart S 𝓕 P) 𝓕 P := by
  have hM_meas : StronglyAdapted 𝓕 (martingalePart S 𝓕 P) := fun t ↦
    (hS_adapted t).sub (stronglyAdapted_predictablePart S 𝓕 P t)
  have hM_int : ∀ t, Integrable (martingalePart S 𝓕 P t) P := fun t ↦
    (hS_int t).sub (integrable_predictablePart S 𝓕 P t)
  refine ⟨hM_meas, fun i j hij ↦ ?_⟩
  induction hij using Succ.rec with
  | rfl => rw [condExp_of_stronglyMeasurable (𝓕.le i) (hM_meas i) (hM_int i)]
  | succ j hij ih =>
    by_cases hj : IsMax j
    · rwa [hj.succ_eq]
    have h_eq : martingalePart S 𝓕 P (succ j) = martingalePart S 𝓕 P j
        + ((S (succ j) - S j) - P[S (succ j) - S j | 𝓕 j]) := by
      simp only [_root_.martingalePart, Pi.sub_apply, predictablePart_succ_of_not_isMax S 𝓕 P hj]
      abel
    have h_int : Integrable (S (succ j) - S j) P := (hS_int (succ j)).sub (hS_int j)
    have h_tower : P[P[S (succ j) - S j | 𝓕 j] | 𝓕 i] =ᵐ[P] P[S (succ j) - S j | 𝓕 i] :=
      condExp_condExp_of_le (𝓕.mono hij) (𝓕.le j)
    rw [h_eq]
    filter_upwards [condExp_add (hM_int j) (h_int.sub integrable_condExp) (𝓕 i),
      condExp_sub h_int integrable_condExp (𝓕 i), h_tower, ih] with ω h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.sub_apply, h3, h4, sub_self, add_zero]

@[simp]
lemma martingalePart_add_predictablePart {ι Ω E : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    martingalePart S 𝓕 P + predictablePart S 𝓕 P = S := by
  simp [_root_.martingalePart]

/-- Sequence of terminal values of the predictable part. -/
noncomputable def predictableSeqTop {ι Ω E : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    (n : ℕ) : Ω → E :=
  predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⊤

/-- The terminal values of the predictable parts on each mesh are integrable. -/
lemma integrable_predictableSeqTop {ι Ω E : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) :
    Integrable (predictableSeqTop S 𝓕 P n) P :=
  integrable_predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⊤

/-- The terminal values of the predictable parts of a martingale vanish on every mesh. -/
lemma predictableSeqTop_eq_zero_of_martingale {ι Ω E : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure Ω} {S : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hS : Martingale S 𝓕 P)
    (n : ℕ) :
    predictableSeqTop S 𝓕 P n =ᵐ[P] 0 := by
  simp only [predictableSeqTop, meshFiltration]
  apply predictablePart_eq_zero_of_martingale _ ⊤
  exact (hS.indexComap (Subtype.mono_coe (· ∈ (mesh ι n))))

/-- Sequence of terminal values of the martingale part. -/
noncomputable def martingaleSeqTop {ι Ω E : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) : Ω → E :=
  martingalePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⊤

/-- The terminal values of the discrete martingale parts are additive. -/
lemma martingaleSeqTop_add {ι Ω E : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {P : Measure Ω}
    {S₁ S₂ : ι → Ω → E} (𝓕 : Filtration ι mΩ) (hS₁ : ∀ t, Integrable (S₁ t) P)
    (hS₂ : ∀ t, Integrable (S₂ t) P) (n : ℕ) :
    martingaleSeqTop (S₁ + S₂) 𝓕 P n =ᵐ[P]
      martingaleSeqTop S₁ 𝓕 P n + martingaleSeqTop S₂ 𝓕 P n :=
  martingalePart_add (fun t : mesh ι n ↦ hS₁ t) (fun t ↦ hS₂ t) ⊤

/-- The terminal values of the martingale parts of a martingale are its terminal value on every
mesh. -/
lemma martingaleSeqTop_eq_self_of_martingale {ι Ω E : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure Ω} {S : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hS : Martingale S 𝓕 P)
    (n : ℕ) :
    martingaleSeqTop S 𝓕 P n =ᵐ[P] S ⊤ := by
  simp only [martingaleSeqTop, meshFiltration]
  apply martingalePart_eq_self_of_martingale _ ⊤
  exact (hS.indexComap (Subtype.mono_coe (· ∈ (mesh ι n))))

/-- If `S = 0` a.e., then the martingale part’s terminal value equals the negative of the
predictable part’s terminal value. -/
lemma martingaleSeqTop_eq_neg_predictableSeqTop {ι Ω E : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : ι → Ω → E} (𝓕 : Filtration ι mΩ) (hstop : S ⊤ =ᶠ[ae P] 0)
    (n : ℕ) :
    martingaleSeqTop S 𝓕 P n =ᶠ[ae P] -predictableSeqTop S 𝓕 P n := by
  simp only [martingaleSeqTop, _root_.martingalePart, Pi.sub_apply, Function.comp_apply, top_eq_top,
    predictableSeqTop]
  grw [neg_eq_zero_sub, hstop]

/-- The terminal values of the martingale parts on each mesh are integrable. -/
lemma integrable_martingaleSeqTop {ι Ω E : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {S : ι → Ω → E} (𝓕 : Filtration ι mΩ) (hS : Integrable (S ⊤) P) (n : ℕ) :
    Integrable (martingaleSeqTop S 𝓕 P n) P := by
  simpa [martingaleSeqTop, _root_.martingalePart, predictableSeqTop] using
    hS.sub (integrable_predictableSeqTop S 𝓕 P n)

/-- The discrete martingale part of an adapted integrable process on the `n`-th mesh is a
martingale. -/
lemma martingale_martingalePart_mesh {ι Ω E : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {S : ι → Ω → E} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration P 𝓕]
    (hS_adapted : StronglyAdapted 𝓕 S) (hS_int : ∀ t, Integrable (S t) P) (n : ℕ) :
    Martingale (martingalePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P) (meshFiltration 𝓕 n) P :=
  martingale_martingalePart (fun t ↦ hS_adapted t) (fun t ↦ hS_int t)

/-- On each mesh, the terminal value of the martingale part has the same expectation as the
initial value of the process. -/
lemma integral_martingaleSeqTop {ι Ω E : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {S : ι → Ω → E}
    (𝓕 : Filtration ι mΩ) [SigmaFiniteFiltration P 𝓕] (hS_adapted : StronglyAdapted 𝓕 S)
    (hS_int : ∀ t, Integrable (S t) P) (n : ℕ) :
    ∫ ω, martingaleSeqTop S 𝓕 P n ω ∂P = ∫ ω, S ⊥ ω ∂P := by
  calc ∫ ω, martingaleSeqTop S 𝓕 P n ω ∂P
      = ∫ ω, (P[martingaleSeqTop S 𝓕 P n|meshFiltration 𝓕 n ⊥]) ω ∂P :=
        (integral_condExp ((meshFiltration 𝓕 n).le ⊥)).symm
    _ = ∫ ω, martingalePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⊥ ω ∂P :=
        integral_congr_ae
          ((martingale_martingalePart_mesh hS_adapted hS_int n).condExp_ae_eq bot_le)
    _ = ∫ ω, S ⊥ ω ∂P := by simp [_root_.martingalePart]

/-- Apply the optional stopping theorem to get equation 4. -/
lemma equation4 {ι Ω E : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {S : ι → Ω → E}
    {𝓕 : Filtration ι mΩ} {n : ℕ} [SigmaFiniteFiltration P 𝓕] (hS_adapted : StronglyAdapted 𝓕 S)
    (hS_int : ∀ t, Integrable (S t) P) (hstop : S ⊤ =ᶠ[ae P] 0)
    {τ : Ω → WithTop (mesh ι n)} (hτ : ∀ ω, τ ω ≤ WithTop.some (⊤ : mesh ι n))
    (hτs : IsStoppingTime (meshFiltration 𝓕 n) τ) :
    stoppedValue (S ∘ Subtype.val) τ =ᵐ[P]
      -P[(predictableSeqTop S 𝓕 P n) | hτs.measurableSpace] +
        stoppedValue (predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P) τ := by
  grw [← condExp_neg, ← martingaleSeqTop_eq_neg_predictableSeqTop 𝓕 hstop]
  simp only [martingaleSeqTop]
  grw [← (martingale_martingalePart_mesh hS_adapted hS_int
    n).stoppedValue_ae_eq_condExp_of_le_const_of_countable_range' hτs hτ (Set.to_countable _),
    ← stoppedValue.add, _root_.martingalePart_add_predictablePart]

section equation5

/-- The mesh stopping time `τₙ(c)` associated with the predictable part on the `n`-th mesh. -/
noncomputable def tauMesh {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) :
    Ω → WithTop (mesh ι n) :=
  fun ω ↦ (((hittingBtwn (fun (t : mesh ι n) ω ↦
    (predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P) (succ t) ω) (Set.Ioi c)
    ⊥ ⊤ ω) : mesh ι n) : WithTop (mesh ι n))

lemma tauMesh_le_top {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) (ω : Ω) :
    tauMesh S 𝓕 P n c ω ≤ (⊤ : mesh ι n) :=
  WithTop.coe_le_coe.2 (hittingBtwn_le ω)

/-- The stopped valued of the predictable part with respect to `τₙ(c)` is less than or equal to
`c`. -/
lemma stoppedValue_predictablePart_tauMesh_le {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω}
    (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    stoppedValue (predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P)
      (tauMesh S 𝓕 P n c) ≤ fun _ ↦ c := by
  intro ω
  let A := predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P
  let τ := hittingBtwn (fun t ω ↦ A (succ t) ω) (Set.Ioi c) ⊥ ⊤ ω
  change A τ ω ≤ c
  by_cases hτ_bot : τ = ⊥
  · simpa [A, hτ_bot] using hc
  · have hpred_lt : pred τ < τ := (pred_lt_iff_ne_bot).2 hτ_bot
    have hnot_min : ¬ IsMin τ := by simpa [isMin_iff_eq_bot] using hτ_bot
    simpa [succ_pred_of_not_isMin hnot_min] using notMem_of_lt_hittingBtwn hpred_lt bot_le

/-- If `f` is strongly measurable with respect to `𝓕 i`, then the process equal to `f` on
`(i, ∞)` and to `0` elsewhere is strongly measurable for the predictable σ-algebra. -/
lemma stronglyMeasurable_predictable_indicator_Ioi {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    {mΩ : MeasurableSpace Ω} [TopologicalSpace E] [Zero E] {𝓕 : Filtration ι mΩ} {i : ι}
    {f : Ω → E} (hf : StronglyMeasurable[𝓕 i] f) :
    StronglyMeasurable[𝓕.predictable]
      ((Set.Ioi i ×ˢ Set.univ).indicator fun p : ι × Ω ↦ f p.2) := by
  classical
  let : MeasurableSpace (ι × Ω) := 𝓕.predictable
  let F (n : ℕ) (p : ι × Ω) : E :=
    (Set.Ioi i ×ˢ Set.univ).indicator (fun p : ι × Ω ↦ hf.approx n p.2) p
  refine ⟨fun n ↦ SimpleFunc.mk (F n) (fun b ↦ ?_) ?_, fun p ↦ ?_⟩
  · have hA (s : Set E) : MeasurableSet[𝓕 i] (hf.approx n ⁻¹' s) := by
      let : MeasurableSpace Ω := 𝓕 i
      exact (hf.approx n).measurableSet_preimage s
    by_cases hb : b = 0
    · have h_eq : F n ⁻¹' {b} = (Set.Ioi i ×ˢ (hf.approx n ⁻¹' {b}ᶜ))ᶜ := by
        ext p
        by_cases hp : i < p.1 <;> simp [F, Set.indicator_apply, hp, hb]
      rw [h_eq]
      exact (measurableSet_predictable_Ioi_prod (hA _)).compl
    · have h_eq : F n ⁻¹' {b} = Set.Ioi i ×ˢ (hf.approx n ⁻¹' {b}) := by
        ext p
        by_cases hp : i < p.1 <;> simp [F, Set.indicator_apply, hp, Ne.symm hb]
      rw [h_eq]
      exact measurableSet_predictable_Ioi_prod (hA _)
  · have h_fin : (Set.range (hf.approx n)).Finite := by
      let : MeasurableSpace Ω := 𝓕 i
      exact (hf.approx n).finite_range
    refine (h_fin.insert 0).subset ?_
    rintro _ ⟨p, rfl⟩
    by_cases hp : i < p.1 <;> simp [F, Set.indicator_apply, hp]
  · by_cases hp : i < p.1
    · simpa [F, Set.indicator_apply, hp] using hf.tendsto_approx p.2
    · simpa [F, Set.indicator_apply, hp] using tendsto_const_nhds

/-- The predictable part is predictable. -/
lemma isPredictable_predictablePart {ι Ω E : Type*} [LinearOrder ι] [LocallyFiniteOrder ι]
    [OrderBot ι] [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    IsStronglyPredictable 𝓕 (predictablePart S 𝓕 P) := by
  classical
  have : Countable ι :=
    Function.Surjective.countable (f := fun n : ℕ ↦ succ^[n] (⊥ : ι))
      fun t ↦ (bot_le (a := t)).exists_succ_iterate
  let f : Finset ι → ι × Ω → E := fun s p ↦
    ∑ i ∈ s, (Set.Ioi i ×ˢ Set.univ).indicator
      (fun q : ι × Ω ↦ (P[S (succ i) - S i | 𝓕 i]) q.2) p
  refine stronglyMeasurable_of_tendsto (atTop : Filter (Finset ι)) (f := f) (fun s ↦ ?_) ?_
  · exact Finset.stronglyMeasurable_fun_sum _ fun i _ ↦
      stronglyMeasurable_predictable_indicator_Ioi stronglyMeasurable_condExp
  · rw [tendsto_pi_nhds]
    rintro ⟨t, ω⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (Finset.Iio t)] with s hs
    simp only [Function.uncurry_apply_pair, _root_.predictablePart, Finset.sum_apply, f]
    rw [← Finset.sum_subset hs]
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [Finset.mem_Iio] at hi
      simp [hi]
    · intro i _ hi
      rw [Finset.mem_Iio] at hi
      simp [hi]

/-- At time `t`, the predictable part is strongly measurable with respect to the previous
σ-algebra. -/
lemma stronglyMeasurable_pred_predictablePart {ι Ω E : Type*} [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [PredOrder ι] [SuccOrder ι] {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω) (t : ι) :
    StronglyMeasurable[𝓕 (pred t)] (predictablePart S 𝓕 P t) :=
  Finset.stronglyMeasurable_sum _ fun _ hi =>
    stronglyMeasurable_condExp.mono (𝓕.mono (le_pred_of_lt (Finset.mem_Iio.1 hi)))

/-- At time `t`, the predictable part is strongly measurable with respect to the previous
σ-algebra. -/
lemma stronglyMeasurable_predictablePart {ι Ω E : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [PredOrder ι] [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω) (t : ι) :
    StronglyMeasurable[𝓕 t] (predictablePart S 𝓕 P t) :=
  (stronglyMeasurable_pred_predictablePart S 𝓕 P t).mono (𝓕.mono (pred_le _))

/-- The predictable part of a process is strongly adapted. -/
lemma stronglyAdapted_predictablePart' {ι Ω E : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    StronglyAdapted 𝓕 (fun t ω ↦ predictablePart S 𝓕 P (succ t) ω) :=
  fun _ => Finset.stronglyMeasurable_sum _ fun _ hi ↦
    stronglyMeasurable_condExp.mono (𝓕.mono (le_of_lt_succ (Finset.mem_Iio.1 hi)))

/-- `τₙ(c)` is indeed a stopping time. -/
lemma isStoppingTime_tauMesh {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) :
    IsStoppingTime (meshFiltration 𝓕 n) (tauMesh S 𝓕 P n c) :=
  (stronglyAdapted_predictablePart'
    (S ∘ Subtype.val) (meshFiltration 𝓕 n) P).adapted.isStoppingTime_hittingBtwn measurableSet_Ioi

/-- Combine equation 4 and `stoppedValue_predictablePart_tauMesh_le` to get this inequality. -/
lemma stoppedValue_le_neg_condExp_predictableSeqTop_add_const {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι]
    [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ}
    (hstop : S ⊤ =ᶠ[ae P] 0)
    (𝓕 : Filtration ι mΩ) (n : ℕ) [SigmaFiniteFiltration P 𝓕] (hS_adapted : StronglyAdapted 𝓕 S)
    (hS_int : ∀ t, Integrable (S t) P) {c : ℝ} (hc : 0 ≤ c) :
    stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n c) ≤ᵐ[P]
      -P[predictableSeqTop S 𝓕 P n | (isStoppingTime_tauMesh S 𝓕 P n c).measurableSpace] +
      (fun _ => c) := by
  filter_upwards [equation4 hS_adapted hS_int hstop (tauMesh_le_top S 𝓕 P n c)
    (isStoppingTime_tauMesh S 𝓕 P n c)] with ω heqω
  rw [heqω]
  exact add_le_add_right (stoppedValue_predictablePart_tauMesh_le S 𝓕 P n hc ω) _

/-- `{τₙ(c) < 1} = {c < Aⁿ₁}`. -/
lemma MeasureTheory.Submartingale.tauMesh_lt_top_eq_lt_predictableSeqTop {ι Ω : Type*}
    [TopologicalSpace ι] [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
    (hs : Submartingale S 𝓕 P) (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)} =ᵐ[P] {ω | c < predictableSeqTop S 𝓕 P n ω} := by
  refine eventuallyEq_set.2 ?_
  have hs_mesh : Submartingale (S ∘ Subtype.val) (meshFiltration 𝓕 n) P :=
    hs.indexComap (Subtype.mono_coe (· ∈ (mesh ι n)))
  filter_upwards [hs_mesh.monotone_predictablePart_ae] with ω hmono
  let A : mesh ι n → Ω → ℝ := _root_.predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P
  by_cases htop_bot : (⊤ : mesh ι n) = ⊥
  · simp [tauMesh, predictableSeqTop, htop_bot, hc]
  · refine ⟨fun hω => ?_, fun htop_gt => ?_⟩
    · simp_all only [tauMesh, WithTop.coe_lt_coe, Std.le_refl, hittingBtwn_lt_iff, Set.Ico_bot,
        Set.mem_Iio, Set.mem_Ioi, predictableSeqTop]
      obtain ⟨j, _, hj⟩ := hω
      exact lt_of_lt_of_le hj (hmono le_top)
    · have hnot_min : ¬ IsMin (⊤ : mesh ι n) := by simpa [isMin_iff_eq_bot] using htop_bot
      have hmem : A (succ (pred ⊤)) ω ∈ Set.Ioi c := by
        simpa [A, succ_pred_of_not_isMin hnot_min, predictableSeqTop] using htop_gt
      have hhit : hittingBtwn (fun (t : mesh ι n) ω ↦ A (succ t) ω) (Set.Ioi c) ⊥ ⊤ ω < ⊤ := by
        rw [hittingBtwn_lt_iff ⊤ le_rfl]
        exact ⟨pred ⊤, ⟨bot_le, (pred_lt_iff_ne_bot).2 htop_bot⟩, hmem⟩
      simpa [tauMesh, A] using hhit

/-- The constant `c` is integrable on the event where `τₙ(c)` hits before the top element. -/
lemma MeasureTheory.Submartingale.integrableOn_const_tauMesh_lt_top {ι Ω : Type*}
    [TopologicalSpace ι] [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
    (hs : Submartingale S 𝓕 P) (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun _ : Ω => c) {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)} P := by
  by_cases! hc0 : c = 0
  · simp [hc0]
  · refine integrableOn_const (LT.lt.ne ?_)
    rw [measure_congr (hs.tauMesh_lt_top_eq_lt_predictableSeqTop n hc)]
    exact (integrable_predictableSeqTop S 𝓕 P n).measure_gt_lt_top (lt_of_le_of_ne hc hc0.symm)

/-- Stopping `S` at the bounded mesh time `τₙ(c)` preserves integrability. -/
lemma MeasureTheory.Submartingale.integrable_stoppedValue_tauMesh {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} (hs : Submartingale S 𝓕 P) (n : ℕ)
    (c : ℝ) :
    Integrable (stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n c)) P :=
  integrable_stoppedValue (mesh ι n) (isStoppingTime_tauMesh S 𝓕 P n c)
    (hs.indexComap (Subtype.mono_coe (· ∈ (mesh ι n)))).integrable
    (tauMesh_le_top S 𝓕 P n c)

/-- The first estimate before equation 5. -/
lemma first_estimate {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {S : ι → Ω → ℝ} (hstop : S ⊤ =ᶠ[ae P] 0) (𝓕 : Filtration ι mΩ) (n : ℕ)
    [SigmaFiniteFiltration P 𝓕] {c : ℝ} (hc : 0 ≤ c) (hs : Submartingale S 𝓕 P) :
    ∫ ω in {ω | c < predictableSeqTop S 𝓕 P n ω}, predictableSeqTop S 𝓕 P n ω ∂P ≤
      c * P.real {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)} -
        ∫ ω in {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)},
          stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n c) ω ∂P :=
  calc
    _ = ∫ ω in {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)},
          P[predictableSeqTop S 𝓕 P n |
            (isStoppingTime_tauMesh S 𝓕 P n c).measurableSpace] ω ∂P := by
      rw [setIntegral_condExp,
        setIntegral_congr_set (hs.tauMesh_lt_top_eq_lt_predictableSeqTop n hc)]
      · exact integrable_predictableSeqTop S 𝓕 P n
      · exact (isStoppingTime_tauMesh S 𝓕 P n c).measurableSet_lt_of_countable' ⊤
    _ ≤ ∫ ω in {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)},
        (c - stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n c) ω) ∂P := by
      refine setIntegral_mono_ae integrable_condExp.integrableOn
        ((hs.integrableOn_const_tauMesh_lt_top n hc).sub
          (hs.integrable_stoppedValue_tauMesh n c).integrableOn) ?_
      filter_upwards [stoppedValue_le_neg_condExp_predictableSeqTop_add_const hstop 𝓕 n
        hs.stronglyAdapted hs.integrable hc] with ω hω
      simp at hω
      linarith [hω]
    _ = _ := by
      rw [integral_sub (hs.integrableOn_const_tauMesh_lt_top n hc)
        (hs.integrable_stoppedValue_tauMesh n c).integrableOn, setIntegral_const]
      ring

/-- If `a ≤ b`, then `{τₙ(b) < 1} ⊆ {τₙ(a) < 1}`. -/
lemma tauMesh_lt_top_subset_of_lt {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    {ω | tauMesh S 𝓕 P n b ω < (⊤ : mesh ι n)} ⊆ {ω | tauMesh S 𝓕 P n a ω < (⊤ : mesh ι n)} := by
  simp_all only [tauMesh, WithTop.coe_lt_coe, Set.ofPred_subset_ofPred]
  exact fun ω hω => (hittingBtwn_anti ((fun t ω ↦ _root_.predictablePart (S ∘ Subtype.val)
    (meshFiltration 𝓕 n) P (succ t) ω)) ⊥ ⊤ (antitone_Ioi hab) ω).trans_lt hω

/-- Stopping the predictable part at the bounded mesh time `τₙ(c)` preserves integrability. -/
lemma integrable_stoppedValue_predictablePart_tauMesh {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω) (n : ℕ) (c : ℝ) :
    Integrable (stoppedValue (predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P)
      (tauMesh S 𝓕 P n c)) P :=
  integrable_stoppedValue (mesh ι n) (isStoppingTime_tauMesh S 𝓕 P n c)
    (integrable_predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P)
    (tauMesh_le_top S 𝓕 P n c)

/-- The second estimate before equation 5. -/
lemma second_estimate {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ} (hstop : S ⊤ =ᶠ[ae P] 0)
    (𝓕 : Filtration ι mΩ) (n : ℕ) [SigmaFiniteFiltration P 𝓕] {c : ℝ} (hc : 0 ≤ c)
    (hs : Submartingale S 𝓕 P) :
    c / 2 * P.real {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)} ≤
      - ∫ ω in {ω | tauMesh S 𝓕 P n (c / 2) ω < (⊤ : mesh ι n)},
        stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n (c / 2)) ω ∂P :=
  have hpred_int := integrable_predictableSeqTop S 𝓕 P n
  have hstopped_pred_int := integrable_stoppedValue_predictablePart_tauMesh S 𝓕 P n (c / 2)
  calc
    _ = ∫ ω in {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)}, c / 2 ∂P := by simp [mul_comm]
    _ ≤ ∫ ω in {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)},
          (predictableSeqTop S 𝓕 P n ω -
            stoppedValue (predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P)
              (tauMesh S 𝓕 P n (c / 2)) ω) ∂P := by
      refine setIntegral_mono_on_ae ?_ ?_ ?_ ?_
      · exact (hs.integrableOn_const_tauMesh_lt_top n hc).div_const 2
      · exact (hpred_int.sub hstopped_pred_int).integrableOn
      · refine (iSup_le (meshFiltration 𝓕 n).le) _
          (((isStoppingTime_tauMesh S 𝓕 P n c).measurableSet _).1 ?_).1
        exact (isStoppingTime_tauMesh S 𝓕 P n c).measurableSet_lt_of_countable' ⊤
      · filter_upwards [hs.tauMesh_lt_top_eq_lt_predictableSeqTop n hc] with ω hτ hω
        have : c < predictableSeqTop S 𝓕 P n ω := hτ.mp hω
        have := stoppedValue_predictablePart_tauMesh_le S 𝓕 P n (by linarith : 0 ≤ c / 2) ω
        linarith
    _ ≤ ∫ ω in {ω | tauMesh S 𝓕 P n (c / 2) ω < (⊤ : mesh ι n)},
          (predictableSeqTop S 𝓕 P n ω -
            stoppedValue (predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P)
              (tauMesh S 𝓕 P n (c / 2)) ω) ∂P := by
      refine setIntegral_mono_set ?_ ?_ ?_
      · exact (hpred_int.sub hstopped_pred_int).integrableOn
      · have hs_mesh : Submartingale (S ∘ Subtype.val) (meshFiltration 𝓕 n) P :=
          hs.indexComap (Subtype.mono_coe (· ∈ (mesh ι n)))
        filter_upwards [ae_restrict_le hs_mesh.monotone_predictablePart_ae] with ω hmono
        simpa [predictableSeqTop, stoppedValue] using hmono le_top
      · exact (tauMesh_lt_top_subset_of_lt S 𝓕 P n (by linarith)).eventuallyLE
    _ = ∫ ω in {ω | tauMesh S 𝓕 P n (c / 2) ω < (⊤ : mesh ι n)}, predictableSeqTop S 𝓕 P n ω ∂P -
          ∫ ω in {ω | tauMesh S 𝓕 P n (c / 2) ω < (⊤ : mesh ι n)},
            stoppedValue (predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P)
              (tauMesh S 𝓕 P n (c / 2)) ω ∂P := by
      rw [integral_sub]
      · exact hpred_int.integrableOn
      · exact hstopped_pred_int.integrableOn
    _ = ∫ ω in {ω | tauMesh S 𝓕 P n (c / 2) ω < (⊤ : mesh ι n)},
          P[predictableSeqTop S 𝓕 P n |
            (isStoppingTime_tauMesh S 𝓕 P n (c / 2)).measurableSpace] ω ∂P -
              ∫ ω in {ω | tauMesh S 𝓕 P n (c / 2) ω < (⊤ : mesh ι n)},
                stoppedValue (predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P)
                  (tauMesh S 𝓕 P n (c / 2)) ω ∂P := by
      rw [setIntegral_condExp]
      · exact hpred_int
      · exact (isStoppingTime_tauMesh S 𝓕 P n (c / 2)).measurableSet_lt_of_countable' ⊤
    _ = _ := by
      rw [← integral_sub integrable_condExp.restrict hstopped_pred_int.integrableOn, ← integral_neg]
      · refine setIntegral_congr_ae ?_ ?_
        · refine (iSup_le (meshFiltration 𝓕 n).le) _
            (((isStoppingTime_tauMesh S 𝓕 P n (c / 2)).measurableSet _).1 ?_).1
          exact (isStoppingTime_tauMesh S 𝓕 P n (c / 2)).measurableSet_lt_of_countable' ⊤
        · filter_upwards [equation4 hs.stronglyAdapted hs.integrable hstop
            (tauMesh_le_top S 𝓕 P n (c / 2)) (isStoppingTime_tauMesh S 𝓕 P n (c / 2))] with ω hω _
          simp at hω
          linarith [hω]

lemma equation5 {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {S : ι → Ω → ℝ} (hstop : S ⊤ =ᶠ[ae P] 0)
    (𝓕 : Filtration ι mΩ) (n : ℕ) [SigmaFiniteFiltration P 𝓕] {c : ℝ} (hc : 0 ≤ c)
    (hs : Submartingale S 𝓕 P) :
    ∫ ω in {ω | c < predictableSeqTop S 𝓕 P n ω}, predictableSeqTop S 𝓕 P n ω ∂P ≤
      -2 * ∫ ω in {ω | tauMesh S 𝓕 P n (c / 2) ω < (⊤ : mesh ι n)},
        stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n (c / 2)) ω ∂P -
          ∫ ω in {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)},
            stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n c) ω ∂P := by
  grw [first_estimate hstop 𝓕 n hc hs]
  linear_combination 2 * (second_estimate hstop 𝓕 n hc hs)

lemma equation5' {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {S : ι → Ω → ℝ} (hstop : S ⊤ =ᶠ[ae P] 0)
    (𝓕 : Filtration ι mΩ) (n : ℕ) [SigmaFiniteFiltration P 𝓕] {c : ℝ} (hc : 0 ≤ c)
    (hs : Submartingale S 𝓕 P) :
    ∫ ω in {ω | c < predictableSeqTop S 𝓕 P n ω}, predictableSeqTop S 𝓕 P n ω ∂P ≤
      ∫ ω in {ω | tauMesh S 𝓕 P n (c / 2) ω < (⊤ : mesh ι n)}, (-2) *
        stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n (c / 2)) ω ∂P +
          ∫ ω in {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)},
            -stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n c) ω ∂P := by
  grw [equation5 hstop 𝓕 n hc hs, ← integral_const_mul_of_integrable, sub_eq_add_neg,
    ← integral_neg]
  exact (hs.integrable_stoppedValue_tauMesh n (c / 2)).restrict

end equation5

end Estimate

section UniformIntegrability

/-- Lift the mesh stopping time `τₙ(c)` to a stopping time on the original index set. -/
noncomputable def tauMeshLift {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) : Ω → WithTop ι :=
  fun ω => ((tauMesh S 𝓕 P n c ω).untopA : mesh ι n)

@[simp]
lemma tauMesh_ne_top {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) (ω : Ω) :
    tauMesh S 𝓕 P n c ω ≠ ⊤ := by
  simp [tauMesh]

@[simp]
lemma tauMeshLift_ne_top {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) (ω : Ω) :
    tauMeshLift S 𝓕 P n c ω ≠ ⊤ := by
  simp [tauMeshLift]

lemma stoppedValue_tauMeshLift {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) :
    stoppedValue S (tauMeshLift S 𝓕 P n c) =
      stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n c) := by
  ext; simp [stoppedValue, tauMeshLift]

/-- The lifted mesh stopping time takes values in the finite mesh, hence has countable range. -/
lemma countable_range_tauMeshLift {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) :
    (Set.range (tauMeshLift S 𝓕 P n c)).Countable := by
  refine (Set.countable_range (fun u : mesh ι n ↦ ((u : ι) : WithTop ι))).mono ?_
  rintro _ ⟨ω, rfl⟩
  exact ⟨(tauMesh S 𝓕 P n c ω).untopA, rfl⟩

/-- We still get a stopping time after the lifting. -/
lemma isStoppingTime_tauMeshLift {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) :
    IsStoppingTime 𝓕 (tauMeshLift S 𝓕 P n c) := by
  intro s
  set T : Finset (mesh ι n) := Finset.univ.filter (fun u ↦ u ≤ s)
  have hTne : T.Nonempty := ⟨⊥, by simp [T]⟩
  set u : mesh ι n := T.max' hTne
  have hu_mem : u ∈ T := T.max'_mem hTne
  have hu_le_s : (u : ι) ≤ s := by simpa [T] using hu_mem
  have hequiv (v : mesh ι n) : (v : ι) ≤ s ↔ v ≤ u :=
    ⟨fun hv ↦ T.le_max' v (by simp [T, hv]), fun hv ↦ le_trans hv hu_le_s⟩
  suffices h : {ω | tauMeshLift S 𝓕 P n c ω ≤ s} = {ω | tauMesh S 𝓕 P n c ω ≤ u} by
    rw [h]; exact (𝓕.mono hu_le_s) _ (isStoppingTime_tauMesh S 𝓕 P n c u)
  ext ω
  simp only [Set.mem_ofPred_eq, tauMeshLift]
  rw [WithTop.coe_le_coe, hequiv]
  exact WithTop.untopA_le_iff (tauMesh_ne_top S 𝓕 P n c ω)

/-- Used in estimating the size of the set `{τₙ(b) < 1}`. -/
lemma integral_predictableSeqTop_eq_neg_integral_bot {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι]
    [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration P 𝓕] (hS_adapted : StronglyAdapted 𝓕 S)
    (hS_int : ∀ t, Integrable (S t) P) (hstop : S ⊤ =ᵐ[P] 0) (n : ℕ) :
    ∫ ω, predictableSeqTop S 𝓕 P n ω ∂P = - ∫ ω, S ⊥ ω ∂P := calc
  _ = - ∫ ω, -predictableSeqTop S 𝓕 P n ω ∂P := by simp [integral_neg]
  _ = - ∫ ω, martingaleSeqTop S 𝓕 P n ω ∂P := by
    simp [integral_congr_ae (martingaleSeqTop_eq_neg_predictableSeqTop 𝓕 hstop n)]
  _ = - ∫ ω, S ⊥ ω ∂P := by
    rw [martingaleSeqTop, ← setIntegral_univ,
      ← (martingale_martingalePart_mesh hS_adapted hS_int n).setIntegral_eq
      (bot_le (a := ⊤)) MeasurableSet.univ]
    simp [_root_.martingalePart]

/-- Estimate for the hitting event `{τₙ(c) < 1}`. -/
lemma measure_tauMesh_lt_top_le {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration P 𝓕] (hs : Submartingale S 𝓕 P) (hstop : S ⊤ =ᵐ[P] 0) (n : ℕ) {c : ℝ}
    (hc : 0 < c) :
    P {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)} ≤
      ENNReal.ofReal (- ∫ ω, S ⊥ ω ∂P) / ENNReal.ofReal c := calc
  P {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)} = P {ω | c < predictableSeqTop S 𝓕 P n ω} :=
    measure_congr (hs.tauMesh_lt_top_eq_lt_predictableSeqTop n hc.le)
  _ ≤ P {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (predictableSeqTop S 𝓕 P n ω)} :=
    measure_mono fun ω hω => ENNReal.ofReal_le_ofReal hω.le
  _ ≤ (∫⁻ ω, ENNReal.ofReal (predictableSeqTop S 𝓕 P n ω) ∂P) / ENNReal.ofReal c :=
    meas_ge_le_lintegral_div
      ((integrable_predictableSeqTop S 𝓕 P n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      (ENNReal.ofReal_ne_zero_iff.2 hc) ENNReal.ofReal_ne_top
  _ = ENNReal.ofReal (∫ ω, predictableSeqTop S 𝓕 P n ω ∂P) / ENNReal.ofReal c := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_predictableSeqTop S 𝓕 P n)]
    have hs_mesh : Submartingale (S ∘ Subtype.val) (meshFiltration 𝓕 n) P :=
      hs.indexComap (Subtype.mono_coe (· ∈ (mesh ι n)))
    filter_upwards [hs_mesh.predictablePart_nonneg'] with ω hω using hω ⊤
  _ = ENNReal.ofReal (- ∫ ω, S ⊥ ω ∂P) / ENNReal.ofReal c := by
    rw [integral_predictableSeqTop_eq_neg_integral_bot hs.stronglyAdapted hs.integrable hstop n]

/-- If `X` is uniformly integrable in `Lᵖ` and the sets `A k i` have supremum-over-`i` measure
tending to `0` along `l`, then `⨆ i, eLpNorm ((A k i).indicator (X (F k i)))` tends to `0`. This
isolates the ε–δ core of uniform integrability from any particular application: reindexing the
family by `F` is harmless because uniform integrability controls the whole index type at once. -/
lemma UniformIntegrable.eLpNorm_tendsto_zero_of_iSup_measure_tendsto_zero
    {α ι κ Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [NormedAddCommGroup E] {X : α → Ω → E}
    {p : ℝ≥0∞} (hX : UniformIntegrable X p μ) {A : κ → ι → Set Ω}
    (hA_meas : ∀ k i, MeasurableSet (A k i)) {F : κ → ι → α} {l : Filter κ}
    (hA : Tendsto (fun k ↦ ⨆ i, μ (A k i)) l (𝓝 0)) :
    Tendsto (fun k ↦ ⨆ i, eLpNorm ((A k i).indicator (X (F k i))) p μ) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at hA ⊢
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · exact Eventually.of_forall fun _ ↦ le_top
  obtain ⟨δ, hδ, hUI⟩ := hX.2.1 (ENNReal.toReal_pos hε.ne' hεtop)
  filter_upwards [hA (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)] with k hk
  refine iSup_le fun i ↦ (hUI (F k i) (A k i) (hA_meas k i)
    ((le_iSup (fun i ↦ μ (A k i)) i).trans hk)).trans_eq (ENNReal.ofReal_toReal hεtop)

/-- A submartingale whose terminal value vanishes is nonpositive. -/
lemma MeasureTheory.Submartingale.ae_le_zero_of_top_ae_eq_zero {ι Ω : Type*} [Preorder ι]
    [OrderTop ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
    (hs : Submartingale S 𝓕 P) (hstop : S ⊤ =ᵐ[P] 0) (t : ι) :
    S t ≤ᵐ[P] 0 := by
  have h0 : P[S ⊤ | 𝓕 t] =ᵐ[P] 0 := (condExp_congr_ae hstop).trans (by rw [condExp_zero])
  filter_upwards [hs.ae_le_condExp (i := t) le_top, h0] with ω h1 h2
  simpa [h2] using h1

/-- For a non-positive constant `a` and a level `b c → ∞`, the supremum over the meshes of the
integral of `a • (stopped value)` over the hitting set `{τₙ(b c) < ⊤}` tends to `0`. The hitting
sets have measure `≤ (-∫ S ⊥) / (b c) → 0` uniformly in the mesh (`measure_tauMesh_lt_top_le`),
and `hd` provides uniform integrability of the stopped values along the lifted stopping times. -/
private lemma tendsto_iSup_setIntegral_tauMesh_zero {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration P 𝓕] (hs : Submartingale S 𝓕 P)
    (hd : UniformIntegrable (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ (∀ ω, T ω ≠ ⊤) ∧
      (Set.range T).Countable}) ↦ stoppedValue S τ.1) 1 P) (hstop : S ⊤ =ᵐ[P] 0)
    (a : ℝ) (ha : a ≤ 0) (b : ℝ≥0 → ℝ) (hb : Tendsto b atTop atTop) :
    Tendsto (fun c : ℝ≥0 ↦ ⨆ k, ENNReal.ofReal
      (∫ ω in {ω | tauMesh S 𝓕 P k (b c) ω < (⊤ : mesh ι k)},
        a * stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P k (b c)) ω ∂P)) atTop (𝓝 0) := by
  have hA_meas (c : ℝ≥0) (k : ℕ) :
      MeasurableSet {ω | tauMesh S 𝓕 P k (b c) ω < (⊤ : mesh ι k)} :=
    (isStoppingTime_tauMesh S 𝓕 P k (b c)).measurableSpace_le _
      ((isStoppingTime_tauMesh S 𝓕 P k (b c)).measurableSet_lt_of_countable' ⊤)
  have hmem (c : ℝ≥0) (k : ℕ) : tauMeshLift S 𝓕 P k (b c) ∈
      {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ (∀ ω, T ω ≠ ⊤) ∧ (Set.range T).Countable} :=
    ⟨isStoppingTime_tauMeshLift S 𝓕 P k (b c), tauMeshLift_ne_top S 𝓕 P k (b c),
      countable_range_tauMeshLift S 𝓕 P k (b c)⟩
  -- (1) each set-integral is `|a|` times the `L¹` norm of the stopped value's indicator
  have hbridge (c : ℝ≥0) (k : ℕ) :
      ENNReal.ofReal (∫ ω in {ω | tauMesh S 𝓕 P k (b c) ω < (⊤ : mesh ι k)},
        a * stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P k (b c)) ω ∂P)
      = ENNReal.ofReal |a| * eLpNorm ({ω | tauMesh S 𝓕 P k (b c) ω < (⊤ : mesh ι k)}.indicator
          (stoppedValue S (tauMeshLift S 𝓕 P k (b c)))) 1 P := by
    rw [stoppedValue_tauMeshLift]
    set g : Ω → ℝ := stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P k (b c))
    have hg_nonpos : g ≤ᵐ[P] 0 := by
      filter_upwards [ae_all_iff.2 fun t : mesh ι k ↦
        hs.ae_le_zero_of_top_ae_eq_zero hstop t] with ω hω
      simpa only [g, stoppedValue, Function.comp_apply] using
        hω (tauMesh S 𝓕 P k (b c) ω).untopA
    have heLpNorm : eLpNorm ({ω | tauMesh S 𝓕 P k (b c) ω < (⊤ : mesh ι k)}.indicator g) 1 P
        = ENNReal.ofReal (∫ ω in {ω | tauMesh S 𝓕 P k (b c) ω < (⊤ : mesh ι k)}, -g ω ∂P) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict (hA_meas c k), eLpNorm_one_eq_lintegral_enorm,
        ← ofReal_integral_norm_eq_lintegral_enorm
          (hs.integrable_stoppedValue_tauMesh k (b c)).restrict]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae hg_nonpos] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonpos hω]
    rw [heLpNorm, ← ENNReal.ofReal_mul (abs_nonneg a)]
    congr 1
    rw [integral_const_mul, integral_neg, abs_of_nonpos ha]
    ring
  -- (2) the hitting sets shrink in measure, uniformly in the mesh: each is bounded by
  -- `(-∫ S ⊥) / (b c)`, which vanishes as `b c → ∞`
  have hmeas : Tendsto (fun c : ℝ≥0 ↦ ⨆ k, P {ω | tauMesh S 𝓕 P k (b c) ω < (⊤ : mesh ι k)})
      atTop (𝓝 0) := by
    have hrhs : Tendsto (fun c : ℝ≥0 ↦
        ENNReal.ofReal (-∫ ω, S ⊥ ω ∂P) / ENNReal.ofReal (b c)) atTop (𝓝 0) := by
      have htop : Tendsto (fun c : ℝ≥0 ↦ ENNReal.ofReal (b c)) atTop (𝓝 ⊤) :=
        ENNReal.tendsto_ofReal_atTop.comp hb
      simpa using ENNReal.Tendsto.const_div htop (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrhs
      (Eventually.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [hb.eventually_gt_atTop 0] with c hc_pos
    exact iSup_le fun k ↦ measure_tauMesh_lt_top_le hs hstop k hc_pos
  -- (3) it suffices that the `L¹` norms vanish — that is uniform integrability (`hd`) fed the
  -- vanishing measures from (2); the reduction is (1) and pulling out the constant `|a|`
  suffices h : Tendsto (fun c : ℝ≥0 ↦ ⨆ k, eLpNorm
      ({ω | tauMesh S 𝓕 P k (b c) ω < (⊤ : mesh ι k)}.indicator
        (stoppedValue S (tauMeshLift S 𝓕 P k (b c)))) 1 P) atTop (𝓝 0) by
    simp_rw [hbridge, ← ENNReal.mul_iSup]
    simpa using ENNReal.Tendsto.const_mul h (Or.inr ENNReal.ofReal_ne_top)
  exact UniformIntegrable.eLpNorm_tendsto_zero_of_iSup_measure_tendsto_zero hd
    (A := fun c k ↦ {ω | tauMesh S 𝓕 P k (b c) ω < (⊤ : mesh ι k)})
    (F := fun c k ↦ ⟨tauMeshLift S 𝓕 P k (b c), hmem c k⟩) hA_meas hmeas

/-- The terminal values of the predictable parts are uniformly integrable. -/
lemma uniformIntegrable_predictableSeqTop {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hs : Submartingale S 𝓕 P)
    (hd : UniformIntegrable (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ (∀ ω, T ω ≠ ⊤) ∧
      (Set.range T).Countable}) ↦ stoppedValue S τ.1) 1 P) (hstop : S ⊤ =ᵐ[P] 0) :
    UniformIntegrable (predictableSeqTop S 𝓕 P) 1 P := by
  refine (uniformIntegrable_iff_tendsto_nnReal_iSup_setIntegral_of_nonneg (fun n => ?_)
    (fun n => ?_) (fun n => ?_)).2 ?_
  · exact (stronglyAdapted_predictablePart
      (S ∘ Subtype.val) (meshFiltration 𝓕 n) P).stronglyMeasurable.aestronglyMeasurable
  · have hs_mesh : Submartingale (S ∘ Subtype.val) (meshFiltration 𝓕 n) P :=
      hs.indexComap (Subtype.mono_coe (· ∈ (mesh ι n)))
    filter_upwards [hs_mesh.predictablePart_nonneg'] with ω hω using hω ⊤
  · exact integrable_predictableSeqTop S 𝓕 P n
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (a := 0) (h := fun c : ℝ≥0 ↦
      (⨆ k, ENNReal.ofReal (∫ ω in {ω | tauMesh S 𝓕 P k (c / 2) ω < (⊤ : mesh ι k)}, (-2) *
        stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P k (c / 2)) ω ∂P)) +
          ⨆ k, ENNReal.ofReal (∫ ω in {ω | tauMesh S 𝓕 P k c ω < (⊤ : mesh ι k)},
            -stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P k c) ω ∂P)) tendsto_const_nhds ?_ ?_ ?_
    · rw [← zero_add (0 : ℝ≥0∞)]
      apply Tendsto.add
      · exact tendsto_iSup_setIntegral_tauMesh_zero hs hd hstop (-2) (by norm_num)
          (fun c => c / 2) ((NNReal.tendsto_coe_atTop.mpr tendsto_id).atTop_div_const (by norm_num))
      · simpa using tendsto_iSup_setIntegral_tauMesh_zero hs hd hstop (-1) (by norm_num)
          (fun c => c) (NNReal.tendsto_coe_atTop.mpr tendsto_id)
    · filter_upwards with c using by positivity
    · filter_upwards with c
      calc
        ⨆ k, ENNReal.ofReal (∫ ω in {ω | c < predictableSeqTop S 𝓕 P k ω},
          predictableSeqTop S 𝓕 P k ω ∂P) ≤ ⨆ k, ENNReal.ofReal
            (∫ ω in {ω | tauMesh S 𝓕 P k (c / 2) ω < (⊤ : mesh ι k)}, (-2) *
              stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P k (c / 2)) ω ∂P +
                ∫ ω in {ω | tauMesh S 𝓕 P k c ω < (⊤ : mesh ι k)},
                  -stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P k c) ω ∂P) := by
          gcongr with k
          exact equation5' hstop 𝓕 k c.2 hs
        _ = ⨆ k, ENNReal.ofReal
            (∫ ω in {ω | tauMesh S 𝓕 P k (c / 2) ω < (⊤ : mesh ι k)}, (-2) *
              stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P k (c / 2)) ω ∂P) +
                ENNReal.ofReal (∫ ω in {ω | tauMesh S 𝓕 P k c ω < (⊤ : mesh ι k)},
                  -stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P k c) ω ∂P) := by
          congr with k
          have hmesh : ∀ᵐ ω ∂P, ∀ t : mesh ι k, S t ω ≤ 0 :=
            ae_all_iff.2 fun t => hs.ae_le_zero_of_top_ae_eq_zero hstop t
          apply ENNReal.ofReal_add
          all_goals
            apply integral_nonneg_of_ae
            simp only [stoppedValue, Function.comp_apply]
          · filter_upwards [ae_restrict_of_ae hmesh] with ω hω
            exact mul_nonneg_of_nonpos_of_nonpos (by simp) (hω ((tauMesh S 𝓕 P k (c / 2) ω).untopA))
          · filter_upwards [ae_restrict_of_ae hmesh] with ω hω
            exact neg_nonneg.2 (hω ((tauMesh S 𝓕 P k c ω).untopA))
        _ ≤ _ := iSup_add_le _ _

/-- The stopped values of a closed martingale `t ↦ P[ξ | 𝓕 t]` at finite stopping times with
countable range are uniformly integrable. -/
lemma uniformIntegrable_stoppedValue_condExp_of_countable_range {ι Ω : Type*} [LinearOrder ι]
    [OrderTop ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ι mΩ} {ξ : Ω → ℝ} :
    UniformIntegrable (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ (∀ ω, T ω ≠ ⊤) ∧
      (Set.range T).Countable}) ↦ stoppedValue (fun i ↦ P[ξ | 𝓕 i]) τ.1) 1 P := by
  have hN : Martingale (fun i ↦ P[ξ | 𝓕 i]) 𝓕 P := martingale_condExp ξ 𝓕 P
  rw [uniformIntegrable_congr_ae (g := fun τ ↦ P[P[ξ | 𝓕 ⊤] | τ.2.1.measurableSpace]) fun τ ↦
    hN.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range' τ.2.1
      (fun ω ↦ WithTop.le_coe_top (τ.2.2.1 ω)) τ.2.2.2]
  exact integrable_condExp.uniformIntegrable_condExp fun τ ↦ τ.2.1.measurableSpace_le

/-- If the stopped values of `S` at finite stopping times with countable range are uniformly
integrable, then so are those of `S - (fun i ↦ P[S ⊤ | 𝓕 i])`. -/
lemma uniformIntegrable_stoppedValue_sub_condExp_of_countable_range {ι Ω : Type*}
    [LinearOrder ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
    (hd : UniformIntegrable (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ (∀ ω, T ω ≠ ⊤) ∧
      (Set.range T).Countable}) ↦ stoppedValue S τ.1) 1 P) :
    UniformIntegrable (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ (∀ ω, T ω ≠ ⊤) ∧
      (Set.range T).Countable}) ↦ stoppedValue (S - fun i ↦ P[S ⊤ | 𝓕 i]) τ.1) 1 P :=
  hd.sub le_rfl uniformIntegrable_stoppedValue_condExp_of_countable_range

/-- For a process of class D, the stopped values at finite stopping times with countable range are
uniformly integrable. -/
lemma ProbabilityTheory.ClassD.uniformIntegrable_of_countable_range {ι Ω : Type*} [LinearOrder ι]
    [OrderTop ι] [MeasurableSpace ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) :
    UniformIntegrable (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ (∀ ω, T ω ≠ ⊤) ∧
      (Set.range T).Countable}) ↦ stoppedValue S τ.1) 1 P :=
  hd.uniformIntegrable.comp fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ (∀ ω, T ω ≠ ⊤) ∧
    (Set.range T).Countable}) ↦ ⟨τ.1, τ.2.1, τ.2.2.1⟩

/-- As the terminal values of predictable parts are uniformly integrable, the terminal values of the
martingale parts are uniformly integrable. -/
lemma uniformIntegrable_martingaleSeqTopAux {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hs : Submartingale S 𝓕 P)
    (hd : UniformIntegrable (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ (∀ ω, T ω ≠ ⊤) ∧
      (Set.range T).Countable}) ↦ stoppedValue S τ.1) 1 P) (hstop : S ⊤ =ᵐ[P] 0) :
    UniformIntegrable (martingaleSeqTop S 𝓕 P) 1 P := by
  rw [uniformIntegrable_congr_ae (martingaleSeqTop_eq_neg_predictableSeqTop 𝓕 hstop)]
  exact (uniformIntegrable_predictableSeqTop hs hd hstop).neg

/-- Prove uniform integrability without the assumption `S ⊤ =ᵐ[P] 0`. -/
lemma uniformIntegrable_martingaleSeqTop {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ}
    (hd : UniformIntegrable (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ (∀ ω, T ω ≠ ⊤) ∧
      (Set.range T).Countable}) ↦ stoppedValue S τ.1) 1 P) (hs : Submartingale S 𝓕 P) :
    UniformIntegrable (martingaleSeqTop S 𝓕 P) 1 P := by
  have h0 : S = S - (fun i => P[S ⊤ | 𝓕 i]) + (fun i => P[S ⊤ | 𝓕 i]) := by simp
  have h1 (i) : Integrable ((S - fun t => P[S ⊤ | 𝓕 t]) i) P :=
    (hs.integrable i).sub integrable_condExp
  rw [h0, uniformIntegrable_congr_ae (martingaleSeqTop_add 𝓕 h1 (fun i => integrable_condExp))]
  refine UniformIntegrable.add (refl 1) ?_ ?_
  · refine uniformIntegrable_martingaleSeqTopAux ?_ ?_ ?_
    · exact hs.sub_martingale (martingale_condExp _ _ _)
    · exact uniformIntegrable_stoppedValue_sub_condExp_of_countable_range hd
    · simp [condExp_of_stronglyMeasurable _ (hs.stronglyMeasurable ⊤) (hs.integrable ⊤)]
  · rw [uniformIntegrable_congr_ae
      (martingaleSeqTop_eq_self_of_martingale (martingale_condExp (S ⊤) 𝓕 P))]
    exact Integrable.uniformIntegrable_condExp (hs.integrable ⊤) (fun _ => 𝓕.le' ⊤)

end UniformIntegrability

-- We define the step extensions of the discrete martingale and predictable parts.
section StepProcesses

/-- The extension of the discrete martingale part `M^n`. -/
noncomputable def martingaleSeqStep {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (n : ℕ) (i : ι) :=
  P[martingaleSeqTop S 𝓕 P n | 𝓕 i]

/-- The half-open mesh interval ending at `t`, with left endpoint the predecessor of `t` in the
finite mesh. -/
def meshPredIoc {ι : Type*} [LinearOrder ι] [OrderBot ι] [OrderTop ι] [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (n : ℕ) (t : mesh ι n) : Set ι :=
  Set.Ioc ((pred t : mesh ι n) : ι) (t : ι)

/-- The mesh step-extension of the discrete predictable part `A^n`. -/
noncomputable def predictableSeqStep {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (n : ℕ) :
    ι → Ω → ℝ :=
  fun t ↦ ∑ u : mesh ι n, (meshPredIoc n u).indicator
    (fun _ : ι ↦ predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P u) t

/-- The mesh step-extension of the discrete predictable part is strongly adapted. -/
lemma stronglyAdapted_predictableSeqStep {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) (S : ι → Ω → ℝ)
    (𝓕 : Filtration ι mΩ) (n : ℕ) :
    StronglyAdapted 𝓕 (predictableSeqStep P S 𝓕 n) := by
  refine fun t => Finset.stronglyMeasurable_sum _ fun u _ => ?_
  by_cases htu : t ∈ meshPredIoc n u
  · have : meshFiltration 𝓕 n (pred u) ≤ 𝓕 t := by simpa [meshFiltration] using 𝓕.mono htu.1.le
    simpa [htu] using (stronglyMeasurable_pred_predictablePart (S ∘ Subtype.val)
      (meshFiltration 𝓕 n) P u).mono this
  · simpa [htu] using stronglyMeasurable_zero

/-- Finite linear combinations of the mesh step-extensions of the discrete predictable parts are
strongly adapted. -/
lemma stronglyAdapted_weights_sum_predictableSeqStep {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) (S : ι → Ω → ℝ)
    (𝓕 : Filtration ι mΩ) (w : ℕ →₀ ℝ) :
    StronglyAdapted 𝓕 (w.sum fun m r ↦ r • predictableSeqStep P S 𝓕 m) := by
  intro t
  simpa [Finsupp.sum] using Finset.stronglyMeasurable_sum w.support fun m _ ↦
    (stronglyAdapted_predictableSeqStep P S 𝓕 m t).const_smul (w m)

/-- On the half-open mesh interval `(pred u, u]`, the step extension of the discrete predictable
part takes the value of the discrete predictable part at `u`. -/
lemma predictableSeqStep_apply_of_mem {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} {n : ℕ} {t : ι}
    {u : mesh ι n} (ht : t ∈ meshPredIoc n u) :
    predictableSeqStep P S 𝓕 n t
      = predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P u := by
  rw [predictableSeqStep, Finset.sum_eq_single u]
  · rw [Set.indicator_of_mem ht]
  · refine fun v _ hvu ↦ Set.indicator_of_notMem (fun htv ↦ ?_) _
    rcases lt_or_gt_of_ne hvu with h | h
    · exact absurd (htv.2.trans (Subtype.coe_le_coe.2 (le_pred_of_lt h))) (not_le.2 ht.1)
    · exact absurd (ht.2.trans (Subtype.coe_le_coe.2 (le_pred_of_lt h))) (not_le.2 htv.1)
  · exact fun hu ↦ absurd (Finset.mem_univ u) hu

/-- At a point of the `n`-th mesh, the step extension of the discrete predictable part is a.e.
equal to the process minus the conditional expectation of the terminal value of the discrete
martingale part. -/
lemma predictableSeqStep_ae_eq_sub_martingaleSeqStep {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration P 𝓕] (hS_adapted : StronglyAdapted 𝓕 S)
    (hS_int : ∀ t, Integrable (S t) P) {n : ℕ} {t : ι} (ht : t ∈ mesh ι n) :
    predictableSeqStep P S 𝓕 n t =ᵐ[P] S t - martingaleSeqStep P S 𝓕 n t := by
  have hkey : martingalePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⟨t, ht⟩
      =ᵐ[P] martingaleSeqStep P S 𝓕 n t :=
    ((martingale_martingalePart_mesh hS_adapted hS_int n).condExp_ae_eq
      (le_top (a := (⟨t, ht⟩ : mesh ι n)))).symm
  filter_upwards [hkey] with ω hω
  calc predictableSeqStep P S 𝓕 n t ω
      = predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⟨t, ht⟩ ω := by
        rcases eq_or_ne (⟨t, ht⟩ : mesh ι n) ⊥ with h | h
        · have hu : t = ⊥ := by simpa using congrArg Subtype.val h
          rw [h, hu]
          simp [predictableSeqStep, meshPredIoc]
        · rw [predictableSeqStep_apply_of_mem
            ⟨Subtype.coe_lt_coe.2 (pred_lt_iff_ne_bot.2 h), le_rfl⟩]
    _ = S t ω - martingalePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⟨t, ht⟩ ω :=
        eq_sub_of_add_eq' (congrFun (congrFun
          (martingalePart_add_predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P) _) ω)
    _ = (S t - martingaleSeqStep P S 𝓕 n t) ω := by rw [hω, Pi.sub_apply]

end StepProcesses

-- Convergence of convex combinations of the step processes, for generic weights.
section WeightsSumConv

/-- Countably many sequences converging in measure admit a common subsequence along which all of
them converge almost everywhere. -/
lemma exists_strictMono_forall_ae_tendsto_of_tendstoInMeasure {κ Ω E : Type*} [Countable κ]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [PseudoEMetricSpace E]
    {f : κ → ℕ → Ω → E} {g : κ → Ω → E}
    (h : ∀ k, TendstoInMeasure μ (f k) atTop (g k)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun n ↦ f k (φ n) ω) atTop (𝓝 (g k ω)) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · exact ⟨id, strictMono_id, ae_of_all _ fun ω k ↦ isEmptyElim k⟩
  obtain ⟨e, he⟩ := exists_surjective_nat κ
  -- Choose `φ` such that `μ {2⁻ⁿ ≤ edist (f (e k) (φ n)) (g (e k))} ≤ 2⁻ⁿ` for all `k ≤ n`.
  obtain ⟨φ, hφ, hφ_le⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, ∀ k ∈ Finset.range (n + 1),
      μ {ω | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (f (e k) (φ n) ω) (g (e k) ω)} ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    refine extraction_forall_of_eventually (P := fun n m ↦ ∀ k ∈ Finset.range (n + 1),
      μ {ω | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (f (e k) m ω) (g (e k) ω)} ≤ (2 : ℝ≥0∞)⁻¹ ^ n) fun n ↦ ?_
    rw [eventually_all_finset]
    intro k _
    have hk := h (e k) ((2 : ℝ≥0∞)⁻¹ ^ n) (ENNReal.pow_pos (by simp) _)
    exact hk.eventually_le_const (ENNReal.pow_pos (by simp) _)
  refine ⟨φ, hφ, ?_⟩
  rw [ae_all_iff]
  intro k
  obtain ⟨j, rfl⟩ := he k
  -- Borel-Cantelli for the sets shifted by `j`
  let s : ℕ → Set Ω := fun n ↦ {ω | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (f (e j) (φ n) ω) (g (e j) ω)}
  have hs_le n : μ (s (n + j)) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    refine (hφ_le (n + j) j (by simp)).trans ?_
    rw [pow_add]
    exact mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le (by simp))
  have h_sum : ∑' n, μ (s (n + j)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hs_le)
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using ENNReal.ofNat_ne_top
  filter_upwards [ae_eventually_notMem h_sum] with ω hω
  rw [tendsto_iff_edist_tendsto_0]
  have h_pow : Tendsto (fun n : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simp)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_pow
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp hω
  filter_upwards [eventually_ge_atTop (N + j)] with n hn
  have hn' := hN (n - j) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at hn'
  simpa [s] using le_of_not_ge hn'

variable {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [LinearOrder ι]
  [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} {a : ℕ → StdSimplex ℝ ℕ} {M : Ω → ℝ}

/-- If convex combinations of the terminal values `M^m_⊤` of the discrete martingale parts converge
in `L¹` to `M`, then at each time `t` the same convex combinations of the processes
`martingaleSeqStep` converge in `L¹` to `P[M | 𝓕 t]`. Proved by using conditional Jensen. -/
lemma tendsto_eLpNorm_weights_sum_martingaleSeqStep (hs : Submartingale S 𝓕 P)
    (hM : Integrable M P)
    (ha : Tendsto (fun n ↦ eLpNorm
      ((a n).weights.sum (fun m r ↦ r • martingaleSeqTop S 𝓕 P m) - M) 1 P) atTop (𝓝 0))
    (t : ι) :
    Tendsto (fun n ↦ eLpNorm
      (((a n).weights.sum fun m r ↦ r • martingaleSeqStep P S 𝓕 m) t - P[M | 𝓕 t]) 1 P)
      atTop (𝓝 0) := by
  have hint (m : ℕ) : Integrable (martingaleSeqTop S 𝓕 P m) P :=
    integrable_martingaleSeqTop 𝓕 (hs.integrable ⊤) m
  have hae (n : ℕ) :
      ((a n).weights.sum fun m r ↦ r • martingaleSeqStep P S 𝓕 m) t - P[M | 𝓕 t] =ᵐ[P]
        P[(a n).weights.sum (fun m r ↦ r • martingaleSeqTop S 𝓕 P m) - M | 𝓕 t] := by
    have h1 : ((a n).weights.sum fun m r ↦ r • martingaleSeqStep P S 𝓕 m) t =ᵐ[P]
        P[(a n).weights.sum (fun m r ↦ r • martingaleSeqTop S 𝓕 P m) | 𝓕 t] := by
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, martingaleSeqStep]
      refine ((condExp_finsetSum (fun m _ ↦ (hint m).smul _) _).trans ?_).symm
      exact eventuallyEq_sum fun m _ ↦ condExp_smul _ _ _
    refine (h1.sub (EventuallyEq.refl _ (P[M | 𝓕 t]))).trans ?_
    exact (condExp_sub (integrable_finsetSum' _ fun m _ ↦ (hint m).smul _) hM _).symm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ha (fun _ ↦ zero_le)
    fun n ↦ ?_
  rw [eLpNorm_congr_ae (hae n)]
  exact eLpNorm_condExp_le_eLpNorm _ le_rfl

variable [IsFiniteMeasure P]

/-- If the weights at step `n` vanish on meshes of index below `n`, then past the index at which
`t` enters the meshes, the convex combination of the processes `predictableSeqStep` at `t` is a.e.
equal to the process minus the same convex combination of the processes `martingaleSeqStep`. -/
lemma weights_sum_predictableSeqStep_ae_eq (hs : Submartingale S 𝓕 P)
    (ha0 : ∀ n, ∀ m < n, (a n).weights m = 0) {t : ι} {k n : ℕ}
    (hk : denseEnum ι k = t) (hkn : k < n) :
    ((a n).weights.sum fun m r ↦ r • predictableSeqStep P S 𝓕 m) t =ᵐ[P]
      S t - ((a n).weights.sum fun m r ↦ r • martingaleSeqStep P S 𝓕 m) t := by
  have hkey : ∀ᵐ ω ∂P, ∀ m, k < m →
      predictableSeqStep P S 𝓕 m t ω = S t ω - martingaleSeqStep P S 𝓕 m t ω :=
    ae_all_iff.2 fun m ↦ by
      by_cases hkm : k < m
      · filter_upwards [predictableSeqStep_ae_eq_sub_martingaleSeqStep hs.stronglyAdapted
          hs.integrable (hk ▸ denseEnum_mem_mesh ι hkm)] with ω hω _
        exact hω
      · exact .of_forall fun ω h ↦ absurd h hkm
  have htotal : ∑ m ∈ (a n).weights.support, (a n).weights m = 1 := by
    simpa [Finsupp.sum] using (a n).total
  filter_upwards [hkey] with ω hω
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hsum : ∑ m ∈ (a n).weights.support, (a n).weights m * predictableSeqStep P S 𝓕 m t ω
      = ∑ m ∈ (a n).weights.support,
        ((a n).weights m * S t ω - (a n).weights m * martingaleSeqStep P S 𝓕 m t ω) := by
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hnm : n ≤ m := by
      by_contra hlt
      exact (Finsupp.mem_support_iff.1 hm) (ha0 n m (not_le.1 hlt))
    rw [hω m (hkn.trans_le hnm), mul_sub]
  rw [hsum, Finset.sum_sub_distrib, ← Finset.sum_mul, htotal, one_mul]

/-- If convex combinations of the terminal values `M^m_⊤` of the discrete martingale parts converge
in `L¹` to `M`, with weights at step `n` vanishing on meshes of index below `n`, then for `t` in
`denseSet ι` the same convex combinations of the processes `predictableSeqStep` at `t` converge in
`L¹` to `S t - P[M | 𝓕 t]`. -/
lemma tendsto_eLpNorm_weights_sum_predictableSeqStep (hs : Submartingale S 𝓕 P)
    (hM : Integrable M P) (ha0 : ∀ n, ∀ m < n, (a n).weights m = 0)
    (ha : Tendsto (fun n ↦ eLpNorm
      ((a n).weights.sum (fun m r ↦ r • martingaleSeqTop S 𝓕 P m) - M) 1 P) atTop (𝓝 0))
    {t : ι} (ht : t ∈ denseSet ι) :
    Tendsto (fun n ↦ eLpNorm
      (((a n).weights.sum fun m r ↦ r • predictableSeqStep P S 𝓕 m) t - (S t - P[M | 𝓕 t])) 1 P)
      atTop (𝓝 0) := by
  obtain ⟨k, hk⟩ := exists_denseEnum_eq ι ht
  refine (tendsto_eLpNorm_weights_sum_martingaleSeqStep hs hM ha t).congr' ?_
  filter_upwards [eventually_gt_atTop k] with n hn
  rw [← eLpNorm_neg]
  refine eLpNorm_congr_ae ?_
  filter_upwards [weights_sum_predictableSeqStep_ae_eq hs ha0 hk hn] with ω hω
  simp only [Pi.neg_apply, Pi.sub_apply, hω]
  ring

/-- If convex combinations of the terminal values `M^m_⊤` of the discrete martingale parts converge
in `L¹` to `M`, with weights at step `n` vanishing on meshes of index below `n`, then there is a
subsequence along which, almost surely, the same convex combinations of the processes
`predictableSeqStep` converge to `S t - P[M | 𝓕 t]` at every point `t` of the countable dense
set. -/
lemma exists_strictMono_ae_tendsto_weights_sum_predictableSeqStep (hs : Submartingale S 𝓕 P)
    (hM : Integrable M P) (ha0 : ∀ n, ∀ m < n, (a n).weights m = 0)
    (ha : Tendsto (fun n ↦ eLpNorm
      ((a n).weights.sum (fun m r ↦ r • martingaleSeqTop S 𝓕 P m) - M) 1 P) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ t ∈ denseSet ι,
      Tendsto (fun n ↦ ((a (φ n)).weights.sum fun m r ↦ r • predictableSeqStep P S 𝓕 m) t ω)
        atTop (𝓝 (S t ω - P[M | 𝓕 t] ω)) := by
  have : Countable (denseSet ι) := (denseSet_countable ι).to_subtype
  have h_meas (t : denseSet ι) : TendstoInMeasure P
      (fun n ↦ ((a n).weights.sum fun m r ↦ r • predictableSeqStep P S 𝓕 m) t) atTop
      (S t - P[M | 𝓕 t]) :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun n ↦ ((stronglyAdapted_weights_sum_predictableSeqStep P S 𝓕 (a n).weights t).mono
        (𝓕.le t)).aestronglyMeasurable)
      ((hs.integrable t).aestronglyMeasurable.sub integrable_condExp.aestronglyMeasurable)
      (tendsto_eLpNorm_weights_sum_predictableSeqStep hs hM ha0 ha t.2)
  obtain ⟨φ, hφ, h⟩ := exists_strictMono_forall_ae_tendsto_of_tendstoInMeasure h_meas
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [h] with ω hω t ht
  exact hω ⟨t, ht⟩

end WeightsSumConv

-- We define the martingale part in the Doob-Meyer decomposition: the càdlàg modification of the
-- martingale of conditional expectations of the `L¹` limit `martingaleLim`.
section MartingalePartLimDef

/-- Show that the terminals values of some convex combinations of the martingale parts converge.
The convex combination at step `n` only involves meshes of index at least `n`, as provided by
`komlos_L1`. The weights are moreover chosen along a subsequence for which the corresponding convex
combinations of the step extensions of the discrete predictable parts converge almost surely,
simultaneously at all points of the countable dense set. -/
lemma exists_martingalPart_lim {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) :
    ∃ M : Ω → ℝ, ∃ a : ℕ → StdSimplex ℝ ℕ, Integrable M P ∧
      (∀ n, ∀ m < n, (a n).weights m = 0) ∧
      Tendsto (fun n ↦ eLpNorm ((a n).weights.sum (fun m r ↦ r • martingaleSeqTop S 𝓕 P m) - M) 1 P)
        atTop (𝓝 0) ∧
      ∀ᵐ ω ∂P, ∀ t ∈ denseSet ι, Tendsto (fun n ↦ ((a n).weights.sum
        fun m r ↦ r • predictableSeqStep P S 𝓕 m) t ω) atTop (𝓝 (S t ω - P[M | 𝓕 t] ω)) := by
  obtain ⟨g, M, hM, h_convex, h_tendsto⟩ :=
    komlos_L1 (uniformIntegrable_martingaleSeqTop hd.uniformIntegrable_of_countable_range hs)
  choose a ha h0 using fun n ↦
    exists_stdSimplex_of_mem_convexTail_reindexed (x := martingaleSeqTop S 𝓕 P) h_convex n
  have hM' : Integrable M P := memLp_one_iff_integrable.1 hM
  have h_tendsto' : Tendsto (fun n ↦ eLpNorm
      ((a n).weights.sum (fun m r ↦ r • martingaleSeqTop S 𝓕 P m) - M) 1 P) atTop (𝓝 0) :=
    h_tendsto.congr fun n ↦ by rw [ha n]
  -- we pass to a subsequence of the weights to get almost sure convergence on the dense set
  obtain ⟨φ, hφ, hφ_ae⟩ :=
    exists_strictMono_ae_tendsto_weights_sum_predictableSeqStep hs hM' h0 h_tendsto'
  exact ⟨M, fun n ↦ a (φ n), hM', fun n m hmn ↦ h0 (φ n) m (hmn.trans_le hφ.le_apply),
    h_tendsto'.comp hφ.tendsto_atTop, hφ_ae⟩

/-- The `L¹` limit of the convex combinations of the terminal values of the discrete martingale
parts, given by `exists_martingalPart_lim`. -/
noncomputable def martingaleLim {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) : Ω → ℝ :=
  (exists_martingalPart_lim hd hs).choose

/-- The martingale part `M` in the Doob-Meyer decomposition of a submartingale of class D: the
càdlàg modification of the martingale `t ↦ P[martingaleLim hd hs | 𝓕 t]`.

All its paths are càdlàg (`isCadlag_martingalePartLim`) and it is a modification of
`t ↦ P[martingaleLim hd hs | 𝓕 t]` (`martingalePartLim_ae_eq`). Under the usual conditions on the
filtration it is adapted, hence a martingale (`martingale_martingalePartLim`). -/
noncomputable def martingalePartLim {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) : ι → Ω → ℝ :=
  cadlagModifReal fun i ↦ P[martingaleLim hd hs | 𝓕 i]

/-- This is the weight associated with the martingale part. -/
noncomputable def weight {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) : ℕ → StdSimplex ℝ ℕ :=
  (exists_martingalPart_lim hd hs).choose_spec.choose

section

variable {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
  [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}

/-- The limit of the convex combinations of the terminal martingale parts is integrable. -/
lemma integrable_martingaleLim (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) :
    Integrable (martingaleLim hd hs) P :=
  (exists_martingalPart_lim hd hs).choose_spec.choose_spec.1

/-- The Komlós weights at step `n` vanish on meshes of index below `n`. -/
lemma weight_apply_eq_zero_of_lt (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) {m n : ℕ}
    (hmn : m < n) : (weight hd hs n).weights m = 0 :=
  (exists_martingalPart_lim hd hs).choose_spec.choose_spec.2.1 n m hmn

/-- `L¹` convergence of the convex combinations of the terminal martingale parts to
`martingaleLim`. -/
lemma tendsto_eLpNorm_weight_sum_martingaleSeqTop (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) :
    Tendsto (fun n ↦ eLpNorm ((weight hd hs n).weights.sum
      (fun m r ↦ r • martingaleSeqTop S 𝓕 P m) - martingaleLim hd hs) 1 P) atTop (𝓝 0) :=
  (exists_martingalPart_lim hd hs).choose_spec.choose_spec.2.2.1

/-- Almost surely, the convex combinations of the step extensions of the discrete predictable parts
converge to `S t - P[martingaleLim hd hs | 𝓕 t]` at every point `t` of the countable dense set. -/
lemma ae_tendsto_weight_sum_predictableSeqStep (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) :
    ∀ᵐ ω ∂P, ∀ t ∈ denseSet ι, Tendsto (fun n ↦ ((weight hd hs n).weights.sum
      fun m r ↦ r • predictableSeqStep P S 𝓕 m) t ω) atTop
      (𝓝 (S t ω - P[martingaleLim hd hs | 𝓕 t] ω)) :=
  (exists_martingalPart_lim hd hs).choose_spec.choose_spec.2.2.2

/-- The martingale part of the decomposition is a modification of the martingale
`t ↦ P[martingaleLim hd hs | 𝓕 t]`. -/
lemma martingalePartLim_ae_eq [𝓕.IsRightContinuous]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (t : ι) :
    martingalePartLim hd hs t =ᵐ[P] P[martingaleLim hd hs | 𝓕 t] :=
  (martingale_condExp (martingaleLim hd hs) 𝓕 P).cadlagModifReal_ae_eq t

/-- The paths of the martingale part of the decomposition are càdlàg. -/
lemma isCadlag_martingalePartLim (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (ω : Ω) :
    IsCadlag (martingalePartLim hd hs · ω) :=
  isCadlag_cadlagModifReal ω

/-- The martingale part of the decomposition is integrable at each time. -/
lemma integrable_martingalePartLim [𝓕.IsRightContinuous]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (t : ι) :
    Integrable (martingalePartLim hd hs t) P :=
  integrable_condExp.congr (martingalePartLim_ae_eq hd hs t).symm

/-- Under the usual conditions, the martingale part of the decomposition is strongly adapted. -/
lemma stronglyAdapted_martingalePartLim [𝓕.IsRightContinuous] [𝓕.IsComplete P]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) :
    StronglyAdapted 𝓕 (martingalePartLim hd hs) :=
  stronglyAdapted_cadlagModifReal
    (martingale_condExp (martingaleLim hd hs) 𝓕 P).isRealQuasimartingale

/-- Under the usual conditions, the martingale part of the decomposition is a martingale. -/
lemma martingale_martingalePartLim [𝓕.IsRightContinuous] [𝓕.IsComplete P]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) :
    Martingale (martingalePartLim hd hs) 𝓕 P := by
  refine ⟨stronglyAdapted_martingalePartLim hd hs, fun i j hij ↦ ?_⟩
  calc P[martingalePartLim hd hs j | 𝓕 i]
      =ᵐ[P] P[P[martingaleLim hd hs | 𝓕 j] | 𝓕 i] :=
        condExp_congr_ae (martingalePartLim_ae_eq hd hs j)
    _ =ᵐ[P] P[martingaleLim hd hs | 𝓕 i] :=
        (martingale_condExp (martingaleLim hd hs) 𝓕 P).condExp_ae_eq hij
    _ =ᵐ[P] martingalePartLim hd hs i := (martingalePartLim_ae_eq hd hs i).symm

/-- At each time, the martingale part of the decomposition has the same expectation as the initial
value of the process. -/
lemma integral_martingalePartLim [𝓕.IsRightContinuous]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (i : ι) :
    ∫ ω, martingalePartLim hd hs i ω ∂P = ∫ ω, S ⊥ ω ∂P := by
  have hint (m : ℕ) : Integrable (martingaleSeqTop S 𝓕 P m) P :=
    integrable_martingaleSeqTop 𝓕 (hs.integrable ⊤) m
  have hg (n : ℕ) : ∫ ω, ((weight hd hs n).weights.sum
      fun m r ↦ r • martingaleSeqTop S 𝓕 P m) ω ∂P = ∫ ω, S ⊥ ω ∂P := by
    have htotal : ∑ m ∈ (weight hd hs n).weights.support, (weight hd hs n).weights m = 1 := by
      simpa [Finsupp.sum] using (weight hd hs n).total
    simp only [Finsupp.sum, Finset.sum_apply]
    rw [integral_finsetSum _ fun m _ ↦ (hint m).smul _]
    simp_rw [Pi.smul_apply, integral_smul,
      integral_martingaleSeqTop 𝓕 hs.stronglyAdapted hs.integrable]
    rw [← Finset.sum_smul, htotal, one_smul]
  have hlim : Tendsto (fun n ↦ ∫ ω, ((weight hd hs n).weights.sum
      fun m r ↦ r • martingaleSeqTop S 𝓕 P m) ω ∂P) atTop
      (𝓝 (∫ ω, martingaleLim hd hs ω ∂P)) :=
    tendsto_integral_of_L1' _ (integrable_martingaleLim hd hs).aestronglyMeasurable
      (.of_forall fun n ↦ integrable_finsetSum' _ fun m _ ↦ (hint m).smul _)
      (tendsto_eLpNorm_weight_sum_martingaleSeqTop hd hs)
  rw [integral_congr_ae (martingalePartLim_ae_eq hd hs i), integral_condExp (𝓕.le i)]
  refine tendsto_nhds_unique hlim ?_
  simp_rw [hg]
  exact tendsto_const_nhds

end

/-- The convexly averaged mesh step-extension `ℳ^n` of the martingale parts. -/
noncomputable def martingaleConvexStep {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) : ι → Ω → ℝ :=
  (weight hd hs n).weights.sum fun m r ↦ r • martingaleSeqStep P S 𝓕 m

/-- `L¹` norm convergence of `martingaleConvexStep`, proved by using conditional Jensen. -/
lemma martingaleConvexStep_eLpNorm_tendsto {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (t : ι) :
    Tendsto (fun n ↦ eLpNorm
      (martingaleConvexStep hd hs n t - martingalePartLim hd hs t) 1 P) atTop (𝓝 0) :=
  (tendsto_eLpNorm_weights_sum_martingaleSeqStep hs (integrable_martingaleLim hd hs)
    (tendsto_eLpNorm_weight_sum_martingaleSeqTop hd hs) t).congr fun _ ↦
    eLpNorm_congr_ae (.sub .rfl (martingalePartLim_ae_eq hd hs t).symm)

end MartingalePartLimDef

-- We define the predictable part in the Doob-Meyer decomposition: the process minus the càdlàg
-- martingale part.
section PredictablePartLimDef

/-- The convexly averaged mesh step-extension `𝒜^n` of the predictable parts. -/
noncomputable def predictableConvexStep {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) : ι → Ω → ℝ :=
  (weight hd hs n).weights.sum fun m r ↦ r • predictableSeqStep P S 𝓕 m

/-- The predictable part `A` in the Doob-Meyer decomposition, defined as `S - M` where the
martingale part `M = martingalePartLim hd hs` is the càdlàg modification of the martingale
`t ↦ P[martingaleLim hd hs | 𝓕 t]`. In particular `A` is càdlàg as soon as `S` is
(`isCadlag_predictablePartLim_ae`). -/
noncomputable def predictablePartLim {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) : ι → Ω → ℝ :=
  S - martingalePartLim hd hs

/-- The predictable part of the decomposition is integrable at each time. -/
lemma integrable_predictablePartLim {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (t : ι) :
    Integrable (predictablePartLim hd hs t) P :=
  (hs.integrable t).sub (integrable_martingalePartLim hd hs t)

/-- If the paths of `S` are almost surely càdlàg, then so are the paths of the predictable part of
the decomposition. -/
lemma isCadlag_predictablePartLim_ae {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    ∀ᵐ ω ∂P, IsCadlag (predictablePartLim hd hs · ω) := by
  filter_upwards [hc] with ω hω
  exact hω.sub (isCadlag_martingalePartLim hd hs ω)

/-- If the paths of `S` are almost surely càdlàg, then the paths of the predictable part of the
decomposition are almost surely right-continuous. -/
lemma isRightContinuous_predictablePartLim_ae {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    ∀ᵐ ω ∂P, IsRightContinuous (predictablePartLim hd hs · ω) :=
  (isCadlag_predictablePartLim_ae hd hs hc).mono fun _ hω ↦ hω.right_continuous

/-- The convexly averaged mesh step-extension of the predictable parts is strongly adapted. -/
lemma stronglyAdapted_predictableConvexStep {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) :
    StronglyAdapted 𝓕 (predictableConvexStep hd hs n) :=
  stronglyAdapted_weights_sum_predictableSeqStep P S 𝓕 (weight hd hs n).weights

end PredictablePartLimDef

-- We discretize a stopping time from the right along the meshes.
section MeshCeil

variable {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [LinearOrder ι]
  [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} {τ : Ω → WithTop ι}

/-- The discretization `σₙ` of a stopping time `τ` from the right along the `n`-th mesh: the
smallest mesh point greater than or equal to `τ`, or `⊤` if `τ = ⊤`. -/
noncomputable def meshCeil (n : ℕ) (τ : Ω → WithTop ι) : Ω → WithTop ι :=
  fun ω ↦ ((mesh ι n).filter fun u : ι ↦ τ ω ≤ (u : WithTop ι)).min

lemma le_meshCeil (n : ℕ) (ω : Ω) : τ ω ≤ meshCeil n τ ω :=
  Finset.le_min fun _ hu ↦ (Finset.mem_filter.1 hu).2

lemma meshCeil_le {n : ℕ} {ω : Ω} {u : ι} (hu : u ∈ mesh ι n) (hτu : τ ω ≤ (u : WithTop ι)) :
    meshCeil n τ ω ≤ (u : WithTop ι) :=
  Finset.min_le (Finset.mem_filter.2 ⟨hu, hτu⟩)

lemma meshCeil_ne_top (n : ℕ) {ω : Ω} (hτ : τ ω ≠ ⊤) : meshCeil n τ ω ≠ ⊤ := by
  intro h
  simp only [meshCeil, Finset.min_eq_top, Finset.filter_eq_empty_iff] at h
  exact h (top_mem_mesh ι n) (WithTop.le_coe_top hτ)

lemma mesh_mem_of_meshCeil_eq_coe {n : ℕ} {ω : Ω} {u : ι}
    (h : meshCeil n τ ω = (u : WithTop ι)) :
    u ∈ mesh ι n ∧ τ ω ≤ (u : WithTop ι) :=
  Finset.mem_filter.1 <| Finset.mem_of_min h

lemma exists_meshCeil_eq_coe (n : ℕ) {ω : Ω} (hτ : τ ω ≠ ⊤) :
    ∃ u ∈ mesh ι n, meshCeil n τ ω = (u : WithTop ι) ∧ τ ω ≤ (u : WithTop ι) := by
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 (meshCeil_ne_top n hτ)
  obtain ⟨h1, h2⟩ := mesh_mem_of_meshCeil_eq_coe hu.symm
  exact ⟨u, h1, hu.symm, h2⟩

lemma meshCeil_eq_bot {n : ℕ} {ω : Ω} (h : τ ω = ((⊥ : ι) : WithTop ι)) :
    meshCeil n τ ω = ((⊥ : ι) : WithTop ι) :=
  le_antisymm (meshCeil_le (bot_mem_mesh ι n) h.le) (h ▸ le_meshCeil n ω)

lemma countable_range_meshCeil (n : ℕ) (τ : Ω → WithTop ι) :
    (Set.range (meshCeil n τ)).Countable := by
  refine ((((mesh ι n).image fun u : ι ↦ (u : WithTop ι)).countable_toSet).insert ⊤).mono ?_
  rintro x ⟨ω, rfl⟩
  rcases eq_or_ne (meshCeil n τ ω) ⊤ with h | h
  · exact h ▸ Set.mem_insert _ _
  · obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 h
    exact hu ▸ Set.mem_insert_of_mem _
      (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (mesh_mem_of_meshCeil_eq_coe hu.symm).1))

/-- The mesh discretization of a stopping time is a stopping time. -/
lemma isStoppingTime_meshCeil (hτ : IsStoppingTime 𝓕 τ) (n : ℕ) :
    IsStoppingTime 𝓕 (meshCeil n τ) := by
  intro t
  have h_eq : {ω | meshCeil n τ ω ≤ t}
      = ⋃ u ∈ {u ∈ mesh ι n | u ≤ t}, {ω | τ ω ≤ (u : WithTop ι)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · intro h
      rcases eq_or_ne (meshCeil n τ ω) ⊤ with htop | htop
      · rw [htop] at h
        exact absurd (top_le_iff.1 h) WithTop.coe_ne_top
      · obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 htop
        obtain ⟨h1, h2⟩ := mesh_mem_of_meshCeil_eq_coe hu.symm
        exact ⟨u, ⟨h1, WithTop.coe_le_coe.1 (hu.le.trans h)⟩, h2⟩
    · rintro ⟨u, ⟨hu_mesh, hut⟩, hτu⟩
      exact (meshCeil_le hu_mesh hτu).trans (WithTop.coe_le_coe.2 hut)
  rw [h_eq]
  exact Finset.measurableSet_biUnion _ fun u hu ↦
    𝓕.mono (Finset.mem_filter.1 hu).2 _ (hτ u)

/-- The mesh discretizations of `τ` converge to `τ` from the right. -/
lemma tendsto_untopA_meshCeil {ω : Ω} (hτ : τ ω ≠ ⊤) :
    Tendsto (fun n ↦ (meshCeil n τ ω).untopA) atTop (𝓝[≥] (τ ω).untopA) := by
  obtain ⟨t₀, ht₀⟩ := WithTop.ne_top_iff_exists.1 hτ
  have hle (n : ℕ) : t₀ ≤ (meshCeil n τ ω).untopA :=
    (WithTop.le_untopA_iff (meshCeil_ne_top n hτ)).2 (ht₀.le.trans (le_meshCeil n ω))
  rw [← ht₀, WithTop.untopA_coe, tendsto_nhdsWithin_iff]
  refine ⟨tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun n ↦ ha.trans_le (hle n),
    fun b hb ↦ ?_⟩, Eventually.of_forall fun n ↦ hle n⟩
  obtain ⟨d, hd_mem, hd₁, hd₂⟩ := exists_mem_denseSet_Ico hb
  obtain ⟨k, hk⟩ := exists_denseEnum_eq ι hd_mem
  filter_upwards [eventually_gt_atTop k] with n hn
  have hceil : meshCeil n τ ω ≤ (d : WithTop ι) :=
    meshCeil_le (hk ▸ denseEnum_mem_mesh ι hn) (ht₀ ▸ WithTop.coe_le_coe.2 hd₁)
  exact ((WithTop.untopA_le_iff (meshCeil_ne_top n hτ)).2 hceil).trans_lt hd₂

/-- Sampling the step extension of the discrete predictable part at `τ` is the same as sampling
it at the mesh discretization `σₙ` of `τ`. -/
lemma stoppedValue_predictableSeqStep_meshCeil {n : ℕ} (hτ_ne : ∀ ω, τ ω ≠ ⊤) :
    stoppedValue (predictableSeqStep P S 𝓕 n) τ
      = stoppedValue (predictableSeqStep P S 𝓕 n) (meshCeil n τ) := by
  funext ω
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (hτ_ne ω)
  obtain ⟨u, humesh, hcoe, hle⟩ := exists_meshCeil_eq_coe n (hτ_ne ω)
  simp only [stoppedValue, hcoe, ← ht, WithTop.untopA_coe]
  rcases eq_or_ne t ⊥ with rfl | ht_bot
  · rw [WithTop.coe_injective (hcoe.symm.trans (meshCeil_eq_bot ht.symm))]
  · have htu : t ≤ u := WithTop.coe_le_coe.1 (ht.trans_le hle)
    have hu_bot : (⟨u, humesh⟩ : mesh ι n) ≠ ⊥ :=
      fun h ↦ ht_bot (le_bot_iff.1 (htu.trans_eq (congrArg Subtype.val h)))
    have hpred : ((pred (⟨u, humesh⟩ : mesh ι n) : mesh ι n) : ι) < t := by
      by_contra hcon
      rw [not_lt] at hcon
      have h2 := meshCeil_le (pred (⟨u, humesh⟩ : mesh ι n)).2
        (le_trans (le_of_eq ht.symm) (by exact_mod_cast hcon))
      rw [hcoe, WithTop.coe_le_coe] at h2
      exact absurd (Subtype.coe_le_coe.1 h2) (not_le.2 (pred_lt_iff_ne_bot.2 hu_bot))
    rw [predictableSeqStep_apply_of_mem (u := ⟨u, humesh⟩) ⟨hpred, htu⟩,
      predictableSeqStep_apply_of_mem (u := ⟨u, humesh⟩)
        ⟨Subtype.coe_lt_coe.2 (pred_lt_iff_ne_bot.2 hu_bot), le_rfl⟩]

/-- Sampled at the mesh discretization `σₙ`, the step extension of the discrete predictable part
decomposes as the sampled process minus the sampled conditional expectations of the terminal
value of the discrete martingale part. -/
lemma stoppedValue_predictableSeqStep_ae_eq [SigmaFiniteFiltration P 𝓕] {n : ℕ}
    (hS_adapted : StronglyAdapted 𝓕 S) (hS_int : ∀ t, Integrable (S t) P)
    (hτ_ne : ∀ ω, τ ω ≠ ⊤) :
    stoppedValue (predictableSeqStep P S 𝓕 n) (meshCeil n τ) =ᵐ[P]
      stoppedValue S (meshCeil n τ)
        - stoppedValue (martingaleSeqStep P S 𝓕 n) (meshCeil n τ) := by
  have hkey : ∀ᵐ ω ∂P, ∀ u : mesh ι n,
      martingalePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P u ω
        = martingaleSeqStep P S 𝓕 n ↑u ω :=
    ae_all_iff.2 fun u ↦
      ((martingale_martingalePart_mesh hS_adapted hS_int n).condExp_ae_eq (le_top (a := u))).symm
  filter_upwards [hkey] with ω hω
  obtain ⟨u, humesh, hcoe, hle⟩ := exists_meshCeil_eq_coe n (hτ_ne ω)
  simp only [stoppedValue, hcoe, WithTop.untopA_coe, Pi.sub_apply]
  calc predictableSeqStep P S 𝓕 n u ω
      = predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⟨u, humesh⟩ ω := by
        rcases eq_or_ne (⟨u, humesh⟩ : mesh ι n) ⊥ with h | h
        · have hu : u = ⊥ := by simpa using congrArg Subtype.val h
          rw [h, hu]
          simp [predictableSeqStep, meshPredIoc]
        · rw [predictableSeqStep_apply_of_mem
            ⟨Subtype.coe_lt_coe.2 (pred_lt_iff_ne_bot.2 h), le_rfl⟩]
    _ = S u ω - martingalePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⟨u, humesh⟩ ω :=
        eq_sub_of_add_eq' (congrFun (congrFun
          (martingalePart_add_predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P) _) ω)
    _ = S u ω - martingaleSeqStep P S 𝓕 n u ω := by rw [hω ⟨u, humesh⟩]

/-- The expectation of the stopped step extension of the discrete predictable part. -/
lemma integral_stoppedValue_predictableSeqStep [MeasurableSpace ι]
    [IsFiniteMeasure P]
    (hd : ClassD S 𝓕 P) (hS_adapted : StronglyAdapted 𝓕 S) (hS_int : ∀ t, Integrable (S t) P)
    (hτ : IsStoppingTime 𝓕 τ) (hτ_ne : ∀ ω, τ ω ≠ ⊤) (n : ℕ) :
    ∫ ω, stoppedValue (predictableSeqStep P S 𝓕 n) τ ω ∂P
      = ∫ ω, stoppedValue S (meshCeil n τ) ω ∂P - ∫ ω, S ⊥ ω ∂P := by
  have hσ : IsStoppingTime 𝓕 (meshCeil n τ) := isStoppingTime_meshCeil hτ n
  have hσ_ne (ω) : meshCeil n τ ω ≠ ⊤ := meshCeil_ne_top n (hτ_ne ω)
  have hσ_le (ω) : meshCeil n τ ω ≤ ((⊤ : ι) : WithTop ι) := WithTop.le_coe_top (hσ_ne ω)
  have hN : Martingale (martingaleSeqStep P S 𝓕 n) 𝓕 P := martingale_condExp _ _ _
  have hint_S : Integrable (stoppedValue S (meshCeil n τ)) P :=
    memLp_one_iff_integrable.1 (hd.uniformIntegrable.memLp ⟨_, hσ, hσ_ne⟩)
  have hint_N : Integrable (stoppedValue (martingaleSeqStep P S 𝓕 n) (meshCeil n τ)) P :=
    hN.integrable_stoppedValue_of_countable_range _ hσ hσ_le (countable_range_meshCeil n τ)
  rw [stoppedValue_predictableSeqStep_meshCeil hτ_ne,
    integral_congr_ae (stoppedValue_predictableSeqStep_ae_eq hS_adapted hS_int hτ_ne)]
  simp only [Pi.sub_apply]
  rw [integral_sub hint_S hint_N]
  congr 1
  calc ∫ ω, stoppedValue (martingaleSeqStep P S 𝓕 n) (meshCeil n τ) ω ∂P
      = ∫ ω, (P[martingaleSeqStep P S 𝓕 n ⊤|hσ.measurableSpace]) ω ∂P := integral_congr_ae <|
        hN.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hσ hσ_le
          (countable_range_meshCeil n τ)
    _ = ∫ ω, P[martingaleSeqTop S 𝓕 P n|𝓕 ⊤] ω ∂P := integral_condExp _
    _ = ∫ ω, martingaleSeqTop S 𝓕 P n ω ∂P := integral_condExp (𝓕.le ⊤)
    _ = ∫ ω, S ⊥ ω ∂P := integral_martingaleSeqTop 𝓕 hS_adapted hS_int n

/-- Expectations of the process sampled at the mesh discretizations of `τ` converge to the
expectation of the process sampled at `τ`. -/
lemma tendsto_integral_stoppedValue_meshCeil
    [MeasurableSpace ι] [IsFiniteMeasure P]
    (hd : ClassD S 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) (hτ_ne : ∀ ω, τ ω ≠ ⊤)
    (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    Tendsto (fun n ↦ ∫ ω, stoppedValue S (meshCeil n τ) ω ∂P) atTop
      (𝓝 (∫ ω, stoppedValue S τ ω ∂P)) := by
  have hUI : UniformIntegrable (fun n ↦ stoppedValue S (meshCeil n τ)) 1 P :=
    hd.uniformIntegrable.comp fun n ↦ ⟨meshCeil n τ, isStoppingTime_meshCeil hτ n,
      fun ω ↦ meshCeil_ne_top n (hτ_ne ω)⟩
  have hmem : MemLp (stoppedValue S τ) 1 P := hd.uniformIntegrable.memLp ⟨τ, hτ, hτ_ne⟩
  have hae : ∀ᵐ ω ∂P, Tendsto (fun n ↦ stoppedValue S (meshCeil n τ) ω) atTop
      (𝓝 (stoppedValue S τ ω)) := by
    filter_upwards [hc] with ω hcad
    exact Tendsto.comp (continuousWithinAt_Ioi_iff_Ici.1 (hcad.right_continuous ((τ ω).untopA)))
      (tendsto_untopA_meshCeil (hτ_ne ω))
  have hL1 : Tendsto (fun n ↦ eLpNorm (stoppedValue S (meshCeil n τ) - stoppedValue S τ) 1 P)
      atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hUI.1 hmem hUI.2.1
      (tendstoInMeasure_of_tendsto_ae hUI.1 hae)
  exact tendsto_integral_of_L1' _ hmem.aestronglyMeasurable
    (.of_forall fun n ↦ memLp_one_iff_integrable.1 (hUI.memLp n)) hL1

end MeshCeil

-- The mesh discretizations make the time index approximable, which gives optional sampling.
section MeshApprox

variable {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [LinearOrder ι]
  [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ}

/-- The meshes are increasing. -/
lemma mesh_mono (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] : Monotone (mesh ι) := by
  intro m n hmn
  unfold mesh
  gcongr

/-- The mesh discretizations of a random time are decreasing in the mesh index. -/
lemma meshCeil_anti (τ : Ω → WithTop ι) : Antitone (fun n ↦ meshCeil n τ) :=
  fun _ _ hmn _ ↦ Finset.min_mono (Finset.filter_subset_filter _ (mesh_mono ι hmn))

/-- The mesh discretizations of a random time converge to it in `WithTop ι`. -/
lemma tendsto_meshCeil (τ : Ω → WithTop ι) (ω : Ω) :
    Tendsto (fun n ↦ meshCeil n τ ω) atTop (𝓝 (τ ω)) := by
  rcases eq_or_ne (τ ω) ⊤ with hτ | hτ
  · have h_top (n : ℕ) : meshCeil n τ ω = ⊤ := top_le_iff.1 (hτ ▸ le_meshCeil n ω)
    simp only [h_top, hτ]
    exact tendsto_const_nhds
  · have h_tendsto := (WithTop.continuous_coe.tendsto _).comp
      ((tendsto_untopA_meshCeil hτ).mono_right nhdsWithin_le_nhds)
    rw [WithTop.coe_untopA hτ] at h_tendsto
    refine h_tendsto.congr fun n ↦ ?_
    simp [WithTop.coe_untopA (meshCeil_ne_top n hτ)]

/-- The mesh discretizations of a stopping time form a discrete approximation sequence. -/
noncomputable def MeasureTheory.IsStoppingTime.meshCeilApproxSequence {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime 𝓕 τ) (μ : Measure Ω) :
    DiscreteApproxSequence 𝓕 τ μ where
  seq n := meshCeil n τ
  isStoppingTime := isStoppingTime_meshCeil hτ
  countable n := countable_range_meshCeil n τ
  antitone := meshCeil_anti τ
  le n ω := le_meshCeil n ω
  tendsto := ae_of_all _ (tendsto_meshCeil τ)

/-- A second-countable time index with a bottom and a top element is approximable: every stopping
time is the limit of its mesh discretizations. -/
noncomputable instance approximable_of_mesh {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω} :
    Approximable 𝓕 μ :=
  ⟨fun _ hτ ↦ hτ.meshCeilApproxSequence μ⟩

end MeshApprox

/-- Optional sampling at a finite stopping time for a right-continuous martingale indexed by a
bounded time set. -/
lemma MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_top {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ι mΩ} {X : ι → Ω → ℝ} {τ : Ω → WithTop ι} (hX : Martingale X 𝓕 P)
    (hRC : ∀ ω, IsRightContinuous (X · ω)) (hτ : IsStoppingTime 𝓕 τ) (hτ_ne : ∀ ω, τ ω ≠ ⊤) :
    stoppedValue X τ =ᵐ[P] P[X ⊤ | hτ.measurableSpace] :=
  hX.stoppedValue_ae_eq_condExp_of_le_const' hRC hτ fun ω ↦ WithTop.le_coe_top (hτ_ne ω)

/-- The value of a right-continuous martingale indexed by a bounded time set at a finite stopping
time is integrable. -/
lemma MeasureTheory.Martingale.integrable_stoppedValue_top {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ι mΩ} {X : ι → Ω → ℝ} {τ : Ω → WithTop ι} (hX : Martingale X 𝓕 P)
    (hRC : ∀ ω, IsRightContinuous (X · ω)) (hτ : IsStoppingTime 𝓕 τ) (hτ_ne : ∀ ω, τ ω ≠ ⊤) :
    Integrable (stoppedValue X τ) P :=
  integrable_condExp.congr (hX.stoppedValue_ae_eq_condExp_top hRC hτ hτ_ne).symm

-- Convergence of the convex combinations of the predictable parts on the dense set.
section PredictablePartLimConv

/-- Past the index at which `t` enters the meshes, `predictableConvexStep` at `t` is a.e. equal
to the process minus `martingaleConvexStep`. -/
lemma predictableConvexStep_ae_eq_sub_martingaleConvexStep {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι]
    [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) {t : ι} {k n : ℕ}
    (hk : denseEnum ι k = t) (hkn : k < n) :
    predictableConvexStep hd hs n t =ᵐ[P] S t - martingaleConvexStep hd hs n t :=
  weights_sum_predictableSeqStep_ae_eq hs (fun _ _ ↦ weight_apply_eq_zero_of_lt hd hs) hk hkn

/-- `L¹` norm convergence of `predictableConvexStep` for `t` in `denseSet ι`. -/
lemma predictableConvexStep_eLpNorm_tendsto {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) {t : ι} (ht : t ∈ denseSet ι) :
    Tendsto (fun n ↦ eLpNorm
      (predictableConvexStep hd hs n t - predictablePartLim hd hs t) 1 P) atTop (𝓝 0) :=
  (tendsto_eLpNorm_weights_sum_predictableSeqStep hs (integrable_martingaleLim hd hs)
    (fun _ _ ↦ weight_apply_eq_zero_of_lt hd hs)
    (tendsto_eLpNorm_weight_sum_martingaleSeqTop hd hs) ht).congr fun _ ↦
    eLpNorm_congr_ae (.sub .rfl (.sub .rfl (martingalePartLim_ae_eq hd hs t).symm))

/-- Almost sure convergence of `predictableConvexStep` to `predictablePartLim`, simultaneously at
all points of the countable dense set. This holds for the whole sequence since the weights were
chosen along a suitable subsequence in `exists_martingalPart_lim`. -/
lemma predictableConvexStep_ae_tendsto {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) :
    ∀ᵐ ω ∂P, ∀ t ∈ denseSet ι, Tendsto (fun n ↦ predictableConvexStep hd hs n t ω) atTop
      (𝓝 (predictablePartLim hd hs t ω)) := by
  have h_eq : ∀ᵐ ω ∂P, ∀ t ∈ denseSet ι,
      martingalePartLim hd hs t ω = P[martingaleLim hd hs | 𝓕 t] ω :=
    (ae_ball_iff (denseSet_countable ι)).2 fun t _ ↦ martingalePartLim_ae_eq hd hs t
  filter_upwards [ae_tendsto_weight_sum_predictableSeqStep hd hs, h_eq] with ω hω h_eq t ht
  rw [predictablePartLim, Pi.sub_apply, Pi.sub_apply, h_eq t ht]
  exact hω t ht

end PredictablePartLimConv

-- Helper lemmas about limits of monotone functions.
section MonotoneLim

/-- The limit of a collection of functions that is eventually monotone is monotone. -/
lemma monotone_of_eventually_monotone_of_tendsto {ι α β : Type*} [Preorder α] [TopologicalSpace β]
    [Preorder β] [OrderClosedTopology β] {l : Filter ι} [l.NeBot] {F : ι → α → β} {f : α → β}
    (hF : ∀ᶠ i in l, Monotone (F i)) (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Monotone f :=
  monotone_of_frequently_monotone_of_tendsto hF.frequently hlim

/-- The limit of a collection of functions that is eventually antitone is antitone. -/
lemma antitone_of_eventually_antitone_of_tendsto {ι α β : Type*} [Preorder α] [TopologicalSpace β]
    [Preorder β] [OrderClosedTopology β] {l : Filter ι} [l.NeBot] {F : ι → α → β} {f : α → β}
    (hF : ∀ᶠ i in l, Antitone (F i)) (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Antitone f :=
  monotone_of_eventually_monotone_of_tendsto (β := βᵒᵈ) hF hlim

/-- The limit of a collection of monotone functions is monotone. -/
lemma monotone_of_monotone_of_tendsto {ι α β : Type*} [Preorder α] [TopologicalSpace β]
    [Preorder β] [OrderClosedTopology β] {l : Filter ι} [l.NeBot] {F : ι → α → β} {f : α → β}
    (hF : ∀ i, Monotone (F i)) (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Monotone f :=
  monotone_of_eventually_monotone_of_tendsto (Eventually.of_forall hF) hlim

/-- The limit of a collection of antitone functions is antitone. -/
lemma antitone_of_antitone_of_tendsto {ι α β : Type*} [Preorder α] [TopologicalSpace β]
    [Preorder β] [OrderClosedTopology β] {l : Filter ι} [l.NeBot] {F : ι → α → β} {f : α → β}
    (hF : ∀ i, Antitone (F i)) (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Antitone f :=
  monotone_of_monotone_of_tendsto (β := βᵒᵈ) hF hlim

/-- If `D` is a dense set and `a` is not isolated from the right, then the comap of `𝓝[>] a`
under the inclusion `D → α` is nontrivial. -/
lemma Dense.comap_val_nhdsWithin_Ioi_neBot {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] {D : Set α} (hD : Dense D) {a : α} (ha : (𝓝[>] a).NeBot) :
    ((𝓝[>] a).comap ((↑) : D → α)).NeBot := by
  refine comap_neBot_iff.2 fun t ht => ?_
  obtain ⟨u, hu, hau, hut⟩ := mem_nhdsWithin.1 ht
  have hmem : u ∩ Set.Ioi a ∈ 𝓝[>] a :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (hu.mem_nhds hau)) self_mem_nhdsWithin
  obtain ⟨d, hd⟩ := hD.inter_open_nonempty (u ∩ Set.Ioi a) (hu.inter isOpen_Ioi)
    (ha.nonempty_of_mem hmem)
  exact ⟨⟨d, hd.2⟩, hut hd.1⟩

/-- This is the dual of `Dense.comap_val_nhdsWithin_Ioi_neBot`. -/
lemma Dense.comap_val_nhdsWithin_Iio_neBot {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] {D : Set α} (hD : Dense D) {a : α} (ha : (𝓝[<] a).NeBot) :
    ((𝓝[<] a).comap ((↑) : D → α)).NeBot := by
  refine comap_neBot_iff.2 fun t ht => ?_
  obtain ⟨u, hu, hau, hut⟩ := mem_nhdsWithin.1 ht
  have hmem : u ∩ Set.Iio a ∈ 𝓝[<] a :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (hu.mem_nhds hau)) self_mem_nhdsWithin
  obtain ⟨d, hd⟩ := hD.inter_open_nonempty (u ∩ Set.Iio a) (hu.inter isOpen_Iio)
    (ha.nonempty_of_mem hmem)
  exact ⟨⟨d, hd.2⟩, hut hd.1⟩

/-- If `f` is right continuous and is monotone on a dense set `D` which contains the points that
are isolated from the right, then `f` is monotone. The assumption on `D` is necessary since
right-continuity gives no information at the points that are isolated from the right, for example
at a top element. -/
lemma Dense.monotone_of_isRightContinuous {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [TopologicalSpace β] [Preorder β] [OrderClosedTopology β] {f : α → β}
    {D : Set α} (hD : Dense D) (hiso : ∀ t, 𝓝[>] t = ⊥ → t ∈ D)
    (hm : Monotone (f ∘ (↑) : D → β)) (hf : IsRightContinuous f) :
    Monotone f := by
  -- we first compare `f a` to the values of `f` at the points of `D` after `a`
  have key {a d : α} (hd : d ∈ D) (had : a < d) : f a ≤ f d := by
    by_cases ha : 𝓝[>] a = ⊥
    · exact hm (a := ⟨a, hiso a ha⟩) (b := ⟨d, hd⟩) had.le
    · have := hD.comap_val_nhdsWithin_Ioi_neBot ⟨ha⟩
      refine le_of_tendsto (Tendsto.comp (hf a) (tendsto_comap (f := ((↑) : D → α)))) ?_
      rw [eventually_comap]
      filter_upwards [Ioo_mem_nhdsGT had] with z hz x rfl
      exact hm (a := x) (b := ⟨d, hd⟩) hz.2.le
  refine monotone_iff_forall_lt.2 fun a b hab => ?_
  by_cases hb : 𝓝[>] b = ⊥
  · exact key (hiso b hb) hab
  · have := hD.comap_val_nhdsWithin_Ioi_neBot ⟨hb⟩
    refine ge_of_tendsto (Tendsto.comp (hf b) (tendsto_comap (f := ((↑) : D → α)))) ?_
    rw [eventually_comap]
    filter_upwards [self_mem_nhdsWithin] with z hz x rfl
    exact key x.2 (hab.trans hz)

/-- A helper lemma. -/
lemma Filter.IsCoboundedUnder.trans {ι α : Type*} {r : α → α → Prop} {l : Filter ι}
    [IsTrans α r] {u v : ι → α} (hle : ∀ᶠ i in l, r (u i) (v i)) (h : IsCoboundedUnder r l u) :
    IsCoboundedUnder r l v := by
  simp only [IsCoboundedUnder, IsCobounded, eventually_map] at *
  obtain ⟨b, hb⟩ := h
  refine ⟨b, fun a ha => hb a ?_⟩
  filter_upwards [ha, hle] with i hi huv using Trans.trans huv hi

/-- Convergence on a dense set of a collection of monotone function controls the `limsup` at a point
if `f` is right continuous at `a`. The dense set has to contain the points that are isolated from
the right, at which right-continuity gives no information. We prove this under the assumption that
`α` has a bottom element which belongs to the dense set, because otherwise `limsup` may have a junk
value which breaks the inequality. -/
lemma limsup_le_of_eventually_monotone_of_tendsto_on_dense {ι α β : Type*} [LinearOrder α]
    [OrderBot α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {l : Filter ι}
    [l.NeBot] {D : Set α} {F : ι → α → β} {f : α → β} (hF : ∀ᶠ i in l, Monotone (F i))
    (hD : Dense D) (hiso : ∀ t, 𝓝[>] t = ⊥ → t ∈ D) (hbot : ⊥ ∈ D) {a : α}
    (hfa : ContinuousWithinAt f (Set.Ioi a) a) (hlim : ∀ t ∈ D, Tendsto (F · t) l (𝓝 (f t))) :
    limsup (F · a) l ≤ f a := by
  by_cases ha : 𝓝[>] a = ⊥
  · rw [(hlim a (hiso a ha)).limsup_eq]
  · have : (comap ((↑) : D → α) (𝓝[>] a)).NeBot := hD.comap_val_nhdsWithin_Ioi_neBot ⟨ha⟩
    refine (isClosed_Ici (a := limsup (F · a) l)).mem_of_tendsto (Tendsto.comp hfa
      (tendsto_comap (f := ((↑) : D → α)))) ?_
    rw [eventually_comap, eventually_nhdsWithin_iff]
    filter_upwards with z hz d rfl
    simp only [Function.comp_apply, Set.mem_Ici, ← (hlim d d.2).limsup_eq]
    refine limsup_le_limsup ?_ ?_ (hlim d d.2).isBoundedUnder_le
    · filter_upwards [hF] with i hi using hi hz.le
    · refine (hlim ⊥ hbot).isCoboundedUnder_le.trans ?_
      filter_upwards [hF] with i hi using hi bot_le

/-- This is the dual of `limsup_le_of_eventually_monotone_of_tendsto_on_dense`. -/
lemma le_liminf_of_eventually_monotone_of_tendsto_on_dense {ι α β : Type*} [LinearOrder α]
    [OrderTop α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {l : Filter ι}
    [l.NeBot] {D : Set α} {F : ι → α → β} {f : α → β} (hF : ∀ᶠ i in l, Monotone (F i))
    (hD : Dense D) (hiso : ∀ t, 𝓝[<] t = ⊥ → t ∈ D) (htop : ⊤ ∈ D) {a : α}
    (hfa : ContinuousWithinAt f (Set.Iio a) a) (hlim : ∀ t ∈ D, Tendsto (F · t) l (𝓝 (f t))) :
    f a ≤ liminf (F · a) l := by
  by_cases ha : 𝓝[<] a = ⊥
  · rw [(hlim a (hiso a ha)).liminf_eq]
  · have : (comap ((↑) : D → α) (𝓝[<] a)).NeBot := hD.comap_val_nhdsWithin_Iio_neBot ⟨ha⟩
    refine (isClosed_Iic (a := liminf (F · a) l)).mem_of_tendsto (Tendsto.comp hfa
      (tendsto_comap (f := ((↑) : D → α)))) ?_
    rw [eventually_comap, eventually_nhdsWithin_iff]
    filter_upwards with z hz d rfl
    simp only [Function.comp_apply, Set.mem_Iic, ← (hlim d d.2).liminf_eq]
    refine liminf_le_liminf ?_ (hlim d d.2).isBoundedUnder_ge ?_
    · filter_upwards [hF] with i hi using hi hz.le
    · refine (hlim ⊤ htop).isCoboundedUnder_ge.trans ?_
      filter_upwards [hF] with i hi using hi le_top

/-- We combine `limsup_le_of_eventually_monotone_of_tendsto_on_dense` and
`le_liminf_of_eventually_monotone_of_tendsto_on_dense` to prove that `F · a` converges to `f a`
if `f` is continuous at `a`. -/
lemma tendsto_of_eventually_monotone_of_tendsto_on_dense {ι α β : Type*} [LinearOrder α]
    [BoundedOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {l : Filter ι}
    [l.NeBot] {D : Set α} {F : ι → α → β} {f : α → β} (hF : ∀ᶠ i in l, Monotone (F i))
    (hD : Dense D) (hiso_right : ∀ t, 𝓝[>] t = ⊥ → t ∈ D) (hiso_left : ∀ t, 𝓝[<] t = ⊥ → t ∈ D)
    (htop : ⊤ ∈ D) (hbot : ⊥ ∈ D) (a : α) (hfa : ContinuousAt f a)
    (hlim : ∀ t ∈ D, Tendsto (F · t) l (𝓝 (f t))) :
    Tendsto (F · a) l (𝓝 (f a)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ ?_ ?_
  · exact le_liminf_of_eventually_monotone_of_tendsto_on_dense hF hD hiso_left htop
      hfa.continuousWithinAt hlim
  · exact limsup_le_of_eventually_monotone_of_tendsto_on_dense hF hD hiso_right hbot
      hfa.continuousWithinAt hlim
  · -- create an analogue of `Filter.IsCoboundedUnder.trans` for `IsBoundedUnder` to replace
    -- `isBoundedUnder_le.mono_le`
    refine (hlim ⊤ htop).isBoundedUnder_le.mono_le ?_
    filter_upwards [hF] with i hi using hi le_top
  · refine (hlim ⊥ hbot).isBoundedUnder_ge.mono_ge ?_
    filter_upwards [hF] with i hi using hi bot_le

/-- A variant of `le_liminf_of_eventually_monotone_of_tendsto_on_dense` in which `f` is only assumed
to have a left limit at `a`: that left limit is at most the `liminf` of `F · a`. At a point `a`
which is isolated from the left, `f.leftLim a = f a` and the inequality follows from the convergence
at `a`, which belongs to `D`. -/
lemma leftLim_le_liminf_of_eventually_monotone_of_tendsto_on_dense {ι α β : Type*} [LinearOrder α]
    [OrderTop α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {l : Filter ι}
    [l.NeBot] {D : Set α} {F : ι → α → β} {f : α → β} (hF : ∀ᶠ i in l, Monotone (F i))
    (hD : Dense D) (hiso : ∀ t, 𝓝[<] t = ⊥ → t ∈ D) (htop : ⊤ ∈ D) {a : α}
    (hfa : ∃ c, Tendsto f (𝓝[<] a) (𝓝 c)) (hlim : ∀ t ∈ D, Tendsto (F · t) l (𝓝 (f t))) :
    f.leftLim a ≤ liminf (F · a) l := by
  by_cases ha : 𝓝[<] a = ⊥
  · rw [(hlim a (hiso a ha)).liminf_eq, leftLim_eq_of_eq_bot f ha]
  · have : (comap ((↑) : D → α) (𝓝[<] a)).NeBot := hD.comap_val_nhdsWithin_Iio_neBot ⟨ha⟩
    refine (isClosed_Iic (a := liminf (F · a) l)).mem_of_tendsto
      (Tendsto.comp (tendsto_leftLim_of_tendsto hfa) (tendsto_comap (f := ((↑) : D → α)))) ?_
    rw [eventually_comap, eventually_nhdsWithin_iff]
    filter_upwards with z hz d rfl
    simp only [Function.comp_apply, Set.mem_Iic, ← (hlim d d.2).liminf_eq]
    refine liminf_le_liminf ?_ (hlim d d.2).isBoundedUnder_ge ?_
    · filter_upwards [hF] with i hi using hi hz.le
    · refine (hlim ⊤ htop).isCoboundedUnder_ge.trans ?_
      filter_upwards [hF] with i hi using hi le_top

end MonotoneLim

section PredictablePartLimMono

lemma predictableSeqStep_eq_sum_indicator {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (n : ℕ) (ω : Ω) (t : ι) :
    predictableSeqStep P S 𝓕 n t ω = ∑ v : mesh ι n, (meshPredIoc n v).indicator
      (fun _ : ι ↦ predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P v ω) t := by
  simp only [predictableSeqStep, Finset.sum_apply]
  exact Finset.sum_congr rfl fun v _ ↦ Set.indicator_apply_apply _ _ t ω

/-- On the mesh cell `Ioc (pred u) u` containing `t`, the step process `predictableSeqStep` is
constant, equal to the discrete predictable part at the cell's right endpoint `u`. -/
lemma predictableSeqStep_apply {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (n : ℕ) (ω : Ω) {t : ι} {u : mesh ι n}
    (ht : t ∈ meshPredIoc n u) :
    predictableSeqStep P S 𝓕 n t ω
      = predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P u ω := by
  rw [predictableSeqStep_eq_sum_indicator,
    Finset.sum_eq_single_of_mem u (Finset.mem_univ _) ?_, Set.indicator_of_mem ht]
  refine fun v _ hvu => Set.indicator_of_notMem (fun hv => hvu ?_) _
  rcases lt_trichotomy v u with h' | h' | h'
  · exact absurd (lt_of_le_of_lt hv.2 (lt_of_le_of_lt
      (Subtype.coe_le_coe.2 (Order.le_pred_of_lt h')) ht.1)) (lt_irrefl t)
  · exact h'
  · exact absurd (lt_of_le_of_lt ht.2 (lt_of_le_of_lt
      (Subtype.coe_le_coe.2 (Order.le_pred_of_lt h')) hv.1)) (lt_irrefl t)

lemma predictableSeqStep_monotone_ae {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hs : Submartingale S 𝓕 P) (n : ℕ) :
    ∀ᵐ ω ∂P, Monotone fun t ↦ predictableSeqStep P S 𝓕 n t ω := by
  have hsub : Submartingale (S ∘ Subtype.val) (meshFiltration 𝓕 n) P :=
    hs.indexComap (Subtype.mono_coe (· ∈ (mesh ι n)))
  have hne (s : ι) : (Finset.univ.filter fun u : mesh ι n ↦ s ≤ (u : ι)).Nonempty := ⟨⊤, by simp⟩
  set ceil : ι → mesh ι n :=
    fun s ↦ (Finset.univ.filter fun u : mesh ι n ↦ s ≤ (u : ι)).min' (hne s)
  have hmem (s : ι) : s ≤ (ceil s : ι) := (Finset.mem_filter.1 (Finset.min'_mem _ (hne s))).2
  have hle (s : ι) (u : mesh ι n) (hu : s ≤ (u : ι)) : ceil s ≤ u :=
    Finset.min'_le _ u (Finset.mem_filter.2 ⟨Finset.mem_univ u, hu⟩)
  filter_upwards [hsub.monotone_predictablePart_ae] with ω hmono
  have hval : ∀ s : ι, predictableSeqStep P S 𝓕 n s ω
      = predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P (ceil s) ω := by
    intro s
    rcases eq_or_ne s ⊥ with rfl | hs0
    · have hceil : ceil ⊥ = ⊥ := le_antisymm (hle ⊥ ⊥ (by simp)) bot_le
      rw [hceil, predictablePart_bot, Pi.zero_apply, predictableSeqStep_eq_sum_indicator]
      refine Finset.sum_eq_zero fun u _ ↦ ?_
      apply Set.indicator_of_notMem fun h ↦ absurd h.1 (not_lt.2 bot_le)
    · refine predictableSeqStep_apply P S 𝓕 n ω (Set.mem_Ioc.2 ⟨?_, hmem s⟩)
      have hcne : ceil s ≠ ⊥ := by
        intro hc
        have h := hmem s
        rw [hc, bot_eq_bot] at h
        exact hs0 (le_bot_iff.1 h)
      exact not_le.1 fun hcon ↦ absurd (hle s _ hcon) (not_le.2
        (Order.pred_lt_of_not_isMin fun hmin ↦ hcne (le_bot_iff.1 (hmin bot_le))))
  intro s₁ s₂ hs12
  simp only [hval s₁, hval s₂]
  exact hmono (hle s₁ (ceil s₂) (hs12.trans (hmem s₂)))

lemma predictableConvexStep_monotone_ae {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) :
    ∀ᵐ ω ∂P, Monotone fun t ↦ predictableConvexStep hd hs n t ω := by
  have key : ∀ᵐ ω ∂P, ∀ m : ℕ, Monotone fun s ↦ predictableSeqStep P S 𝓕 m s ω :=
    ae_all_iff.2 fun m ↦ predictableSeqStep_monotone_ae hs m
  filter_upwards [key] with ω hω
  simp only [predictableConvexStep, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
  exact Monotone.finset_sum fun m _ ↦
    (hω m).const_smul_of_nonneg ((weight hd hs n).weights_nonneg m)

/-- If `f i ≤ g i` almost everywhere for all `i`, `f` tends to `f'` in measure and `g` tends to
`g'` in measure, then `f' ≤ g'` almost everywhere. -/
lemma MeasureTheory.TendstoInMeasure.ae_le {α ι E : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [PseudoEMetricSpace E] [Preorder E] [OrderClosedTopology E] {u : Filter ι}
    [u.NeBot] [u.IsCountablyGenerated] {f g : ι → α → E} {f' g' : α → E}
    (hf : TendstoInMeasure μ f u f') (hg : TendstoInMeasure μ g u g')
    (hfg : ∀ i, f i ≤ᵐ[μ] g i) :
    f' ≤ᵐ[μ] g' := by
  obtain ⟨ns, hns, hf_ae⟩ := hf.exists_seq_tendsto_ae'
  obtain ⟨φ, hφ, hg_ae⟩ := (hg.comp hns).exists_seq_tendsto_ae
  filter_upwards [hf_ae, hg_ae, ae_all_iff.2 fun n ↦ hfg (ns (φ n))] with x hfx hgx hle
  exact le_of_tendsto_of_tendsto' (hfx.comp hφ.tendsto_atTop) hgx hle

/-- The predictable part `A` is almost surely monotone on the countable dense set. -/
lemma predictablePartLim_monotoneOn_denseSet_ae {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) :
    ∀ᵐ ω ∂P, MonotoneOn (fun t ↦ predictablePartLim hd hs t ω) (denseSet ι) := by
  have hlim {t : ι} (ht : t ∈ denseSet ι) :
      TendstoInMeasure P (fun n ↦ predictableConvexStep hd hs n t) atTop
        (predictablePartLim hd hs t) :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun n ↦ ((stronglyAdapted_predictableConvexStep hd hs n t).mono
        (𝓕.le t)).aestronglyMeasurable)
      (integrable_predictablePartLim hd hs t).aestronglyMeasurable
      (predictableConvexStep_eLpNorm_tendsto hd hs ht)
  have hle : ∀ᵐ ω ∂P, ∀ s ∈ denseSet ι, ∀ t ∈ denseSet ι, s ≤ t →
      predictablePartLim hd hs s ω ≤ predictablePartLim hd hs t ω := by
    simp_rw [ae_ball_iff (denseSet_countable ι), eventually_imp_distrib_left]
    intro s hs_mem t ht_mem hst
    refine (hlim hs_mem).ae_le (hlim ht_mem) fun n ↦ ?_
    filter_upwards [predictableConvexStep_monotone_ae hd hs n] with ω hω using hω hst
  filter_upwards [hle] with ω hω s hs_mem t ht_mem hst using hω s hs_mem t ht_mem hst

/-- If the paths of `S` are almost surely càdlàg, then the predictable part `A` is almost surely
monotone: it is monotone on the countable dense set and right-continuous. -/
lemma predictablePartLim_monotone_ae {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    ∀ᵐ ω ∂P, Monotone fun t ↦ predictablePartLim hd hs t ω := by
  filter_upwards [predictablePartLim_monotoneOn_denseSet_ae hd hs,
    isRightContinuous_predictablePartLim_ae hd hs hc] with ω hmono hrcω
  exact (denseSet_dense ι).monotone_of_isRightContinuous (fun _ ↦ mem_denseSet_of_nhdsGT_eq_bot)
    (fun s t hst ↦ hmono s.2 t.2 hst) hrcω

end PredictablePartLimMono

section PredictableConvexStepPredictable

/-- The mesh step-extension of the discrete predictable part is strongly predictable: it is a
finite sum of processes of the form `1_{(pred u, u]} Aⁿ_u`, where `Aⁿ_u` is measurable with respect
to the σ-algebra at time `pred u`. -/
lemma isStronglyPredictable_predictableSeqStep {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (n : ℕ) :
    IsStronglyPredictable 𝓕 (predictableSeqStep P S 𝓕 n) := by
  let A := predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P
  -- we write the indicator of `(pred u, u]` as a difference of indicators of `(pred u, ∞)` and
  -- `(u, ∞)`
  have h_eq : Function.uncurry (predictableSeqStep P S 𝓕 n) = fun p : ι × Ω ↦
      ∑ u : mesh ι n, ((Set.Ioi ((pred u : mesh ι n) : ι) ×ˢ Set.univ).indicator
          (fun q : ι × Ω ↦ A u q.2) p
        - (Set.Ioi (u : ι) ×ˢ Set.univ).indicator (fun q : ι × Ω ↦ A u q.2) p) := by
    ext ⟨t, ω⟩
    simp only [Function.uncurry_apply_pair, predictableSeqStep_eq_sum_indicator, meshPredIoc]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    have hpu : ((pred u : mesh ι n) : ι) ≤ u := Subtype.coe_le_coe.2 (pred_le u)
    by_cases h1 : ((pred u : mesh ι n) : ι) < t <;> by_cases h2 : (u : ι) < t
    · simp [h1, h2, not_le.2 h2, A]
    · simp [h1, h2, not_lt.1 h2, A]
    · exact absurd (hpu.trans_lt h2) h1
    · simp [h1, h2]
  rw [IsStronglyPredictable, h_eq]
  refine Finset.stronglyMeasurable_fun_sum _ fun u _ ↦ StronglyMeasurable.sub ?_ ?_
  · exact stronglyMeasurable_predictable_indicator_Ioi
      (stronglyMeasurable_pred_predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P u)
  · exact stronglyMeasurable_predictable_indicator_Ioi
      (stronglyMeasurable_predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P u)

/-- The convexly averaged mesh step-extension of the predictable parts is strongly predictable. -/
lemma isStronglyPredictable_predictableConvexStep {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) (n : ℕ) :
    IsStronglyPredictable 𝓕 (predictableConvexStep hd hs n) := by
  have h_eq : Function.uncurry (predictableConvexStep hd hs n) = fun p : ι × Ω ↦
      ∑ m ∈ (weight hd hs n).weights.support,
        (weight hd hs n).weights m • Function.uncurry (predictableSeqStep P S 𝓕 m) p := by
    ext ⟨t, ω⟩
    simp [predictableConvexStep, Finsupp.sum, Finset.sum_apply]
  rw [IsStronglyPredictable, h_eq]
  exact Finset.stronglyMeasurable_fun_sum _ fun m _ ↦
    (isStronglyPredictable_predictableSeqStep P S 𝓕 m).const_smul _

end PredictableConvexStepPredictable

section PredictablePartIsStronglyPredictable

/-- The pointwise limsup of strongly predictable processes is strongly predictable. -/
lemma IsStronglyPredictable.limsup {ι Ω E : Type*} [Preorder ι] [OrderBot ι]
    {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [ConditionallyCompleteLinearOrder E]
    [OrderTopology E] [SecondCountableTopology E] {X : ℕ → ι → Ω → E}
    (hX : ∀ n, IsStronglyPredictable 𝓕 (X n)) :
    IsStronglyPredictable 𝓕 (fun t ω ↦ limsup (fun n ↦ X n t ω) atTop) := by
  rw [IsStronglyPredictable, stronglyMeasurable_iff_measurable]
  exact Measurable.limsup fun n => stronglyMeasurable_iff_measurable.1 (hX n)

/-- The limsup of convexly averaged mesh step-extension of the predictable parts is strongly
predictable. -/
lemma isStronglyPredictable_limsup_predictableConvexStep {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι]
    [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) :
    IsStronglyPredictable 𝓕 (fun t ω => limsup (predictableConvexStep hd hs · t ω) atTop) :=
  IsStronglyPredictable.limsup fun n => isStronglyPredictable_predictableConvexStep hd hs n

/-- For each random time `τ`, almost everywhere,
`limsup (fun n => stoppedValue 𝒜^n τ ω) atTop ≤ stoppedValue A τ ω`. -/
lemma limsup_stoppedValue_predictableConvexStep_ae_le_stoppedValue_predictablePartLim {ι Ω : Type*}
    [TopologicalSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι]
    [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous]
    (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) (τ : Ω → WithTop ι) (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    (fun ω ↦ limsup (fun n ↦ stoppedValue (predictableConvexStep hd hs n) τ ω) atTop) ≤ᵐ[P]
      stoppedValue (predictablePartLim hd hs) τ := by
  filter_upwards [predictableConvexStep_ae_tendsto hd hs,
    isRightContinuous_predictablePartLim_ae hd hs hc,
    ae_all_iff.2 (predictableConvexStep_monotone_ae hd hs)] with ω hconvω hrcω hmonoω
  exact limsup_le_of_eventually_monotone_of_tendsto_on_dense (.of_forall hmonoω)
    (denseSet_dense ι) (fun _ ↦ mem_denseSet_of_nhdsGT_eq_bot) (bot_mem_denseSet ι) (hrcω _) hconvω

/-- For each finite stopping time `τ`, `∫ ω, stoppedValue 𝒜^n τ ω ∂P` converges to
`∫ ω, stoppedValue A τ ω ∂P`. -/
lemma integral_stoppedValue_predictableConvexStep_tendsto_stoppedValue_predictablePartLim
    {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous] [𝓕.IsComplete P] (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ)
    (hτ_ne : ∀ ω, τ ω ≠ ⊤) (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    Tendsto (fun n ↦ ∫ ω, stoppedValue (predictableConvexStep hd hs n) τ ω ∂P) atTop
      (𝓝 <| ∫ ω, stoppedValue (predictablePartLim hd hs) τ ω ∂P) := by
  have hint (m : ℕ) : Integrable (stoppedValue (predictableSeqStep P S 𝓕 m) τ) P := by
    have hσ : IsStoppingTime 𝓕 (meshCeil m τ) := isStoppingTime_meshCeil hτ m
    have hσ_ne (ω) : meshCeil m τ ω ≠ ⊤ := meshCeil_ne_top m (hτ_ne ω)
    have hS : Integrable (stoppedValue S (meshCeil m τ)) P :=
      memLp_one_iff_integrable.1 (hd.uniformIntegrable.memLp ⟨_, hσ, hσ_ne⟩)
    have hN : Integrable (stoppedValue (martingaleSeqStep P S 𝓕 m) (meshCeil m τ)) P :=
      (martingale_condExp _ _ _).integrable_stoppedValue_of_countable_range _ hσ
        (fun ω ↦ WithTop.le_coe_top (hσ_ne ω)) (countable_range_meshCeil m τ)
    rw [stoppedValue_predictableSeqStep_meshCeil hτ_ne]
    exact (integrable_congr (stoppedValue_predictableSeqStep_ae_eq hs.stronglyAdapted
      hs.integrable hτ_ne).symm).1 (hS.sub hN)
  have h1 (n : ℕ) : ∫ ω, stoppedValue (predictableConvexStep hd hs n) τ ω ∂P
      = ((weight hd hs n).weights.sum
          fun m r ↦ r • ∫ ω, stoppedValue S (meshCeil m τ) ω ∂P) - ∫ ω, S ⊥ ω ∂P := by
    have hstop : stoppedValue (predictableConvexStep hd hs n) τ
        = ∑ m ∈ (weight hd hs n).weights.support,
            (weight hd hs n).weights m • stoppedValue (predictableSeqStep P S 𝓕 m) τ := by
      funext ω
      simp [predictableConvexStep, stoppedValue, Finsupp.sum, Finset.sum_apply]
    rw [hstop]
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ fun m _ ↦ (hint m).smul _]
    simp_rw [Pi.smul_apply, integral_smul,
      integral_stoppedValue_predictableSeqStep hd hs.stronglyAdapted hs.integrable hτ hτ_ne,
      smul_sub]
    have htotal : ∑ m ∈ (weight hd hs n).weights.support, (weight hd hs n).weights m = 1 := by
      simpa [Finsupp.sum] using (weight hd hs n).total
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, htotal, one_smul, Finsupp.sum]
  have hMPL : Martingale (martingalePartLim hd hs) 𝓕 P := martingale_martingalePartLim hd hs
  have hRC (ω : Ω) : IsRightContinuous (martingalePartLim hd hs · ω) :=
    (isCadlag_martingalePartLim hd hs ω).right_continuous
  have h2 : ∫ ω, stoppedValue (predictablePartLim hd hs) τ ω ∂P
      = ∫ ω, stoppedValue S τ ω ∂P - ∫ ω, S ⊥ ω ∂P := by
    have hint_S : Integrable (stoppedValue S τ) P :=
      memLp_one_iff_integrable.1 (hd.uniformIntegrable.memLp ⟨τ, hτ, hτ_ne⟩)
    have hint_M : Integrable (stoppedValue (martingalePartLim hd hs) τ) P :=
      hMPL.integrable_stoppedValue_top hRC hτ hτ_ne
    rw [predictablePartLim, stoppedValue.sub]
    simp only [Pi.sub_apply]
    rw [integral_sub hint_S hint_M,
      integral_congr_ae (hMPL.stoppedValue_ae_eq_condExp_top hRC hτ hτ_ne), integral_condExp _,
      integral_martingalePartLim hd hs]
  simp_rw [h1, h2]
  exact (tendsto_weights_sum_of_forall_lt_eq_zero
    (tendsto_integral_stoppedValue_meshCeil hd hτ hτ_ne hc)
    fun n m hmn ↦ weight_apply_eq_zero_of_lt hd hs hmn).sub_const _

private theorem limsup_lintegral_le_nat' {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {f : ℕ → Ω → ℝ≥0∞} (g : Ω → ℝ≥0∞) (hf_meas : ∀ n, AEMeasurable (f n) P)
    (h_bound : ∀ n, f n ≤ᵐ[P] g) (h_fin : ∫⁻ ω, g ω ∂P ≠ ∞) :
    limsup (fun n ↦ ∫⁻ ω, f n ω ∂P) atTop ≤ ∫⁻ ω, limsup (fun n ↦ f n ω) atTop ∂P :=
  calc
    limsup (fun n ↦ ∫⁻ ω, f n ω ∂P) atTop = ⨅ n : ℕ, ⨆ i ≥ n, ∫⁻ ω, f i ω ∂P :=
      limsup_eq_iInf_iSup_of_nat
    _ ≤ ⨅ n : ℕ, ∫⁻ ω, ⨆ i ≥ n, f i ω ∂P := iInf_mono fun _ ↦ iSup₂_lintegral_le _
    _ = ∫⁻ ω, ⨅ n : ℕ, ⨆ i ≥ n, f i ω ∂P := by
      refine (lintegral_iInf' ?_ ?_ ?_).symm
      · exact fun n ↦ .biSup _ (Set.to_countable _) fun i _ ↦ hf_meas i
      · exact .of_forall fun ω n m hnm ↦ iSup_le_iSup_of_subset fun i hi ↦ le_trans hnm hi
      · refine ne_top_of_le_ne_top h_fin (lintegral_mono_ae ?_)
        exact (ae_all_iff.2 h_bound).mono fun ω hω ↦ iSup_le fun i ↦ iSup_le fun _ ↦ hω i
    _ = ∫⁻ ω, limsup (fun n ↦ f n ω) atTop ∂P := by simp only [limsup_eq_iInf_iSup_of_nat]

/-- Reverse Fatou's lemma for the lower Lebesgue integral along a countably generated filter,
`AEMeasurable` version. -/
theorem limsup_lintegral_le' {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ι : Type*}
    {L : Filter ι} [L.IsCountablyGenerated] {f : ι → Ω → ℝ≥0∞} (g : Ω → ℝ≥0∞)
    (hf_meas : ∀ i, AEMeasurable (f i) P) (h_bound : ∀ i, f i ≤ᵐ[P] g)
    (h_fin : ∫⁻ ω, g ω ∂P ≠ ∞) :
    limsup (fun i ↦ ∫⁻ ω, f i ω ∂P) L ≤ ∫⁻ ω, limsup (fun i ↦ f i ω) L ∂P := by
  by_cases! hL : ¬ L.NeBot
  · simp_all
  · obtain ⟨x, hx⟩ := exists_seq_tendsto_limsup (u := fun i ↦ ∫⁻ ω, f i ω ∂P) (f := L)
    calc limsup (fun i ↦ ∫⁻ ω, f i ω ∂P) L = limsup (fun n ↦ ∫⁻ ω, f (x n) ω ∂P) atTop :=
          hx.1.limsup_eq.symm
      _ ≤ ∫⁻ ω, limsup (fun n ↦ f (x n) ω) atTop ∂P :=
          limsup_lintegral_le_nat' g (fun n ↦ hf_meas (x n)) (fun n ↦ h_bound (x n)) h_fin
      _ ≤ ∫⁻ ω, limsup (fun i ↦ f i ω) L ∂P := lintegral_mono fun ω ↦
          hx.2.limsup_comp_le_limsup (u := fun i ↦ f i ω) isCobounded_le_of_bot isBounded_le_of_top

private lemma aemeasurable_limsup {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {ι : Type*} [Countable ι] {L : Filter ι} [L.IsCountablyGenerated] {X : ι → Ω → ℝ}
    (hX_meas : ∀ i, AEMeasurable (X i) P) :
    AEMeasurable (fun ω ↦ limsup (fun i ↦ X i ω) L) P := by
  obtain ⟨b, hb⟩ := L.exists_antitone_basis
  exact ⟨_, Measurable.limsup' (fun i ↦ (hX_meas i).measurable_mk)
      ⟨hb.toHasBasis, Set.countable_univ⟩ fun n ↦ (b n).to_countable,
    (ae_all_iff.2 fun i ↦ (hX_meas i).ae_eq_mk).mono fun ω hω ↦
      congrArg (limsup · L) (funext hω)⟩

private lemma limsup_integral_le_integral_limsup_of_le' {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ι : Type*} [Countable ι] {L : Filter ι} [L.NeBot]
    [L.IsCountablyGenerated] {X : ι → Ω → ℝ} {Y : Ω → ℝ}
    (hX_meas : ∀ i, AEMeasurable (X i) P) (hX_nonneg : ∀ i, 0 ≤ᵐ[P] X i) (hY : Integrable Y P)
    (hXY : ∀ i, X i ≤ᵐ[P] Y) :
    limsup (fun i ↦ ∫ ω, X i ω ∂P) L ≤ ∫ ω, limsup (fun i ↦ X i ω) L ∂P := by
  have hint : ∀ {f : Ω → ℝ}, AEMeasurable f P → 0 ≤ᵐ[P] f → f ≤ᵐ[P] Y → Integrable f P :=
    fun hf h0 h1 ↦ hY.mono' hf.aestronglyMeasurable <|
      (h0.and h1).mono fun ω ⟨ha, hb⟩ ↦ by rwa [Real.norm_eq_abs, abs_of_nonneg ha]
  have hXi : ∀ i, Integrable (X i) P := fun i ↦ hint (hX_meas i) (hX_nonneg i) (hXY i)
  have ⟨i₀⟩ := L.nonempty_of_neBot
  have hY_nonneg : 0 ≤ᵐ[P] Y := (hX_nonneg i₀).trans (hXY i₀)
  have hae : ∀ᵐ ω ∂P, IsBoundedUnder (· ≤ ·) L (fun i ↦ X i ω) ∧
      IsCoboundedUnder (· ≤ ·) L (fun i ↦ X i ω) := by
    filter_upwards [ae_all_iff.2 hXY, ae_all_iff.2 hX_nonneg] with ω hub hlb
    exact ⟨isBoundedUnder_of ⟨Y ω, hub⟩, isCoboundedUnder_le_of_le L hlb⟩
  have hL_nonneg : 0 ≤ᵐ[P] fun ω ↦ limsup (fun i ↦ X i ω) L := by
    filter_upwards [ae_all_iff.2 hX_nonneg, hae] with ω hlb hbdd
    refine le_limsup_of_le hbdd.1 fun b hb ↦ ?_
    obtain ⟨i, hi⟩ := (hb.and (Eventually.of_forall hlb)).exists
    exact hi.2.trans hi.1
  have hLi : Integrable (fun ω ↦ limsup (fun i ↦ X i ω) L) P :=
    hint (aemeasurable_limsup hX_meas) hL_nonneg <| by
      filter_upwards [ae_all_iff.2 hXY, hae] with ω hub hbdd
      exact limsup_le_of_le hbdd.2 (Eventually.of_forall hub)
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hL_nonneg),
    ofReal_integral_eq_lintegral_ofReal hLi hL_nonneg,
    ENNReal.ofReal_limsup
      (isCoboundedUnder_le_of_le L fun i ↦ integral_nonneg_of_ae (hX_nonneg i))
      (isBoundedUnder_of ⟨∫ ω, Y ω ∂P, fun i ↦ integral_mono_ae (hXi i) hY (hXY i)⟩)]
  simp_rw [ofReal_integral_eq_lintegral_ofReal (hXi _) (hX_nonneg _)]
  refine (limsup_lintegral_le' _ (fun i ↦ (hX_meas i).ennreal_ofReal)
      (fun i ↦ (hXY i).mono fun ω h ↦ ENNReal.ofReal_le_ofReal h)
      (by rw [← ofReal_integral_eq_lintegral_ofReal hY hY_nonneg]
          exact ENNReal.ofReal_ne_top)).trans
    (le_of_eq (lintegral_congr_ae
      (hae.mono fun ω hbdd ↦ (ENNReal.ofReal_limsup hbdd.2 hbdd.1).symm)))

private lemma limsup_integral_le_integral_limsup_of_le_of_le' {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ι : Type*} [Countable ι] {L : Filter ι} [L.NeBot]
    [L.IsCountablyGenerated] {X : ι → Ω → ℝ} {W Y : Ω → ℝ}
    (hX_meas : ∀ i, AEMeasurable (X i) P) (hW : Integrable W P) (hY : Integrable Y P)
    (hWX : ∀ i, W ≤ᵐ[P] X i) (hXY : ∀ i, X i ≤ᵐ[P] Y) :
    limsup (fun i ↦ ∫ ω, X i ω ∂P) L ≤ ∫ ω, limsup (fun i ↦ X i ω) L ∂P := by
  have hXi : ∀ i, Integrable (X i) P := fun i ↦
    integrable_of_le_of_le (hX_meas i).aestronglyMeasurable (hWX i) (hXY i) hW hY
  have hae : ∀ᵐ ω ∂P, IsBoundedUnder (· ≤ ·) L (fun i ↦ X i ω) ∧
      IsCoboundedUnder (· ≤ ·) L (fun i ↦ X i ω) := by
    filter_upwards [ae_all_iff.2 hXY, ae_all_iff.2 hWX] with ω hub hlb
    exact ⟨isBoundedUnder_of ⟨Y ω, hub⟩, isCoboundedUnder_le_of_le L hlb⟩
  have hZ : limsup (fun i ↦ ∫ ω, X i ω - W ω ∂P) L
      ≤ ∫ ω, limsup (fun i ↦ X i ω - W ω) L ∂P :=
    limsup_integral_le_integral_limsup_of_le' (fun i ↦ (hX_meas i).sub hW.aemeasurable)
      (fun i ↦ (hWX i).mono fun ω h ↦ sub_nonneg.2 h) (hY.sub hW)
      (fun i ↦ (hXY i).mono fun ω h ↦ by simpa using sub_le_sub_right h (W ω))
  have hLW : ∀ᵐ ω ∂P, limsup (fun i ↦ X i ω - W ω) L = limsup (fun i ↦ X i ω) L - W ω := by
    filter_upwards [hae] with ω hbdd
    simpa [sub_eq_add_neg] using limsup_add_const L (fun i ↦ X i ω) (-W ω) hbdd.1 hbdd.2
  have hL_int : Integrable (fun ω ↦ limsup (fun i ↦ X i ω) L) P := by
    refine integrable_of_le_of_le (aemeasurable_limsup hX_meas).aestronglyMeasurable ?_ ?_ hW hY
    · filter_upwards [ae_all_iff.2 hWX, hae] with ω hlb hbdd
      refine le_limsup_of_le hbdd.1 fun b hb ↦ ?_
      obtain ⟨i, hi⟩ := (hb.and (Eventually.of_forall hlb)).exists
      exact hi.2.trans hi.1
    · filter_upwards [ae_all_iff.2 hXY, hae] with ω hub hbdd
      exact limsup_le_of_le hbdd.2 (Eventually.of_forall hub)
  have h_bdd : IsBoundedUnder (· ≤ ·) L (fun i ↦ ∫ ω, X i ω ∂P) :=
    isBoundedUnder_of ⟨∫ ω, Y ω ∂P, fun i ↦ integral_mono_ae (hXi i) hY (hXY i)⟩
  have h_cobdd : IsCoboundedUnder (· ≤ ·) L (fun i ↦ ∫ ω, X i ω ∂P) :=
    isCoboundedUnder_le_of_le L fun i ↦ integral_mono_ae hW (hXi i) (hWX i)
  have hZ_eq : (fun i ↦ ∫ ω, X i ω - W ω ∂P) = fun i ↦ (∫ ω, X i ω ∂P) + -∫ ω, W ω ∂P := by
    funext i
    rw [integral_sub (hXi i) hW, sub_eq_add_neg]
  rw [hZ_eq, limsup_add_const L _ (-∫ ω, W ω ∂P) h_bdd h_cobdd, integral_congr_ae hLW,
    integral_sub hL_int hW, sub_eq_add_neg] at hZ
  exact le_of_add_le_add_right hZ

/-- Reverse Fatou's lemma along a countably generated filter for a family uniformly bounded
below by an integrable function `W`. -/
theorem limsup_integral_le_integral_limsup_of_le_of_tendsto_integral_posPart_sub {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ι : Type*} [Countable ι] {L : Filter ι} [L.NeBot]
    [L.IsCountablyGenerated] {X : ι → Ω → ℝ} {W Y : Ω → ℝ}
    (hX_int : ∀ i, Integrable (X i) P) (hW : Integrable W P) (hWX : ∀ i, W ≤ᵐ[P] X i)
    (hY : Integrable Y P)
    (hX_bdd : ∀ᵐ ω ∂P, IsBoundedUnder (· ≤ ·) L fun i ↦ X i ω)
    (h_tendsto : Tendsto (fun i ↦ ∫ ω, max (X i ω - Y ω) 0 ∂P) L (𝓝 0))
    (hL_int : Integrable (fun ω ↦ limsup (fun i ↦ X i ω) L) P) :
    limsup (fun i ↦ ∫ ω, X i ω ∂P) L ≤ ∫ ω, limsup (fun i ↦ X i ω) L ∂P := by
  have hmin_int : ∀ i, Integrable (fun ω ↦ X i ω ⊓ Y ω) P := fun i ↦ (hX_int i).inf hY
  have hpos_int : ∀ i, Integrable (fun ω ↦ max (X i ω - Y ω) 0) P :=
    fun i ↦ ((hX_int i).sub hY).pos_part
  have hWY_int : Integrable (fun ω ↦ W ω ⊓ Y ω) P := hW.inf hY
  have hmin_lb : ∀ i, (fun ω ↦ W ω ⊓ Y ω) ≤ᵐ[P] fun ω ↦ X i ω ⊓ Y ω := fun i ↦
    (hWX i).mono fun ω h ↦ inf_le_inf_right _ h
  have hmin_ub : ∀ i, (fun ω ↦ X i ω ⊓ Y ω) ≤ᵐ[P] Y := fun i ↦ .of_forall fun ω ↦ inf_le_right
  set u : ι → ℝ := fun i ↦ ∫ ω, X i ω ⊓ Y ω ∂P with hu_def
  set v : ι → ℝ := fun i ↦ ∫ ω, max (X i ω - Y ω) 0 ∂P with hv_def
  have h_pt : ∀ i ω, X i ω = X i ω ⊓ Y ω + max (X i ω - Y ω) 0 := by
    intro i ω
    rcases le_total (X i ω) (Y ω) with h | h
    · rw [inf_of_le_left h, max_eq_right (by linarith), add_zero]
    · rw [inf_of_le_right h, max_eq_left (by linarith)]
      ring
  have hsum : (fun i ↦ ∫ ω, X i ω ∂P) = u + v := by
    funext i
    rw [hu_def, hv_def, Pi.add_apply, ← integral_add (hmin_int i) (hpos_int i)]
    exact integral_congr_ae (.of_forall (h_pt i))
  have h_bdd_u : IsBoundedUnder (· ≤ ·) L u :=
    isBoundedUnder_of ⟨∫ ω, Y ω ∂P, fun i ↦ integral_mono_ae (hmin_int i) hY (hmin_ub i)⟩
  have h_cobdd_u : IsBoundedUnder (· ≥ ·) L u :=
    isBoundedUnder_of ⟨∫ ω, W ω ⊓ Y ω ∂P, fun i ↦ integral_mono_ae hWY_int (hmin_int i) (hmin_lb i)⟩
  have h_le : limsup (fun i ↦ ∫ ω, X i ω ∂P) L ≤ limsup u L :=
    calc limsup (fun i ↦ ∫ ω, X i ω ∂P) L = limsup (u + v) L := by rw [hsum]
      _ ≤ limsup u L + limsup v L :=
        limsup_add_le h_cobdd_u h_bdd_u
          (isCoboundedUnder_le_of_le L fun i ↦ integral_nonneg_of_ae
            (.of_forall fun ω ↦ le_max_right _ _)) h_tendsto.isBoundedUnder_le
      _ = limsup u L := by rw [show limsup v L = 0 from h_tendsto.limsup_eq, add_zero]
  have hL_min_int : Integrable (fun ω ↦ limsup (fun i ↦ X i ω ⊓ Y ω) L) P := by
    refine integrable_of_le_of_le
      (aemeasurable_limsup fun i ↦ (hmin_int i).aemeasurable).aestronglyMeasurable ?_ ?_ hWY_int hY
    · filter_upwards [hX_bdd, ae_all_iff.2 hmin_lb] with ω hbdd hlb
      refine le_limsup_of_le (hbdd.mono_le (.of_forall fun i ↦ inf_le_left)) fun c hc ↦ ?_
      obtain ⟨i, hi⟩ := (hc.and (Eventually.of_forall hlb)).exists
      exact hi.2.trans hi.1
    · filter_upwards [ae_all_iff.2 hmin_lb] with ω hlb
      exact limsup_le_of_le (isCoboundedUnder_le_of_le L hlb)
        (Eventually.of_forall fun i ↦ inf_le_right)
  refine h_le.trans ((limsup_integral_le_integral_limsup_of_le_of_le'
    (fun i ↦ (hmin_int i).aemeasurable) hWY_int hY hmin_lb hmin_ub).trans ?_)
  refine integral_mono_ae hL_min_int hL_int ?_
  filter_upwards [hX_bdd, ae_all_iff.2 hmin_lb] with ω hbdd hlb
  exact limsup_le_limsup (.of_forall fun i ↦ inf_le_left)
    (isCoboundedUnder_le_of_le L hlb) hbdd

/-- Reverse Fatou's lemma for the lower Lebesgue integral along a countably generated filter,
when the integral of the truncated difference `X i - g` tends to `0`. -/
theorem limsup_lintegral_le_of_tendsto_lintegral_sub {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {X : ι → Ω → ℝ≥0∞} {g : Ω → ℝ≥0∞}
    (hX_meas : ∀ i, AEMeasurable (X i) P) (hg_meas : AEMeasurable g P)
    (hg_fin : ∫⁻ ω, g ω ∂P ≠ ∞)
    (h_tendsto : Tendsto (fun i ↦ ∫⁻ ω, X i ω - g ω ∂P) L (𝓝 0)) :
    limsup (fun i ↦ ∫⁻ ω, X i ω ∂P) L ≤ ∫⁻ ω, limsup (fun i ↦ X i ω) L ∂P := by
  have hmin_meas : ∀ i, AEMeasurable (fun ω ↦ X i ω ⊓ g ω) P :=
    fun i ↦ (hX_meas i).inf hg_meas
  set u : ι → ℝ≥0∞ := fun i ↦ ∫⁻ ω, X i ω ⊓ g ω ∂P with hu_def
  set v : ι → ℝ≥0∞ := fun i ↦ ∫⁻ ω, X i ω - g ω ∂P with hv_def
  have hsum : (fun i ↦ ∫⁻ ω, X i ω ∂P) = u + v := by
    funext i
    rw [hu_def, hv_def, Pi.add_apply, ← lintegral_add_left' (hmin_meas i)]
    refine lintegral_congr fun ω ↦ ?_
    rw [add_comm, tsub_add_min]
  have h_limsup : limsup (fun i ↦ ∫⁻ ω, X i ω ∂P) L = limsup u L := by
    rw [hsum, ENNReal.limsup_add_of_right_tendsto_zero h_tendsto]
  rw [h_limsup]
  refine (limsup_lintegral_le' g hmin_meas (fun i ↦ .of_forall fun ω ↦ inf_le_right)
    hg_fin).trans ?_
  exact lintegral_mono fun ω ↦ limsup_le_limsup (.of_forall fun i ↦ inf_le_left)
    isCobounded_le_of_bot isBounded_le_of_top

section StoppedValueIntegrable

/-- The step extension of the discrete predictable part vanishes at `⊥`. -/
lemma predictableSeqStep_bot {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (n : ℕ) :
    predictableSeqStep P S 𝓕 n ⊥ = 0 := by
  funext ω
  rw [predictableSeqStep_eq_sum_indicator]
  exact Finset.sum_eq_zero fun u _ ↦
    Set.indicator_of_notMem (fun h ↦ absurd h.1 (not_lt.2 bot_le)) _

variable {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
  [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} {τ : Ω → WithTop ι}

/-- The convexly averaged step extension of the predictable parts vanishes at `⊥`. -/
lemma predictableConvexStep_bot (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) :
    predictableConvexStep hd hs n ⊥ = 0 := by
  funext ω
  simp [predictableConvexStep, Finsupp.sum, Finset.sum_apply, predictableSeqStep_bot]

/-- The stopped step extension of the discrete predictable part is integrable. -/
lemma integrable_stoppedValue_predictableSeqStep (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P)
    (hτ : IsStoppingTime 𝓕 τ) (hτ_ne : ∀ ω, τ ω ≠ ⊤) (m : ℕ) :
    Integrable (stoppedValue (predictableSeqStep P S 𝓕 m) τ) P := by
  have hσ : IsStoppingTime 𝓕 (meshCeil m τ) := isStoppingTime_meshCeil hτ m
  have hσ_ne (ω) : meshCeil m τ ω ≠ ⊤ := meshCeil_ne_top m (hτ_ne ω)
  have hS : Integrable (stoppedValue S (meshCeil m τ)) P :=
    memLp_one_iff_integrable.1 (hd.uniformIntegrable.memLp ⟨_, hσ, hσ_ne⟩)
  have hN : Integrable (stoppedValue (martingaleSeqStep P S 𝓕 m) (meshCeil m τ)) P :=
    (martingale_condExp _ _ _).integrable_stoppedValue_of_countable_range _ hσ
      (fun ω ↦ WithTop.le_coe_top (hσ_ne ω)) (countable_range_meshCeil m τ)
  rw [stoppedValue_predictableSeqStep_meshCeil hτ_ne]
  exact (integrable_congr (stoppedValue_predictableSeqStep_ae_eq hs.stronglyAdapted
    hs.integrable hτ_ne).symm).1 (hS.sub hN)

/-- The stopped convexly averaged step extension of the predictable parts is integrable. -/
lemma integrable_stoppedValue_predictableConvexStep (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) (hτ_ne : ∀ ω, τ ω ≠ ⊤) (n : ℕ) :
    Integrable (stoppedValue (predictableConvexStep hd hs n) τ) P := by
  have hstop : stoppedValue (predictableConvexStep hd hs n) τ
      = ∑ m ∈ (weight hd hs n).weights.support,
          (weight hd hs n).weights m • stoppedValue (predictableSeqStep P S 𝓕 m) τ := by
    funext ω
    simp [predictableConvexStep, stoppedValue, Finsupp.sum, Finset.sum_apply]
  rw [hstop]
  exact integrable_finsetSum' _ fun m _ ↦
    (integrable_stoppedValue_predictableSeqStep hd hs hτ hτ_ne m).smul
      ((weight hd hs n).weights m)

/-- The predictable part of the Doob-Meyer decomposition stopped at a finite stopping time is
integrable. -/
lemma integrable_stoppedValue_predictablePartLim [𝓕.IsRightContinuous]
    [𝓕.IsComplete P] (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (hτ : IsStoppingTime 𝓕 τ)
    (hτ_ne : ∀ ω, τ ω ≠ ⊤) :
    Integrable (stoppedValue (predictablePartLim hd hs) τ) P := by
  have hint_S : Integrable (stoppedValue S τ) P :=
    memLp_one_iff_integrable.1 (hd.uniformIntegrable.memLp ⟨τ, hτ, hτ_ne⟩)
  have hint_M : Integrable (stoppedValue (martingalePartLim hd hs) τ) P :=
    (martingale_martingalePartLim hd hs).integrable_stoppedValue_top
      (fun ω ↦ (isCadlag_martingalePartLim hd hs ω).right_continuous) hτ hτ_ne
  rw [predictablePartLim, stoppedValue.sub]
  exact hint_S.sub hint_M

end StoppedValueIntegrable

variable {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
  [MeasurableSpace ι]
  [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous]

/-- For each finite stopping time `τ`, almost everywhere,
`limsup (fun n => stoppedValue 𝒜^n τ ω) atTop = stoppedValue A τ ω`. -/
lemma limsup_stoppedValue_predictableConvexStep_ae_eq_stoppedValue_predictablePartLim
    [𝓕.IsComplete P]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P)
    {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) (hτ_ne : ∀ ω, τ ω ≠ ⊤)
    (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    (fun ω ↦ limsup (fun n ↦ stoppedValue (predictableConvexStep hd hs n) τ ω) atTop) =ᵐ[P]
      stoppedValue (predictablePartLim hd hs) τ := by
  set X : ℕ → Ω → ℝ := fun n ↦ stoppedValue (predictableConvexStep hd hs n) τ
  have hX_int (n : ℕ) : Integrable (X n) P :=
    integrable_stoppedValue_predictableConvexStep hd hs hτ hτ_ne n
  have hA_int : Integrable (stoppedValue (predictablePartLim hd hs) τ) P :=
    integrable_stoppedValue_predictablePartLim hd hs hτ hτ_ne
  have hL_le : (fun ω ↦ limsup (fun n ↦ X n ω) atTop) ≤ᵐ[P]
      stoppedValue (predictablePartLim hd hs) τ :=
    limsup_stoppedValue_predictableConvexStep_ae_le_stoppedValue_predictablePartLim hd hs τ hc
  have hmono : ∀ᵐ ω ∂P, ∀ n, Monotone fun t ↦ predictableConvexStep hd hs n t ω :=
    ae_all_iff.2 (predictableConvexStep_monotone_ae hd hs)
  have hX_nonneg : ∀ᵐ ω ∂P, ∀ n, 0 ≤ X n ω := by
    filter_upwards [hmono] with ω hω n
    have h : predictableConvexStep hd hs n ⊥ ω ≤ X n ω := hω n bot_le
    rwa [congrFun (predictableConvexStep_bot hd hs n) ω] at h
  have hX_le_top : ∀ᵐ ω ∂P, ∀ n, X n ω ≤ predictableConvexStep hd hs n ⊤ ω := by
    filter_upwards [hmono] with ω hω n
    exact hω n le_top
  have hX_bdd : ∀ᵐ ω ∂P, IsBoundedUnder (· ≤ ·) atTop fun n ↦ X n ω := by
    filter_upwards [hX_le_top, predictableConvexStep_ae_tendsto hd hs] with ω hle hconvω
    exact (hconvω ⊤ (top_mem_denseSet ι)).isBoundedUnder_le.mono_le (.of_forall hle)
  have hL_nonneg : 0 ≤ᵐ[P] fun ω ↦ limsup (fun n ↦ X n ω) atTop := by
    filter_upwards [hX_nonneg, hX_bdd] with ω h0 hbdd
    refine le_limsup_of_le hbdd fun b hb ↦ ?_
    obtain ⟨n, hn⟩ := hb.exists
    exact (h0 n).trans hn
  have hL_meas : AEMeasurable (fun ω ↦ limsup (fun n ↦ X n ω) atTop) P :=
    ⟨_, Measurable.limsup fun n ↦ (hX_int n).aemeasurable.measurable_mk,
      (ae_all_iff.2 fun n ↦ (hX_int n).aemeasurable.ae_eq_mk).mono fun ω hω ↦
        congrArg (limsup · atTop) (funext hω)⟩
  have hL_int : Integrable (fun ω ↦ limsup (fun n ↦ X n ω) atTop) P :=
    integrable_of_le_of_le hL_meas.aestronglyMeasurable hL_nonneg hL_le (integrable_zero _ _ _)
      hA_int
  have hY_int : Integrable (predictablePartLim hd hs ⊤) P :=
    integrable_predictablePartLim hd hs ⊤
  have htop_int (n : ℕ) : Integrable (predictableConvexStep hd hs n ⊤) P := by
    have h := integrable_stoppedValue_predictableConvexStep hd hs (isStoppingTime_const 𝓕 (⊤ : ι))
      (fun _ ↦ WithTop.coe_ne_top) n
    rwa [stoppedValue_const] at h
  have h_tendsto : Tendsto (fun n ↦ ∫ ω, max (X n ω - predictablePartLim hd hs ⊤ ω) 0 ∂P)
      atTop (𝓝 0) := by
    have hD_int (n : ℕ) :
        Integrable (predictableConvexStep hd hs n ⊤ - predictablePartLim hd hs ⊤) P :=
      (htop_int n).sub hY_int
    have h_lim : Tendsto (fun n ↦ (eLpNorm
        (predictableConvexStep hd hs n ⊤ - predictablePartLim hd hs ⊤) 1 P).toReal)
        atTop (𝓝 0) := by
      rw [← ENNReal.toReal_zero]
      exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
        (predictableConvexStep_eLpNorm_tendsto hd hs (top_mem_denseSet ι))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_lim
      (fun n ↦ integral_nonneg fun ω ↦ le_max_right _ _) fun n ↦ ?_
    calc ∫ ω, max (X n ω - predictablePartLim hd hs ⊤ ω) 0 ∂P
        ≤ ∫ ω, ‖(predictableConvexStep hd hs n ⊤ - predictablePartLim hd hs ⊤) ω‖ ∂P := by
          refine integral_mono_ae ((hX_int n).sub hY_int).pos_part (hD_int n).norm ?_
          filter_upwards [hX_le_top] with ω hω
          exact max_le ((sub_le_sub_right (hω n) _).trans (le_abs_self _)) (abs_nonneg _)
      _ = (eLpNorm (predictableConvexStep hd hs n ⊤ - predictablePartLim hd hs ⊤) 1 P).toReal := by
          rw [integral_norm_eq_lintegral_enorm (hD_int n).aestronglyMeasurable,
            eLpNorm_one_eq_lintegral_enorm]
  have h_fatou : limsup (fun n ↦ ∫ ω, X n ω ∂P) atTop
      ≤ ∫ ω, limsup (fun n ↦ X n ω) atTop ∂P :=
    limsup_integral_le_integral_limsup_of_le_of_tendsto_integral_posPart_sub hX_int
      (integrable_zero _ _ _) (fun n ↦ hX_nonneg.mono fun ω h ↦ h n) hY_int hX_bdd h_tendsto
      hL_int
  have h_int_le : ∫ ω, stoppedValue (predictablePartLim hd hs) τ ω ∂P
      ≤ ∫ ω, limsup (fun n ↦ X n ω) atTop ∂P := by
    rw [← (integral_stoppedValue_predictableConvexStep_tendsto_stoppedValue_predictablePartLim
      hd hs hτ hτ_ne hc).limsup_eq]
    exact h_fatou
  exact (integral_eq_iff_of_ae_le hL_int hA_int hL_le).1
    (le_antisymm (integral_mono_ae hL_int hA_int hL_le) h_int_le)

/-- Under the usual conditions, the predictable part of the decomposition is strongly
progressive. -/
lemma isStronglyProgressive_predictablePartLim [OpensMeasurableSpace ι]
    [𝓕.IsComplete P] (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) :
    IsStronglyProgressive 𝓕 (predictablePartLim hd hs) :=
  hd.isStronglyProgressive.sub
    ((stronglyAdapted_martingalePartLim hd hs).isStronglyProgressive_of_rightContinuous
      fun ω ↦ (isCadlag_martingalePartLim hd hs ω).right_continuous)

/-- Almost surely, `limsup (predictableConvexStep hd hs · t ω) atTop ≤ predictablePartLim hd hs t ω`
for all times `t`. -/
lemma limsup_predictableConvexStep_le_predictablePartLim_ae
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    ∀ᵐ ω ∂P, ∀ t, limsup (predictableConvexStep hd hs · t ω) atTop ≤
      predictablePartLim hd hs t ω := by
  filter_upwards [predictableConvexStep_ae_tendsto hd hs,
    isRightContinuous_predictablePartLim_ae hd hs hc,
    ae_all_iff.2 (predictableConvexStep_monotone_ae hd hs)] with ω hconvω hrcω hmonoω t
  exact limsup_le_of_eventually_monotone_of_tendsto_on_dense (.of_forall hmonoω)
    (denseSet_dense ι) (fun _ ↦ mem_denseSet_of_nhdsGT_eq_bot) (bot_mem_denseSet ι) (hrcω t) hconvω

/-- Almost surely, the left limit of `predictablePartLim hd hs` at `t` is at most
`limsup (predictableConvexStep hd hs · t ω) atTop`, for all times `t`. -/
lemma leftLim_predictablePartLim_le_limsup_predictableConvexStep_ae
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    ∀ᵐ ω ∂P, ∀ t, (predictablePartLim hd hs · ω).leftLim t ≤
      limsup (predictableConvexStep hd hs · t ω) atTop := by
  filter_upwards [predictableConvexStep_ae_tendsto hd hs,
    isCadlag_predictablePartLim_ae hd hs hc,
    ae_all_iff.2 (predictableConvexStep_monotone_ae hd hs)] with ω hconvω hcadlagω hmonoω t
  refine (leftLim_le_liminf_of_eventually_monotone_of_tendsto_on_dense (.of_forall hmonoω)
    (denseSet_dense ι) (fun _ ↦ mem_denseSet_of_nhdsLT_eq_bot) (top_mem_denseSet ι)
    (hcadlagω.left_limit t)
    hconvω).trans (liminf_le_limsup ?_ ?_)
  · exact (hconvω ⊤ (top_mem_denseSet ι)).isBoundedUnder_le.mono_le
      (.of_forall fun n ↦ hmonoω n le_top)
  · exact (hconvω ⊥ (bot_mem_denseSet ι)).isBoundedUnder_ge.mono_ge
      (.of_forall fun n ↦ hmonoω n bot_le)

/-- Almost surely, for all `ε > 0`, there are only finitely many times at which
`limsup (predictableConvexStep hd hs · t ω) atTop` is smaller than `predictablePartLim hd hs t ω`
by more than `ε`: these are times of jumps of size at least `ε` of the càdlàg path of
`predictablePartLim hd hs`. -/
lemma finite_setOf_lt_predictablePartLim_sub_limsup_predictableConvexStep_ae
    [CompactSpace ι] (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P)
    (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    ∀ᵐ ω ∂P, ∀ ε > 0, {t | ε < predictablePartLim hd hs t ω -
      limsup (predictableConvexStep hd hs · t ω) atTop}.Finite := by
  filter_upwards [isCadlag_predictablePartLim_ae hd hs hc,
    leftLim_predictablePartLim_le_limsup_predictableConvexStep_ae hd hs hc]
    with ω hcadlagω hleω ε hε
  refine (hcadlagω.finite_largeLeftJumpSet (Metric.dist_mem_uniformity hε)).subset fun t ht ↦ ?_
  simp only [largeLeftJumpSet, Set.mem_ofPred_eq, not_lt]
  rw [Set.mem_ofPred_eq] at ht
  calc ε ≤ predictablePartLim hd hs t ω - (predictablePartLim hd hs · ω).leftLim t := by
        linarith [hleω t]
    _ ≤ dist (predictablePartLim hd hs t ω) ((predictablePartLim hd hs · ω).leftLim t) :=
        le_abs_self _

/-- The processes `fun t ω ↦ limsup (predictableConvexStep hd hs · t ω) atTop` and
`predictablePartLim hd hs` are indistinguishable. -/
lemma limsup_predictableConvexStep_eq_predictablePartLim {ι : Type*} [CompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [MeasurableSpace ι]
    [BorelSpace ι] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous] [𝓕.IsComplete P]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    ∀ᵐ ω ∂P, ∀ t, limsup (predictableConvexStep hd hs · t ω) atTop =
      predictablePartLim hd hs t ω := by
  -- the début theorem below is stated for Polish spaces
  have : PolishSpace ι := .of_compactSpace_of_secondCountableTopology
  set L : ι → Ω → ℝ := fun t ω ↦ limsup (predictableConvexStep hd hs · t ω) atTop
  set A : ι → Ω → ℝ := predictablePartLim hd hs
  -- the set `B k` of times at which `A - L > 1 / (k + 1)` is progressively measurable
  have hAL : IsStronglyProgressive 𝓕 (fun t ω ↦ A t ω - L t ω) :=
    (isStronglyProgressive_predictablePartLim hd hs).sub
      (isStronglyPredictable_limsup_predictableConvexStep hd hs).isStronglyProgressive
  let B (k : ℕ) : Set (ι × Ω) := {p | 1 / ((k : ℝ) + 1) < A p.1 p.2 - L p.1 p.2}
  have hB (k : ℕ) : ProgMeasurableSet (B k) 𝓕 := measurableSet_Ioi.progMeasurableSet_preimage hAL
  -- hence its début, truncated at `⊤`, is a finite stopping time, at which `L` and `A` coincide
  let σ (k : ℕ) : Ω → WithTop ι := fun ω ↦ min (debut (B k) ⊥ ω) ((⊤ : ι) : WithTop ι)
  have hσ (k : ℕ) : IsStoppingTime 𝓕 (σ k) :=
    (isStoppingTime_debut P (hB k) ⊥).min (isStoppingTime_const 𝓕 ⊤)
  have hσ_ne (k : ℕ) (ω : Ω) : σ k ω ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  have h_eq : ∀ᵐ ω ∂P, ∀ k, L (σ k ω).untopA ω = A (σ k ω).untopA ω := ae_all_iff.2 fun k ↦
    limsup_stoppedValue_predictableConvexStep_ae_eq_stoppedValue_predictablePartLim hd hs (hσ k)
      (hσ_ne k) hc
  filter_upwards [h_eq, limsup_predictableConvexStep_le_predictablePartLim_ae hd hs hc,
    finite_setOf_lt_predictablePartLim_sub_limsup_predictableConvexStep_ae hd hs hc]
    with ω h_eq h_le h_fin t
  refine le_antisymm (h_le t) (not_lt.1 fun h_lt ↦ ?_)
  -- if `L t ω < A t ω` then some `B k` has a nonempty and finite section at `ω`, which contains
  -- its début: a contradiction since `L` and `A` coincide at the début
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 h_lt)
  have hex : ∃ s ≥ ⊥, (s, ω) ∈ B k := ⟨t, bot_le, hk⟩
  have hmem : ((debut (B k) ⊥ ω).untopA, ω) ∈ B k :=
    debut_mem_set_of_finite ((h_fin _ (by positivity)).subset fun s hs ↦ hs.2) hex
  have hσ_eq : σ k ω = debut (B k) ⊥ ω := min_eq_left (WithTop.le_coe_top (debut_ne_top_iff.2 hex))
  have h_eq' := h_eq k
  rw [hσ_eq] at h_eq'
  simp only [B, Set.mem_ofPred_eq, h_eq', sub_self] at hmem
  exact absurd hmem (not_lt.2 (by positivity))

end PredictablePartIsStronglyPredictable

section DoobMeyer

/-- **Doob–Meyer decomposition** of a càdlàg submartingale of class D. -/
theorem ProbabilityTheory.ClassD.doob_meyer {ι Ω : Type*} [CompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [MeasurableSpace ι]
    [BorelSpace ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous] [𝓕.IsComplete P]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (hc : ∀ ω, IsCadlag (S · ω)) :
    ∃ (M A : ι → Ω → ℝ), S = M + A ∧ Martingale M 𝓕 P ∧ (∀ ω, IsCadlag (M · ω)) ∧
      IsStronglyPredictable 𝓕 A ∧ (∀ ω, IsCadlag (A · ω)) ∧ (∀ ω, Monotone (A · ω)) ∧
      A ⊥ = 0 := by
  have hc' : ∀ᵐ ω ∂P, IsCadlag (S · ω) := .of_forall hc
  -- the limsup process `L` and the good set `G`, whose complement is a null set
  let L : ι → Ω → ℝ := fun t ω ↦ limsup (predictableConvexStep hd hs · t ω) atTop
  have hL : IsStronglyPredictable 𝓕 L := isStronglyPredictable_limsup_predictableConvexStep hd hs
  let G : Set Ω := {ω | (∀ t, L t ω = predictablePartLim hd hs t ω) ∧
    Monotone (predictablePartLim hd hs · ω) ∧ IsCadlag (predictablePartLim hd hs · ω)}
  have hG_ae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [limsup_predictableConvexStep_eq_predictablePartLim hd hs hc',
      predictablePartLim_monotone_ae hd hs hc', isCadlag_predictablePartLim_ae hd hs hc']
      with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  have hN_null : P Gᶜ = 0 := hG_ae
  have hG_meas (t : ι) : MeasurableSet[𝓕 t] G :=
    (Filtration.IsComplete.measurableSet_of_null hN_null t).of_compl
  -- the predictable part `A` and its values on `G` and `Gᶜ`
  let A : ι → Ω → ℝ := fun t ↦ G.indicator (L t)
  have hA_mem {ω : Ω} (hω : ω ∈ G) (t : ι) : A t ω = predictablePartLim hd hs t ω := by
    simp only [A, Set.indicator_of_mem hω, hω.1 t]
  have hA_notMem {ω : Ω} (hω : ω ∉ G) (t : ι) : A t ω = 0 := Set.indicator_of_notMem hω _
  have hA_pred : IsStronglyPredictable 𝓕 A := by
    have h_eq : Function.uncurry A = (Set.univ ×ˢ G).indicator (Function.uncurry L) := by
      ext ⟨t, ω⟩
      by_cases hω : ω ∈ G <;> simp [A, hω]
    rw [IsStronglyPredictable, h_eq]
    exact StronglyMeasurable.indicator hL (measurableSet_predictable_univ_prod (hG_meas ⊥))
  have hM_mem {ω : Ω} (hω : ω ∈ G) (t : ι) : (S - A) t ω = martingalePartLim hd hs t ω := by
    simp only [Pi.sub_apply, hA_mem hω t, predictablePartLim, sub_sub_cancel]
  have hA_bot : A ⊥ = 0 := by
    have hL_bot : L ⊥ = 0 := by
      funext ω
      simp [L, predictableConvexStep_bot]
    simp [A, hL_bot]
  refine ⟨S - A, A, (sub_add_cancel S A).symm, ?_, fun ω ↦ ?_, hA_pred, fun ω ↦ ?_, fun ω ↦ ?_,
    hA_bot⟩
  · refine (martingale_martingalePartLim hd hs).congr ?_ ?_
    · exact fun t ↦ (hs.stronglyAdapted t).sub (hA_pred.stronglyAdapted t)
    · intro t
      filter_upwards [hG_ae] with ω hω using (hM_mem hω t).symm
  · by_cases hω : ω ∈ G
    · simpa only [hM_mem hω] using isCadlag_martingalePartLim hd hs ω
    · simpa only [Pi.sub_apply, hA_notMem hω, sub_zero] using hc ω
  · by_cases hω : ω ∈ G
    · simpa only [hA_mem hω] using hω.2.2
    · simpa only [hA_notMem hω] using isCadlag_const (ι := ι) (0 : ℝ)
  · by_cases hω : ω ∈ G
    · simpa only [hA_mem hω] using hω.2.1
    · simpa only [hA_notMem hω] using monotone_const (α := ι) (c := (0 : ℝ))

end DoobMeyer
