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
public import Mathlib.Topology.Order.LiminfLimsup

import Mathlib.Order.CompleteLattice.Group

/-! # Doob-Meyer decomposition theorem

-/

@[expose] public section

open MeasureTheory Filter Order ProbabilityTheory Convexity
open scoped NNReal ENNReal Topology

section DenseMesh

/-- The fixed countable dense set used instead of dyadics, with both endpoints adjoined. -/
noncomputable def denseSet (ι : Type*) [LE ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] : Set ι :=
  (TopologicalSpace.exists_countable_dense ι).choose ∪ ({⊥, ⊤} : Set ι)

lemma denseSet_countable (ι : Type*) [LE ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] : (denseSet ι).Countable := by
  have h_dense_countable := (TopologicalSpace.exists_countable_dense ι).choose_spec.1
  simpa [denseSet] using h_dense_countable.union (by simp : ({⊥, ⊤} : Set ι).Countable)

lemma denseSet_dense (ι : Type*) [LE ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] : Dense (denseSet ι) :=
  (TopologicalSpace.exists_countable_dense ι).choose_spec.2.mono (Set.subset_union_left)

/-- A choice of enumeration of the countable dense set used to construct finite meshes. -/
noncomputable def denseEnum (ι : Type*) [LE ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] : ℕ → ι :=
  have : Nonempty (denseSet ι) := ⟨⟨⊥, by simp [denseSet]⟩⟩
  Subtype.val ∘ (countable_iff_exists_surjective.mp (denseSet_countable ι)).choose

/-- The `n`-th finite mesh: the first `n` points of the dense enumeration, plus endpoints. -/
noncomputable def mesh (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] (n : ℕ) : Finset ι :=
  insert ⊥ <| insert ⊤ <| (Finset.range n).image (denseEnum ι)

lemma bot_mem_mesh (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] (n : ℕ) : (⊥ : ι) ∈ mesh ι n := by simp [mesh]

lemma top_mem_mesh (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] (n : ℕ) : (⊤ : ι) ∈ mesh ι n := by simp [mesh]

instance (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] (n : ℕ) : OrderBot (mesh ι n) where
  bot := ⟨⊥, bot_mem_mesh ι n⟩
  bot_le _ := bot_le

instance (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] (n : ℕ) : OrderTop (mesh ι n) where
  top := ⟨⊤, top_mem_mesh ι n⟩
  le_top _ := le_top

@[simp]
lemma top_eq_top (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] (n : ℕ) : (⊤ : mesh ι n) = (⊤ : ι) := by rfl

@[simp]
lemma bot_eq_bot (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] (n : ℕ) : (⊥ : mesh ι n) = (⊥ : ι) := by rfl

noncomputable instance (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] (n : ℕ) : LocallyFiniteOrder (mesh ι n) :=
  Fintype.toLocallyFiniteOrder

noncomputable instance (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] (n : ℕ) : SuccOrder (mesh ι n) :=
  LinearLocallyFiniteOrder.succOrder (mesh ι n)

noncomputable instance (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] (n : ℕ) : PredOrder (mesh ι n) :=
  LinearLocallyFiniteOrder.predOrder (mesh ι n)

noncomputable instance (ι : Type*) [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] (n : ℕ) : CompleteLinearOrder (mesh ι n) :=
  Fintype.toCompleteLinearOrder (mesh ι n)

end DenseMesh

section Estimate

/-- The filtration obtained by restricting `𝓕` to a finite dense mesh. -/
def meshFiltration {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [LinearOrder ι]
    [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ι mΩ) (n : ℕ) :
    Filtration (mesh ι n) mΩ :=
  𝓕.indexComap (Subtype.mono_coe (SetLike.coe (mesh ι n)))

instance sigmaFiniteFiltration_meshFiltration {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
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
    [CompleteSpace E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
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

/-- For a submartingale indexed by a countable type, the predictable part is monotone a.e. -/
lemma MeasureTheory.Submartingale.monotone_predictablePart_ae {ι Ω E : Type*} [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [SuccOrder ι] [Countable ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [PartialOrder E]
    [IsOrderedAddMonoid E] {S : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hs : Submartingale S 𝓕 P) :
    ∀ᵐ ω ∂P, Monotone (_root_.predictablePart S 𝓕 P · ω) := by
  have hnonneg : ∀ᵐ ω ∂P, ∀ i : ι, 0 ≤ P[S (succ i) - S i | 𝓕 i] ω :=
    ae_all_iff.2 fun i ↦ hs.condExp_sub_nonneg (le_succ i)
  filter_upwards [hnonneg] with ω hω a b hab
  simp only [_root_.predictablePart, Finset.sum_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iio_subset_Iio hab) fun i _ _ ↦ hω i

/-- For a submartingale indexed by a countable type, the predictable part is nonnegative a.e. -/
lemma MeasureTheory.Submartingale.predictablePart_nonneg' {ι Ω E : Type*} [LinearOrder ι]
    [LocallyFiniteOrder ι] [OrderBot ι] [SuccOrder ι] [Countable ι] {mΩ : MeasurableSpace Ω}
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

/-- The martingale part of a process is a martingale. -/
lemma martingale_martingalePart {ι Ω E : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    Martingale (martingalePart S 𝓕 P) 𝓕 P := by
  sorry

@[simp]
lemma martingalePart_add_predictablePart {ι Ω E : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    martingalePart S 𝓕 P + predictablePart S 𝓕 P = S := by
  simp [_root_.martingalePart]

/-- Sequence of terminal values of the predictable part. -/
noncomputable def predictableSeqTop {ι Ω E : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    (n : ℕ) : Ω → E :=
  predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⊤

/-- The terminal values of the predictable parts on each mesh are integrable. -/
lemma integrable_predictableSeqTop {ι Ω E : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) :
    Integrable (predictableSeqTop S 𝓕 P n) P :=
  integrable_predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⊤

/-- The terminal values of the predictable parts of a martingale vanish on every mesh. -/
lemma predictableSeqTop_eq_zero_of_martingale {ι Ω E : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure Ω} {S : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hS : Martingale S 𝓕 P)
    (n : ℕ) :
    predictableSeqTop S 𝓕 P n =ᵐ[P] 0 := by
  simp only [predictableSeqTop, meshFiltration]
  apply predictablePart_eq_zero_of_martingale _ ⊤
  exact (hS.indexComap (Subtype.mono_coe (SetLike.coe (mesh ι n))))

/-- Sequence of terminal values of the martingale part. -/
noncomputable def martingaleSeqTop {ι Ω E : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) : Ω → E :=
  martingalePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⊤

/-- The terminal values of the discrete martingale parts are additive. -/
lemma martingaleSeqTop_add {ι Ω E : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {P : Measure Ω}
    {S₁ S₂ : ι → Ω → E} (𝓕 : Filtration ι mΩ) (hS₁ : ∀ t, Integrable (S₁ t) P)
    (hS₂ : ∀ t, Integrable (S₂ t) P) (n : ℕ) :
    martingaleSeqTop (S₁ + S₂) 𝓕 P n =ᵐ[P]
      martingaleSeqTop S₁ 𝓕 P n + martingaleSeqTop S₂ 𝓕 P n :=
  martingalePart_add (fun t : mesh ι n ↦ hS₁ t) (fun t ↦ hS₂ t) ⊤

/-- The terminal values of the martingale parts of a martingale are its terminal value on every
mesh. -/
lemma martingaleSeqTop_eq_self_of_martingale {ι Ω E : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure Ω} {S : ι → Ω → E} {𝓕 : Filtration ι mΩ} (hS : Martingale S 𝓕 P)
    (n : ℕ) :
    martingaleSeqTop S 𝓕 P n =ᵐ[P] S ⊤ := by
  simp only [martingaleSeqTop, meshFiltration]
  apply martingalePart_eq_self_of_martingale _ ⊤
  exact (hS.indexComap (Subtype.mono_coe (SetLike.coe (mesh ι n))))

/-- If `S = 0` a.e., then the martingale part’s terminal value equals the negative of the
predictable part’s terminal value. -/
lemma martingaleSeqTop_eq_neg_predictableSeqTop {ι Ω E : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {S : ι → Ω → E} (𝓕 : Filtration ι mΩ) (hstop : S ⊤ =ᶠ[ae P] 0)
    (n : ℕ) :
    martingaleSeqTop S 𝓕 P n =ᶠ[ae P] -predictableSeqTop S 𝓕 P n := by
  simp only [martingaleSeqTop, _root_.martingalePart, Pi.sub_apply, Function.comp_apply, top_eq_top,
    predictableSeqTop]
  grw [neg_eq_zero_sub, hstop]

/-- Apply the optional stopping theorem to get equation 4. Note that `T1 Space` is needed to make
sure that `mesh ι n` has order topology. -/
lemma equation4 {ι Ω E : Type*} [TopologicalSpace ι] [T1Space ι] [SecondCountableTopology ι]
    [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {S : ι → Ω → E}
    {𝓕 : Filtration ι mΩ} {n : ℕ} [SigmaFiniteFiltration P 𝓕] (hstop : S ⊤ =ᶠ[ae P] 0)
    {τ : Ω → WithTop (mesh ι n)} (hτ : ∀ ω, τ ω ≤ WithTop.some (⊤ : mesh ι n))
    (hτs : IsStoppingTime (meshFiltration 𝓕 n) τ) :
    stoppedValue (S ∘ Subtype.val) τ =ᵐ[P]
      -P[(predictableSeqTop S 𝓕 P n) | hτs.measurableSpace] +
        stoppedValue (predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P) τ := by
  grw [← condExp_neg, ← martingaleSeqTop_eq_neg_predictableSeqTop 𝓕 hstop]
  simp only [martingaleSeqTop]
  grw [← (martingale_martingalePart (S ∘ Subtype.val)
    (meshFiltration 𝓕 n) P).stoppedValue_ae_eq_condExp_of_le_const hτs hτ,
    ← stoppedValue.add, _root_.martingalePart_add_predictablePart]

section equation5

/-- The mesh stopping time `τₙ(c)` associated with the predictable part on the `n`-th mesh. -/
noncomputable def tauMesh {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} (S : ι → Ω → ℝ)
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) :
    Ω → WithTop (mesh ι n) :=
  fun ω ↦ (((hittingBtwn (fun (t : mesh ι n) ω ↦
    (predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P) (succ t) ω) (Set.Ioi c)
    ⊥ ⊤ ω) : mesh ι n) : WithTop (mesh ι n))

lemma tauMesh_le_top {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} (S : ι → Ω → ℝ)
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) (ω : Ω) :
    tauMesh S 𝓕 P n c ω ≤ (⊤ : mesh ι n) :=
  WithTop.coe_le_coe.2 (hittingBtwn_le ω)

/-- The stopped valued of the predictable part with respect to `τₙ(c)` is less than or equal to
`c`. -/
lemma stoppedValue_predictablePart_tauMesh_le {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω}
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

/-- The predictable part is predictable. -/
lemma isPredictable_predictablePart {ι Ω E : Type*} [LinearOrder ι] [LocallyFiniteOrder ι]
    [OrderBot ι] [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    IsStronglyPredictable 𝓕 (predictablePart S 𝓕 P) := by
  sorry

/-- At time `t`, the predictable part is strongly measurable with respect to the previous
σ-algebra. -/
lemma stronglyMeasurable_pred_predictablePart {ι Ω E : Type*} [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [PredOrder ι] [SuccOrder ι] {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω) (t : ι) :
    StronglyMeasurable[𝓕 (pred t)] (predictablePart S 𝓕 P t) :=
  Finset.stronglyMeasurable_sum _ fun _ hi =>
    stronglyMeasurable_condExp.mono (𝓕.mono (le_pred_of_lt (Finset.mem_Iio.1 hi)))

/-- At time `t`, the predictable part is strongly measurable with respect to the previous
σ-algebra. -/
lemma stronglyMeasurable_predictablePart {ι Ω E : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [PredOrder ι] [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω) (t : ι) :
    StronglyMeasurable[𝓕 t] (predictablePart S 𝓕 P t) :=
  (stronglyMeasurable_pred_predictablePart S 𝓕 P t).mono (𝓕.mono (pred_le _))

/-- The predictable part of a process is strongly adapted. -/
lemma stronglyAdapted_predictablePart {ι Ω E : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    StronglyAdapted 𝓕 (predictablePart S 𝓕 P) :=
  fun _ => Finset.stronglyMeasurable_sum _ fun _ hi =>
    stronglyMeasurable_condExp.mono (𝓕.mono (Finset.mem_Iio.1 hi).le)

/-- The predictable part of a process is strongly adapted. -/
lemma stronglyAdapted_predictablePart' {ι Ω E : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    StronglyAdapted 𝓕 (fun t ω ↦ predictablePart S 𝓕 P (succ t) ω) :=
  fun _ => Finset.stronglyMeasurable_sum _ fun _ hi ↦
    stronglyMeasurable_condExp.mono (𝓕.mono (le_of_lt_succ (Finset.mem_Iio.1 hi)))

/-- `τₙ(c)` is indeed a stopping time. -/
lemma isStoppingTime_tauMesh {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} (S : ι → Ω → ℝ)
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) :
    IsStoppingTime (meshFiltration 𝓕 n) (tauMesh S 𝓕 P n c) :=
  (stronglyAdapted_predictablePart'
    (S ∘ Subtype.val) (meshFiltration 𝓕 n) P).adapted.isStoppingTime_hittingBtwn measurableSet_Ioi

/-- Combine equation 4 and `stoppedValue_predictablePart_tauMesh_le` to get this inequality. -/
lemma stoppedValue_le_neg_condExp_predictableSeqTop_add_const {ι Ω : Type*} [TopologicalSpace ι]
    [T1Space ι] [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι]
    [OrderTop ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ} (hstop : S ⊤ =ᶠ[ae P] 0)
    (𝓕 : Filtration ι mΩ) (n : ℕ) [SigmaFiniteFiltration P 𝓕] {c : ℝ} (hc : 0 ≤ c) :
    stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n c) ≤ᵐ[P]
      -P[predictableSeqTop S 𝓕 P n | (isStoppingTime_tauMesh S 𝓕 P n c).measurableSpace] +
      (fun _ => c) := by
  filter_upwards [equation4 hstop (tauMesh_le_top S 𝓕 P n c) (isStoppingTime_tauMesh S 𝓕 P n c)]
    with ω heqω
  rw [heqω]
  exact add_le_add_right (stoppedValue_predictablePart_tauMesh_le S 𝓕 P n hc ω) _

/-- `{τₙ(c) < 1} = {c < Aⁿ₁}`. -/
lemma MeasureTheory.Submartingale.tauMesh_lt_top_eq_lt_predictableSeqTop {ι Ω : Type*}
    [TopologicalSpace ι] [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
    (hs : Submartingale S 𝓕 P) (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)} =ᵐ[P] {ω | c < predictableSeqTop S 𝓕 P n ω} := by
  refine eventuallyEq_set.2 ?_
  have hs_mesh : Submartingale (S ∘ Subtype.val) (meshFiltration 𝓕 n) P :=
    hs.indexComap (Subtype.mono_coe (SetLike.coe (mesh ι n)))
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
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
    (hs : Submartingale S 𝓕 P) (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun _ : Ω => c) {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)} P := by
  by_cases! hc0 : c = 0
  · simp [hc0]
  · refine integrableOn_const (LT.lt.ne ?_)
    rw [measure_congr (hs.tauMesh_lt_top_eq_lt_predictableSeqTop n hc)]
    exact (integrable_predictableSeqTop S 𝓕 P n).measure_gt_lt_top (lt_of_le_of_ne hc hc0.symm)

/-- Stopping `S` at the bounded mesh time `τₙ(c)` preserves integrability. -/
lemma MeasureTheory.Submartingale.integrable_stoppedValue_tauMesh {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} (hs : Submartingale S 𝓕 P) (n : ℕ)
    (c : ℝ) :
    Integrable (stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n c)) P :=
  integrable_stoppedValue (mesh ι n) (isStoppingTime_tauMesh S 𝓕 P n c)
    (hs.indexComap (Subtype.mono_coe (SetLike.coe (mesh ι n)))).integrable
    (tauMesh_le_top S 𝓕 P n c)

/-- The first estimate before equation 5. -/
lemma first_estimate {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι] [SecondCountableTopology ι]
    [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω}
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
      · exact (isStoppingTime_tauMesh S 𝓕 P n c).measurableSet_lt' ⊤
    _ ≤ ∫ ω in {ω | tauMesh S 𝓕 P n c ω < (⊤ : mesh ι n)},
        (c - stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n c) ω) ∂P := by
      refine setIntegral_mono_ae integrable_condExp.integrableOn
        ((hs.integrableOn_const_tauMesh_lt_top n hc).sub
          (hs.integrable_stoppedValue_tauMesh n c).integrableOn) ?_
      filter_upwards [stoppedValue_le_neg_condExp_predictableSeqTop_add_const hstop 𝓕 n hc]
        with ω hω
      simp at hω
      linarith [hω]
    _ = _ := by
      rw [integral_sub (hs.integrableOn_const_tauMesh_lt_top n hc)
        (hs.integrable_stoppedValue_tauMesh n c).integrableOn, setIntegral_const]
      ring

/-- If `a ≤ b`, then `{τₙ(b) < 1} ⊆ {τₙ(a) < 1}`. -/
lemma tauMesh_lt_top_subset_of_lt {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} (S : ι → Ω → ℝ)
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    {ω | tauMesh S 𝓕 P n b ω < (⊤ : mesh ι n)} ⊆ {ω | tauMesh S 𝓕 P n a ω < (⊤ : mesh ι n)} := by
  simp_all only [tauMesh, WithTop.coe_lt_coe, Set.setOf_subset_setOf]
  exact fun ω hω => (hittingBtwn_anti ((fun t ω ↦ _root_.predictablePart (S ∘ Subtype.val)
    (meshFiltration 𝓕 n) P (succ t) ω)) ⊥ ⊤ (antitone_Ioi hab) ω).trans_lt hω

/-- Stopping the predictable part at the bounded mesh time `τₙ(c)` preserves integrability. -/
lemma integrable_stoppedValue_predictablePart_tauMesh {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω) (n : ℕ) (c : ℝ) :
    Integrable (stoppedValue (predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P)
      (tauMesh S 𝓕 P n c)) P :=
  integrable_stoppedValue (mesh ι n) (isStoppingTime_tauMesh S 𝓕 P n c)
    (integrable_predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P)
    (tauMesh_le_top S 𝓕 P n c)

/-- The second estimate before equation 5. -/
lemma second_estimate {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
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
      · refine (((isStoppingTime_tauMesh S 𝓕 P n c).measurableSet _).1 ?_).1
        exact (isStoppingTime_tauMesh S 𝓕 P n c).measurableSet_lt' ⊤
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
          hs.indexComap (Subtype.mono_coe (SetLike.coe (mesh ι n)))
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
      · exact (isStoppingTime_tauMesh S 𝓕 P n (c / 2)).measurableSet_lt' ⊤
    _ = _ := by
      rw [← integral_sub integrable_condExp.restrict hstopped_pred_int.integrableOn, ← integral_neg]
      · refine setIntegral_congr_ae ?_ ?_
        · refine (((isStoppingTime_tauMesh S 𝓕 P n (c / 2)).measurableSet _).1 ?_).1
          exact (isStoppingTime_tauMesh S 𝓕 P n (c / 2)).measurableSet_lt' ⊤
        · filter_upwards [equation4 hstop (tauMesh_le_top S 𝓕 P n (c / 2))
            (isStoppingTime_tauMesh S 𝓕 P n (c / 2))] with ω hω _
          simp at hω
          linarith [hω]

lemma equation5 {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι] [SecondCountableTopology ι]
    [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω}
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

lemma equation5' {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι] [SecondCountableTopology ι]
    [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω}
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
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} (S : ι → Ω → ℝ)
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) : Ω → WithTop ι :=
  fun ω => ((tauMesh S 𝓕 P n c ω).untopA : mesh ι n)

@[simp]
lemma tauMesh_ne_top {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} (S : ι → Ω → ℝ)
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) (ω : Ω) :
    tauMesh S 𝓕 P n c ω ≠ ⊤ := by
  simp [tauMesh]

@[simp]
lemma tauMeshLift_ne_top {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} (S : ι → Ω → ℝ)
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) (ω : Ω) :
    tauMeshLift S 𝓕 P n c ω ≠ ⊤ := by
  simp [tauMeshLift]

lemma stoppedValue_tauMeshLift {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} (S : ι → Ω → ℝ)
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) :
    stoppedValue S (tauMeshLift S 𝓕 P n c) =
      stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P n c) := by
  ext; simp [stoppedValue, tauMeshLift]

/-- We still get a stopping time after the lifting. -/
lemma isStoppingTime_tauMeshLift {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} (S : ι → Ω → ℝ)
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) (c : ℝ) :
    IsStoppingTime 𝓕 (tauMeshLift S 𝓕 P n c) := by
  sorry

/-- Used in estimating the size of the set `{τₙ(b) < 1}`. -/
lemma integral_predictableSeqTop_eq_neg_integral_bot {ι Ω : Type*} [TopologicalSpace ι]
    [T1Space ι] [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι]
    [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration P 𝓕] (hstop : S ⊤ =ᵐ[P] 0) (n : ℕ) :
    ∫ ω, predictableSeqTop S 𝓕 P n ω ∂P = - ∫ ω, S ⊥ ω ∂P := calc
  _ = - ∫ ω, -predictableSeqTop S 𝓕 P n ω ∂P := by simp [integral_neg]
  _ = - ∫ ω, martingaleSeqTop S 𝓕 P n ω ∂P := by
    simp [integral_congr_ae (martingaleSeqTop_eq_neg_predictableSeqTop 𝓕 hstop n)]
  _ = - ∫ ω, S ⊥ ω ∂P := by
    rw [martingaleSeqTop, ← setIntegral_univ,
      ← (martingale_martingalePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P).setIntegral_eq
      (bot_le (a := ⊤)) MeasurableSet.univ]
    simp [_root_.martingalePart]

/-- Estimate for the hitting event `{τₙ(c) < 1}`. -/
lemma measure_tauMesh_lt_top_le {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
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
      hs.indexComap (Subtype.mono_coe (SetLike.coe (mesh ι n)))
    filter_upwards [hs_mesh.predictablePart_nonneg'] with ω hω using hω ⊤
  _ = ENNReal.ofReal (- ∫ ω, S ⊥ ω ∂P) / ENNReal.ofReal c := by
    rw [integral_predictableSeqTop_eq_neg_integral_bot hstop n]

/-- The terminal values of the predictable parts are uniformly integrable. -/
lemma uniformIntegrable_predictableSeqTop {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hs : Submartingale S 𝓕 P)
    (hd : UniformIntegrable (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}) ↦
      stoppedValue S τ.1) 1 P) (hstop : S ⊤ =ᵐ[P] 0) (ht : ∀ t, S t ≤ᵐ[P] 0) :
    UniformIntegrable (predictableSeqTop S 𝓕 P) 1 P := by
  refine (uniformIntegrable_iff_tendsto_nnReal_iSup_setIntegral_of_nonneg (fun n => ?_)
    (fun n => ?_) (fun n => ?_)).2 ?_
  · exact (stronglyAdapted_predictablePart
      (S ∘ Subtype.val) (meshFiltration 𝓕 n) P).stronglyMeasurable.aestronglyMeasurable
  · have hs_mesh : Submartingale (S ∘ Subtype.val) (meshFiltration 𝓕 n) P :=
      hs.indexComap (Subtype.mono_coe (SetLike.coe (mesh ι n)))
    filter_upwards [hs_mesh.predictablePart_nonneg'] with ω hω using hω ⊤
  · exact integrable_predictableSeqTop S 𝓕 P n
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (a := 0) (h := fun c : ℝ≥0 ↦
      (⨆ k, ENNReal.ofReal (∫ ω in {ω | tauMesh S 𝓕 P k (c / 2) ω < (⊤ : mesh ι k)}, (-2) *
        stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P k (c / 2)) ω ∂P)) +
          ⨆ k, ENNReal.ofReal (∫ ω in {ω | tauMesh S 𝓕 P k c ω < (⊤ : mesh ι k)},
            -stoppedValue (S ∘ Subtype.val) (tauMesh S 𝓕 P k c) ω ∂P)) tendsto_const_nhds ?_ ?_ ?_
    · rw [← zero_add (0 : ℝ≥0∞)]
      apply Tendsto.add
      · -- use `hd` to prove the following two sorries
        sorry
      · sorry
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
          have hmesh : ∀ᵐ ω ∂P, ∀ t : mesh ι k, S t ω ≤ 0 := ae_all_iff.2 fun t => ht t
          apply ENNReal.ofReal_add
          all_goals
            apply integral_nonneg_of_ae
            simp only [stoppedValue, Function.comp_apply]
          · filter_upwards [ae_restrict_of_ae hmesh] with ω hω
            exact mul_nonneg_of_nonpos_of_nonpos (by simp) (hω ((tauMesh S 𝓕 P k (c / 2) ω).untopA))
          · filter_upwards [ae_restrict_of_ae hmesh] with ω hω
            exact neg_nonneg.2 (hω ((tauMesh S 𝓕 P k c ω).untopA))
        _ ≤ _ := iSup_add_le _ _

/-- As the terminal values of predictable parts are uniformly integrable, the terminal values of the
martingale parts are uniformly integrable. -/
lemma uniformIntegrable_martingaleSeqTopAux {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hs : Submartingale S 𝓕 P)
    (hd : UniformIntegrable (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}) ↦
      stoppedValue S τ.1) 1 P) (hstop : S ⊤ =ᵐ[P] 0) (ht : ∀ t, S t ≤ᵐ[P] 0) :
    UniformIntegrable (martingaleSeqTop S 𝓕 P) 1 P := by
  rw [uniformIntegrable_congr_ae (martingaleSeqTop_eq_neg_predictableSeqTop 𝓕 hstop)]
  exact (uniformIntegrable_predictableSeqTop hs hd hstop ht).neg

/-- Prove uniform integrability without the assumption `S ⊤ =ᵐ[P] 0` and `∀ t, S t ≤ᵐ[P] 0`. -/
lemma uniformIntegrable_martingaleSeqTop {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ}
    (hd : UniformIntegrable (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}) ↦
      stoppedValue S τ.1) 1 P) (hs : Submartingale S 𝓕 P) :
    UniformIntegrable (martingaleSeqTop S 𝓕 P) 1 P := by
  have h0 : S = S - (fun i => P[S ⊤ | 𝓕 i]) + (fun i => P[S ⊤ | 𝓕 i]) := by simp
  have h1 (i) : Integrable ((S - fun t => P[S ⊤ | 𝓕 t]) i) P :=
    (hs.integrable i).sub integrable_condExp
  rw [h0, uniformIntegrable_congr_ae (martingaleSeqTop_add 𝓕 h1 (fun i => integrable_condExp))]
  refine UniformIntegrable.add (refl 1) ?_ ?_
  · refine uniformIntegrable_martingaleSeqTopAux ?_ ?_ ?_ fun i => ?_
    · exact hs.sub_martingale (martingale_condExp _ _ _)
    · sorry
    · simp [condExp_of_stronglyMeasurable _ (hs.stronglyMeasurable ⊤) (hs.integrable ⊤)]
    · filter_upwards [hs.ae_le_condExp (i := i) le_top] with ω
      simp
  · rw [uniformIntegrable_congr_ae
      (martingaleSeqTop_eq_self_of_martingale (martingale_condExp (S ⊤) 𝓕 P))]
    exact Integrable.uniformIntegrable_condExp (hs.integrable ⊤) (fun _ => 𝓕.le' ⊤)

end UniformIntegrability

-- We define the martingale part in the doob-meyer decomposition.
section MartingalePartLimDef

/-- Show that the terminals values of some convex combinations of the martingale parts converge. -/
lemma exists_martingalPart_lim {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) :
    ∃ M : Ω → ℝ, ∃ a : ℕ → StdSimplex ℝ ℕ,
      Tendsto (fun n ↦ eLpNorm ((a n).weights.sum (fun m r ↦ r • martingaleSeqTop S 𝓕 P m) - M) 1 P)
      atTop (𝓝 0) := by
  sorry

/-- This is the martingalePart in the doob-meyer decomposition of a submartingale. -/
noncomputable def martingalePartLim {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (i : ι) :=
  P[(exists_martingalPart_lim hd hs).choose | 𝓕 i]

lemma martingale_martingalePartLim {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) :
    Martingale (martingalePartLim hd hs) 𝓕 P :=
  martingale_condExp (exists_martingalPart_lim hd hs).choose 𝓕 P

/-- This is the weight associated with the martingale part. -/
noncomputable def weight {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) : ℕ → StdSimplex ℝ ℕ :=
  (exists_martingalPart_lim hd hs).choose_spec.choose

/-- The extension of the discrete martingale part `M^n`. -/
noncomputable def martingaleSeqStep {ι Ω : Type*} [TopologicalSpace ι] [SecondCountableTopology ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (n : ℕ) (i : ι) :=
  P[martingaleSeqTop S 𝓕 P n | 𝓕 i]

/-- The convexly averaged mesh step-extension `ℳ^n` of the martingale parts. -/
noncomputable def martingaleConvexStep {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) : ι → Ω → ℝ :=
  (weight hd hs n).weights.sum fun m r ↦ r • martingaleSeqStep P S 𝓕 m

/-- `L¹` norm convergence of `martingaleConvexStep`, proved by using conditional Jensen. -/
lemma martingaleConvexStep_eLpNorm_tendsto {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) (t : ι) :
    Tendsto (fun n ↦ eLpNorm
      (martingaleConvexStep hd hs n t - martingalePartLim hd hs t) 1 P) atTop (𝓝 0) := by
  sorry

end MartingalePartLimDef

-- We define the predictable part in the doob-meyer decomposition.
section PredictablePartLimDef

/-- The half-open mesh interval ending at `t`, with left endpoint the predecessor of `t` in the
finite mesh. -/
def meshPredIoc {ι : Type*} [LinearOrder ι] [OrderBot ι] [OrderTop ι] [TopologicalSpace ι]
    [SecondCountableTopology ι] (n : ℕ) (t : mesh ι n) : Set ι :=
  Set.Ioc ((pred t : mesh ι n) : ι) (t : ι)

/-- The mesh step-extension of the discrete predictable part `A^n`. -/
noncomputable def predictableSeqStep {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (n : ℕ) :
    ι → Ω → ℝ :=
  fun t ↦ ∑ u : mesh ι n, (meshPredIoc n u).indicator
    (fun _ : ι ↦ predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P u) t

/-- The convexly averaged mesh step-extension `𝒜^n` of the predictable parts. -/
noncomputable def predictableConvexStep {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) : ι → Ω → ℝ :=
  (weight hd hs n).weights.sum fun m r ↦ r • predictableSeqStep P S 𝓕 m

/-- The predictable part `A` in the Doob-Meyer decomposition, defined as `S - M`. -/
noncomputable def predictablePartLim {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) : ι → Ω → ℝ :=
  S - martingalePartLim hd hs

/-- `L¹` norm convergence of `predictableConvexStep` for `t` in `denseSet ι`. -/
lemma predictableConvexStep_eLpNorm_tendsto {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) {t : ι}
    (ht : t ∈ denseSet ι) :
    Tendsto (fun n ↦ eLpNorm
      (predictableConvexStep hd hs n t - predictablePartLim hd hs t) 1 P) atTop (𝓝 0) := by
  sorry

/-- Almost everywhere convergence of `predictableConvexStep`. -/
lemma predictableConvexStep_ae_tendsto {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) {t : ι}
    (ht : t ∈ denseSet ι) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ predictableConvexStep hd hs (φ n) t ω)
        atTop (𝓝 (predictablePartLim hd hs t ω)) := by
  sorry

end PredictablePartLimDef

-- Helper lemmas about limits of monotone functions.
section MonotoneLim

/-- The limit of a collection of functions that is frequently monotone is monotone. -/
lemma monotone_of_frequently_monotone_of_tendsto {ι α β : Type*} [Preorder α] [TopologicalSpace β]
    [Preorder β] [OrderClosedTopology β] {l : Filter ι} {F : ι → α → β} {f : α → β}
    (hF : ∃ᶠ i in l, Monotone (F i)) (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Monotone f :=
  isClosed_monotone.mem_of_frequently_of_tendsto hF ((tendsto_pi_nhds).2 hlim)

/-- The limit of a collection of functions that is frequently antitone is antitone. -/
lemma antitone_of_frequently_antitone_of_tendsto {ι α β : Type*} [Preorder α] [TopologicalSpace β]
    [Preorder β] [OrderClosedTopology β] {l : Filter ι} {F : ι → α → β} {f : α → β}
    (hF : ∃ᶠ i in l, Antitone (F i)) (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Antitone f :=
  monotone_of_frequently_monotone_of_tendsto (β := βᵒᵈ) hF hlim

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

/-- This is an auxillary lemma used to prove `Dense.monotone_of_isRightContinuous`. It is saying
that if `D` is a dense set and `a, b` are two points such that `a < b`, then the comap of
`𝓝[Set.Ioi a] a` under the inclusion `D → α` is nontrivial. Note that `a < b` is necessary as
this is clearly not true if `a` is a top element. -/
lemma Dense.comap_val_nhdsWithin_Ioi_neBot {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [DenselyOrdered α] {D : Set α} (hD : Dense D) {a b : α} (hab : a < b) :
    ((𝓝[Set.Ioi a] a).comap ((↑) : D → α)).NeBot := by
  refine comap_neBot_iff.2 fun t ht => ?_
  obtain ⟨c, hc⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hab).1 ht
  obtain ⟨d, hd⟩ := hD.inter_open_nonempty (Set.Ioo a c) isOpen_Ioo (Set.nonempty_Ioo.2 hc.1.1)
  exact ⟨⟨d, hd.2⟩, hc.2 hd.1⟩

/-- This is the dual of `Dense.comap_val_nhdsWithin_Ioi_neBot`. -/
lemma Dense.comap_val_nhdsWithin_Iio_neBot {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [DenselyOrdered α] {D : Set α} (hD : Dense D) {a b : α} (hab : b < a) :
    ((𝓝[Set.Iio a] a).comap ((↑) : D → α)).NeBot := by
  refine comap_neBot_iff.2 fun t ht => ?_
  obtain ⟨c, hc⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hab).1 ht
  obtain ⟨d, hd⟩ := hD.inter_open_nonempty (Set.Ioo c a) isOpen_Ioo (Set.nonempty_Ioo.2 hc.1.2)
  exact ⟨⟨d, hd.2⟩, hc.2 hd.1⟩

/-- If `f` is monotone on a dense set `D` and is right continuous, then `f` is monotone. We prove
under the assumption that `α` has a top element `⊤` and `⊤ ∈ D`, which is a necessary assumption
because otherwise it is possible that `⊤` is an isolated point. This theorem should be also true
when `α` satisfies `NoTopOrder α`. -/
lemma Dense.monotone_of_isRightContinuous {α β : Type*} [LinearOrder α] [OrderTop α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [TopologicalSpace β]
    [Preorder β] [t : OrderClosedTopology β] {f : α → β} {D : Set α} (hD : Dense D) (htop : ⊤ ∈ D)
    (hm : Monotone (f ∘ (↑) : D → β)) (hf : f.IsRightContinuous) :
    Monotone f := by
  refine monotone_iff_forall_lt.2 fun a b hab => ?_
  by_cases! hbtop : b = ⊤
  · have : (comap ((↑) : D → α) (𝓝[>] a)).NeBot := hD.comap_val_nhdsWithin_Ioi_neBot hab
    rw [hbtop]
    refine (isClosed_Iic (a := f ⊤)).mem_of_tendsto (Tendsto.comp (hf a)
      (tendsto_comap (f := ((↑) : D → α)))) ?_
    rw [eventually_comap, eventually_nhdsWithin_iff]
    filter_upwards with z hz d rfl using hm (Subtype.mk_le_mk.2 le_top : d ≤ ⟨⊤, htop⟩)
  · -- This part should work when `α` satisfies `NoTopOrder α`.
    let I : D × D → α × α := Prod.map Subtype.val Subtype.val
    have : ((𝓝[Set.Ioi a ×ˢ Set.Ioi b] ⟨a, b⟩).comap I).NeBot := by
      simp only [nhdsWithin_prod_eq, comap_prodMap_prod, I]
      exact (hD.comap_val_nhdsWithin_Ioi_neBot hab).prod
        (hD.comap_val_nhdsWithin_Ioi_neBot hbtop.lt_top)
    have : ∀ᶠ (p : D × D) in (𝓝[Set.Ioi a ×ˢ Set.Ioi b] ⟨a, b⟩).comap I, p.1 ≤ p.2 := by
      rw [eventually_comap, eventually_nhdsWithin_iff]
      have := isOpen_lt_prod.mem_nhds_iff.2 (by simp [hab] : ⟨a, b⟩ ∈ {p : α × α | p.1 < p.2})
      filter_upwards [this] with p hlt _ a rfl using hlt.le
    exact t.isClosed_le'.mem_of_tendsto (Tendsto.comp ((hf a).prodMap (hf b)) tendsto_comap)
      (this.mono fun d hd => hm hd)

/-- A helper lemma. -/
lemma Filter.IsCoboundedUnder.trans {ι α : Type*} {r : α → α → Prop} {l : Filter ι} [l.NeBot]
    [IsTrans α r] {u v : ι → α} (hle : ∀ᶠ i in l, r (u i) (v i)) (h : IsCoboundedUnder r l u) :
    IsCoboundedUnder r l v := by
  simp only [IsCoboundedUnder, IsCobounded, eventually_map] at *
  obtain ⟨b, hb⟩ := h
  refine ⟨b, fun a ha => hb a ?_⟩
  filter_upwards [ha, hle] with i hi huv using Trans.trans huv hi

/-- Convergence on a dense set of a collection of monotone function controls the `limsup` at a point
if `f` is right continuous at `a`. We prove this under the assumption that `α` has both a bottom
element and a top element. The bottom element is needed because otherwise `limsup` evaluated at the
bottome element may give a junk value to break the inequality. -/
lemma limsup_le_of_eventually_monotone_of_tendsto_on_dense {ι α β : Type*} [LinearOrder α]
    [BoundedOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {l : Filter ι}
    [l.NeBot] {D : Set α} {F : ι → α → β} {f : α → β} (hF : ∀ᶠ i in l, Monotone (F i))
    (hD : Dense D) (htop : ⊤ ∈ D) (hbot : ⊥ ∈ D) {a : α} (hfa : ContinuousWithinAt f (Set.Ioi a) a)
    (hlim : ∀ t ∈ D, Tendsto (F · t) l (𝓝 (f t))) :
    limsup (F · a) l ≤ f a := by
  by_cases! ha : a = ⊤
  · rw [ha, (hlim ⊤ htop).limsup_eq]
  · have : (comap ((↑) : D → α) (𝓝[>] a)).NeBot := hD.comap_val_nhdsWithin_Ioi_neBot ha.lt_top
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
    [BoundedOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {l : Filter ι}
    [l.NeBot] {D : Set α} {F : ι → α → β} {f : α → β} (hF : ∀ᶠ i in l, Monotone (F i))
    (hD : Dense D) (htop : ⊤ ∈ D) (hbot : ⊥ ∈ D) {a : α} (hfa : ContinuousWithinAt f (Set.Iio a) a)
    (hlim : ∀ t ∈ D, Tendsto (F · t) l (𝓝 (f t))) :
    f a ≤ liminf (F · a) l := by
  by_cases! ha : a = ⊥
  · rw [ha, (hlim ⊥ hbot).liminf_eq]
  · have : (comap ((↑) : D → α) (𝓝[<] a)).NeBot := hD.comap_val_nhdsWithin_Iio_neBot ha.bot_lt
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
    [BoundedOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {l : Filter ι}
    [l.NeBot] {D : Set α} {F : ι → α → β} {f : α → β} (hF : ∀ᶠ i in l, Monotone (F i))
    (hD : Dense D) (htop : ⊤ ∈ D) (hbot : ⊥ ∈ D) (a : α) (hfa : ContinuousAt f a)
    (hlim : ∀ t ∈ D, Tendsto (F · t) l (𝓝 (f t))) :
    Tendsto (F · a) l (𝓝 (f a)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ ?_ ?_
  · exact le_liminf_of_eventually_monotone_of_tendsto_on_dense hF hD htop hbot
      hfa.continuousWithinAt hlim
  · exact limsup_le_of_eventually_monotone_of_tendsto_on_dense hF hD htop hbot
      hfa.continuousWithinAt hlim
  · -- create an analogue of `Filter.IsCoboundedUnder.trans` for `IsBoundedUnder` to replace
    -- `isBoundedUnder_le.mono_le`
    refine (hlim ⊤ htop).isBoundedUnder_le.mono_le ?_
    filter_upwards [hF] with i hi using hi le_top
  · refine (hlim ⊥ hbot).isBoundedUnder_ge.mono_ge ?_
    filter_upwards [hF] with i hi using hi bot_le

end MonotoneLim

section PredictablePartLimMono

lemma predictableSeqStep_eq_sum_indicator {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (S : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (n : ℕ) (ω : Ω) (t : ι) :
    predictableSeqStep P S 𝓕 n t ω = ∑ v : mesh ι n, (meshPredIoc n v).indicator
      (fun _ : ι ↦ predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P v ω) t := by
  simp only [predictableSeqStep, Finset.sum_apply]
  exact Finset.sum_congr rfl fun v _ ↦ Set.indicator_apply_apply _ _ t ω

lemma predictableSeqStep_monotone_ae {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hs : Submartingale S 𝓕 P) (n : ℕ) (t : ι) :
    ∀ᵐ ω ∂P, Monotone fun t ↦ predictableSeqStep P S 𝓕 n t ω := by
  sorry

lemma predictableConvexStep_monotone_ae {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) (t : ι) :
    ∀ᵐ ω ∂P, Monotone fun t ↦ predictableConvexStep hd hs n t ω := by
  sorry

lemma predictablePartLim_monotone_ae {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) (t : ι) :
    ∀ᵐ ω ∂P, Monotone fun t ↦ predictablePartLim hd hs t ω := by
  sorry

end PredictablePartLimMono

section PredictableConvexStepPredictable

/-- The indicator of a half-open interval `Ioc a b` with constant value `c` is left-continuous:
when approached from the left it is eventually constant, so it is continuous within `Iio t` at `t`
for every `t`. -/
lemma continuousWithinAt_Iio_indicator_Ioc {α M : Type*} [LinearOrder α] [TopologicalSpace α]
    [ClosedIicTopology α] [Zero M] [TopologicalSpace M] (a b : α) (c : M) (t : α) :
    ContinuousWithinAt ((Set.Ioc a b).indicator (fun _ ↦ c)) (Set.Iio t) t := by
  refine continuousWithinAt_const.congr_of_eventuallyEq ?_ rfl
  rcases le_or_gt t a with hta | hat
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp_all [hx.le.trans hta]
  · rcases le_or_gt t b with htb | hbt
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hat)]
        with x hx_lt hx_gt
      simp_all [hx_lt.le.trans htb]
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hbt)] with x hx_gt
      simp_all

/-- The mesh step-extension of the discrete predictable part is left-continuous in time. -/
lemma predictableSeqStep_leftContinuous {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [ClosedIicTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (n : ℕ) (ω : Ω) (t : ι) :
    ContinuousWithinAt (fun s ↦ predictableSeqStep P S 𝓕 n s ω) (Set.Iio t) t := by
  have hrw : (fun s ↦ predictableSeqStep P S 𝓕 n s ω)
      = fun s ↦ ∑ u : mesh ι n, (meshPredIoc n u).indicator
          (fun _ : ι ↦ predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P u ω) s := by
    funext s
    simp only [predictableSeqStep, Finset.sum_apply]
    exact Finset.sum_congr rfl fun u _ ↦ Set.indicator_apply_apply _ _ s ω
  rw [hrw]
  exact tendsto_finsetSum _ fun u _ ↦ continuousWithinAt_Iio_indicator_Ioc _ _ _ t

/-- `predictableConvexStep` is left-continuous in time. -/
lemma predictableConvexStep_leftContinuous {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [ClosedIicTopology ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) (ω : Ω) (t : ι) :
    ContinuousWithinAt (fun s ↦ predictableConvexStep hd hs n s ω) (Set.Iio t) t := by
  have hrw : (fun s ↦ predictableConvexStep hd hs n s ω)
      = fun s ↦ ∑ m ∈ (weight hd hs n).weights.support,
          (weight hd hs n).weights m • predictableSeqStep P S 𝓕 m s ω := by
    funext s
    simp only [predictableConvexStep, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
  rw [hrw]
  exact tendsto_finsetSum _ fun m _ ↦ (predictableSeqStep_leftContinuous m ω t).const_smul _

/-- The mesh step-extension of the discrete predictable part is strongly adapted. -/
lemma stronglyAdapted_predictableSeqStep {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P] (S : ι → Ω → ℝ)
    (𝓕 : Filtration ι mΩ) (n : ℕ) :
    StronglyAdapted 𝓕 (predictableSeqStep P S 𝓕 n) := by
  refine fun t => Finset.stronglyMeasurable_sum _ fun u _ => ?_
  by_cases htu : t ∈ meshPredIoc n u
  · have : meshFiltration 𝓕 n (pred u) ≤ 𝓕 t := by simpa [meshFiltration] using 𝓕.mono htu.1.le
    simpa [htu] using (stronglyMeasurable_pred_predictablePart (S ∘ Subtype.val)
      (meshFiltration 𝓕 n) P u).mono this
  · simpa [htu] using stronglyMeasurable_zero

/-- The convexly averaged mesh step-extension of the predictable parts is strongly adapted. -/
lemma stronglyAdapted_predictableConvexStep {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) :
    StronglyAdapted 𝓕 (predictableConvexStep hd hs n) := by
  intro t
  simpa [predictableConvexStep, Finsupp.sum] using
    Finset.stronglyMeasurable_sum ((weight hd hs n).weights.support) fun m _hm ↦
      (stronglyAdapted_predictableSeqStep P S 𝓕 m t).const_smul ((weight hd hs n).weights m)

/-- The convexly averaged mesh step-extension of the predictable parts is strongly predictable. -/
lemma isStronglyPredictable_predictableConvexStep {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] [DenselyOrdered ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) (n : ℕ) :
    IsStronglyPredictable 𝓕 (predictableConvexStep hd hs n) :=
  (stronglyAdapted_predictableConvexStep hd hs n).isStronglyPredictable_of_leftContinuous
    (predictableConvexStep_leftContinuous hd hs n)

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
    [T1Space ι] [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι]
    [OrderTop ι] [OrderTopology ι] [DenselyOrdered ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) :
    IsStronglyPredictable 𝓕 (fun t ω => limsup (predictableConvexStep hd hs · t ω) atTop) :=
  IsStronglyPredictable.limsup fun n => isStronglyPredictable_predictableConvexStep hd hs n

/-- For each stopping time `τ`, `limsup (fun n => stoppedValue 𝒜^n τ) atTop ≤ stoppedValue A τ`
almost everywhere. Use `limsup_le_of_eventually_monotone_of_tendsto_on_dense`. -/
lemma limsup_stoppedValue_predictableConvexStep_ae_le_stoppedValue_predictablePartLim {ι Ω : Type*}
    [TopologicalSpace ι] [T1Space ι] [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι]
    [OrderBot ι] [OrderTop ι] [OrderTopology ι] [DenselyOrdered ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ)
    (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    limsup (fun n => stoppedValue (predictableConvexStep hd hs n) τ) atTop ≤ᵐ[P]
      stoppedValue (predictablePartLim hd hs) τ := by
  sorry

/-- Prove that `∫ ω, stoppedValue 𝒜^n τ ω ∂P` converges to `∫ ω, stoppedValue A τ ω ∂P`. -/
lemma integral_stoppedValue_predictableConvexStep_tendsto_stoppedValue_predictablePartLim
    {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι] [SecondCountableTopology ι] [MeasurableSpace ι]
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [OrderTopology ι] [DenselyOrdered ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime 𝓕 τ) :
    Tendsto (fun n => ∫ ω, stoppedValue (predictableConvexStep hd hs n) τ ω ∂P) atTop
      (𝓝 <| ∫ ω, stoppedValue (predictablePartLim hd hs) τ ω ∂P) := by
  sorry

/-- Reverse Fatou's lemma. See also `limsup_lintegral_le`. -/
lemma limsup_integral_le_integral_limsup_of_tendsto_integral_posPart_sub {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX_nonneg : ∀ n, 0 ≤ᵐ[P] X n) (hY : Integrable Y P) (hY_nonneg : 0 ≤ᵐ[P] Y)
    (h_tendsto : Tendsto (fun n => ∫ ω, max (X n ω - Y ω) 0 ∂P) atTop (𝓝 0)) :
    limsup (fun n => ∫ ω, X n ω ∂P) atTop ≤ ∫ ω, limsup (fun n => X n ω) atTop ∂P := by
  sorry

/-- For each stopping time `τ`, `limsup (fun n => stoppedValue 𝒜^n τ) atTop = stoppedValue A τ`
almost everywhere. -/
lemma limsup_stoppedValue_predictableConvexStep_ae_eq_stoppedValue_predictablePartLim {ι Ω : Type*}
    [TopologicalSpace ι] [T1Space ι] [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι]
    [OrderBot ι] [OrderTop ι] [OrderTopology ι] [DenselyOrdered ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ)
    (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    limsup (fun n => stoppedValue (predictableConvexStep hd hs n) τ) atTop =ᵐ[P]
      stoppedValue (predictablePartLim hd hs) τ := by
  refine (integral_eq_iff_of_ae_le ?_ ?_ ?_).1 ?_
  · -- maybe it is better to first prove an analogue of `ae_eq_of_ae_le_of_lintegral_le` that
    -- asssumes `0 ≤ f` instead of integrability of `f`.
    sorry
  · sorry
  · exact
      limsup_stoppedValue_predictableConvexStep_ae_le_stoppedValue_predictablePartLim hd hs hτ hc
  · refine le_antisymm ?_ ?_
    · refine integral_mono_of_nonneg ?_ ?_ ?_
      · sorry
      · sorry
      · exact (limsup_stoppedValue_predictableConvexStep_ae_le_stoppedValue_predictablePartLim
          hd hs hτ hc)
    · calc
      ∫ ω, stoppedValue (predictablePartLim hd hs) τ ω ∂P =
        limsup (fun n => ∫ ω, stoppedValue (predictableConvexStep hd hs n) τ ω ∂P) atTop :=
        ((integral_stoppedValue_predictableConvexStep_tendsto_stoppedValue_predictablePartLim
          hd hs hτ).limsup_eq).symm
        -- Use Fatou's lemma for the following sorry
        -- We use integral instead of lintegral because
        -- 1. `ae_eq_of_ae_le_of_lintegral_le` is the analogue of `ae_eq_of_ae_le_of_lintegral_le`,
        -- but it still requires a proof that the lintegral is not equal to infinity.
        -- 2. these processes are naturally real valued.
        -- 3. I think it is useful to prove reverse Fatou's lemma for integral as one should be
        -- able to apply for functions taking negative values.
      _ ≤ _ := by sorry

/-- Show that `fun t ω => limsup (predictableConvexStep hd hs · t ω` and `predictablePartLim hd hs`
are indistinguishable. -/
lemma limsup_predictableConvexStep_eq_predictablePartLim {ι Ω : Type*}
    [TopologicalSpace ι] [T1Space ι] [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι]
    [OrderBot ι] [OrderTop ι] [OrderTopology ι] [DenselyOrdered ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    ∀ᵐ ω ∂P, ∀ t, limsup (predictableConvexStep hd hs · t ω) atTop =
      predictablePartLim hd hs t ω := by
  sorry

end PredictablePartIsStronglyPredictable

section DoobMeyer

theorem ClassD.doob_meyer {ι Ω : Type*} [TopologicalSpace ι] [T1Space ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [SuccOrder ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} (hs : Submartingale S 𝓕 P) :
    ∃ (M A : ι → Ω → ℝ), S = M + A ∧ Martingale M 𝓕 P ∧ (∀ ω, IsCadlag (M · ω)) ∧
      IsStronglyPredictable 𝓕 A ∧ (∀ ω, IsCadlag (A · ω)) ∧ (∀ ω, Monotone (A · ω)) := by
  sorry

end DoobMeyer

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
  [MeasurableSpace ι]

namespace ProbabilityTheory

namespace IsLocalSubmartingale

theorem doob_meyer (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∃ (M A : ι → Ω → ℝ), X = M + A ∧ IsLocalMartingale M 𝓕 P ∧ (∀ ω, IsCadlag (M · ω)) ∧
      IsStronglyProgressive 𝓕 A ∧ (∀ ω, IsCadlag (A · ω)) ∧ (HasLocallyIntegrableSup A 𝓕 P)
      ∧ (∀ ω, Monotone (A · ω)) := by
  sorry

/-- The local martingale part of the Doob-Meyer decomposition of the local submartingale. -/
noncomputable
def martingalePart (X : ι → Ω → ℝ)
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ :=
  (hX.doob_meyer hX_cadlag).choose

/-- The predictable part of the Doob-Meyer decomposition of the local submartingale. -/
noncomputable
def predictablePart (X : ι → Ω → ℝ)
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose

lemma martingalePart_add_predictablePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    X = hX.martingalePart X hX_cadlag + hX.predictablePart X hX_cadlag :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.1

lemma isLocalMartingale_martingalePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    IsLocalMartingale (hX.martingalePart X hX_cadlag) 𝓕 P :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.1

lemma cadlag_martingalePart (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∀ ω, IsCadlag (hX.martingalePart X hX_cadlag · ω) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.1

lemma isStronglyProgressive_predictablePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    IsStronglyProgressive 𝓕 (hX.predictablePart X hX_cadlag) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.1

lemma cadlag_predictablePart (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∀ ω, IsCadlag (hX.predictablePart X hX_cadlag · ω) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.1

lemma hasLocallyIntegrableSup_predictablePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    HasLocallyIntegrableSup (hX.predictablePart X hX_cadlag) 𝓕 P :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.2.1

lemma monotone_predictablePart (hX : IsLocalSubmartingale X 𝓕 P)
    (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∀ ω, Monotone (hX.predictablePart X hX_cadlag · ω) :=
  (hX.doob_meyer hX_cadlag).choose_spec.choose_spec.2.2.2.2.2.2

end IsLocalSubmartingale

end ProbabilityTheory
