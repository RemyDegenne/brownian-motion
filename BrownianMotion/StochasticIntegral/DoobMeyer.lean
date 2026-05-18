/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.ClassD
public import BrownianMotion.StochasticIntegral.Komlos
public import Mathlib.Order.Interval.Finset.SuccPred

/-! # Doob-Meyer decomposition theorem

-/

@[expose] public section

open MeasureTheory Filter Order
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

namespace DoobMeyer

section DenseMesh

variable (ι) [LinearOrder ι] [OrderBot ι] [OrderTop ι] [TopologicalSpace ι]
  [SecondCountableTopology ι]

/-- The fixed countable dense set used instead of dyadics, with both endpoints adjoined. -/
noncomputable def denseSet : Set ι :=
  (TopologicalSpace.exists_countable_dense ι).choose ∪ ({⊥, ⊤} : Set ι)

lemma denseSet_countable : (denseSet ι).Countable := by
  have h_dense_countable := (TopologicalSpace.exists_countable_dense ι).choose_spec.1
  simpa [denseSet] using h_dense_countable.union (by simp : ({⊥, ⊤} : Set ι).Countable)

lemma denseSet_dense : Dense (denseSet ι) :=
  (TopologicalSpace.exists_countable_dense ι).choose_spec.2.mono (Set.subset_union_left)

/-- A choice of enumeration of the countable dense set used to construct finite meshes. -/
noncomputable def denseEnum : ℕ → ι :=
  have : Nonempty (denseSet ι) := ⟨⟨⊥, by simp [denseSet]⟩⟩
  Subtype.val ∘ (countable_iff_exists_surjective.mp (denseSet_countable ι)).choose

lemma denseEnum_mem (n : ℕ) : denseEnum ι n ∈ denseSet ι :=
  letI : Nonempty (denseSet ι) := ⟨⟨⊥, by simp [denseSet]⟩⟩
  ((countable_iff_exists_surjective.mp (denseSet_countable ι)).choose n).property

lemma exists_denseEnum_eq_of_mem {t : ι} (ht : t ∈ denseSet ι) :
    ∃ n, denseEnum ι n = t := by
  letI : Nonempty (denseSet ι) := ⟨⟨⊥, by simp [denseSet]⟩⟩
  obtain ⟨n, hn⟩ :=
    (countable_iff_exists_surjective.mp (denseSet_countable ι)).choose_spec ⟨t, ht⟩
  exact ⟨n, congrArg Subtype.val hn⟩

/-- The `n`-th finite mesh: the first `n` points of the dense enumeration, plus endpoints. -/
noncomputable def mesh (n : ℕ) : Finset ι :=
  insert ⊥ <| insert ⊤ <| (Finset.range n).image (denseEnum ι)

lemma bot_mem_mesh (n : ℕ) : (⊥ : ι) ∈ mesh ι n := by simp [mesh]

lemma top_mem_mesh (n : ℕ) : (⊤ : ι) ∈ mesh ι n := by simp [mesh]

instance (n : ℕ) : OrderBot (mesh ι n) where
  bot := ⟨⊥, bot_mem_mesh ι n⟩
  bot_le _ := bot_le

instance (n : ℕ) : OrderTop (mesh ι n) where
  top := ⟨⊤, top_mem_mesh ι n⟩
  le_top _ := le_top

@[simp]
lemma coe_mesh_bot (n : ℕ) : ((⊥ : mesh ι n) : ι) = ⊥ :=
  rfl

@[simp]
lemma coe_mesh_top (n : ℕ) : ((⊤ : mesh ι n) : ι) = ⊤ :=
  rfl

noncomputable instance (n : ℕ) : LocallyFiniteOrder (mesh ι n) :=
  Fintype.toLocallyFiniteOrder

noncomputable instance (n : ℕ) : SuccOrder (mesh ι n) :=
  LinearLocallyFiniteOrder.succOrder (mesh ι n)

lemma mesh_subset_denseSet (n : ℕ) : ↑(mesh ι n) ⊆ denseSet ι := by
  intro t ht
  simp only [mesh, Finset.mem_coe, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at ht
  rcases ht with rfl | rfl | ⟨k, -, rfl⟩
  · simp [denseSet]
  · simp [denseSet]
  · exact denseEnum_mem ι k

lemma mesh_mono {n m : ℕ} (hnm : n ≤ m) : mesh ι n ⊆ mesh ι m := by
  intro t ht
  simp only [mesh, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at ht ⊢
  rcases ht with rfl | rfl | ⟨k, hk, rfl⟩
  · simp
  · simp
  · exact Or.inr <| Or.inr ⟨k, lt_of_lt_of_le hk hnm, rfl⟩

lemma mesh_subset_succ (n : ℕ) : mesh ι n ⊆ mesh ι (n + 1) :=
  mesh_mono ι n.le_succ

noncomputable def meshSet : Set ι :=
  {t | ∃ n : ℕ, t ∈ mesh ι n}

lemma mem_meshSet_iff {t : ι} : t ∈ meshSet ι ↔ t ∈ denseSet ι := by
  refine ⟨?_, ?_⟩
  · rintro ⟨n, ht⟩
    exact mesh_subset_denseSet ι n ht
  · intro ht
    obtain ⟨n, hn⟩ := exists_denseEnum_eq_of_mem ι ht
    refine ⟨n + 1, ?_⟩
    simp only [mesh, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
    exact Or.inr <| Or.inr ⟨n, by simp, hn⟩

lemma dense_meshSet : Dense (meshSet ι) := by
  rw [dense_iff_closure_eq]
  calc
    closure (meshSet ι)
        = closure (denseSet ι) := by
          congr 1
          ext t
          exact mem_meshSet_iff ι
    _ = Set.univ := (denseSet_dense ι).closure_eq

end DenseMesh

section DiscreteDecomposition

variable {κ : Type*} [LinearOrder κ] [OrderBot κ] [LocallyFiniteOrder κ] [SuccOrder κ]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Predictable part of a discrete process indexed by a locally finite successor order.

On a finite mesh this is the usual Doob decomposition increment
`A_{succ i} - A_i = E[S_{succ i} - S_i | 𝓕_i]`, summed over all mesh points before the
current time. -/
noncomputable def predictablePart (S : κ → Ω → E) (𝓕 : Filtration κ mΩ) (P : Measure Ω) :
    κ → Ω → E :=
  fun t ↦ ∑ i ∈ Finset.Iio t, P[S (succ i) - S i | 𝓕 i]

/-- Martingale part of a discrete process. -/
noncomputable def martingalePart (S : κ → Ω → E) (𝓕 : Filtration κ mΩ) (P : Measure Ω) :
    κ → Ω → E :=
  S - predictablePart S 𝓕 P

@[simp]
lemma predictablePart_bot (S : κ → Ω → E) (𝓕 : Filtration κ mΩ) :
    predictablePart S 𝓕 P ⊥ = 0 := by
  simp [predictablePart]

lemma martingalePart_add_predictablePart (S : κ → Ω → E) (𝓕 : Filtration κ mΩ) :
    martingalePart S 𝓕 P + predictablePart S 𝓕 P = S :=
  sub_add_cancel _ _

lemma stronglyAdapted_predictablePart (S : κ → Ω → E) (𝓕 : Filtration κ mΩ) :
    StronglyAdapted 𝓕 (predictablePart S 𝓕 P) := by
  intro t
  exact Finset.stronglyMeasurable_sum _ fun i hi ↦
    stronglyMeasurable_condExp.mono (𝓕.mono (le_of_lt (Finset.mem_Iio.mp hi)))

lemma stronglyAdapted_predictablePart_succ (S : κ → Ω → E) (𝓕 : Filtration κ mΩ) :
    StronglyAdapted 𝓕 fun t ↦ predictablePart S 𝓕 P (succ t) := by
  intro t
  exact Finset.stronglyMeasurable_sum _ fun i hi ↦
    stronglyMeasurable_condExp.mono (𝓕.mono (le_of_lt_succ (Finset.mem_Iio.mp hi)))

lemma predictablePart_succ_of_not_isMax (S : κ → Ω → E) (𝓕 : Filtration κ mΩ)
    {t : κ} (ht : ¬ IsMax t) :
    predictablePart S 𝓕 P (succ t)
      = predictablePart S 𝓕 P t + P[S (succ t) - S t | 𝓕 t] := by
  classical
  rw [predictablePart, Finset.Iio_succ_eq_Iic_of_not_isMax ht, ← Finset.Iio_insert t,
    Finset.sum_insert]
  · simp [predictablePart, add_comm]
  · simp

end DiscreteDecomposition

section MeshApproximation

variable {ι : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι]
  [LinearOrder ι] [OrderBot ι] [OrderTop ι]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The filtration obtained by restricting `𝓕` to a finite dense mesh. -/
def meshFiltration (𝓕 : Filtration ι mΩ) (n : ℕ) :
    Filtration (mesh ι n) mΩ :=
  𝓕.indexComap (Subtype.mono_coe (SetLike.coe (mesh ι n)))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Sequence of terminal values the predictable part. -/
noncomputable def predictableSeq (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) :=
  predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⊤

/-- Sequence of terminal values the martingale part. -/
noncomputable def martingaleSeq (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) :=
  martingalePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⊤

variable {S : ι → Ω → E} [LE E] {𝓕 : Filtration ι mΩ}

omit [MeasurableSpace ι] in
lemma submartingale_mesh (hs : Submartingale S 𝓕 P) (n : ℕ) :
    Submartingale (S ∘ Subtype.val) (meshFiltration 𝓕 n) P :=
  hs.indexComap (Subtype.mono_coe (SetLike.coe (mesh ι n)))

/-- The terminal values of the predictable parts are uniformly integrable. -/
lemma uniformIntegrable_terminal_predictablePart (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) :
    UniformIntegrable (predictableSeq S 𝓕 P) 1 P := by
  sorry

private lemma UniformIntegrable.neg {α β γ : Type*} [MeasurableSpace β] [NormedAddCommGroup γ]
    {f : α → β → γ} {p : ℝ≥0∞} {μ : Measure β} (hf : UniformIntegrable f p μ) :
    UniformIntegrable (-f) p μ :=
  uniformIntegrable_of_dominated hf (fun i ↦ (hf.aestronglyMeasurable i).neg)
    fun i ↦ ⟨i, by simp⟩

/-- As the terminal values of predictable parts are uniformly integrable, the terminal values of the
martingale parts are uniformly integrable. -/
lemma uniformIntegrable_terminal_martingalePart_of_predictablePart (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) :
    UniformIntegrable (martingaleSeq S 𝓕 P) 1 P := by
  have hS_top : UniformIntegrable (fun _ : ℕ ↦ S ⊤) 1 P :=
    hd.uniformIntegrable'.comp fun _ : ℕ ↦ (⊤ : ι)
  have hA : UniformIntegrable (predictableSeq S 𝓕 P) 1 P :=
    uniformIntegrable_terminal_predictablePart hs hc hd
  refine (hS_top.add le_rfl (UniformIntegrable.neg hA)).ae_eq ?_
  intro n
  filter_upwards with ω
  simp [martingaleSeq, martingalePart, predictableSeq, sub_eq_add_neg]

/-- Show that the terminals values of the martingale parts converge. -/
lemma exists_martingalPart_lim (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) :
    ∃ M : Ω → E, ∃ a : ℕ → StdSimplex ℝ ℕ,
      (∀ n, ∀ m < n, (a n).weights m = 0) ∧
      Tendsto (fun n ↦ eLpNorm ((a n).sum (fun m r ↦ r • martingaleSeq S 𝓕 P m) - M) 1 P)
      atTop (𝓝 0) := by
  sorry

/-- This is the martingalePart in the doob-meyer decomposition of a submartingale. -/
noncomputable def martingalePartLim (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) (i : ι) :=
  P[(exists_martingalPart_lim hs hc hd).choose | 𝓕 i]

lemma martingale_martingalePart (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) (i : ι) :
    Martingale (martingalePartLim hs hc hd) 𝓕 P := by
  sorry

/-- This is the weight associated with the martingale part. -/
noncomputable def weight (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) :=
  (exists_martingalPart_lim hs hc hd).choose_spec.choose

lemma weight_zero_of_lt (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) :
    ∀ n, ∀ m < n, ((weight hs hc hd) n).weights m = 0 :=
  (exists_martingalPart_lim hs hc hd).choose_spec.choose_spec.1

lemma tendsto_weighted_martingaleSeq (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) :
    Tendsto (fun n ↦ eLpNorm (((weight hs hc hd) n).sum
      (fun m r ↦ r • martingaleSeq S 𝓕 P m) - (exists_martingalPart_lim hs hc hd).choose)
      1 P) atTop (𝓝 0) :=
  (exists_martingalPart_lim hs hc hd).choose_spec.choose_spec.2

end MeshApproximation

end DoobMeyer

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
  [MeasurableSpace ι]

namespace IsLocalSubmartingale

theorem doob_meyer (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ∃ (M A : ι → Ω → ℝ), X = M + A ∧ IsLocalMartingale M 𝓕 P ∧ (∀ ω, IsCadlag (M · ω)) ∧
      IsPredictable 𝓕 A ∧ (∀ ω, IsCadlag (A · ω)) ∧ (HasLocallyIntegrableSup A 𝓕 P)
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

lemma isPredictable_predictablePart
    (hX : IsLocalSubmartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    IsPredictable 𝓕 (hX.predictablePart X hX_cadlag) :=
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
