/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.ClassD
public import BrownianMotion.StochasticIntegral.Komlos

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

end DenseMesh

section UniformIntegrability

variable {ι : Type*} [TopologicalSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι]
  [LinearOrder ι] [OrderBot ι] [OrderTop ι] [LocallyFiniteOrder ι] [SuccOrder ι]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The filtration obtained by restricting `𝓕` to a finite dense mesh. -/
def meshFiltration (𝓕 : Filtration ι mΩ) (n : ℕ) :
    Filtration (mesh ι n) mΩ :=
  𝓕.indexComap (Subtype.mono_coe (SetLike.coe (mesh ι n)))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Predictable part of a discrete process. -/
noncomputable def predictablePart (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    ι → Ω → E :=
  fun n ↦ ∑ i ∈ Finset.Iio n, P[S (succ i) - S i | 𝓕 i]

/-- Martingale part of a discrete process. -/
noncomputable def martingalePart (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    ι → Ω → E :=
  S - predictablePart S 𝓕 P

/-- Sequence of terminal values the predictable part. -/
noncomputable def predictableSeq (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) :=
  predictablePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⊤

/-- Sequence of terminal values the martingale part. -/
noncomputable def martingaleSeq (S : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) (n : ℕ) :=
  martingalePart (S ∘ Subtype.val) (meshFiltration 𝓕 n) P ⊤

variable {S : ι → Ω → E} [LE E] {𝓕 : Filtration ι mΩ}

/-- The terminal values of the predictable parts are uniformly integrable. -/
lemma uniformIntegrable_terminal_predictablePart (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) :
    UniformIntegrable (predictableSeq S 𝓕 P) 1 P := by
  sorry

/-- As the terminal values of predictable parts are uniformly integrable, the terminal values of the
martingale parts are uniformly integrable. -/
lemma uniformIntegrable_terminal_martingalePart_of_predictablePart (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) :
    UniformIntegrable (martingaleSeq S 𝓕 P) 1 P := by
  sorry

/-- Show that the terminals values of the martingale parts converge. -/
lemma exists_martingalPart_lim (hs : Submartingale S 𝓕 P)
    (hc : ∀ ω, IsCadlag (S · ω)) (hd : ClassD S 𝓕 P) :
    ∃ M : Ω → E, ∃ a : ℕ → StdSimplex ℝ ℕ,
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

end UniformIntegrability

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
