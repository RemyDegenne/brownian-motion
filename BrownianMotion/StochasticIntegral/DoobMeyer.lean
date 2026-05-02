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

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
  [MeasurableSpace ι]

namespace DoobMeyer

section DenseMesh

variable [OrderTop ι] [SecondCountableTopology ι]

/-- The fixed countable dense set used instead of dyadics, with both endpoints adjoined. -/
noncomputable def denseSet : Set ι :=
  (TopologicalSpace.exists_countable_dense ι).choose ∪ ({⊥, ⊤} : Set ι)

lemma denseSet_countable : (denseSet (ι := ι)).Countable := by
  sorry

lemma denseSet_dense : Dense (denseSet (ι := ι)) := by
  sorry

/-- A choice of enumeration of the countable dense set used to construct finite meshes. -/
noncomputable def denseEnum : ℕ → ι := by
  classical
  haveI : Nonempty (denseSet (ι := ι)) := ⟨⟨⊥, by simp [denseSet]⟩⟩
  exact Subtype.val ∘ (countable_iff_exists_surjective.mp (denseSet_countable (ι := ι))).choose

/-- The `n`-th finite mesh: the first `n` points of the dense enumeration, plus endpoints. -/
noncomputable def mesh (n : ℕ) : Finset ι := by
  classical
  exact insert ⊥ <| insert ⊤ <| (Finset.range n).image (denseEnum (ι := ι))

/-- The finite ordered index type carried by the `n`-th mesh. -/
abbrev MeshIdx (n : ℕ) : Type _ :=
  {t : ι // t ∈ mesh (ι := ι) n}

lemma mesh_mono {n m : ℕ} (hnm : n ≤ m) : mesh (ι := ι) n ⊆ mesh (ι := ι) m := by
  sorry

lemma bot_mem_mesh (n : ℕ) : (⊥ : ι) ∈ mesh (ι := ι) n := by
  sorry

lemma top_mem_mesh (n : ℕ) : (⊤ : ι) ∈ mesh (ι := ι) n := by
  sorry

lemma dense_iUnion_mesh : Dense (⋃ n, (mesh (ι := ι) n : Set ι)) := by
  sorry

lemma eventually_mem_mesh_of_mem_denseSet {t : ι} (ht : t ∈ denseSet (ι := ι)) :
    ∀ᶠ n in atTop, t ∈ mesh (ι := ι) n := by
  sorry

end DenseMesh

section MeshDecomposition

variable [OrderTop ι] [SecondCountableTopology ι] {S : ι → Ω → ℝ}

/-- The filtration obtained by restricting `𝓕` to a finite dense mesh. -/
noncomputable def meshFiltration (𝓕 : Filtration ι mΩ) (n : ℕ) :
    Filtration (MeshIdx (ι := ι) n) mΩ :=
  𝓕.indexComap (f := fun t : MeshIdx (ι := ι) n ↦ (t : ι))
    (Subtype.mono_coe (p := fun t : ι ↦ t ∈ mesh (ι := ι) n))

/-- The process obtained by restricting `S` to a finite dense mesh. -/
def meshProcess (S : ι → Ω → ℝ) (n : ℕ) :
    MeshIdx (ι := ι) n → Ω → ℝ :=
  fun t ω ↦ S t ω

lemma submartingale_meshProcess (hS : Submartingale S 𝓕 P) (n : ℕ) :
    Submartingale (meshProcess (ι := ι) S n) (meshFiltration 𝓕 n) P := by
  sorry

/-- Statement-level placeholder for the generalized finite-mesh Doob decomposition.

Once mathlib PR #31008 is available, `A` and `M` should be `MeasureTheory.predictablePart` and
`MeasureTheory.martingalePart` for `meshProcess S n`. -/
lemma exists_mesh_decomposition
    (hS : Submartingale S 𝓕 P) (n : ℕ) :
    ∃ A M : MeshIdx (ι := ι) n → Ω → ℝ,
      meshProcess (ι := ι) S n = M + A ∧
      Martingale M (meshFiltration 𝓕 n) P ∧
      A ⟨⊥, bot_mem_mesh (ι := ι) n⟩ = 0 ∧
      (∀ᵐ ω ∂P, Monotone (fun t ↦ A t ω)) := by
  sorry

/-- The terminal value of a mesh-indexed process. -/
def terminalValue {n : ℕ} (Y : MeshIdx (ι := ι) n → Ω → ℝ) : Ω → ℝ :=
  Y ⟨⊤, top_mem_mesh (ι := ι) n⟩

end MeshDecomposition

section UniformIntegrability

variable [OrderTop ι] [SecondCountableTopology ι] [BorelSpace ι] {S : ι → Ω → ℝ}

/-- The mesh stopping time used in Rao's terminal uniform-integrability estimate. -/
noncomputable def meshHittingTime (n : ℕ)
    (A : MeshIdx (ι := ι) n → Ω → ℝ) (c : ℝ) : Ω → WithTop ι := by
  sorry

lemma isStoppingTime_meshHittingTime
    (n : ℕ) (A : MeshIdx (ι := ι) n → Ω → ℝ) (c : ℝ) :
    IsStoppingTime 𝓕 (meshHittingTime (ι := ι) n A c) := by
  sorry

/-- Terminal uniform integrability for the finite-mesh predictable and martingale parts. -/
lemma uniformIntegrable_terminal_parts
    (hS_sub : Submartingale S 𝓕 P)
    (hS_cadlag : ∀ ω, IsCadlag (S · ω))
    (hS_D : ClassD S 𝓕 P)
    {A M : (n : ℕ) → MeshIdx (ι := ι) n → Ω → ℝ}
    (hAM : ∀ n,
      meshProcess (ι := ι) S n = M n + A n ∧
      Martingale (M n) (meshFiltration 𝓕 n) P ∧
      A n ⟨⊥, bot_mem_mesh (ι := ι) n⟩ = 0 ∧
      (∀ᵐ ω ∂P, Monotone (fun t ↦ A n t ω))) :
    UniformIntegrable (fun n ↦ terminalValue (ι := ι) (A n)) 1 P ∧
      UniformIntegrable (fun n ↦ terminalValue (ι := ι) (M n)) 1 P := by
  sorry

end UniformIntegrability

section KomlosLimit

variable [OrderTop ι] [SecondCountableTopology ι] {MTop : ℕ → Ω → ℝ}

lemma exists_komlos_terminal_convexification
    (hMTop : UniformIntegrable MTop 1 P) :
    ∃ (calMTop : ℕ → Ω → ℝ) (Mlim : Ω → ℝ),
      (∀ n, calMTop n ∈ _root_.convexHull ℝ≥0 (Set.range fun m ↦ MTop (n + m))) ∧
      Tendsto (fun n ↦ eLpNorm (calMTop n - Mlim) 1 P) atTop (𝓝 0) := by
  exact komlos_L1 hMTop

lemma condExp_komlos_terminal_convergence
    [SigmaFiniteFiltration P 𝓕]
    {calMTop : ℕ → Ω → ℝ} {Mlim : Ω → ℝ}
    (hlim : Tendsto (fun n ↦ eLpNorm (calMTop n - Mlim) 1 P) atTop (𝓝 0)) :
    ∀ t, Tendsto
      (fun n ↦ eLpNorm (P[calMTop n | 𝓕 t] - P[Mlim | 𝓕 t]) 1 P)
      atTop (𝓝 0) := by
  sorry

end KomlosLimit

section StepExtensions

variable [OrderTop ι] [SecondCountableTopology ι] [DenselyOrdered ι]
  {S : ι → Ω → ℝ}

/-- Least mesh point above `t`. -/
noncomputable def ceilMesh (n : ℕ) (t : ι) : MeshIdx (ι := ι) n := by
  sorry

lemma le_ceilMesh (n : ℕ) (t : ι) : t ≤ (ceilMesh (ι := ι) n t : ι) := by
  sorry

lemma ceilMesh_eq_of_mem {n : ℕ} {t : ι} (ht : t ∈ mesh (ι := ι) n) :
    ceilMesh (ι := ι) n t = ⟨t, ht⟩ := by
  sorry

lemma monotone_ceilMesh (n : ℕ) : Monotone (fun t ↦ (ceilMesh (ι := ι) n t : ι)) := by
  sorry

/-- Left-continuous mesh extension of a predictable part. -/
noncomputable def barA {n : ℕ} (A : MeshIdx (ι := ι) n → Ω → ℝ) :
    ι → Ω → ℝ :=
  fun t ω ↦ A (ceilMesh (ι := ι) n t) ω

lemma barA_leftContinuous {n : ℕ} (A : MeshIdx (ι := ι) n → Ω → ℝ) :
    ∀ ω t, ContinuousWithinAt (barA (ι := ι) A · ω) (Set.Iio t) t := by
  sorry

lemma barA_predictable {n : ℕ} (A : MeshIdx (ι := ι) n → Ω → ℝ)
    (hA_adapted : StronglyAdapted (meshFiltration 𝓕 n) A) :
    IsPredictable 𝓕 (barA (ι := ι) A) := by
  sorry

lemma predictable_finset_sum_smul
    {s : Finset ℕ} {w : ℕ → ℝ} {Y : ℕ → ι → Ω → ℝ}
    (hY : ∀ n ∈ s, IsPredictable 𝓕 (Y n)) :
    IsPredictable 𝓕 (fun t ω ↦ Finset.sum s (fun n ↦ w n * Y n t ω)) := by
  sorry

lemma calA_tendsto_on_denseSet
    {calA : ℕ → ι → Ω → ℝ} {M : ι → Ω → ℝ}
    (hcalA_eq : ∀ t ∈ denseSet (ι := ι),
      Tendsto (fun n ↦ eLpNorm (calA n t - (S t - M t)) 1 P) atTop (𝓝 0)) :
    ∀ t ∈ denseSet (ι := ι),
      Tendsto (fun n ↦ eLpNorm (calA n t - (S t - M t)) 1 P) atTop (𝓝 0) :=
  hcalA_eq

end StepExtensions

section DeterministicLimitLemmas

variable [OrderTop ι] [SecondCountableTopology ι] [DenselyOrdered ι]
  {D : Set ι} {f f₀ : ι → ℝ} {F : ℕ → ι → ℝ} {t : ι}

lemma monotone_of_dense_rightContinuous
    (hD_dense : Dense D)
    (hf_rc : Function.RightContinuous f)
    (hf_mono_D : MonotoneOn f D) :
    Monotone f := by
  sorry

lemma incr_fun_lim_dense_rightCont_lim_eq
    (hF_mono : ∀ n, Monotone (F n))
    (hf₀_rc : Function.RightContinuous f₀)
    (hD_lim : ∀ t ∈ D, Tendsto (fun n ↦ F n t) atTop (𝓝 (f₀ t)))
    (hf₀_cont : ContinuousAt f₀ t) :
    Tendsto (fun n ↦ F n t) atTop (𝓝 (f₀ t)) := by
  sorry

end DeterministicLimitLemmas

section PredictabilityLimit

variable [OrderTop ι] [SecondCountableTopology ι] [DenselyOrdered ι]
  {A : ι → Ω → ℝ} {Aseq : ℕ → ι → Ω → ℝ}

/-- Predictability is stable under an a.e. pointwise limit of predictable processes. -/
lemma predictable_of_ae_tendsto_predictable
    (hpred : ∀ n, IsPredictable 𝓕 (Aseq n))
    (hlim : ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n ↦ Aseq n t ω) atTop (𝓝 (A t ω))) :
    IsPredictable 𝓕 A := by
  sorry

/-- The stopping-time identity used to handle jump times of the limiting increasing process. -/
lemma tendsto_at_stoppingTime_of_mesh_approximations
    {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) (hτ_fin : ∀ ω, τ ω ≠ ⊤) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ Aseq n ((τ ω).untopA) ω) atTop
        (𝓝 (A ((τ ω).untopA) ω)) := by
  sorry

end PredictabilityLimit

section BoundedClassD

variable [OrderTop ι] [SecondCountableTopology ι] [DenselyOrdered ι]
  [BorelSpace ι] [IsFiniteMeasure P]
  [𝓕.IsRightContinuous] [𝓕.IsComplete P]

/-- Bounded-index, class-D Doob-Meyer decomposition.  This is the non-local theorem that should
be proved first. -/
theorem doob_meyer_classD
    (hX_sub : Submartingale X 𝓕 P)
    (hX_cadlag : ∀ ω, IsCadlag (X · ω))
    (hX_classD : ClassD X 𝓕 P) :
    ∃ (M A : ι → Ω → ℝ),
      X = M + A ∧
      Martingale M 𝓕 P ∧
      (∀ ω, IsCadlag (M · ω)) ∧
      IsPredictable 𝓕 A ∧
      (∀ ω, IsCadlag (A · ω)) ∧
      A ⊥ = 0 ∧
      (∀ ω, Monotone (A · ω)) := by
  sorry

end BoundedClassD

end DoobMeyer

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
