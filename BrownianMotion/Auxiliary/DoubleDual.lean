/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Reflexive spaces

A normed space `E` over `𝕜` is reflexive if the canonical map
`NormedSpace.inclusionInDoubleDual 𝕜 E` from `E` to its double dual is surjective. Mathlib has no
definition of reflexive spaces: in this file reflexivity is the hypothesis
`Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E)`.

## Main statements

* `NormedSpace.completeSpace_of_surjective_inclusionInDoubleDual`: a reflexive space is complete.
* `NormedSpace.surjective_inclusionInDoubleDual_of_isClosed`: a closed subspace of a reflexive
  space is reflexive.
* `InnerProductSpace.surjective_inclusionInDoubleDual`: a Hilbert space is reflexive.
* `NormedSpace.exists_norm_le_one_forall_apply_eq`: Helly's theorem in a reflexive space. If the
  scalars `g i` and the continuous linear forms `φ i` are such that
  `‖∑ i, c i * g i‖ ≤ ‖∑ i, c i • φ i‖` for all finitely supported families of scalars `c`, then
  there is a point `y` of norm at most `1` such that `φ i y = g i` for all `i`.

We also prove consequences of the Hahn-Banach theorem which are used in the proofs:

* `Submodule.exists_strongDual_forall_apply_eq_zero_of_notMem`: a point which does not belong to a
  closed subspace is separated from it by a continuous linear form which vanishes on the subspace.
* `NormedSpace.exists_seq_strongDual_forall_apply_eq_zero_imp`: in a separable normed space, there
  is a sequence of continuous linear forms which separates the points.
* `NormedSpace.exists_strongDual_forall_apply_eq_of_forall_norm_le`: a linear form which is
  dominated by the norm of a linear map `L` factors through `L`, by a continuous linear form of
  norm at most `1`.

-/

public section

open Function TopologicalSpace
open scoped ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A point which does not belong to a closed subspace `F` is separated from `F` by a continuous
linear form which vanishes on `F`. -/
theorem Submodule.exists_strongDual_forall_apply_eq_zero_of_notMem (F : Submodule 𝕜 E)
    (hF : IsClosed (F : Set E)) {y : E} (hy : y ∉ F) :
    ∃ ψ : StrongDual 𝕜 E, (∀ z ∈ F, ψ z = 0) ∧ ψ y ≠ 0 := by
  have : IsClosed (F : Set E) := hF
  have hy' : ‖F.mkQ y‖ ≠ 0 := by
    rwa [Ne, norm_eq_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨g, -, hg⟩ := exists_dual_vector 𝕜 (F.mkQ y) hy'
  refine ⟨g.comp F.mkQL, fun z hz ↦ ?_, ?_⟩
  · simp [(Submodule.Quotient.mk_eq_zero F).2 hz]
  · change g (F.mkQ y) ≠ 0
    rw [hg]
    exact RCLike.ofReal_ne_zero.2 hy'

namespace NormedSpace

variable (𝕜) in
/-- In a separable normed space, there is a sequence of continuous linear forms which separates
the points. -/
theorem exists_seq_strongDual_forall_apply_eq_zero_imp (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [SeparableSpace E] :
    ∃ φ : ℕ → StrongDual 𝕜 E, ∀ y : E, (∀ k, φ k y = 0) → y = 0 := by
  choose φ hφ_norm hφ using fun k ↦ exists_dual_vector'' 𝕜 (denseSeq E k)
  refine ⟨φ, fun y hy ↦ ?_⟩
  have h (k : ℕ) : ‖denseSeq E k‖ ≤ ‖y - denseSeq E k‖ := by
    calc ‖denseSeq E k‖ = ‖φ k (y - denseSeq E k)‖ := by simp [hy k, hφ k]
      _ ≤ ‖φ k‖ * ‖y - denseSeq E k‖ := (φ k).le_opNorm _
      _ ≤ ‖y - denseSeq E k‖ := mul_le_of_le_one_left (norm_nonneg _) (hφ_norm k)
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := (denseRange_denseSeq E).exists_dist_lt y (half_pos hε)
  rw [dist_eq_norm] at hk
  linarith [norm_le_insert' y (denseSeq E k), h k]

/-- A reflexive space is complete. -/
theorem completeSpace_of_surjective_inclusionInDoubleDual
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) : CompleteSpace E :=
  ((inclusionInDoubleDualLi 𝕜 (E := E)).isometry.isUniformInducing.completeSpace_congr hE).2
    inferInstance

/-- A closed subspace of a reflexive space is reflexive. -/
theorem surjective_inclusionInDoubleDual_of_isClosed
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) {F : Submodule 𝕜 E}
    (hF : IsClosed (F : Set E)) :
    Surjective (inclusionInDoubleDual 𝕜 F) := by
  intro Λ
  -- `Λ` composed with the restriction of linear forms to `F` is the evaluation at a point `y`
  obtain ⟨y, hy⟩ := hE (Λ.comp (ContinuousLinearMap.precomp 𝕜 F.subtypeL))
  have hyψ (ψ : StrongDual 𝕜 E) : ψ y = Λ (ψ.comp F.subtypeL) := by
    rw [← dual_def 𝕜 E y ψ, hy]
    rfl
  -- `y ∈ F`, since every continuous linear form which vanishes on `F` vanishes at `y`
  have hyF : y ∈ F := by
    by_contra hyF
    obtain ⟨ψ, hψF, hψy⟩ := F.exists_strongDual_forall_apply_eq_zero_of_notMem hF hyF
    have hψ : ψ.comp F.subtypeL = 0 := ContinuousLinearMap.ext fun z ↦ hψF z z.2
    exact hψy (by rw [hyψ, hψ, map_zero])
  -- every continuous linear form on `F` is the restriction of a continuous linear form on `E`
  refine ⟨⟨y, hyF⟩, ContinuousLinearMap.ext fun ψ ↦ ?_⟩
  obtain ⟨ψ', hψ', -⟩ := exists_extension_norm_eq F ψ
  have hψ'_eq : ψ'.comp F.subtypeL = ψ := ContinuousLinearMap.ext hψ'
  rw [dual_def, ← hψ'_eq, ← hyψ]
  rfl

/-- A linear form `A` which is dominated by the norm of a linear map `L` factors through `L`: there
is a continuous linear form `Λ` of norm at most `1` such that `Λ (L c) = A c` for all `c`.
This is a consequence of the Hahn-Banach theorem. -/
theorem exists_strongDual_forall_apply_eq_of_forall_norm_le {V X : Type*} [AddCommGroup V]
    [Module 𝕜 V] [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] (L : V →ₗ[𝕜] X) (A : V →ₗ[𝕜] 𝕜)
    (h : ∀ c, ‖A c‖ ≤ ‖L c‖) :
    ∃ Λ : StrongDual 𝕜 X, ‖Λ‖ ≤ 1 ∧ ∀ c, Λ (L c) = A c := by
  have h_ker : LinearMap.ker L ≤ LinearMap.ker A := fun c hc ↦ by
    simpa [LinearMap.mem_ker.1 hc] using h c
  -- the linear form `L c ↦ A c` on the range of `L` has norm at most `1`
  let f₀ : LinearMap.range L →ₗ[𝕜] 𝕜 :=
    (LinearMap.ker L).liftQ A h_ker ∘ₗ L.quotKerEquivRange.symm.toLinearMap
  have hf₀ (c : V) : f₀ ⟨L c, LinearMap.mem_range_self L c⟩ = A c := by
    change (LinearMap.ker L).liftQ A h_ker (L.quotKerEquivRange.symm ⟨L c, _⟩) = A c
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hf₀_le (x : LinearMap.range L) : ‖f₀ x‖ ≤ 1 * ‖x‖ := by
    obtain ⟨_, c, rfl⟩ := x
    rw [hf₀, one_mul]
    exact h c
  obtain ⟨Λ, hΛ, hΛ_norm⟩ :=
    exists_extension_norm_eq (LinearMap.range L) (f₀.mkContinuous 1 hf₀_le)
  exact ⟨Λ, hΛ_norm.trans_le (f₀.mkContinuous_norm_le zero_le_one _),
    fun c ↦ (hΛ ⟨_, LinearMap.mem_range_self L c⟩).trans (hf₀ c)⟩

/-- **Helly's theorem** in a reflexive space: if the scalars `g i` and the continuous linear forms
`φ i` are such that `‖∑ i, c i * g i‖ ≤ ‖∑ i, c i • φ i‖` for all finitely supported families of
scalars `c`, then there is a point `y` of norm at most `1` such that `φ i y = g i` for all `i`. -/
theorem exists_norm_le_one_forall_apply_eq (hE : Surjective (inclusionInDoubleDual 𝕜 E))
    {ι : Type*} (φ : ι → StrongDual 𝕜 E) (g : ι → 𝕜)
    (h : ∀ c : ι →₀ 𝕜, ‖Finsupp.linearCombination 𝕜 g c‖ ≤ ‖Finsupp.linearCombination 𝕜 φ c‖) :
    ∃ y : E, ‖y‖ ≤ 1 ∧ ∀ i, φ i y = g i := by
  obtain ⟨Λ, hΛ_norm, hΛ⟩ := exists_strongDual_forall_apply_eq_of_forall_norm_le _ _ h
  obtain ⟨y, rfl⟩ := hE Λ
  refine ⟨y, ((inclusionInDoubleDualLi 𝕜).norm_map y).symm.trans_le hΛ_norm, fun i ↦ ?_⟩
  simpa [dual_def] using hΛ (Finsupp.single i 1)

end NormedSpace

/-- A Hilbert space is reflexive. -/
theorem InnerProductSpace.surjective_inclusionInDoubleDual {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] :
    Surjective (NormedSpace.inclusionInDoubleDual 𝕜 H) := by
  intro Λ
  let T := InnerProductSpace.toDual 𝕜 H
  -- `y ↦ conj (Λ ⟪y, ·⟫)` is a continuous linear form, represented by a vector by the Riesz theorem
  let ψ : StrongDual 𝕜 H := LinearMap.mkContinuous
    { toFun := fun y ↦ conj (Λ (T y))
      map_add' := fun y z ↦ by simp
      map_smul' := fun c y ↦ by simp [map_smulₛₗ] } ‖Λ‖
    fun y ↦ by simpa [T] using Λ.le_opNorm (T y)
  refine ⟨T.symm ψ, ContinuousLinearMap.ext fun φ ↦ ?_⟩
  obtain ⟨z, rfl⟩ := T.surjective φ
  rw [NormedSpace.dual_def, InnerProductSpace.toDual_apply_apply, ← inner_conj_symm,
    InnerProductSpace.toDual_symm_apply]
  simp [ψ]
