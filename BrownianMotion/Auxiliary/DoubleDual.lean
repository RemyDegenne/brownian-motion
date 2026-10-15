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

A topological vector space `E` over a normed field `𝕜` is reflexive if the canonical map
`StrongDual.inclusionInDoubleDualₗ 𝕜 E` from `E` to its strong bidual
`StrongDual 𝕜 (StrongDual 𝕜 E)`, which sends `x` to the evaluation at `x`, is a homeomorphism.
The strong dual carries the topology of uniform convergence on bounded sets.

This is a topological notion, different from the algebraic notion `Module.IsReflexive`, which asks
for the canonical map to the algebraic double dual `Module.Dual 𝕜 (Module.Dual 𝕜 E)` to be
bijective. For example, an infinite-dimensional Hilbert space is reflexive in the topological sense
but not in the algebraic sense. A finite-dimensional normed space is reflexive in both senses: see
`FiniteDimensional.isReflexive` and `Module.instIsReflexiveOfFiniteOfProjective`.

For a normed space `E`, the canonical map is `NormedSpace.inclusionInDoubleDual 𝕜 E`, which is
continuous. It is an isometry, hence `E` is reflexive if and only if it is surjective.

## Main definitions

* `StrongDual.inclusionInDoubleDualₗ`: the canonical map from a topological vector space to its
  strong bidual, as a linear map.
* `StrongDual.IsReflexive`: a topological vector space is reflexive if
  `StrongDual.inclusionInDoubleDualₗ` is a homeomorphism.

## Main statements

* `NormedSpace.isReflexive_iff_surjective_inclusionInDoubleDual`: a normed space is reflexive if
  and only if the canonical map to its double dual is surjective.
* `StrongDual.IsReflexive.completeSpace`: a reflexive normed space is complete.
* `StrongDual.IsReflexive.submodule_of_isClosed`: a closed subspace of a reflexive normed space is
  reflexive.
* `InnerProductSpace.isReflexive`: a Hilbert space is reflexive.
* `FiniteDimensional.isReflexive`: a finite-dimensional normed space is reflexive.
* `NormedSpace.exists_norm_le_one_forall_apply_eq`: **Helly's theorem** in a reflexive space. If
  the scalars `g i` and the continuous linear forms `φ i` are such that
  `‖∑ i, c i * g i‖ ≤ ‖∑ i, c i • φ i‖` for all finitely supported families of scalars `c`, then
  there is a point `y` of norm at most `1` such that `φ i y = g i` for all `i`.

We also prove consequences of the Hahn-Banach theorem which are used in the proofs:

* `Submodule.exists_strongDual_forall_apply_eq_zero_of_notMem_topologicalClosure`: a point which
  does not belong to the closure of a subspace is separated from it by a continuous linear form
  which vanishes on the subspace.
* `TopologicalSpace.IsSeparable.exists_seq_strongDual_eq_zero_of_forall_apply_eq_zero`: for a
  separable set `t` in a normed space, there is a sequence of continuous linear forms whose only
  common zero in `t` is `0`.
* `NormedSpace.exists_strongDual_forall_apply_eq_of_forall_norm_le`: a linear form which is
  dominated by the norm of a linear map `L` factors through `L`, by a continuous linear form of
  norm at most `1`.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/

@[expose] public section

open Function TopologicalSpace
open scoped ComplexConjugate

/-! ### Reflexive topological vector spaces -/

namespace StrongDual

variable (𝕜 E : Type*) [NormedField 𝕜] [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [ContinuousSMul 𝕜 E]

/-- The canonical map from a topological vector space `E` to its strong bidual, which sends `x` to
the evaluation at `x`, as a linear map. This is the topological analogue of `Module.Dual.eval`.
For a normed space, this is the linear map underlying `NormedSpace.inclusionInDoubleDual`. -/
-- On Mathlib master, this is `ContinuousLinearMap.applyₗ 𝕜 (.id 𝕜)`.
def inclusionInDoubleDualₗ : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) where
  toFun x := ⟨⟨⟨fun f ↦ f x, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩, continuous_eval_const x⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

variable {𝕜 E} in
@[simp]
lemma inclusionInDoubleDualₗ_apply (x : E) (f : StrongDual 𝕜 E) :
    inclusionInDoubleDualₗ 𝕜 E x f = f x := rfl

/-- A topological vector space `E` is reflexive if the canonical map
`StrongDual.inclusionInDoubleDualₗ 𝕜 E` from `E` to its strong bidual is a homeomorphism.

This is not the algebraic notion `Module.IsReflexive`, which concerns the algebraic double dual. -/
class IsReflexive : Prop where
  isHomeomorph_inclusionInDoubleDualₗ : IsHomeomorph (inclusionInDoubleDualₗ 𝕜 E)

end StrongDual

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Consequences of the Hahn-Banach theorem -/

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A point which does not belong to the closure of a subspace `F` is separated from `F` by a
continuous linear form which vanishes on `F`. -/
theorem Submodule.exists_strongDual_forall_apply_eq_zero_of_notMem_topologicalClosure
    (F : Submodule 𝕜 E) {y : E} (hy : y ∉ F.topologicalClosure) :
    ∃ ψ : StrongDual 𝕜 E, (∀ z ∈ F, ψ z = 0) ∧ ψ y ≠ 0 := by
  -- the image of `y` in the normed space `E ⧸ F.topologicalClosure` is not zero
  have : IsClosed (F.topologicalClosure : Set E) := F.isClosed_topologicalClosure
  have hy' : ‖F.topologicalClosure.mkQ y‖ ≠ 0 := by
    rwa [Ne, norm_eq_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨g, -, hg⟩ := exists_dual_vector 𝕜 (F.topologicalClosure.mkQ y) hy'
  refine ⟨g.comp F.topologicalClosure.mkQL, fun z hz ↦ ?_, ?_⟩
  · simp [(Submodule.Quotient.mk_eq_zero _).2 (F.le_topologicalClosure hz)]
  · rw [ContinuousLinearMap.comp_apply, Submodule.mkQL_apply, hg]
    exact RCLike.ofReal_ne_zero.2 hy'

/-- A linear form `A` which is dominated by the norm of a linear map `L` factors through `L`: there
is a continuous linear form `Λ` of norm at most `1` such that `Λ (L c) = A c` for all `c`.
This is a consequence of the Hahn-Banach theorem. -/
theorem NormedSpace.exists_strongDual_forall_apply_eq_of_forall_norm_le {V X : Type*}
    [AddCommGroup V] [Module 𝕜 V] [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] (L : V →ₗ[𝕜] X)
    (A : V →ₗ[𝕜] 𝕜) (h : ∀ c, ‖A c‖ ≤ ‖L c‖) :
    ∃ Λ : StrongDual 𝕜 X, ‖Λ‖ ≤ 1 ∧ ∀ c, Λ (L c) = A c := by
  have h_ker : LinearMap.ker L ≤ LinearMap.ker A := fun c hc ↦ by
    simpa [LinearMap.mem_ker.1 hc] using h c
  -- the linear form `L c ↦ A c` on the range of `L` has norm at most `1`
  let f₀ : LinearMap.range L →ₗ[𝕜] 𝕜 :=
    (LinearMap.ker L).liftQ A h_ker ∘ₗ L.quotKerEquivRange.symm.toLinearMap
  have hf₀ (c : V) : f₀ ⟨L c, LinearMap.mem_range_self L c⟩ = A c := by
    simp [f₀, LinearMap.quotKerEquivRange_symm_apply_image]
  have hf₀_le (x : LinearMap.range L) : ‖f₀ x‖ ≤ 1 * ‖x‖ := by
    obtain ⟨_, c, rfl⟩ := x
    rw [hf₀, one_mul]
    exact h c
  obtain ⟨Λ, hΛ, hΛ_norm⟩ :=
    exists_extension_norm_eq (LinearMap.range L) (f₀.mkContinuous 1 hf₀_le)
  exact ⟨Λ, hΛ_norm.trans_le (f₀.mkContinuous_norm_le zero_le_one _),
    fun c ↦ (hΛ ⟨_, LinearMap.mem_range_self L c⟩).trans (hf₀ c)⟩

end Seminormed

variable (𝕜) in
/-- For a separable set `t` in a normed space, there is a sequence of continuous linear forms
which separates the points of `t` from `0`: the only point of `t` at which all of them vanish
is `0`. -/
theorem TopologicalSpace.IsSeparable.exists_seq_strongDual_eq_zero_of_forall_apply_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {t : Set E} (ht : IsSeparable t) :
    ∃ φ : ℕ → StrongDual 𝕜 E, ∀ y ∈ t, (∀ k, φ k y = 0) → y = 0 := by
  -- `t` is contained in the closure of the range of a sequence `u`
  obtain ⟨c, hc, htc⟩ := ht
  obtain ⟨u, hu⟩ := (hc.insert 0).exists_eq_range (Set.insert_nonempty 0 c)
  have htu : t ⊆ closure (Set.range u) :=
    hu ▸ htc.trans (closure_mono (Set.subset_insert 0 c))
  -- `φ k` is a continuous linear form of norm at most `1` such that `φ k (u k) = ‖u k‖`
  choose φ hφ_norm hφ using fun k ↦ exists_dual_vector'' 𝕜 (u k)
  refine ⟨φ, fun y hyt hy ↦ ?_⟩
  have h (k : ℕ) : ‖u k‖ ≤ ‖y - u k‖ := by
    calc ‖u k‖ = ‖φ k (y - u k)‖ := by simp [hy k, hφ k]
      _ ≤ ‖φ k‖ * ‖y - u k‖ := (φ k).le_opNorm _
      _ ≤ ‖y - u k‖ := mul_le_of_le_one_left (norm_nonneg _) (hφ_norm k)
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := Metric.mem_closure_iff.1 (htu hyt) (ε / 2) (half_pos hε)
  rw [dist_eq_norm] at hk
  linarith [norm_le_insert' y (u k), h k]

/-! ### Reflexive normed spaces -/

/-- `StrongDual.inclusionInDoubleDualₗ` is the linear map underlying
`NormedSpace.inclusionInDoubleDual`. -/
@[simp]
lemma NormedSpace.toLinearMap_inclusionInDoubleDual {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    (inclusionInDoubleDual 𝕜 E).toLinearMap = StrongDual.inclusionInDoubleDualₗ 𝕜 E := rfl

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open NormedSpace

/-- A normed space is reflexive if and only if the canonical map to its double dual is
surjective. -/
theorem NormedSpace.isReflexive_iff_surjective_inclusionInDoubleDual :
    StrongDual.IsReflexive 𝕜 E ↔ Surjective (inclusionInDoubleDual 𝕜 E) := by
  have h_eq : ⇑(StrongDual.inclusionInDoubleDualₗ 𝕜 E) = inclusionInDoubleDual 𝕜 E := by
    rw [← toLinearMap_inclusionInDoubleDual, ContinuousLinearMap.coe_coe]
  refine ⟨fun hE ↦ h_eq ▸ hE.isHomeomorph_inclusionInDoubleDualₗ.surjective, fun hE ↦ ⟨?_⟩⟩
  rw [h_eq]
  exact (LinearIsometryEquiv.ofSurjective (inclusionInDoubleDualLi 𝕜) hE).toHomeomorph.isHomeomorph

namespace StrongDual.IsReflexive

variable (𝕜 E) in
/-- A reflexive normed space is complete. -/
theorem completeSpace [IsReflexive 𝕜 E] : CompleteSpace E :=
  ((inclusionInDoubleDualLi 𝕜 (E := E)).isometry.isUniformInducing.completeSpace_congr
    (isReflexive_iff_surjective_inclusionInDoubleDual.1 ‹_›)).2 inferInstance

/-- A closed subspace of a reflexive normed space is reflexive. -/
theorem submodule_of_isClosed [IsReflexive 𝕜 E] (F : Submodule 𝕜 E) (hF : IsClosed (F : Set E)) :
    IsReflexive 𝕜 F := by
  rw [isReflexive_iff_surjective_inclusionInDoubleDual]
  intro Λ
  -- `Λ` composed with the restriction of linear forms to `F` is the evaluation at a point `y`
  obtain ⟨y, hy⟩ := isReflexive_iff_surjective_inclusionInDoubleDual.1 ‹_›
    (Λ.comp (ContinuousLinearMap.precomp 𝕜 F.subtypeL))
  have hyψ (ψ : StrongDual 𝕜 E) : ψ y = Λ (ψ.comp F.subtypeL) := by
    rw [← dual_def 𝕜 E y ψ, hy]
    rfl
  -- `y ∈ F`, since every continuous linear form which vanishes on `F` vanishes at `y`
  have hyF : y ∈ F := by
    by_contra hyF
    obtain ⟨ψ, hψF, hψy⟩ := F.exists_strongDual_forall_apply_eq_zero_of_notMem_topologicalClosure
      (hF.submodule_topologicalClosure_eq ▸ hyF)
    have hψ : ψ.comp F.subtypeL = 0 := ContinuousLinearMap.ext fun z ↦ hψF z z.2
    exact hψy (by rw [hyψ, hψ, map_zero])
  -- every continuous linear form on `F` is the restriction of a continuous linear form on `E`
  refine ⟨⟨y, hyF⟩, ContinuousLinearMap.ext fun ψ ↦ ?_⟩
  obtain ⟨ψ', hψ', -⟩ := exists_extension_norm_eq F ψ
  have hψ'_eq : ψ'.comp F.subtypeL = ψ := ContinuousLinearMap.ext hψ'
  rw [dual_def, ← hψ'_eq, ← hyψ]
  rfl

end StrongDual.IsReflexive

open Module in
/-- A finite-dimensional normed space is reflexive. -/
instance FiniteDimensional.isReflexive [FiniteDimensional 𝕜 E] : StrongDual.IsReflexive 𝕜 E := by
  rw [isReflexive_iff_surjective_inclusionInDoubleDual]
  -- `inclusionInDoubleDual` is an injective linear map between spaces of the same dimension
  have h_inj : Injective (inclusionInDoubleDual 𝕜 E : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)) :=
    (inclusionInDoubleDualLi 𝕜 (E := E)).injective
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := 𝕜) (V := E)
    (V₂ := StrongDual 𝕜 (StrongDual 𝕜 E)) ?_).1 h_inj
  rw [← LinearMap.toContinuousLinearMap.finrank_eq, Subspace.dual_finrank_eq,
    ← LinearMap.toContinuousLinearMap.finrank_eq, Subspace.dual_finrank_eq]

/-- **Helly's theorem** in a reflexive space: if the scalars `g i` and the continuous linear forms
`φ i` are such that `‖∑ i, c i * g i‖ ≤ ‖∑ i, c i • φ i‖` for all finitely supported families of
scalars `c`, then there is a point `y` of norm at most `1` such that `φ i y = g i` for all `i`. -/
theorem NormedSpace.exists_norm_le_one_forall_apply_eq [StrongDual.IsReflexive 𝕜 E] {ι : Type*}
    (φ : ι → StrongDual 𝕜 E) (g : ι → 𝕜)
    (h : ∀ c : ι →₀ 𝕜, ‖Finsupp.linearCombination 𝕜 g c‖ ≤ ‖Finsupp.linearCombination 𝕜 φ c‖) :
    ∃ y : E, ‖y‖ ≤ 1 ∧ ∀ i, φ i y = g i := by
  obtain ⟨Λ, hΛ_norm, hΛ⟩ := exists_strongDual_forall_apply_eq_of_forall_norm_le _ _ h
  obtain ⟨y, rfl⟩ := isReflexive_iff_surjective_inclusionInDoubleDual.1 ‹_› Λ
  refine ⟨y, ((inclusionInDoubleDualLi 𝕜).norm_map y).symm.trans_le hΛ_norm, fun i ↦ ?_⟩
  simpa [dual_def] using hΛ (Finsupp.single i 1)

end Normed

/-- A Hilbert space is reflexive. -/
instance InnerProductSpace.isReflexive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] : StrongDual.IsReflexive 𝕜 H := by
  rw [NormedSpace.isReflexive_iff_surjective_inclusionInDoubleDual]
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
