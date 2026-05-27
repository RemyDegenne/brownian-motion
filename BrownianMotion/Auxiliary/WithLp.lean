module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open WithLp ENNReal

lemma PiLp.coe_proj (p : ENNReal) {ι : Type*} (𝕜 : Type*) {E : ι → Type*} [Semiring 𝕜]
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] {i : ι} :
    ⇑(proj p (𝕜 := 𝕜) E i) = fun x ↦ x i := rfl

@[simp]
lemma EuclideanSpace.proj_apply {ι 𝕜 : Type*} [RCLike 𝕜] {i : ι} (x : EuclideanSpace 𝕜 ι) :
    proj i x = x i := rfl

lemma ContinuousLinearMap.coe_proj' (R : Type*) {ι : Type*} [Semiring R] {φ : ι → Type*}
    [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)] (i : ι) :
    ⇑(ContinuousLinearMap.proj (R := R) (φ := φ) i) = fun x ↦ x i := rfl

lemma EuclideanSpace.coe_equiv_symm {ι 𝕜 : Type*} [RCLike 𝕜] :
    ⇑(EuclideanSpace.equiv ι 𝕜).symm = toLp 2 := rfl
