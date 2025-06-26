import Mathlib.Analysis.InnerProductSpace.PiL2

lemma PiLp.coe_proj (p : ENNReal) {ι : Type*} (𝕜 : Type*) {E : ι → Type*} [Semiring 𝕜]
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] {i : ι} :
    ⇑(proj p (𝕜 := 𝕜) E i) = fun x ↦ x i := rfl

lemma EuclideanSpace.coe_proj {ι : Type*} (𝕜 : Type*) [RCLike 𝕜] {i : ι} :
    ⇑(@proj ι 𝕜 _ i) = fun x ↦ x i := rfl

@[simp]
lemma EuclideanSpace.proj_apply {ι 𝕜 : Type*} [RCLike 𝕜] {i : ι} (x : EuclideanSpace 𝕜 ι) :
    proj i x = x i := rfl
