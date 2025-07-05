import Mathlib.Analysis.InnerProductSpace.PiL2

open WithLp ENNReal

lemma PiLp.coe_proj (p : ENNReal) {ι : Type*} (𝕜 : Type*) {E : ι → Type*} [Semiring 𝕜]
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] {i : ι} :
    ⇑(proj p (𝕜 := 𝕜) E i) = fun x ↦ x i := rfl

lemma EuclideanSpace.coe_proj {ι : Type*} (𝕜 : Type*) [RCLike 𝕜] {i : ι} :
    ⇑(@proj ι 𝕜 _ i) = fun x ↦ x i := rfl

@[simp]
lemma EuclideanSpace.proj_apply {ι 𝕜 : Type*} [RCLike 𝕜] {i : ι} (x : EuclideanSpace 𝕜 ι) :
    proj i x = x i := rfl

lemma ContinuousLinearMap.coe_proj' (R : Type*) {ι : Type*} [Semiring R] {φ : ι → Type*}
    [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)] (i : ι) :
    ⇑(ContinuousLinearMap.proj (R := R) (φ := φ) i) = fun x ↦ x i := rfl

lemma EuclideanSpace.coe_equiv_symm {ι 𝕜 : Type*} [RCLike 𝕜] :
    ⇑(EuclideanSpace.equiv ι 𝕜).symm = toLp 2 := rfl

section single
-- PR #26498

lemma LinearMap.sum_single_apply {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]
    (φ : ι → Type*) [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)] (v : Π i, φ i) :
    ∑ i, Pi.single i (v i) = v := by
  ext i
  simp

variable (p : ℝ≥0∞) {V : Type*} [AddCommGroup V]

@[simp] lemma WithLp.ofLp_sum {ι : Type*} [Fintype ι] (x : ι → WithLp p V) :
    ofLp (∑ i, x i) = ∑ i, ofLp (x i) := rfl

@[simp] lemma WithLp.toLp_sum {ι : Type*} [Fintype ι] (x : ι → V) :
    toLp p (∑ i, x i) = ∑ i, toLp p (x i) := rfl

namespace PiLp

variable (p : ℝ≥0∞) {𝕜 : Type*} {ι : Type*} (β : ι → Type*) [hp : Fact (1 ≤ p)]
    [Fintype ι] [Semiring 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
    [∀ i, Module 𝕜 (β i)] (c : 𝕜) [DecidableEq ι]

variable (𝕜) {β} in
/-- The canonical injection from `β i` to `PiLp p β` as a linear isometry. -/
protected def single {i : ι} : β i →ₗᵢ[𝕜] PiLp p β where
  toLinearMap := (WithLp.linearEquiv p 𝕜 (Π i, β i)).symm.toLinearMap.comp (.single 𝕜 β i)
  norm_map' x := norm_toLp_single p β i x

@[simp]
lemma single_apply {i : ι} (x : β i) : PiLp.single p 𝕜 x = toLp p (Pi.single i x) := rfl

lemma sum_single (x : Π i, β i) :
    ∑ i, PiLp.single p 𝕜 (x i) = toLp p x := by
  simp_rw [single_apply, ← toLp_sum, LinearMap.sum_single_apply (R := 𝕜)]

lemma sum_single' (x : PiLp p β) :
    ∑ i, PiLp.single p 𝕜 (x i) = x := by
  simp_rw [single_apply, ← toLp_sum, LinearMap.sum_single_apply (R := 𝕜)]
  ext; simp

lemma sum_comp_single {γ : Type*} [AddCommGroup γ] [Module 𝕜 γ] (L : PiLp p β →ₗ[𝕜] γ)
    (x : Π i, β i) : ∑ i, L (PiLp.single p 𝕜 (x i)) = L (toLp p x) := by
  simp [← map_sum, sum_single, -single_apply]

lemma sum_comp_single' {γ : Type*} [AddCommGroup γ] [Module 𝕜 γ] (L : PiLp p β →ₗ[𝕜] γ)
    (x : PiLp p β) : ∑ i, L (PiLp.single p 𝕜 (x i)) = L x := by
  simp [← map_sum, sum_single', -single_apply]

end PiLp

end single
