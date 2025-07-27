import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef

lemma sum_single_apply {ι : Type*} (φ : ι → Type*) [∀ i, AddCommMonoid (φ i)] [Fintype ι]
    [DecidableEq ι] (v : (i : ι) → φ i) :
    ∑ i, Pi.single i (v i) = v := by
  ext i
  simp

lemma Matrix.PosSemidef.nonneg_apply_self {n R : Type*} [Fintype n] [CommRing R] [PartialOrder R]
    [StarRing R] {M : Matrix n n R} (hM : M.PosSemidef) (i : n) : 0 ≤ M i i := by
  classical
  convert hM.2 (Pi.single i 1)
  have : star (Pi.single (M := fun _ ↦ R) i 1) = Pi.single i 1 := by
    ext j
    simp [Pi.single_apply, apply_ite star]
  simp [this]

section mkContinuous₂

namespace LinearMap

variable {E F G 𝕜 : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (f : E →ₗ[𝕜] F →ₗ[𝕜] G)

/-- Given a bilinear map whose codomains are finite dimensional, outputs the continuous
version. -/
def mkContinuous₂OfFiniteDimensional : E →L[𝕜] F →L[𝕜] G :=
  letI g x : F →L[𝕜] G := (f x).toContinuousLinearMap
  letI h : E →ₗ[𝕜] F →L[𝕜] G :=
    { toFun := g
      map_add' x y := by ext z; simp [g]
      map_smul' m x := by ext y; simp [g] }
  h.toContinuousLinearMap

@[simp]
lemma mkContinuous₂OfFiniteDimensional_apply (x : E) (y : F) :
    f.mkContinuous₂OfFiniteDimensional x y = f x y := rfl

end LinearMap

end mkContinuous₂

section InnerProductSpace

open scoped InnerProductSpace

lemma OrthonormalBasis.inner_eq {𝕜 E ι : Type*} [NormedAddCommGroup E] [RCLike 𝕜]
    [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) {i j : ι} :
    ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 := by
  by_cases h : i = j
  · simp only [h, ↓reduceIte]
    apply RCLike.ext
    · simp
    · simp
  · simp [h]

theorem OrthonormalBasis.norm_sq_eq_sum_sq_inner_right {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ⟪b i, x⟫_ℝ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right]
  simp

theorem OrthonormalBasis.norm_sq_eq_sum_sq_inner_left {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ⟪x, b i⟫_ℝ ^ 2 := by
  simp_rw [b.norm_sq_eq_sum_sq_inner_right, real_inner_comm]

theorem EuclideanSpace.real_norm_sq_eq {n : Type*} [Fintype n] (x : EuclideanSpace ℝ n) :
    ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  congr with i; simp

@[simp]
theorem basisFun_inner {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜] (x : EuclideanSpace 𝕜 ι) (i : ι) :
    ⟪EuclideanSpace.basisFun ι 𝕜 i, x⟫_𝕜 = x i := by
  simp [← OrthonormalBasis.repr_apply_apply]

lemma EuclideanSpace.real_inner_eq {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    ⟪x, y⟫_ℝ = ∑ i, x i * y i := by
  nth_rw 1 [← (EuclideanSpace.basisFun ι ℝ).sum_repr' x, sum_inner]
  simp_rw [real_inner_smul_left, basisFun_inner]

theorem inner_basisFun_real {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) (i : ι) :
    inner ℝ x (EuclideanSpace.basisFun ι ℝ i) = x i := by
  rw [real_inner_comm, basisFun_inner]

namespace OrthonormalBasis

variable {ι ι' 𝕜 E E' : Type*} [Fintype ι] [Fintype ι'] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] (b : OrthonormalBasis ι 𝕜 E)
    (b' : OrthonormalBasis ι' 𝕜 E') (e : ι ≃ ι')

/-- The `LinearIsometryEquiv` which maps an orthonormal basis to another. This is a convenience
wrapper around `Orthonormal.equiv`. -/
protected noncomputable def equiv : E ≃ₗᵢ[𝕜] E' :=
  Orthonormal.equiv (v := b.toBasis) (v' := b'.toBasis) b.orthonormal b'.orthonormal e

lemma equiv_apply_basis (i : ι) : b.equiv b' e (b i) = b' (e i) := by
  simp only [OrthonormalBasis.equiv, Orthonormal.equiv, LinearEquiv.coe_isometryOfOrthonormal]
  rw [← b.coe_toBasis, Basis.equiv_apply, b'.coe_toBasis]

lemma equiv_apply (x : E) : b.equiv b' e x = ∑ i, b.repr x i • b' (e i) := by
  nth_rw 1 [← b.sum_repr x, map_sum]
  simp_rw [map_smul, equiv_apply_basis]

lemma equiv_apply_euclideanSpace (x : EuclideanSpace 𝕜 ι) :
    (EuclideanSpace.basisFun ι 𝕜).equiv b (Equiv.refl ι) x = ∑ i, x i • b i := by
  simp_rw [equiv_apply, EuclideanSpace.basisFun_repr, Equiv.refl_apply]

end OrthonormalBasis

@[simp]
lemma inner_toDual_symm_eq_self {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (L : NormedSpace.Dual 𝕜 E) :
  inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm L) = L := by ext; simp

lemma InnerProductSpace.toDual_apply_eq_toDualMap_apply {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] (x : E) :
  InnerProductSpace.toDual 𝕜 E x = InnerProductSpace.toDualMap 𝕜 E x := rfl

theorem OrthonormalBasis.norm_dual {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) (L : NormedSpace.Dual ℝ E) :
    ‖L‖ ^ 2 = ∑ i, L (b i) ^ 2 := by
  have := FiniteDimensional.of_fintype_basis b.toBasis
  simp_rw [← (InnerProductSpace.toDual ℝ E).symm.norm_map, b.norm_sq_eq_sum_sq_inner_left,
    InnerProductSpace.toDual_symm_apply]

@[simp]
lemma LinearIsometryEquiv.coe_coe_eq_coe {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F) :
    ⇑f.toLinearIsometry.toContinuousLinearMap = ⇑f := rfl

end InnerProductSpace

section zero

namespace ContinuousLinearMap

@[simp]
lemma flip_zero {𝕜 𝕜₂ 𝕜₃ E F G : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] [SeminormedAddCommGroup G] [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃] [NormedSpace 𝕜 E]
    [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
    [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃] :
    ContinuousLinearMap.flip (0 : E →SL[σ₁₃] F →SL[σ₂₃] G) = 0 := rfl

@[simp]
lemma bilinearComp_zero {𝕜 𝕜₂ 𝕜₃ 𝕜₁' 𝕜₂' E F G E' F' : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
    [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
    [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [NontriviallyNormedField 𝕜₁']
    [NontriviallyNormedField 𝕜₂'] [NormedSpace 𝕜₁' E'] [NormedSpace 𝕜₂' F'] {σ₁' : 𝕜₁' →+* 𝕜}
    {σ₁₃' : 𝕜₁' →+* 𝕜₃} {σ₂' : 𝕜₂' →+* 𝕜₂} {σ₂₃' : 𝕜₂' →+* 𝕜₃} [RingHomCompTriple σ₁' σ₁₃ σ₁₃']
    [RingHomCompTriple σ₂' σ₂₃ σ₂₃'] [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃']
    [RingHomIsometric σ₂₃'] {gE : E' →SL[σ₁'] E} {gF : F' →SL[σ₂'] F} :
    ContinuousLinearMap.bilinearComp (0 : E →SL[σ₁₃] F →SL[σ₂₃] G) gE gF = 0 := rfl

end ContinuousLinearMap

end zero
