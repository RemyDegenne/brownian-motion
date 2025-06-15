import BrownianMotion.Gaussian.CovMatrix

/-!
# Facts about Gaussian distributions

This file contains facts about Gaussian distributions which should go to Mathlib.
-/

open Complex MeasureTheory

open scoped NNReal InnerProductSpace ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

lemma charFunDual_eq_charFun_toDual_symm {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [InnerProductSpace ℝ E] {mE : MeasurableSpace E} {μ : Measure E} (L : NormedSpace.Dual ℝ E) :
    charFunDual μ L = charFun μ ((InnerProductSpace.toDual ℝ E).symm L) := by
  rw [charFun_eq_charFunDual_toDualMap]
  congr with x
  simp

@[simp]
lemma inner_toDual_symm_eq_self {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (L : NormedSpace.Dual 𝕜 E) :
  inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm L) = L := by ext; simp

lemma lol {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace E]
    [CompleteSpace F] [MeasurableSpace E] {μ : Measure E} (h : Integrable id μ) (L : E →L[𝕜] F) :
    μ[L] = L μ[id] := by
  change ∫ x, L (id x) ∂μ = _
  rw [L.integral_comp_comm h]

lemma isGaussian_iff_charFun [IsFiniteMeasure μ] : IsGaussian μ ↔
    ∀ t, charFun μ t = exp (μ[fun x ↦ ⟪t, x⟫_ℝ] * I - Var[fun x ↦ ⟪t, x⟫_ℝ; μ] / 2) := by
  rw [isGaussian_iff_charFunDual_eq]
  constructor
  · intro h t
    convert h (InnerProductSpace.toDualMap ℝ E t)
    exact charFun_eq_charFunDual_toDualMap t
  · intro h L
    convert h ((InnerProductSpace.toDual ℝ E).symm L)
    · exact charFunDual_eq_charFun_toDual_symm L
    all_goals simp

lemma IsGaussian.charFun_eq' [SecondCountableTopology E] [hμ : IsGaussian μ] (t : E) :
    charFun μ t = exp (⟪t, μ[id]⟫_ℝ * I - covInnerBilin μ t t / 2) := by
  rw [isGaussian_iff_charFun.1 hμ]
  congr
  · simp_rw [integral_complex_ofReal, ← integral_inner (IsGaussian.integrable_id μ), id]
  · rw [covInnerBilin_self (IsGaussian.memLp_id μ 2 (by norm_num))]

omit [CompleteSpace E]

lemma IsGaussian.charFun_eq [FiniteDimensional ℝ E] [hμ : IsGaussian μ] (t : E) :
    charFun μ t = exp (⟪t, μ[id]⟫_ℝ * I -
    ((stdOrthonormalBasis ℝ E).repr t) ⬝ᵥ
    (covMatrix μ).mulVec ((stdOrthonormalBasis ℝ E).repr t) / 2) := by
  rw [IsGaussian.charFun_eq', covInnerBilin_eq_dotProduct_covMatrix_mulVec]

lemma test1 {μ : Measure ℝ} {m : ℝ} {v : ℝ≥0}
    (h : μ = gaussianReal m v) : μ = gaussianReal μ[id] Var[id; μ].toNNReal := by
  simp [h]

lemma test [FiniteDimensional ℝ E] [IsFiniteMeasure μ] : IsGaussian μ ↔
    ∃ (m : E)
      (M : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ),
      M.PosSemidef ∧ ∀ t, charFun μ t = exp (⟪t, m⟫_ℝ * I -
    ((stdOrthonormalBasis ℝ E).repr t) ⬝ᵥ
    M.mulVec ((stdOrthonormalBasis ℝ E).repr t) / 2) := by
  refine ⟨fun h ↦ ⟨μ[id], covMatrix μ, posSemidef_covMatrix, IsGaussian.charFun_eq⟩, ?_⟩
  · rintro ⟨m, M, hM, h⟩
    constructor
    intro L
    have : μ.map L = gaussianReal (L m)
        (((stdOrthonormalBasis ℝ E).repr ((InnerProductSpace.toDual ℝ E).symm L)) ⬝ᵥ
        (M.mulVec ((stdOrthonormalBasis ℝ E).repr
        ((InnerProductSpace.toDual ℝ E).symm L)))).toNNReal := by
      apply Measure.ext_of_charFun
      ext t
      rw [charFun_map_eq_charFunDual_smul, charFunDual_eq_charFun_toDual_symm, charFun_gaussianReal,
        h, InnerProductSpace.toDual_symm_apply]
      congr
      · simp
      · rw [map_smul, map_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_smul,
          smul_eq_mul, Complex.ofReal_mul, pow_two, Complex.ofReal_mul, mul_comm ((t : ℂ) * _)]
        congr
        rw [Real.coe_toNNReal]
        exact hM.2 _
    rw [test1 this]
    congr
    · rw [integral_map (by fun_prop) (by fun_prop)]
      simp
    · rw [variance_map aemeasurable_id (by fun_prop)]
      simp



end ProbabilityTheory
