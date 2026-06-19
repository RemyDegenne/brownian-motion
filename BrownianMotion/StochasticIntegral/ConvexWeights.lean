module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-
# Lemmas on StdSimplex
-/

@[expose] public section

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {M N P : Type*}

namespace Convexity

open StdSimplex

/-- Given a doubly-indexed family of convex weights `cw : ℕ → ℕ → StdSimplex R ℕ`,
`iteratedComb cw k n` is the iterated convex multiplication obtained by combining
the weights `cw 0 n, cw 1 n, …, cw k n` via `iConvexComb`. -/
public noncomputable def iteratedComb (cw : ℕ → ℕ → StdSimplex R ℕ) : ℕ → ℕ → StdSimplex R ℕ
  | 0 => cw 0
  | k + 1 => fun n ↦ iConvexComb (cw (k + 1) n) (iteratedComb cw k)

lemma iteratedComb_congr {cw1 cw2 : ℕ → ℕ → StdSimplex R ℕ} {k : ℕ}
    (h : ∀ i ≤ k, cw1 i = cw2 i) :
    iteratedComb cw1 k = iteratedComb cw2 k := by
  induction k with
  | zero => simp [iteratedComb, h]
  | succ k ih => simp [iteratedComb, h, ih (fun i hi => h i (Nat.le_succ_of_le hi))]

lemma iConvexComb_sum_smul {E : Type*} (a : StdSimplex R M) (b : M → StdSimplex R N) (f : N → E)
    [AddCommGroup E] [Module R E] [IsDomain R] :
    (iConvexComb a b).weights.sum (fun m cwm ↦ cwm • f m) =
  a.weights.sum (fun i wi ↦ wi • (b i).weights.sum (fun m bm ↦ bm • f m)) := by
  classical
  simp only [iConvexComb, weights_sConvexComb, weights_map]
  rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul]),
      Finsupp.sum_mapDomain_index (fun _ => by simp)
      (fun d r₁ r₂ => by simp [add_smul, Finsupp.sum_add_index, add_smul])]
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finsupp.support_smul_eq (by grind)]
  simp [Finset.smul_sum, Finsupp.smul_apply, smul_smul]

open MeasureTheory
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Type*} [MeasurableSpace Ω]

lemma eLpNorm_weights_sum_le {μ : Measure Ω} (w : StdSimplex ℝ ℕ)
    {h : ℕ → Ω → E} (hmeas : ∀ m, AEStronglyMeasurable (h m) μ) {B : ℝ≥0∞}
    (hB : ∀ m, eLpNorm (h m) 1 μ ≤ B) :
    eLpNorm (w.weights.sum fun m c ↦ c • h m) 1 μ ≤ B := by
  rw [Finsupp.sum]
  calc eLpNorm (∑ m ∈ w.weights.support, w.weights m • h m) 1 μ
      ≤ ∑ m ∈ w.weights.support, eLpNorm (w.weights m • h m) 1 μ :=
        eLpNorm_sum_le (fun m _ ↦ (hmeas m).const_smul _) le_rfl
    _ ≤ ∑ m ∈ w.weights.support, ENNReal.ofReal (w.weights m) * B :=
        Finset.sum_le_sum fun m _ ↦ by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (w.nonneg m)]
          exact mul_le_mul_right (hB m) _
    _ = B := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun m _ ↦ w.nonneg m,
          show ∑ m ∈ w.weights.support, w.weights m = 1 from w.total, ENNReal.ofReal_one,
          one_mul]

lemma coeFn_sum_smul {μ : Measure Ω} {p : ℝ≥0∞} (s : Finset ℕ) (c : ℕ → ℝ)
    {h : ℕ → Ω → E} (hmem : ∀ m, MemLp (h m) p μ) :
    ⇑(∑ m ∈ s, c m • (hmem m).toLp (h m)) =ᵐ[μ] ∑ m ∈ s, c m • h m := by
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero E p μ
  | insert j t hjt ih =>
    rw [Finset.sum_insert hjt, Finset.sum_insert hjt]
    exact (Lp.coeFn_add _ _).trans <|
      ((Lp.coeFn_smul _ _).trans ((hmem j).coeFn_toLp.const_smul (c j))).add ih

end Convexity
