module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-
# Lemmas on StdSimplex
-/

@[expose] public section

variable {R : Type*} [PartialOrder R] [Semiring R] {M N P : Type*}

namespace Convexity.StdSimplex

instance instFunLike : FunLike (StdSimplex R M) M R := {
  coe s := s.weights.toFun
  coe_injective := fun _ _ h ↦ ext (Finsupp.ext fun i ↦ congrFun h i)
}

variable [IsStrictOrderedRing R]

/-- Given convex weights `a : StdSimplex R ι` and a family of convex weights
`b : ι → StdSimplex R ι'`, `StdSimplex.bind a b` is the convex combination of the `b k`, weighted
by `a`, defined as monadic bind. -/
noncomputable def bind (a : StdSimplex R M) (b : M → StdSimplex R N) : StdSimplex R N :=
  (a.map b).join

variable (a : StdSimplex R M) (b : M → StdSimplex R N)

@[simp]
lemma bind_single (i : M) : bind (single i) b = b i := by simp [bind, join]

@[simp]
lemma bind_const (c : StdSimplex R N) : bind a (fun _ ↦ c) = c := by simp [bind, join]

lemma weights_bind :
    (bind a b).weights = (fun m ↦ ∑ k ∈ a.weights.support, a.weights k * (b k).weights m) := by
  ext m
  rw [bind, join, map]
  simp only [Finsupp.sum_apply]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  simp [Finsupp.sum]

lemma support_subset_support_bind {a : StdSimplex R M} (b : M → StdSimplex R N)
    {i : M} (hi : i ∈ a.weights.support) :
    (b i).weights.support ⊆ (bind a b).weights.support := by
  intro m hm
  have hpos : 0 < a.weights i * (b i).weights m :=
    mul_pos ((a.nonneg i).lt_of_ne' (by grind)) (((b i).nonneg m).lt_of_ne' (by grind))
  have hnonneg (k : M) (hk : k ∈ a.weights.support) : 0 ≤ a.weights k * (b k).weights m := by
    exact mul_nonneg (a.nonneg k) ((b k).nonneg m)
  have hsum_pos : 0 < ∑ k ∈ a.weights.support, a.weights k * (b k).weights m :=
    lt_of_lt_of_le hpos (Finset.single_le_sum hnonneg hi)
  rw [Finsupp.mem_support_iff, weights_bind]
  positivity

/-- Given a doubly-indexed family of convex weights `cw : ℕ → ℕ → StdSimplex R ℕ`,
`iteratedBind cw k n` is the iterated convex multiplication obtained by combining
the weights `cw 0 n, cw 1 n, …, cw k n` via `StdSimplex.bind`. -/
noncomputable def iteratedBind (cw : ℕ → ℕ → StdSimplex R ℕ) : ℕ → ℕ → StdSimplex R ℕ
  | 0 => cw 0
  | k + 1 => fun n ↦ bind (cw (k + 1) n) (iteratedBind cw k)

lemma iteratedBind_congr {cw1 cw2 : ℕ → ℕ → StdSimplex R ℕ} {k : ℕ}
    (h : ∀ i ≤ k, cw1 i = cw2 i) :
    iteratedBind cw1 k = iteratedBind cw2 k := by
  induction k with
  | zero => simp [iteratedBind, h]
  | succ k ih => simp [iteratedBind, h, ih (fun i hi => h i (Nat.le_succ_of_le hi))]

lemma bind_sum_smul {E : Type*} (f : N → E) [AddCommGroup E] [Module R E] [IsDomain R] :
  (bind a b).weights.sum (fun m cwm ↦ cwm • f m) =
  a.weights.sum (fun i wi ↦ wi • (b i).weights.sum (fun m bm ↦ bm • f m)) := by
  classical
  simp only [bind, StdSimplex.join, StdSimplex.map]
  rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul]),
      Finsupp.sum_mapDomain_index (fun _ => by simp)
      (fun d r₁ r₂ => by simp [add_smul, Finsupp.sum_add_index, add_smul])]
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hsupp : (a.weights i • (b i).weights).support = (b i).weights.support :=
    Finsupp.support_smul_eq (by grind)
  simp [hsupp, Finset.smul_sum, Finsupp.smul_apply, smul_smul]

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

end Convexity.StdSimplex
