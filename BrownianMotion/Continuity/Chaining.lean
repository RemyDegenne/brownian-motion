import BrownianMotion.Continuity.CoveringNumber

/-!
# Chaining

### References
- https://arxiv.org/pdf/2107.13837.pdf Lemma 6.2
- Talagrand, The generic chaining
- Vershynin, High-Dimensional Probability (section 4.2 and chapter 8)

-/

variable {α ι : Type*} {x y : α} {A : Set α}

-- TODO: find a name
/-- Closest point to `x` in the set `s i`. -/
def π [Dist α] (s : ι → Finset α) (x : α) (i : ι) : α :=
  sorry

lemma dist_π_le [Dist α] {s : ι → Finset α} {i : ι} (hy : y ∈ s i) :
    dist x (π s x i) ≤ dist x y := by
  sorry

/-- Closest point to `x` in a minimal `(ε i)`-cover of `A`. -/
noncomputable
def πCov [Dist α] (A : Set α) (ε : ι → ℝ) (x : α) (i : ι) : α :=
  π (fun j ↦ minimalCover (ε j) A) x i

lemma dist_πCov [Dist α] {ε : ι → ℝ} {i : ι} (hxA : x ∈ A) :
    dist x (πCov A ε x i) ≤ ε i := by
  sorry

lemma dist_πCov_succ_le_add [PseudoMetricSpace α] {ε : ℕ → ℝ} {i : ℕ} (hxA : x ∈ A) :
    dist (πCov A ε x i) (πCov A ε x (i + 1)) ≤ ε i + ε (i + 1) := by
  calc dist (πCov A ε x i) (πCov A ε x (i + 1))
    ≤ dist (πCov A ε x i) x + dist x (πCov A ε x (i + 1)) := dist_triangle _ _ _
  _ ≤ ε i + ε (i + 1) := add_le_add ((dist_comm _ _).trans_le (dist_πCov hxA)) (dist_πCov hxA)

lemma dist_πCov_succ_le_two_mul [PseudoMetricSpace α] {ε : ℕ → ℝ} (hε : Antitone ε) {i : ℕ}
    (hxA : x ∈ A) :
    dist (πCov A ε x i) (πCov A ε x (i + 1)) ≤ 2 * ε i := by
  calc dist (πCov A ε x i) (πCov A ε x (i + 1)) ≤ ε i + ε (i + 1) := dist_πCov_succ_le_add hxA
  _ ≤ 2 * ε i := by rw [two_mul]; exact add_le_add le_rfl (hε (Nat.le_succ _))

lemma dist_πCov_le_add_dist [PseudoMetricSpace α] {ε : ℕ → ℝ} {i : ℕ} (hxA : x ∈ A) (hyA : y ∈ A) :
    dist (πCov A ε x i) (πCov A ε y i) ≤ 2 * ε i + dist x y := by
  calc dist (πCov A ε x i) (πCov A ε y i)
    ≤ dist (πCov A ε x i) y + dist y (πCov A ε y i) := dist_triangle _ _ _
  _ ≤ dist (πCov A ε x i) x + dist x y + dist y (πCov A ε y i) :=
        add_le_add (dist_triangle _ _ _) le_rfl
  _ = dist (πCov A ε x i) x + dist y (πCov A ε y i) + dist x y := by abel
  _ ≤ 2 * ε i + dist x y := by
        rw [two_mul]
        refine add_le_add (add_le_add ?_ (dist_πCov hyA)) le_rfl
        exact (dist_comm _ _).trans_le (dist_πCov hxA)
