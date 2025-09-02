/-
Copyright (c) 2025 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli
-/

import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Process.Filtration

/-!
This file contains the definitions and some theorems about t-approximable sets, which are needed
in the proof of the Debut Theorem.
-/

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology


namespace MeasureTheory

variable {T Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Preorder T] [TopologicalSpace T]
variable {f : Filtration T mΩ} {t : T}

/- NB: we definitely need more hypotheses on T, for example we may need `Set.Iic t` to be compact
(what would be a good way to impose this? It seems that there exists the class `isClosed_Iic`
that does exactly that, maybe it is enough). Anyways, let us put them only where they are needed. -/

section 𝒦_sets

/- TODO: Can this definition be written more clearly, I wanted to write something like
`{ A ×ˢ C | (A ⊆ Set.Iic t) ∧ IsCompact A ∧ MeasurableSet[f t] C }`, but it gives me invalid
pattern error, I'm not sure why. I also tried with an inductive definition, maybe it is a bit more
clean, for now I am keeping that one. -/

/- NB: a set in lean (s : Set α) is defined as a function s : α → Prop, and s a for a : α just
means that a ∈ s. However I think this notation should be mostly hidden from the user, so is it ok
to leave the definitions mentioning this explicitely? -/

/-- `𝓚₀(t)` is the collection of subsets of `[0, t] × Ω` of the form `A × C`, where `A` is
compact and `C` is (f t)-measurable. -/
inductive 𝓚₀ (f : Filtration T mΩ) (t : T) : Set (Set (T × Ω)) where
  | prod {K C} (hA_subs : K ⊆ Set.Iic t) (hA : IsCompact K) (hM : MeasurableSet[f t] C) :
    𝓚₀ f t (K ×ˢ C)

@[simp]
lemma empty_mem_𝓚₀ (f : Filtration T mΩ) (t : T) : ∅ ∈ 𝓚₀ f t := by
  convert 𝓚₀.prod (Set.empty_subset _) isCompact_empty (@MeasurableSet.empty _ (f t))
  exact Set.prod_empty.symm

lemma mem_𝓚₀_iff (f : Filtration T mΩ) (t : T) (B : Set (T × Ω)) :
    B ∈ 𝓚₀ f t ↔ ∃ K C, B = K ×ˢ C ∧ K ⊆ Set.Iic t ∧ IsCompact K ∧ MeasurableSet[f t] C := by
  -- easy, just unfold the definition correctly (how do you unfold an inductive definition?)
  sorry

lemma subset_Iic_of_mem_𝓚₀ {B : Set (T × Ω)} (hB : B ∈ 𝓚₀ f t) :
    B ⊆ Set.Iic t ×ˢ .univ := by
  have ⟨A, C, hB_eq, hA_subs, hA, hC⟩ := (mem_𝓚₀_iff ..).mp hB
  exact hB_eq ▸ Set.prod_mono hA_subs (Set.subset_univ _)

/-- If `B ∈ 𝓚₀(t)`, then its projetion over `Ω` is (f t)-measurable. -/
lemma measurableSet_snd_of_mem_𝓚₀ {B : Set (T × Ω)} (hB : B ∈ 𝓚₀ f t) :
    MeasurableSet[f t] (Prod.snd '' B) := by
  -- easy, divide the case K = ∅
  sorry

/-- `𝓚(t)` is the collection of finite unions of sets in `𝓚₀(t)`. -/
inductive 𝓚 (f : Filtration T mΩ) (t : T) : Set (Set (T × Ω)) where
  | base {B : Set (T × Ω)} (hB : B ∈ 𝓚₀ f t) : 𝓚 f t B
  | union {B B' : Set (T × Ω)} (hB : B ∈ 𝓚 f t) (hB' : B' ∈ 𝓚 f t) :
      𝓚 f t (B ∪ B')

lemma 𝓚₀_subset_𝓚 (f : Filtration T mΩ) (t : T) : 𝓚₀ f t ⊆ 𝓚 f t := fun _ hB ↦ 𝓚.base hB

lemma mem_𝓚_iff (f : Filtration T mΩ) (t : T) (B : Set (T × Ω)) :
    B ∈ 𝓚 f t ↔ ∃ s : Finset (Set (T × Ω)),
      (s : Set _) ⊆ 𝓚₀ f t ∧ B = ⋃ x ∈ s, x := by
  -- farily easy
  sorry

lemma subset_Iic_of_mem_𝓚 {B : Set (T × Ω)} (hB : B ∈ 𝓚 f t) :
    B ⊆ Set.Iic t ×ˢ .univ := by
  induction hB with
  | base hB => exact subset_Iic_of_mem_𝓚₀ hB
  | union _ _ hB hB' => exact Set.union_subset hB hB'

/-- `𝓚(t)` is closed under union. -/
lemma union_mem_𝓚 {f : Filtration T mΩ} {t : T}
    {B B' : Set (T × Ω)} (hB : B ∈ 𝓚 f t) (hB' : B' ∈ 𝓚 f t) : B ∪ B' ∈ 𝓚 f t := by
  -- easy
  sorry

/-- If `B ∈ 𝓚(t)`, then its projection over `Ω` is (f t)-measurable. -/
lemma measurableSet_snd_of_mem_𝓚 {B : Set (T × Ω)} (hB : B ∈ 𝓚 f t) :
    MeasurableSet[f t] (Prod.snd '' B) := by
  /- should be easy, just use `measurableSet_snd_of_mem_𝓚₀` and the fact that the union of snd is
  snd of the union (`Set.image_union`) and then the fact that union of measurable is measurable -/
  sorry

inductive 𝓚δ (f : Filtration T mΩ) (t : T) : Set (Set (T × Ω)) where
  | iInter {ℬ : Set (Set (T × Ω))} (h_nonempty : ℬ.Nonempty) (h_subs : ℬ ⊆ 𝓚 f t)
    (h_count : Countable ℬ) : 𝓚δ f t (⋂ B ∈ ℬ, B)

lemma subset_Iic_of_mem_𝓚δ {B : Set (T × Ω)} (hB : B ∈ 𝓚δ f t) :
    B ⊆ Set.Iic t ×ˢ .univ := by
  induction hB with
  | iInter h_nonempty h_subs h_count =>
    have ⟨B, hB⟩ := h_nonempty
    exact Set.iInter₂_subset_of_subset B hB (subset_Iic_of_mem_𝓚 (h_subs hB))

/-- `𝓚δ(t)` is closed under union. -/
lemma union_mem_𝓚δ {f : Filtration T mΩ} {t : T}
    {B B' : Set (T × Ω)} (hB : B ∈ 𝓚δ f t) (hB' : B' ∈ 𝓚δ f t) : B ∪ B' ∈ 𝓚δ f t := by
  -- easy, you can use `union_mem_𝓚`, `Set.iInter_union` and `Set.union_iInter`
  sorry

/- TODO: check that this is provable even without the hypothesis that `B := ⋂ B_n ⊆ 𝒦δ`, I'm not
completely sure. If it is not possible to prove it like this, then just add the hypothesis
`⋂ B_n ⊆ 𝒦δ`. -/
/-- In `𝓚δ`, the projection over `Ω` and countable intersections commute. -/
lemma iInf_snd_eq_snd_iInf_of_mem_𝓚δ {t : T} {ι : Type*} [Countable ι]
    {ℬ : ι → Set (T × Ω)} (hℬ : ∀ i, ℬ i ∈ 𝓚δ f t) :
    ⋂ i, Prod.snd '' ℬ i = Prod.snd '' (⋂ i, ℬ i) := by
  -- see proof in the blueprint

  /- the intersection of the `S(Bn)` is compact since each of them is compact, why? maybe we can
  use the fact that they are all contained in the compact set `Set.Iic t` and they are closed (why
  are they closed?? it should be fairly easy to show it starting from the claim that `S(A)` is cpct
  for `A ∈ 𝒦₀`)
  maybe use `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` for the second case
  to show that the intersection is nonempty and reach the contradiction -/
  sorry

/-- If `B ∈ 𝓚δ(t)`, then its projetion over `Ω` is (f t)-measurable. -/
lemma measurableSet_snd_of_mem_𝓚δ {B : Set (T × Ω)} (hB : B ∈ 𝓚δ f t) :
    MeasurableSet[f t] (Prod.snd '' B) := by
  -- use `iInf_snd_eq_snd_iInf_of_mem_𝓚δ`, `measurableSet_snd_of_mem_𝓚` and the definition of `𝒦δ`
  sorry

end 𝒦_sets

section 𝓛_sets

/-- `𝓛₀(X)` is the collection of sets of the form `A ×ˢ B`, where `A : Set X` is compact and
`B ∈ 𝓚 f t`. -/
inductive 𝓛₀ (X : Type*) [TopologicalSpace X] (f : Filtration T mΩ) (t : T) :
    Set (Set (X × (T × Ω))) where
  | prod {A B} (hA : IsCompact A) (hB : B ∈ 𝓚 f t) : 𝓛₀ X f t (A ×ˢ B)

/-- `𝓛₁(X)` is the collection of finite unions of sets in `𝓛₀(X)`. -/
inductive 𝓛₁ (X : Type*) [TopologicalSpace X] (f : Filtration T mΩ) (t : T) :
    Set (Set (X × (T × Ω))) where
  | base {L} (hL : L ∈ 𝓛₀ X f t) : 𝓛₁ X f t L
  | union {L L'} (hL : L ∈ 𝓛₁ X f t) (hL' : L' ∈ 𝓛₁ X f t) : 𝓛₁ X f t (L ∪ L')

/-- `𝓛(X)` is the collection of intersections of countable decreasing sequences in `𝓛₁(X)`. -/
inductive 𝓛 (X : Type*) [TopologicalSpace X] (f : Filtration T mΩ) (t : T) :
    Set (Set (X × (T × Ω))) where
  | iInter {L : ℕ → Set (X × (T × Ω))} (h_anti : Antitone L) (hL : ∀ n, L n ∈ 𝓛₁ X f t) :
      𝓛 X f t (⋂ n, L n)

/-- `𝓛σ(X)` is the collection of unions of countable increasing sequences in `𝓛(X)`. -/
inductive 𝓛σ (X : Type*) [TopologicalSpace X] (f : Filtration T mΩ) (t : T) :
    Set (Set (X × (T × Ω))) where
  | iUnion {L : ℕ → Set (X × (T × Ω))} (h_incr : Monotone L) (hL : ∀ n, L n ∈ 𝓛 X f t) :
      𝓛σ X f t (⋃ n, L n)

/-- `𝓛σδ(X)` is the collection of intersections of countable decreasing sequences in `𝓛σ(X)`. -/
inductive 𝓛σδ (X : Type*) [TopologicalSpace X] (f : Filtration T mΩ) (t : T) :
    Set (Set (X × (T × Ω))) where
  | iInter {L : ℕ → Set (X × (T × Ω))} (h_anti : Antitone L) (hL : ∀ n, L n ∈ 𝓛σ X f t) :
      𝓛σδ X f t (⋂ n, L n)

/- is this the best way to state that there exists a compact T2 topological space `X`? is there a
more compact way, without having to write `∃` 4 times? -/
/-- If `A` is measurable with respect to the product sigma algebra of the Borel sigma algebra on
`T` and `f t`, then there exists a compact Hausdorff space `X` and a set `B ∈ 𝓛σδ X f t` such that
`A` is the projection of `B` on `T × Ω`. -/
lemma exists_mem_𝓛σδ_of_measurableSet {mT : MeasurableSpace T} [BorelSpace T]
    {A : Set (T × Ω)} (hA_subs : A ⊆ Set.Iic t ×ˢ .univ) (hA : MeasurableSet[mT.prod (f t)] A) :
    ∃ X : Type*, ∃ _ : TopologicalSpace X, ∃ _ : CompactSpace X, ∃ _ : T2Space X,
      ∃ B ∈ 𝓛σδ X f t, A = Prod.snd '' B := by
  /- See the proof of lemma A.2 in the paper. This will need some work and probably some
  auxiliary lemmas.

  possible strategy: define the class M, then prove as a lemma that it is a monotone class, prove
  that it contains K(t) then it contains I(t) (which is an algebra), then use the monotone class
  theorem inside the proof of this lemma to conclude.
  we will need the monotone class theorem, a quick search in mathlib does not give me any
  satisfactory result. maybe I need to write a separate file for this and prove this theorem myself,
  but I have no idea how difficult it is. Maybe there is something similar already partially
  implemented, see this Zulip message:
  https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Proof.3A.20.20isField.20ss.20.E2.88.A7.20isMonoClass.20ss.20.E2.86.94.20isSigmaField.20ss.20.3F/near/448825855 -/
  sorry


end 𝓛_sets

/- Is this the right way to define an approximable set? In this way we have the approximation ready
to use, without having to use .choose, but maybe it makes sense to have a Prop instead? Also, do we
actually need this to be explicit? I'm not sure, but for now I leave it as a structure -/

/- does it make sense to have `ε : ENNReal`, or would it be better to have `ε : ℝ` or `ε : ℝ≥0`?
having `ε : ENNReal` has the advantage that we dont have coercions inside the formula, but maybe
it does not affect much? for now I leave it as `ENNReal`, but if it gives any trouble we can
change it. -/
/-- An approximation of `A ⊆ Set.Iic t ×ˢ .univ` is a sequence of sets `B ε ⊆ A` for every `ε > 0`
such that `B ε ∈ 𝓚δ f t`, and the projection of `B ε` on `Ω` approximates `A` in measure
as `ε` tends to `0`. -/
structure Approximation (f : Filtration T mΩ) (P : Measure Ω) (t : T) (A : Set (T × Ω)) where
  B : ℝ≥0∞ → Set (T × Ω)
  A_subset : A ⊆ Set.Iic t ×ˢ .univ
  B_mem : ∀ ε > 0, B ε ∈ 𝓚δ f t
  B_subset_A : ∀ ε > 0, B ε ⊆ A
  le : ∀ ε > 0, P (Prod.snd '' A) ≤ P (Prod.snd '' B ε) + ε

namespace Approximation

variable {P : Measure Ω} {A : Set (T × Ω)}

/-- A set `A ∈ 𝓚δ(t)` is approximable (the approximation is the set itself). -/
def of_mem_𝓚δ (P : Measure Ω) (hA : A ∈ 𝓚δ f t) : Approximation f P t A where
  B := fun _ ↦ A
  A_subset := subset_Iic_of_mem_𝓚δ hA
  B_mem := fun _ _ ↦ hA
  B_subset_A := fun _ _ _ a ↦ a
  le := fun _ _ ↦ le_self_add

/-- Given an approximation `𝒜`, then `𝒜.B' n` is the union of `B 1, B (1/2), ..., B (1/n)`.
This gives us an increasing approximating sequence. -/
def B' (𝒜 : Approximation f P t A) : ℕ → Set (T × Ω) :=
  fun n ↦ ⋃ m ∈ Finset.Icc 1 n, 𝒜.B (1 / m)

@[simp]
lemma B'_zero (𝒜 : Approximation f P t A) : 𝒜.B' 0 = ∅ := by
  simp [B']

lemma B'_succ (𝒜 : Approximation f P t A) (n : ℕ) :
    𝒜.B' (n + 1) = 𝒜.B' n ∪ 𝒜.B (1 / (n + 1)) := by
  have : Finset.Icc 1 (n + 1) = Finset.Icc 1 n ∪ {n + 1} := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  rw [B', this, B', Finset.set_biUnion_union]
  simp

lemma B_subset_B' (𝒜 : Approximation f P t A) (n : ℕ) [NeZero n] :
    𝒜.B (1 / n) ⊆ 𝒜.B' n := by
  -- easy, use the definition of B'
  sorry

lemma B'_mem (𝒜 : Approximation f P t A) (n : ℕ) : 𝒜.B' n ∈ 𝓚δ f t := by
  -- easy, use the definition of B', B_mem and the fact that 𝓚δ is closed under union
  sorry

lemma B'_subset_A (𝒜 : Approximation f P t A) (n : ℕ) : 𝒜.B' n ⊆ A := by
  -- easy, use the definition of B' and B_subset_A
  sorry

lemma le' (𝒜 : Approximation f P t A) (n : ℕ) :
    P (Prod.snd '' A) ≤ P (Prod.snd '' 𝒜.B' n) + 1 / n := by
  -- easy, use the definition of B', le and the fact that B (1 / n) ⊆ B' n
  sorry

lemma B'_mono (𝒜 : Approximation f P t A) : Monotone 𝒜.B' := by
  -- easy, use the definition of B'
  sorry

lemma measurableSet_snd_iUnion_B' (𝒜 : Approximation f P t A) :
    MeasurableSet[f t] (Prod.snd '' (⋃ n, 𝒜.B' n)) := by
  /- easy, use `measurableSet_snd_of_mem_𝓚δ`, the fact that a union of projections is the
  projection of the union and the fact that a countable union of measurable sets is measurable -/
  sorry

lemma measure_snd_iUnion_B' (𝒜 : Approximation f P t A) :
    P (Prod.snd '' (⋃ n, 𝒜.B' n)) = P (Prod.snd '' A) := by
  /- see part of the proof of `lem:measurable_of_t_approx` in the blueprint. The idea is: let `π` be
  the projection over `Ω`, `P(π(B)) = lim P(π(B_n)) = P(π(A))` -/
  sorry

lemma measure_snd_diff [IsFiniteMeasure P] (𝒜 : Approximation f P t A) :
    P (Prod.snd '' A \ Prod.snd '' (⋃ n, 𝒜.B' n)) = 0 := by
  /- easy, use `MeasureTheory.measure_diff` and the fact that `π(B) ⊆ π(A)` to say that
  `P(π(A) \ π(B)) = 0`. -/
  sorry

-- we probably need a complete measure space for this lemma to hold.
/-- If there exists an approximation of `A`, then the projection of `A` over `Ω` is measurable
with respect to `f t`. -/
lemma measurableSet_snd (𝒜 : Approximation f P t A) :
    MeasurableSet[f t] (Prod.snd '' A) := by
  /- easy, use the completeness and `measure_snd_diff` to get measurability for `(π(A) \ π(B))`,
  then measurableSet_snd_iUnion_B' to get measurability for `π(B)`, and finally use the fact that
  `π(A) = (π(A) \ π(B)) ∪ π(B)`. -/
  sorry

/- maybe it is better to state this with an inf instead of a limit? or maybe it is better to state
it as in the paper, i.e. `∀ ε > 0, ∃ B ∈ 𝓚δ f t, P (Prod.snd '' A \ Prod.snd '' B) < ε` ? In any
case it should be fairly easy to go from one to the other. -/
lemma tendsto_measure_diff_B' (𝒜 : Approximation f P t A) :
    Tendsto (fun n ↦ P (Prod.snd '' A \ Prod.snd '' 𝒜.B' n)) atTop (𝓝 0) := by
  /- check the proof in the blueprint, much of the needed infrastructure is already formalized just
  above this.-/
  sorry

/- Question: Is `A ⊆ Set.Iic t ×ˢ .univ ∧ MeasurableSet[mT.prod (f t)] A` equivalent to
`A ∈ 𝓑 (Set.Iic t) × (f i)` (the last one is not syntactically correct in lean, with that I mean
that A is measurable wrt the product σ algebra of the borel σ algebra induced by T on Set.Iic t and
the σ alg on Ω, the problem with writing this explicitely is that we should first project A into
`Set.Iic t ×ˢ Ω` and I fear that is not going to be very clean and usable). I'm pretty sure that if
`A ⊆ Set.Iic t ×ˢ .univ` then it is just equivalent to being measurable wrt the global product σ
algebra, so for now I'm going to formalize it that way, but it would be good if someone double
checks that. -/

-- is there a notation for `mT.prod (f t)`? `mT × (f t)` does not work
/- how much is it needed that we take the Borel σ algebra on `T`? Take this into consideration when
writing the proof, maybe we can relax this hypothesis. -/
-- this is the main theorem of this file.
/-- If `A` is measurable with respect to the product sigma algebra of the Borel sigma algebra on
`T` and `f t`, then it is approximable. -/
def of_mem_prod_borel {mT : MeasurableSpace T} [BorelSpace T] (P : Measure Ω)
    (hA_subs : A ⊆ Set.Iic t ×ˢ .univ) (hA : MeasurableSet[mT.prod (f t)] A) :
    Approximation f P t A where
  -- See the proof in the blueprint
  B := sorry
  A_subset := sorry
  B_mem := sorry
  B_subset_A := sorry
  le := sorry

end Approximation

end MeasureTheory
