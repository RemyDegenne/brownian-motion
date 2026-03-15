/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Choquet.CompactSystem
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Analytic sets in the sense of a paved space


TODO: we use `IsCompactSystem`, which corresponds to semi-compact pavings for D-M. We use this and
not compact pavings (which would be the same, but for arbitrary intersections instead of countable
ones), because it's sufficient for our applications, and because it's easier to work with.

-/

open scoped ENNReal NNReal

variable {𝓧 𝓨 𝓚 : Type*} {p : Set 𝓧 → Prop} {q : Set 𝓚 → Prop} {s t : Set 𝓧} {f : ℕ → Set 𝓧}

namespace MeasureTheory

/-- A set `s` is analytic for a paving (predicate) `p` and a type `𝓚` if there exists a compact
system `q` of `𝓚` such that `s` is the projections of a set `t` that satisfies
`memProdSigmaDelta p q`. -/
def IsPavingAnalyticFor (p : Set 𝓧 → Prop) (𝓚 : Type*) (s : Set 𝓧) : Prop :=
  ∃ q : Set 𝓚 → Prop, q ∅ ∧ IsCompactSystem q ∧
    ∃ t : Set (𝓧 × 𝓚), memProdSigmaDelta p q t ∧ s = Prod.fst '' t

/-- A set `s` is analytic for a paving (predicate) `p` if there exists a type `𝓚` and a compact
system `q` of `𝓚` such that `s` is the projections of a set `t` that satisfies
`memProdSigmaDelta p q`. -/
def IsPavingAnalytic (p : Set 𝓧 → Prop) (s : Set 𝓧) : Prop :=
  ∃ 𝓚 : Type, Nonempty 𝓚 ∧ IsPavingAnalyticFor p 𝓚 s

lemma IsPavingAnalyticFor.isPavingAnalytic {𝓚 : Type} [Nonempty 𝓚]
    (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalytic p s := ⟨𝓚, ‹_›, hs⟩

lemma isPavingAnalyticFor_of_prop (𝓚 : Type*) [Nonempty 𝓚] (hs : p s) :
    IsPavingAnalyticFor p 𝓚 s := by
  classical
  refine ⟨fun t ↦ t = ∅ ∨ t = .univ, ?_, ?_, ⟨s ×ˢ .univ, ?_, by ext; simp⟩⟩
  · simp
  · sorry
  · exact memProdSigmaDelta_of_prop hs (by simp)

lemma isPavingAnalytic_of_prop (hs : p s) : IsPavingAnalytic p s :=
  (isPavingAnalyticFor_of_prop ℝ hs).isPavingAnalytic

lemma IsPavingAnalyticFor.mono {p' : Set 𝓧 → Prop} (hp : ∀ s, p s → p' s)
    (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor p' 𝓚 s := by
  obtain ⟨q, hq_empty, hq_compact, t, ht_prod, rfl⟩ := hs
  refine ⟨q, hq_empty, hq_compact, ⟨t, ?_, rfl⟩⟩
  exact ht_prod.mono hp fun _ ↦ id

lemma IsPavingAnalytic.mono {p' : Set 𝓧 → Prop} (hp : ∀ s, p s → p' s)
    (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic p' s := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  exact (IsPavingAnalyticFor.mono hp hs𝓚).isPavingAnalytic

-- He paragraph after 1.25
lemma IsPavingAnalyticFor.exists_memSigma_superset (hs : IsPavingAnalyticFor p 𝓚 s) :
    ∃ t, memSigma p t ∧ s ⊆ t := by
  obtain ⟨q, hq_empty, hq_compact, B, hB_prod, rfl⟩ := hs
  rw [memProdSigmaDelta_iff] at hB_prod
  obtain ⟨A, K, hA, hK, rfl⟩ := hB_prod
  refine ⟨⋃ m, A 0 m, ?_, ?_⟩
  · exact ⟨fun m ↦ A 0 m, fun m ↦ hA 0 m, rfl⟩
  · intro x hx
    simp only [Set.mem_image, Set.mem_iInter, Set.mem_iUnion, Set.mem_prod, Prod.exists,
      exists_and_right, exists_eq_right] at hx ⊢
    obtain ⟨_, h⟩ := hx
    choose n hn _ using h
    exact ⟨n 0, hn 0⟩

lemma IsPavingAnalyticFor.empty (𝓚 : Type*) (hp_empty : p ∅) : IsPavingAnalyticFor p 𝓚 ∅ := by
  rcases isEmpty_or_nonempty 𝓚 with h_empty | h_nonempty
  · refine ⟨fun _ ↦ true, by simp, ?_, ∅ ×ˢ ∅, memProdSigmaDelta_of_prop hp_empty rfl, by simp⟩
    simp only [IsCompactSystem, implies_true, forall_const]
    intro C _
    have h_eq_empty n : C n = ∅ := Set.eq_empty_of_isEmpty (C n)
    refine ⟨{0}, ?_⟩
    simpa using h_eq_empty 0
  · exact isPavingAnalyticFor_of_prop 𝓚 hp_empty

@[simp]
lemma IsPavingAnalytic.empty (hp_empty : p ∅) : IsPavingAnalytic p ∅ :=
  (IsPavingAnalyticFor.empty ℝ hp_empty).isPavingAnalytic

@[simp]
lemma isPavingAnalyticFor_iff_eq_empty (𝓚 : Type*) [IsEmpty 𝓚] (hp_empty : p ∅) (s : Set 𝓧) :
    IsPavingAnalyticFor p 𝓚 s ↔ s = ∅ := by
  refine ⟨fun hs ↦ ?_, fun hs_empty ↦ ?_⟩
  · obtain ⟨q, hq_empty, hq_compact, t, h_prod, h_eq⟩ := hs
    rw [h_eq]
    simp only [Set.image_eq_empty]
    exact Set.eq_empty_of_isEmpty t
  · rw [hs_empty]
    exact IsPavingAnalyticFor.empty 𝓚 hp_empty

-- He 1.26
lemma IsPavingAnalyticFor.iInter {𝓚 : ℕ → Type*} {s : ℕ → Set 𝓧}
    (hs : ∀ n, IsPavingAnalyticFor p (𝓚 n) (s n)) :
    IsPavingAnalyticFor p (Π n, 𝓚 n) (⋂ n, s n) := by
  choose q hq_empty hq_compact B hB_prod hB_eq using hs
  let C n : Set (𝓧 × ((i : ℕ) → 𝓚 i)) := {p | (p.1, p.2 n) ∈ B n}
  let q' : Set (Π n, 𝓚 n) → Prop := fun s : Set (Π n, 𝓚 n) ↦
    -- modeled on squareCylinders, but with univ instead of a finset
    s ∈ Set.univ.pi '' (Set.univ.pi (fun n ↦ {x | q n x ∨ x = Set.univ}))
  refine ⟨q', ?_, ?_, ⋂ n, C n, ?_, ?_⟩
  · simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_const,
    Set.univ_pi_eq_empty_iff, q']
    exact ⟨fun _ ↦ ∅, by simp only [exists_const, and_true]; exact fun _ ↦ .inl (hq_empty _)⟩
  · -- a product of compact systems is a compact system
    sorry
  · refine memDelta.iInter fun n ↦ ?_
    rw [← memProdSigmaDelta]
    simp_rw [memProdSigmaDelta_iff] at hB_prod ⊢
    choose A K hA hK hB_eq using hB_prod
    refine ⟨A n, fun i j ↦ {y | y n ∈ K n i j}, hA n, fun i j ↦ ?_, ?_⟩
    · simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_const, q']
      rcases Set.eq_empty_or_nonempty (K n i j) with hK_empty | hK_nonempty
      · simp only [hK_empty, Set.mem_empty_iff_false, Set.setOf_false]
        exact ⟨fun _ ↦ ∅, by
          simp only [Set.univ_pi_empty, and_true]; exact fun _ ↦ .inl (hq_empty _)⟩
      refine ⟨fun k ↦ if k = n then K k i j else Set.univ, fun k ↦ ?_, ?_⟩
      · simp only [ite_eq_right_iff]
        split_ifs with hk
        · subst hk
          exact .inl (hK k i j)
        · simp [hk]
      · ext; simp
    ext
    simp [hB_eq, C]
  · simp_rw [hB_eq]
    ext x
    simp only [Set.mem_iInter, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
      Set.mem_setOf_eq, C]
    refine ⟨fun h ↦ ?_, fun ⟨y, hy⟩ n ↦ ⟨y n, hy n⟩⟩
    choose y hy using h
    exact ⟨y, hy⟩

lemma IsPavingAnalytic.iInter {s : ℕ → Set 𝓧} (hs : ∀ n, IsPavingAnalytic p (s n)) :
    IsPavingAnalytic p (⋂ n, s n) := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  exact (IsPavingAnalyticFor.iInter hs𝓚).isPavingAnalytic

-- He 1.26
lemma IsPavingAnalyticFor.iUnion {𝓚 : ℕ → Type*} {s : ℕ → Set 𝓧}
    (hs : ∀ n, IsPavingAnalyticFor p (𝓚 n) (s n)) :
    IsPavingAnalyticFor p (Σ n, 𝓚 n) (⋃ n, s n) := by
  choose q hq_empty hq_compact B hB_prod hB_eq using hs
  let C := Prod.swap ''
    ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm '' (Set.sigma Set.univ (fun n ↦ Prod.swap '' (B n))))
  let q'' := fun t : Set (Σ n, 𝓚 n) ↦
    ∃ s : Finset ℕ, t ∈ (s : Set ℕ).sigma '' (Set.univ.pi (fun n ↦ {x | q n x ∨ x = Set.univ}))
  refine ⟨q'', ?_, ?_, C, ?_, ?_⟩
  · simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const, q'']
    refine ⟨∅, fun _ ↦ Set.univ, ?_⟩
    simp only [Finset.coe_empty, Set.sigma_univ, Set.preimage_empty, and_true]
    exact fun _ ↦ .inr rfl
  · -- sum of compact systems is a compact system
    sorry
  · choose A hA hB_eq using hB_prod
    have hC_eq : C = ⋂ k, Prod.swap '' ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm ''
        (Set.sigma Set.univ (fun n ↦ Prod.swap '' (A n k)))) := by
      simp only [C, hB_eq]
      rw [← Set.image_iInter Prod.swap_bijective, ← Set.image_iInter (Equiv.bijective _)]
      simp_rw [Set.image_iInter Prod.swap_bijective]
      congr
      ext
      simp
    rw [hC_eq]
    refine memDelta.iInter fun k ↦ memDelta_of_prop ?_
    simp_rw [memSigma_memProd_iff] at hA
    choose B K hB hK hA_eq using hA
    simp_rw [hA_eq]
    have h_eq : Prod.swap '' ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm '' Set.univ.sigma
        fun n ↦ Prod.swap '' ⋃ n_1, B n k n_1 ×ˢ K n k n_1)
      = ⋃ n_1, Prod.swap '' ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm '' Set.univ.sigma
        fun n ↦ Prod.swap '' (B n k n_1 ×ˢ K n k n_1)) := by ext; simp; grind
    rw [h_eq]
    refine memSigma.iUnion fun i ↦ ?_
    simp only [Set.image_swap_prod, Set.sigma_eq_biUnion, Set.mem_univ, Set.iUnion_true,
      Set.image_iUnion]
    refine memSigma.iUnion fun j ↦ memSigma_of_prop ?_
    refine ⟨B j k i, Sigma.mk j '' (K j k i), hB _ _ _, ?_, ?_⟩
    · simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_const, q'']
      refine ⟨{j}, fun j ↦ K j k i, ?_⟩
      simp only [Finset.coe_singleton, Set.singleton_sigma, and_true]
      exact fun m ↦ .inl (hK _ _ _)
    · ext
      simp
      grind
  · simp only [hB_eq, Equiv.sigmaProdDistrib_symm_apply, C]
    ext y
    simp only [Set.mem_iUnion, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
      Set.mem_sigma_iff, Set.mem_univ, Prod.swap_prod_mk, true_and, Sigma.exists, Prod.mk.injEq,
      ↓existsAndEq, exists_eq_right_right, Sigma.mk.injEq, and_true]
    grind

lemma IsPavingAnalytic.iUnion {s : ℕ → Set 𝓧}
    (hs : ∀ n, IsPavingAnalytic p (s n)) :
    IsPavingAnalytic p (⋃ n, s n) := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  exact (IsPavingAnalyticFor.iUnion hs𝓚).isPavingAnalytic

-- He 1.26
lemma IsPavingAnalyticFor.inter {𝓚' : Type*} {t : Set 𝓧}
    (hs : IsPavingAnalyticFor p 𝓚 s) (ht : IsPavingAnalyticFor p 𝓚' t) :
    IsPavingAnalyticFor p (𝓚 × 𝓚') (s ∩ t) := by
  obtain ⟨q, hq_empty, hq_compact, B, hB_prod, hB_eq⟩ := hs
  obtain ⟨q', hq'_empty, hq'_compact, B', hB'_prod, hB'_eq⟩ := ht
  let C : Set (𝓧 × (𝓚 × 𝓚')) := {p | (p.1, p.2.1) ∈ B}
  let C' : Set (𝓧 × (𝓚 × 𝓚')) := {p | (p.1, p.2.2) ∈ B'}
  let q'' : Set (𝓚 × 𝓚') → Prop :=
    memProd (fun t ↦ q t ∨ t = Set.univ) (fun t ↦ q' t ∨ t = Set.univ)
  refine ⟨q'', ?_, ?_, C ∩ C', ?_, ?_⟩
  · simp [q'', memProd]
    grind
  · refine IsCompactSystem.memProd ?_ ?_
    · sorry -- IsCompactSystem.insert_univ
    · sorry
  · refine memDelta.inter ?_ ?_
    · rw [← memProdSigmaDelta]
      simp_rw [memProdSigmaDelta_iff] at hB_prod ⊢
      choose A K hA hK hB_eq using hB_prod
      refine ⟨A, fun i j ↦ {y | y.1 ∈ K i j}, hA, fun i j ↦ ?_, ?_⟩
      · simp only [memProd, exists_and_left, q'']
        rcases Set.eq_empty_or_nonempty (K i j) with hK_empty | hK_nonempty
        · simp only [hK_empty, Set.mem_empty_iff_false, Set.setOf_false]
          exact ⟨∅, by simp [hq_empty]⟩
        refine ⟨K i j, ?_⟩
        simp only [hK, true_or, true_and]
        refine ⟨Set.univ, ?_⟩
        simp only [or_true, true_and]
        ext
        simp
      · ext y
        simp only [hB_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq, C]
    · rw [← memProdSigmaDelta]
      simp_rw [memProdSigmaDelta_iff] at hB'_prod ⊢
      choose A K hA hK hB_eq using hB'_prod
      refine ⟨A, fun i j ↦ {y | y.2 ∈ K i j}, hA, fun i j ↦ ?_, ?_⟩
      · simp only [memProd, exists_and_left, q'']
        rcases Set.eq_empty_or_nonempty (K i j) with hK_empty | hK_nonempty
        · simp only [hK_empty, Set.mem_empty_iff_false, Set.setOf_false]
          exact ⟨∅, by simp [hq_empty]⟩
        refine ⟨Set.univ, ?_⟩
        simp only [or_true, true_and]
        refine ⟨K i j, ?_⟩
        simp only [hK, true_or, true_and]
        ext
        simp
      · ext y
        simp only [hB_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq, C']
  · ext
    simp [hB_eq, hB'_eq, C, C']

lemma IsPavingAnalytic.inter {t : Set 𝓧}
    (hs : IsPavingAnalytic p s) (ht : IsPavingAnalytic p t) :
    IsPavingAnalytic p (s ∩ t) := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  choose 𝓚' h𝓚' ht𝓚' using ht
  exact (IsPavingAnalyticFor.inter hs𝓚 ht𝓚').isPavingAnalytic

-- He 1.26
lemma IsPavingAnalyticFor.union {𝓚' : Type*} {t : Set 𝓧}
    (hs : IsPavingAnalyticFor p 𝓚 s) (ht : IsPavingAnalyticFor p 𝓚' t) :
    IsPavingAnalyticFor p (𝓚 ⊕ 𝓚') (s ∪ t) := by
  choose q hq_empty hq_compact B hB_prod hB_eq using hs
  choose q' hq'_empty hq'_compact B' hB'_prod hB'_eq using ht
  let C : Set (𝓧 × (𝓚 ⊕ 𝓚')) :=
    (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm (B, B')
  let q'' := fun t ↦ Sum.inl ⁻¹' t ∈ {x | q x ∨ x = Set.univ} ∧
    Sum.inr ⁻¹' t ∈ {x | q' x ∨ x = Set.univ}
  refine ⟨q'', ?_, ?_, C, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, Set.preimage_eq_univ_iff, Set.preimage_empty,
      Set.subset_empty_iff, Set.range_eq_empty_iff, q'']
    exact ⟨.inl hq_empty, .inl hq'_empty⟩
  · -- sum of compact systems is a compact system
    sorry
  · choose A hA hB_eq using hB_prod
    choose A' hA' hB'_eq using hB'_prod
    have hC_eq : C = ⋂ k,
    (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm (A k, A' k) := by
      simp only [C, hB_eq, hB'_eq]
      rw [← Set.image_iInter (Equiv.bijective _)]
      congr
      ext
      sorry
    rw [hC_eq]
    refine memDelta.iInter fun k ↦ memDelta_of_prop ?_
    simp_rw [memSigma_memProd_iff] at hA hA'
    choose B K hB hK hA_eq using hA
    choose B' K' hB' hK' hA'_eq using hA'
    simp_rw [hA_eq, hA'_eq]
    have h_eq : (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm
          (⋃ n, B k n ×ˢ K k n, ⋃ n, B' k n ×ˢ K' k n)
        = ⋃ n, (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm
          (B k n ×ˢ K k n, B' k n ×ˢ K' k n) := by
      sorry
    rw [h_eq]
    refine memSigma.iUnion fun i ↦ ?_
    simp only [Set.sumEquiv, Set.le_eq_subset, OrderIso.symm_mk, RelIso.coe_fn_mk,
      Equiv.coe_fn_symm_mk]
    rw [Set.image_union]
    refine memSigma.union (memSigma_of_prop ?_) (memSigma_of_prop ?_)
    · refine ⟨B k i, Sum.inl '' (K k i), hB _ _, ?_, ?_⟩
      · simp only [Set.mem_setOf_eq, Set.preimage_eq_univ_iff, Set.preimage_inr_image_inl, q'']
        refine ⟨.inl ?_, .inl hq'_empty⟩
        sorry
      · ext
        simp [Equiv.prodSumDistrib]
        grind
    · refine ⟨B' k i, Sum.inr '' (K' k i), hB' _ _, ?_, ?_⟩
      · simp only [Set.mem_setOf_eq, Set.preimage_eq_univ_iff, Set.preimage_inl_image_inr, q'']
        refine ⟨.inl hq_empty, .inl ?_⟩
        sorry
      · ext
        simp [Equiv.prodSumDistrib]
        grind
  · simp only [hB_eq, hB'_eq, C]
    ext
    simp [Equiv.prodSumDistrib, Equiv.sumProdDistrib, Set.sumEquiv]

lemma IsPavingAnalytic.union {t : Set 𝓧}
    (hs : IsPavingAnalytic p s) (ht : IsPavingAnalytic p t) :
    IsPavingAnalytic p (s ∪ t) := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  choose 𝓚' h𝓚' ht𝓚' using ht
  exact (IsPavingAnalyticFor.union hs𝓚 ht𝓚').isPavingAnalytic

lemma isPavingAnalyticFor_of_memDelta_of_imp {p' : Set 𝓧 → Prop}
    (hs : memDelta p' s) (hqp : ∀ x, p' x → IsPavingAnalyticFor p 𝓚 x) :
    IsPavingAnalyticFor p (Π _ : ℕ, 𝓚) s := by
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalyticFor.iInter fun n ↦ hqp _ (hA n)

lemma isPavingAnalytic_of_memDelta_of_imp {p' : Set 𝓧 → Prop}
    (hs : memDelta p' s) (hqp : ∀ x, p' x → IsPavingAnalytic p x) :
    IsPavingAnalytic p s := by
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalytic.iInter fun n ↦ hqp _ (hA n)

lemma isPavingAnalyticFor_of_memSigma_of_imp {p' : Set 𝓧 → Prop}
    (hs : memSigma p' s) (hqp : ∀ x, p' x → IsPavingAnalyticFor p 𝓚 x) :
    IsPavingAnalyticFor p (Σ _ : ℕ, 𝓚) s := by
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalyticFor.iUnion fun n ↦ hqp _ (hA n)

lemma isPavingAnalytic_of_memSigma_of_imp {p' : Set 𝓧 → Prop}
    (hs : memSigma p' s) (hqp : ∀ x, p' x → IsPavingAnalytic p x) :
    IsPavingAnalytic p s := by
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalytic.iUnion fun n ↦ hqp _ (hA n)

-- He 1.28
/-- The projection of an analytic set is analytic. -/
lemma IsPavingAnalyticFor.fst {𝓚' : Type*} (hq_empty : q ∅) (hq : IsCompactSystem q)
    {s : Set (𝓧 × 𝓚)} (hs : IsPavingAnalyticFor (memProd p q) 𝓚' s) :
    IsPavingAnalyticFor p (𝓚 × 𝓚') (Prod.fst '' s) := by
  obtain ⟨q', hq'_empty, hq', K, hK, rfl⟩ := hs
  refine ⟨memProd q q', ?_, hq.memProd hq', Equiv.prodAssoc 𝓧 𝓚 𝓚' '' K, ?_, by ext; simp⟩
  · exact ⟨∅, ∅, hq_empty, hq'_empty, by simp⟩
  simp_rw [memProdSigmaDelta_iff] at hK ⊢
  obtain ⟨B, K', hB, hK', rfl⟩ := hK
  choose A K hA hK h_eq using hB
  refine ⟨A, fun n m ↦ K n m ×ˢ K' n m, hA, fun n m ↦ ?_, ?_⟩
  · exact ⟨K n m, K' n m, hK n m, hK' n m, rfl⟩
  · rw [Set.image_iInter (Equiv.prodAssoc 𝓧 𝓚 𝓚').bijective]
    simp_rw [Set.image_iUnion]
    congr
    ext
    simp
    grind

/-- The projection of an analytic set is analytic. -/
lemma IsPavingAnalytic.fst {𝓚 : Type} [Nonempty 𝓚] {q : Set 𝓚 → Prop}
    (hq_empty : q ∅) (hq : IsCompactSystem q)
    {s : Set (𝓧 × 𝓚)} (hs : IsPavingAnalytic (memProd p q) s) :
    IsPavingAnalytic p (Prod.fst '' s) := by
  obtain ⟨𝓚', h𝓚', hs𝓚'⟩ := hs
  exact (hs𝓚'.fst hq_empty hq).isPavingAnalytic

lemma IsPavingAnalyticFor.prod_left {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (ht : r t) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor (memProd r p) 𝓚 (t ×ˢ s) := by
  obtain ⟨q, hq_empty, hq_compact, s', hs_prod, hs_eq⟩ := hs
  have h_eq' : t ×ˢ s = Prod.fst '' ((Equiv.prodAssoc _ _ _).symm '' (t ×ˢ s')) := by
    rw [hs_eq]
    ext
    simp
    grind
  refine ⟨q, hq_empty, hq_compact, (Equiv.prodAssoc _ _ _).symm '' (t ×ˢ s'), ?_, h_eq'⟩
  simp_rw [memProdSigmaDelta_iff] at hs_prod ⊢
  obtain ⟨A, K, hA, hK, rfl⟩ := hs_prod
  refine ⟨fun n m ↦ t ×ˢ A n m, K, fun n m ↦ ?_, hK, ?_⟩
  · exact ⟨t, A n m, ht, hA n m, rfl⟩
  · rw [Set.prod_iInter, Set.image_iInter (Equiv.prodAssoc _ _ _).symm.bijective]
    simp_rw [Set.prod_iUnion, Set.image_iUnion]
    congr
    ext
    simp
    grind

lemma IsPavingAnalytic.prod_left {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (ht : r t) (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic (memProd r p) (t ×ˢ s) := by
  obtain ⟨𝓚, h𝓚, hs𝓚⟩ := hs
  exact (hs𝓚.prod_left ht).isPavingAnalytic

lemma IsPavingAnalyticFor.prod_right {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (hs : IsPavingAnalyticFor p 𝓚 s) (ht : r t) :
    IsPavingAnalyticFor (memProd p r) 𝓚 (s ×ˢ t) := by
  obtain ⟨q, hq_compact, s', hs_prod, hs_eq⟩ := hs
  sorry -- adapt the left proof

lemma IsPavingAnalytic.prod_right {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (hs : IsPavingAnalytic p s) (ht : r t) :
    IsPavingAnalytic (memProd p r) (s ×ˢ t) := by
  obtain ⟨𝓚, h𝓚, hs𝓚⟩ := hs
  exact (hs𝓚.prod_right ht).isPavingAnalytic

lemma isPavingAnalyticFor_of_memProd_isPavingAnalyticFor_left {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓨 × 𝓧)} (ht : memProd r (IsPavingAnalyticFor p 𝓚) t) :
    IsPavingAnalyticFor (memProd r p) 𝓚 t := by
  obtain ⟨A, s, hA, hs, rfl⟩ := ht
  exact hs.prod_left hA

lemma isPavingAnalytic_of_memProd_isPavingAnalytic_left {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓨 × 𝓧)} (ht : memProd r (IsPavingAnalytic p) t) :
    IsPavingAnalytic (memProd r p) t := by
  obtain ⟨A, s, hA, hs, rfl⟩ := ht
  exact hs.prod_left hA

lemma isPavingAnalyticFor_of_memProd_isPavingAnalyticFor_right {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓧 × 𝓨)} (ht : memProd (IsPavingAnalyticFor p 𝓚) r t) :
    IsPavingAnalyticFor (memProd p r) 𝓚 t := by
  obtain ⟨A, s, hA, hs, rfl⟩ := ht
  exact hA.prod_right hs

lemma isPavingAnalytic_of_memProd_isPavingAnalytic_right {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓧 × 𝓨)} (ht : memProd (IsPavingAnalytic p) r t) :
    IsPavingAnalytic (memProd p r) t := by
  obtain ⟨A, s, hA, hs, rfl⟩ := ht
  exact hA.prod_right hs

lemma isPavingAnalyticFor_of_memSigma_memProd_isPavingAnalyticFor_left
    {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set (𝓨 × 𝓧)}
    (ht : memSigma (memProd r (IsPavingAnalyticFor p 𝓚)) t) :
    IsPavingAnalyticFor (memProd r p) (Σ _ : ℕ, 𝓚) t := by
  refine isPavingAnalyticFor_of_memSigma_of_imp (p' := memProd r (IsPavingAnalyticFor p 𝓚)) ht ?_
  intro s hs
  exact isPavingAnalyticFor_of_memProd_isPavingAnalyticFor_left hs

lemma isPavingAnalyticFor_of_memSigma_memProd_isPavingAnalyticFor_right
    {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set (𝓧 × 𝓨)}
    (ht : memSigma (memProd (IsPavingAnalyticFor p 𝓚) r) t) :
    IsPavingAnalyticFor (memProd p r) (Σ _ : ℕ, 𝓚) t := by
  refine isPavingAnalyticFor_of_memSigma_of_imp (p' := memProd (IsPavingAnalyticFor p 𝓚) r) ht ?_
  intro s hs
  exact isPavingAnalyticFor_of_memProd_isPavingAnalyticFor_right hs

lemma IsPavingAnalyticFor.prod_memSigma_left {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (ht : memSigma r t) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor (memProd r p) (Σ _ : ℕ, 𝓚) (t ×ˢ s) := by
  refine isPavingAnalyticFor_of_memSigma_memProd_isPavingAnalyticFor_left ?_
  obtain ⟨A, hA, rfl⟩ := ht
  refine ⟨fun n ↦ A n ×ˢ s, fun n ↦ memProd_prod (hA n) hs, ?_⟩
  rw [Set.iUnion_prod_const]

lemma IsPavingAnalyticFor.prod_memSigma_right {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set 𝓨} (hs : IsPavingAnalyticFor p 𝓚 s) (ht : memSigma r t) :
    IsPavingAnalyticFor (memProd p r) (Σ _ : ℕ, 𝓚) (s ×ˢ t) := by
  refine isPavingAnalyticFor_of_memSigma_memProd_isPavingAnalyticFor_right ?_
  obtain ⟨A, hA, rfl⟩ := ht
  refine ⟨fun n ↦ s ×ˢ A n, fun n ↦ memProd_prod hs (hA n), ?_⟩
  rw [Set.prod_iUnion]

-- He 1.27
lemma IsPavingAnalyticFor.prod {𝓨 𝓚' : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (ht : IsPavingAnalyticFor r 𝓚' t) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor (memProd r p) ((Σ _ : ℕ, 𝓚') × (Σ _ : ℕ, 𝓚)) (t ×ˢ s) := by
  obtain ⟨t₁, ht₁, ht₁_subset⟩ := ht.exists_memSigma_superset
  obtain ⟨s₁, hs₁, hs₁_subset⟩ := hs.exists_memSigma_superset
  have h_eq : t ×ˢ s = (t ×ˢ s₁) ∩ (t₁ ×ˢ s) := by ext; simp; grind
  rw [h_eq]
  refine IsPavingAnalyticFor.inter ?_ ?_
  · exact ht.prod_memSigma_right hs₁
  · exact hs.prod_memSigma_left ht₁

lemma IsPavingAnalytic.prod {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (ht : IsPavingAnalytic r t) (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic (memProd r p) (t ×ˢ s) := by
  obtain ⟨𝓚', h𝓚', ht'⟩ := ht
  obtain ⟨𝓚, h𝓚, hs'⟩ := hs
  exact (IsPavingAnalyticFor.prod ht' hs').isPavingAnalytic

-- He 1.29
lemma isPavingAnalyticFor_isPavingAnalyticFor
    (hs : IsPavingAnalyticFor (IsPavingAnalyticFor p 𝓚) 𝓚 s) :
    IsPavingAnalyticFor p (𝓚 × (ℕ → (_ : ℕ) × 𝓚)) s := by
  obtain ⟨q, hq_empty, hq, t, ht, rfl⟩ := hs
  suffices IsPavingAnalyticFor (memProd p q) (ℕ → (_ : ℕ) × 𝓚) t by
    exact this.fst hq_empty hq
  refine isPavingAnalyticFor_of_memDelta_of_imp ht fun t ht ↦ ?_
  refine isPavingAnalyticFor_of_memSigma_of_imp ht fun t ht ↦ ?_
  exact isPavingAnalyticFor_of_memProd_isPavingAnalyticFor_right ht

lemma isPavingAnalytic_isPavingAnalytic
    (hs : IsPavingAnalytic (IsPavingAnalytic p) s) :
    IsPavingAnalytic p s := by
  obtain ⟨𝓚, h𝓚, hs'⟩ := hs
  obtain ⟨q, hq_empty, hq, t, ht, rfl⟩ := hs'
  suffices IsPavingAnalytic (memProd p q) t from (this.fst hq_empty hq)
  refine isPavingAnalytic_of_memDelta_of_imp ht fun t ht ↦ ?_
  refine isPavingAnalytic_of_memSigma_of_imp ht fun t ht ↦ ?_
  exact isPavingAnalytic_of_memProd_isPavingAnalytic_right ht

-- He 1.30
lemma IsPavingAnalytiFor.inter_set (hs : IsPavingAnalyticFor p 𝓚 s) (t : Set 𝓧) :
    IsPavingAnalyticFor (fun u ↦ ∃ v, p v ∧ u = v ∩ t) 𝓚 (s ∩ t) := by
  obtain ⟨q, hq_empty, hq, A, hA, rfl⟩ := hs
  let A' := (t ×ˢ .univ) ∩ A
  refine ⟨q, hq_empty, hq, A', ?_, ?_⟩
  · simp_rw [memProdSigmaDelta_iff] at hA ⊢
    obtain ⟨B, K, hB, hK, rfl⟩ := hA
    refine ⟨fun n m ↦ B n m ∩ t, K, fun n m ↦ ?_, hK, ?_⟩
    · exact ⟨B n m, hB n m, rfl⟩
    · simp only [A']
      simp_rw [Set.inter_iInter, Set.inter_iUnion]
      congr
      ext n : 1
      congr
      ext m x
      simp
      grind
  · ext; simp [A']; grind

-- He 1.30
lemma exists_isPavingAnalyticFor_of_inter_set (t : Set 𝓧)
    (hs : IsPavingAnalyticFor (fun u ↦ ∃ v, p v ∧ u = v ∩ t) 𝓚 s) :
    ∃ s', IsPavingAnalyticFor p 𝓚 s' ∧ s = s' ∩ t := by
  obtain ⟨q, hq_empty, hq, A, hA, rfl⟩ := hs
  rw [memProdSigmaDelta_iff] at hA
  obtain ⟨B, K, hB, hK, rfl⟩ := hA
  choose A' hA' hBA' using hB
  refine ⟨Prod.fst '' (⋂ n, ⋃ m, A' n m ×ˢ K n m), ?_, ?_⟩
  · refine ⟨q, hq_empty, hq, ?_⟩
    refine ⟨⋂ n, ⋃ m, A' n m ×ˢ K n m, ?_, rfl⟩
    rw [memProdSigmaDelta_iff]
    exact ⟨A', K, hA', hK, rfl⟩
  · simp only [hBA']
    have h_eq n m : (A' n m ∩ t) ×ˢ K n m = (A' n m ×ˢ K n m) ∩ (t ×ˢ .univ) := by
      ext; simp; grind
    simp_rw [h_eq, ← Set.iUnion_inter, ← Set.iInter_inter]
    suffices h_eq' : ∀ (s : Set (𝓧 × 𝓚)), Prod.fst '' (s ∩ (t ×ˢ .univ)) = Prod.fst '' s ∩ t by
      rw [h_eq']
    intro s
    ext s
    simp

-- He 1.31
lemma isPavingAnalytic_of_measurableSet_generateFrom (hp_empty : p ∅)
    (hp : ∀ s, p s → IsPavingAnalytic p sᶜ)
    (hs : MeasurableSet[MeasurableSpace.generateFrom {t | p t}] s) :
    IsPavingAnalytic p s := by
  let G : Set (Set 𝓧) := {t | IsPavingAnalytic p t ∧ IsPavingAnalytic p tᶜ}
  suffices s ∈ G by
    simp only [Set.mem_setOf_eq, G] at this
    exact this.1
  have hsG : MeasurableSet[MeasurableSpace.generateFrom G] s := by
    have h_subset : {t | p t} ⊆ G := by
      intro t ht
      simp only [Set.mem_setOf_eq, G]
      exact ⟨isPavingAnalytic_of_prop ht, hp t ht⟩
    have h_mono := MeasurableSpace.generateFrom_mono h_subset
    exact h_mono s hs
  refine MeasurableSpace.induction_on_inter (s := G) (C := fun s hs ↦ s ∈ G) ?_ ?_ ?_ ?_ ?_ ?_ s hsG
  · rfl
  · intro s hs t ht hst
    simp only [Set.mem_setOf_eq, G] at hs ht ⊢
    rw [Set.compl_inter]
    exact ⟨hs.1.inter ht.1, hs.2.union ht.2⟩
  · simp only [Set.mem_setOf_eq, Set.compl_empty, G]
    specialize hp ∅ hp_empty
    simp only [Set.compl_empty] at hp
    exact ⟨isPavingAnalytic_of_prop hp_empty, hp⟩
  · exact fun _ ↦ id
  · simp only [Set.mem_setOf_eq, compl_compl, and_imp, G]
    intro t _ ht htc
    exact ⟨htc, ht⟩
  · intro f hf_disj hf_meas hfG
    simp only [Set.mem_setOf_eq, Set.compl_iUnion, G] at hfG ⊢
    exact ⟨IsPavingAnalytic.iUnion fun n ↦ (hfG n).1,
      IsPavingAnalytic.iInter fun n ↦ (hfG n).2⟩

lemma aux (K : Set ℝ) (hK : IsCompact K) : memSigma IsCompact Kᶜ := by
  sorry

lemma aux' [MeasurableSpace 𝓧] (s : Set (𝓧 × ℝ)) (hs : memProd MeasurableSet IsCompact s) :
    memSigma (memProd MeasurableSet IsCompact) sᶜ := by
  obtain ⟨A, K, hA, hK, rfl⟩ := hs
  have hK' := aux K hK
  rw [Set.compl_prod_eq_union]
  refine memSigma.union ?_ ?_
  · sorry
  · sorry

lemma borel_eq_generateFrom_isCompact : borel ℝ = MeasurableSpace.generateFrom IsCompact := by
  refine le_antisymm ?_ ?_
  · rw [borel_eq_generateFrom_Icc]
    refine MeasurableSpace.generateFrom_mono fun s hs ↦ ?_
    obtain ⟨a, b, hab, rfl⟩ := hs
    exact isCompact_Icc
  · rw [MeasurableSpace.generateFrom_le_iff]
    exact fun _ hs ↦ hs.measurableSet

-- He 1.32 (1)
lemma _root_.MeasurableSet.isPavingAnalytic_isCompact_real {s : Set ℝ} (hs : MeasurableSet s) :
    IsPavingAnalytic IsCompact s := by
  have hs' : MeasurableSet[MeasurableSpace.generateFrom IsCompact] s := by
    rwa [← borel_eq_generateFrom_isCompact]
  refine isPavingAnalytic_of_measurableSet_generateFrom ?_ ?_ hs'
  · exact isCompact_empty
  · intro t ht
    exact isPavingAnalytic_of_memSigma_of_imp (aux t ht) (fun K hK ↦ isPavingAnalytic_of_prop hK)

-- He 1.32 (1)
lemma IsPavingAnalytic_measurableSet_iff_isPavingAnalytic_compact (s : Set ℝ) :
    IsPavingAnalytic IsCompact s ↔ IsPavingAnalytic MeasurableSet s := by
  refine ⟨fun hs ↦ hs.mono fun _ hs ↦ hs.measurableSet, fun hs ↦ ?_⟩
  exact isPavingAnalytic_isPavingAnalytic
    (hs.mono fun _ ↦ MeasurableSet.isPavingAnalytic_isCompact_real)

lemma isCountablySpanning_isCompact : IsCountablySpanning (IsCompact (X := ℝ)) := by
  refine ⟨fun n : ℕ ↦ Set.Icc (-n : ℝ) n, fun _ ↦ isCompact_Icc, ?_⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true]
  simp_rw [← abs_le]
  exact ⟨⌈|x|⌉₊, Nat.le_ceil _⟩

-- He 1.32 (2)
lemma _root_.MeasurableSet.isPavingAnalytic_memProd {s : Set (𝓧 × ℝ)} {m𝓧 : MeasurableSpace 𝓧}
    (hs : MeasurableSet s) :
    IsPavingAnalytic (memProd MeasurableSet IsCompact) s := by
  have h_compl (t : Set (𝓧 × ℝ)) (ht : memProd MeasurableSet IsCompact t) :
      IsPavingAnalytic (memProd MeasurableSet IsCompact) tᶜ := by
    exact isPavingAnalytic_of_memSigma_of_imp (aux' t ht) fun s hs ↦ isPavingAnalytic_of_prop hs
  refine isPavingAnalytic_of_measurableSet_generateFrom ?_ h_compl ?_
  · have : (∅ : Set (𝓧 × ℝ)) = ∅ ×ˢ ∅ := by simp
    rw [this]
    exact memProd_prod MeasurableSet.empty isCompact_empty
  · convert hs
    have h_prod_eq := generateFrom_eq_prod (α := 𝓧) (β := ℝ) (C := setOf MeasurableSet)
      (D := setOf IsCompact) MeasurableSpace.generateFrom_measurableSet ?_
      isCountablySpanning_measurableSet isCountablySpanning_isCompact
    swap
    · rw [Real.measurableSpace, borel_eq_generateFrom_isCompact]
      rfl
    rw [← h_prod_eq]
    congr with s
    simp only [Set.mem_setOf_eq, memProd]
    grind

-- He 1.32 (2)
lemma isPavingAnalytic_memProd_measurableSet_isCompact_iff {s : Set (𝓧 × ℝ)} [MeasurableSpace 𝓧] :
    IsPavingAnalytic (memProd MeasurableSet IsCompact) s ↔ IsPavingAnalytic MeasurableSet s := by
  refine ⟨fun hs ↦ hs.mono fun s hs ↦ ?_, fun hs ↦ ?_⟩
  · obtain ⟨A, K, hA, hK, rfl⟩ := hs
    exact hA.prod hK.measurableSet
  · exact isPavingAnalytic_isPavingAnalytic (hs.mono fun _ ↦ MeasurableSet.isPavingAnalytic_memProd)

-- He 1.32 (3)
lemma isPavingAnalytic_fst_of_memProd_measurableSet_isCompact [MeasurableSpace 𝓧] {s : Set (𝓧 × ℝ)}
    (hs : IsPavingAnalytic (memProd MeasurableSet IsCompact) s) :
    IsPavingAnalytic MeasurableSet (Prod.fst '' s) :=
  hs.fst isCompact_empty isCompactSystem_isCompact

lemma _root_.MeasurableSet.isPavingAnalytic_fst {m𝓧 : MeasurableSpace 𝓧} {s : Set (𝓧 × ℝ)}
    (hs : MeasurableSet s) :
    IsPavingAnalytic MeasurableSet (Prod.fst '' s) :=
  isPavingAnalytic_fst_of_memProd_measurableSet_isCompact
    (MeasurableSet.isPavingAnalytic_memProd hs)

/-- A set `s` of a measurable space `𝓧` is measurably analytic for a measurable space `𝓚` if it
is the projection of a measurable set of `𝓧 × 𝓚`. -/
def IsMeasurableAnalyticFor (𝓚 : Type*) [MeasurableSpace 𝓚] [MeasurableSpace 𝓧] (s : Set 𝓧) :
    Prop :=
  ∃ t : Set (𝓧 × 𝓚), MeasurableSet t ∧ s = Prod.fst '' t

/-- A set `s` of a measurable space `𝓧` is measurably analytic if it is the projection of
a measurable set of `𝓧 × ℝ`. -/
def IsMeasurableAnalytic [MeasurableSpace 𝓧] (s : Set 𝓧) : Prop :=
  IsMeasurableAnalyticFor ℝ s

/-- If a set is analytic in the measurable sense for any space `𝓚`, then it is analytic for `ℝ`. -/
lemma IsMeasurableAnalyticFor.isMeasurableAnalytic [MeasurableSpace 𝓧]
    [MeasurableSpace 𝓚] [StandardBorelSpace 𝓚]
    (hs : IsMeasurableAnalyticFor 𝓚 s) :
    IsMeasurableAnalytic s := by
  let f := embeddingReal 𝓚
  have hf : MeasurableEmbedding f := measurableEmbedding_embeddingReal 𝓚
  obtain ⟨t, ht, rfl⟩ := hs
  let t' : Set (𝓧 × ℝ) := Prod.map id f '' t
  refine ⟨t', ?_, ?_⟩
  · refine MeasurableEmbedding.measurableSet_image' ?_ ht
    exact MeasurableEmbedding.id.prodMap hf
  · ext
    simp [t']

lemma IsMeasurableAnalytic.isPavingAnalytic {m𝓧 : MeasurableSpace 𝓧} (hs : IsMeasurableAnalytic s) :
    IsPavingAnalytic MeasurableSet s := by
  obtain ⟨t, ht, rfl⟩ := hs
  exact MeasurableSet.isPavingAnalytic_fst ht

end MeasureTheory
