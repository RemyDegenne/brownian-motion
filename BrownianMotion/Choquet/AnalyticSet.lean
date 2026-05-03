/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Choquet.CompactSystem
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Analytic sets in the sense of a paved space

TODO: we use `IsCompactSystem`, which corresponds to semi-compact pavings for D-M. We use this and
not compact pavings (which would be the same, but for arbitrary intersections instead of countable
ones), because it's sufficient for our applications, and because it's easier to work with.

-/

@[expose] public section

open scoped ENNReal NNReal

variable {𝓧 𝓨 𝓚 𝓚' ι : Type*} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)} {s t : Set 𝓧} {f : ℕ → Set 𝓧}

theorem Set.iInter_prod {α β ι : Type*} {s : Set α} {t : ι → Set β} [hι : Nonempty ι] :
    (⋂ i, t i) ×ˢ s = ⋂ i, t i ×ˢ s := by
  ext x
  simp only [Set.mem_prod, Set.mem_iInter]
  exact ⟨fun ⟨h1, h2⟩ i ↦ ⟨h1 i, h2⟩, fun h ↦ ⟨fun i ↦ (h i).1, (h hι.some).2⟩⟩

lemma isCompactSystem_singleton_empty {α : Type*} : IsCompactSystem {(∅ : Set α)} :=
  fun C hC _ ↦ ⟨0, by simpa using hC 0⟩

/-- The set of Finset coercions forms a compact system. -/
lemma IsCompactSystem.finsetCoe :
    IsCompactSystem {t : Set 𝓚 | ∃ s : Finset 𝓚, (s : Set 𝓚) = t} := by
  let : TopologicalSpace 𝓚 := ⊥
  have : DiscreteTopology 𝓚 := ⟨rfl⟩
  apply of_nonempty_iInter
  intro C hC hC_nonempty
  choose s hs using hC
  have hsub : ∀ n, Set.dissipate C n ⊆ (s 0 : Set 𝓚) :=
    fun n => (Set.antitone_dissipate (Nat.zero_le n)).trans
      (Set.dissipate_subset le_rfl |>.trans (by rw [← hs 0]))
  have h_compact : IsCompact (Set.dissipate C 0) :=
    (s 0).finite_toSet.subset (hsub 0) |>.isCompact
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (Set.dissipate C ·)
    (fun i => Set.antitone_dissipate (Nat.le_succ i))
    hC_nonempty h_compact
    (fun _ => isClosed_discrete _)
  simp only [Set.iInter_dissipate, Set.mem_iInter] at hx
  simp only [Set.nonempty_iInter]
  use x

/-- Transport a compact system along an equivalence of types. -/
lemma IsCompactSystem.equiv (e : 𝓚 ≃ 𝓚') {S : Set (Set 𝓚)} (hS : IsCompactSystem S) :
    IsCompactSystem {t : Set 𝓚' | e ⁻¹' t ∈ S} := by
  intro D hD hD_empty
  have h (s : Set 𝓚') : s = ∅ ↔ e ⁻¹' s = ∅ := by
    repeat rw [Set.eq_empty_iff_forall_notMem]
    refine ⟨fun h x => h (e x), fun h x hx => h (e.invFun x) (by simp [hx])⟩
  rw [h, Set.preimage_iInter] at hD_empty
  obtain ⟨N, hN⟩ := hS (fun i => e ⁻¹' D i) hD hD_empty
  rw [Set.dissipate, ← Set.preimage_iInter₂] at hN
  refine ⟨N, by rw [Set.dissipate, h, hN]⟩

theorem iInter_sigma_eq_empty_iff {𝓚 : ι → Type*} {β : Type*} (s : β → Set ι)
    (f : β → (i : ι) → Set (𝓚 i)) :
     ⋂ b, (s b).sigma (f b) = ∅ ↔ ∀ i ∈ ⋂ b, s b, ⋂ b, f b i = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_iInter, Set.mem_sigma_iff]
  exact ⟨fun h i hi x hx => h ⟨i, x⟩ fun b => ⟨hi b, hx b⟩,
    fun h ⟨i, x⟩ hx => h i (fun b => (hx b).1) x (fun b => (hx b).2)⟩

/-- Variant with an additional condition `p b` (e.g. `b ≤ n` for `dissipate`). -/
theorem iInter₂_sigma_eq_empty_iff {𝓚 : ι → Type*} {β : Type*} {p : β → Prop}
    (s : β → Set ι) (f : β → (i : ι) → Set (𝓚 i)) :
    ⋂ (b) (_ : p b), (s b).sigma (f b) = ∅ ↔
      ∀ i ∈ ⋂ (b) (_ : p b), s b, ⋂ (b) (_ : p b), f b i = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_iInter, Set.mem_sigma_iff]
  exact ⟨fun h i hi x hx => h ⟨i, x⟩ fun b hb => ⟨hi b hb, hx b hb⟩,
    fun h ⟨i, x⟩ hx => h i (fun b hb => (hx b hb).1) x (fun b hb => (hx b hb).2)⟩

lemma IsCompactSystem.sigma {𝓚 : ι → Type*} {q : (i : ι) → Set (Set (𝓚 i))}
    (hq : ∀ i, IsCompactSystem (q i)) :
    IsCompactSystem {t : Set (Σ i, 𝓚 i) |
      ∃ s : Finset ι, t ∈ (s : Set ι).sigma '' (Set.univ.pi q)} := by
  classical
  intro C hC hC_empty
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_pi, Set.mem_univ,
    forall_const] at hC
  choose s f hf hCfs using hC
  simp_rw [Set.dissipate, ← hCfs]
  simp_rw [← hCfs, iInter_sigma_eq_empty_iff] at hC_empty
  by_cases h : ⋂ b, (s b : Set ι) = ∅
  · obtain ⟨n₀, hn₀⟩ := IsCompactSystem.finsetCoe (fun b => (s b : Set ι))
      (fun b => ⟨s b, rfl⟩) h
    refine ⟨n₀, ?_⟩
    rw [Set.dissipate] at hn₀
    simp_rw [iInter₂_sigma_eq_empty_iff, hn₀]
    simp
  · have hs : (s 0).Nonempty := by
      rw [← Finset.coe_nonempty, Set.nonempty_iff_ne_empty]
      exact fun h0 => h <| Set.subset_eq_empty (Set.iInter_subset _ 0) h0
    obtain ⟨j₀, hj₀⟩ := hs
    classical
    have key₀ : ∀ j ∈ ⋂ b, s b, ∃ N,
        ⋂ (b ≤ N), f b j = ∅ := by
      intro j hj
      exact hq j (f · j) (fun i ↦ hf i j) (hC_empty j hj)
    have key₁ : ∀ j ∉ ⋂ b, s b, ∃ N, j ∉ s N := by
      intro j hj
      simpa [Set.mem_iInter, not_forall] using hj
    -- For each j ∈ s 0, find N(j) such that the fibre over j in the bounded sigma is empty.
    have key : ∀ j ∈ s 0, ∃ N,
        ∀ x, (⟨j, x⟩ : Σ k, 𝓚 k) ∉ ⋂ y, ⋂ (_ : y ≤ N), (s y : Set ι).sigma (f y) := by
      intro j _
      by_cases hjs : j ∈ ⋂ b, s b
      · obtain ⟨N, hN⟩ := key₀ j hjs
        refine ⟨N, fun x hx => ?_⟩
        have hxslice : x ∈ ⋂ b, ⋂ _ : b ≤ N, f b j := by
          simp only [Set.mem_iInter, Set.mem_sigma_iff] at hx ⊢
          exact fun b hb => (hx b hb).2
        rw [hN] at hxslice; exact hxslice
      · obtain ⟨b, hb⟩ := key₁ j hjs
        refine ⟨b, fun x hx => ?_⟩
        have : (⟨j, x⟩ : Σ k, 𝓚 k) ∈ (s b : Set ι).sigma (f b) :=
          (Set.mem_iInter.mp (Set.mem_iInter.mp hx b) le_rfl)
        exact hb (Finset.mem_coe.mp (Set.mem_sigma_iff.mp this).1)
    choose N hN using key
    use (s 0).attach.sup fun jh => N jh.val jh.prop
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨j, x⟩ hjx
    have hj0 : j ∈ s 0 := by
      have : (⟨j, x⟩ : Σ k, 𝓚 k) ∈ (s 0 : Set ι).sigma (f 0) :=
        Set.mem_iInter.mp (Set.mem_iInter.mp hjx 0) (Nat.zero_le _)
      exact Finset.mem_coe.mp (Set.mem_sigma_iff.mp this).1
    have hle : N j hj0 ≤ ((s 0).attach.sup fun jh => N jh.val jh.prop) :=
      Finset.le_sup (f := fun jh : { x // x ∈ s 0 } => N jh.val jh.prop)
        (Finset.mem_attach _ ⟨j, hj0⟩)
    exact hN j hj0 x
      (Set.iInter₂_mono' (fun b' j' => ⟨b', j'.trans hle, Set.Subset.rfl⟩) hjx)

/-- Sigma variant with fixed `s = Finset.univ`: subsystem of `IsCompactSystem.sigma`. -/
lemma IsCompactSystem.sigma_ofFintype [Finite ι] {𝓚 : ι → Type*}
    {q : (i : ι) → Set (Set (𝓚 i))} (hq : ∀ i, IsCompactSystem (q i)) :
    IsCompactSystem (Set.univ.sigma '' (Set.univ.pi q)) := by
  have : Fintype ι := Fintype.ofFinite ι
  intro C hC hC_empty
  refine IsCompactSystem.sigma hq C (fun i => ?_) hC_empty
  obtain ⟨f, hf, hfC⟩ := hC i
  refine ⟨(Finset.univ : Finset ι), f, fun j _ => hf j (Set.mem_univ _), ?_⟩
  rw [Finset.coe_univ]; exact hfC

lemma IsCompactSystem.sum.{u} {𝓚 𝓚' : Type u} {q : Set (Set 𝓚)} {q' : Set (Set 𝓚')}
    (hq : IsCompactSystem q) (hq' : IsCompactSystem q') :
    IsCompactSystem {t | Sum.inl ⁻¹' t ∈ q ∧ Sum.inr ⁻¹' t ∈ q'} := by
  let Q : ∀ b : Bool, Set (Set (bif b then 𝓚' else 𝓚)) :=
    fun b => match b with | true => q' | false => q
  have hQ : ∀ b, IsCompactSystem (Q b) := fun b => by cases b <;> assumption
  have h_equiv := IsCompactSystem.equiv (Equiv.sumEquivSigmaBool 𝓚 𝓚').symm
    (IsCompactSystem.sigma_ofFintype hQ)
  convert h_equiv using 1
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const]
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨fun | true => Sum.inr ⁻¹' t | false => Sum.inl ⁻¹' t,
      fun | true => hr | false => hl,
      by ext ⟨b, x⟩; cases b <;> · simp [Equiv.sumEquivSigmaBool]; rfl⟩
  · rintro ⟨f, hf, hfC⟩
    have slice : ∀ b x, x ∈ f b ↔ (Equiv.sumEquivSigmaBool 𝓚 𝓚').symm ⟨b, x⟩ ∈ t :=
      fun b x => by simpa using Set.ext_iff.mp hfC ⟨b, x⟩
    exact ⟨by convert hf false using 1; ext x; exact (slice false x).symm,
            by convert hf true using 1; ext x; exact (slice true x).symm⟩

-- check if we need to insert univ or not
-- PP: we don't need to insert univ in order for the lemma to be true. We proved that we can insert
-- univ in any compact system, and it stays a compact system.
-- this is proved in xxx
-- proved in some mathlib PR
lemma IsCompactSystem.pi {𝓚 : ℕ → Type*} {q : (n : ℕ) → Set (Set (𝓚 n))}
    (hq : ∀ n, IsCompactSystem (q n)) :
    IsCompactSystem (Set.univ.pi '' (Set.univ.pi (fun n ↦ insert Set.univ (q n)))) := by
  sorry

namespace MeasureTheory

/-- A set `s` is analytic for a paving (predicate) `p` and a type `𝓚` if there exists a compact
system `q` of `𝓚` such that `s` is the projections of a set `t` that satisfies
`prodSigmaDelta p q`. -/
def IsPavingAnalyticFor (p : Set (Set 𝓧)) (𝓚 : Type*) (s : Set 𝓧) : Prop :=
  ∃ q : Set (Set 𝓚), ∅ ∈ q ∧ IsCompactSystem q ∧
    ∃ t : Set (𝓧 × 𝓚), t ∈ prodSigmaDelta p q ∧ s = Prod.fst '' t

/-- A set `s` is analytic for a paving (predicate) `p` if there exists a type `𝓚` and a compact
system `q` of `𝓚` such that `s` is the projections of a set `t` that satisfies
`prodSigmaDelta p q`. -/
def IsPavingAnalytic (p : Set (Set 𝓧)) (s : Set 𝓧) : Prop :=
  ∃ 𝓚 : Type, Nonempty 𝓚 ∧ IsPavingAnalyticFor p 𝓚 s

lemma IsPavingAnalyticFor.isPavingAnalytic {𝓚 : Type} [Nonempty 𝓚]
    (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalytic p s := ⟨𝓚, ‹_›, hs⟩

lemma isPavingAnalyticFor_of_mem (𝓚 : Type*) [Nonempty 𝓚] (hs : s ∈ p) :
    IsPavingAnalyticFor p 𝓚 s := by
  classical
  refine ⟨{Set.univ, ∅}, ?_, ?_, ⟨s ×ˢ .univ, ?_, by ext; simp⟩⟩
  · simp
  · exact IsCompactSystem.insert_univ isCompactSystem_singleton_empty
  · exact mem_prodSigmaDelta_of_mem hs (by simp)

lemma isPavingAnalytic_of_mem (hs : s ∈ p) : IsPavingAnalytic p s :=
  (isPavingAnalyticFor_of_mem ℝ hs).isPavingAnalytic

lemma IsPavingAnalyticFor.mono {p' : Set (Set 𝓧)} (hp : p ⊆ p') (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor p' 𝓚 s := by
  obtain ⟨q, hq_empty, hq_compact, t, ht_prod, rfl⟩ := hs
  refine ⟨q, hq_empty, hq_compact, ⟨t, ?_, rfl⟩⟩
  exact prodSigmaDelta.mono hp (fun _ ↦ id) ht_prod

lemma IsPavingAnalytic.mono {p' : Set (Set 𝓧)} (hp : p ⊆ p') (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic p' s := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  exact (IsPavingAnalyticFor.mono hp hs𝓚).isPavingAnalytic

-- He paragraph after 1.25
lemma IsPavingAnalyticFor.exists_mem_countableSupClosure_superset (hs : IsPavingAnalyticFor p 𝓚 s) :
    ∃ t, t ∈ countableSupClosure p ∧ s ⊆ t := by
  obtain ⟨q, hq_empty, hq_compact, B, hB_prod, rfl⟩ := hs
  rw [mem_prodSigmaDelta_iff] at hB_prod
  obtain ⟨A, hA, K, hK, rfl⟩ := hB_prod
  refine ⟨⋃ m, A 0 m, ?_, ?_⟩
  · exact ⟨fun m ↦ A 0 m, hA 0, rfl⟩
  · intro x hx
    simp only [Set.mem_image, Set.mem_iInter, Set.mem_iUnion, Set.mem_prod, Prod.exists,
      exists_and_right, exists_eq_right] at hx ⊢
    obtain ⟨_, h⟩ := hx
    choose n hn _ using h
    exact ⟨n 0, hn 0⟩

lemma IsPavingAnalyticFor.empty (𝓚 : Type*) (hp_empty : ∅ ∈ p) : IsPavingAnalyticFor p 𝓚 ∅ := by
  rcases isEmpty_or_nonempty 𝓚 with h_empty | h_nonempty
  · refine ⟨Set.univ, by simp, ?_, ∅ ×ˢ ∅, mem_prodSigmaDelta_of_mem hp_empty (by simp), by simp⟩
    simp only [IsCompactSystem]
    intro C _ _
    have h_eq_empty n : C n = ∅ := Set.eq_empty_of_isEmpty (C n)
    refine ⟨0, ?_⟩
    simpa using h_eq_empty 0
  · exact isPavingAnalyticFor_of_mem 𝓚 hp_empty

@[simp]
lemma IsPavingAnalytic.empty (hp_empty : ∅ ∈ p) : IsPavingAnalytic p ∅ :=
  (IsPavingAnalyticFor.empty ℝ hp_empty).isPavingAnalytic

@[simp]
lemma isPavingAnalyticFor_iff_eq_empty (𝓚 : Type*) [IsEmpty 𝓚] (hp_empty : ∅ ∈ p) (s : Set 𝓧) :
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
  let q' : Set (Set (Π n, 𝓚 n)) :=
    -- modeled on squareCylinders, but with univ instead of a finset
    Set.univ.pi '' (Set.univ.pi (fun n ↦ insert Set.univ (q n)))
  refine ⟨q', ?_, ?_, ⋂ n, C n, ?_, ?_⟩
  · simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const, Set.univ_pi_eq_empty_iff, q']
    exact ⟨fun _ ↦ ∅, by simp only [exists_const, and_true]; exact fun _ ↦ .inr (hq_empty _)⟩
  · exact IsCompactSystem.pi hq_compact
  · refine countableInfClosed_countableInfClosure.iInf_mem fun n ↦ ?_
    rw [← prodSigmaDelta]
    simp_rw [mem_prodSigmaDelta_iff] at hB_prod ⊢
    choose A hA K hK hB_eq using hB_prod
    refine ⟨A n, hA n, fun i j ↦ {y | y n ∈ K n i j}, fun i j ↦ ?_, ?_⟩
    · simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const, q']
      rcases Set.eq_empty_or_nonempty (K n i j) with hK_empty | hK_nonempty
      · simp only [hK_empty, Set.mem_empty_iff_false, Set.setOf_false]
        exact ⟨fun _ ↦ ∅, by
          simp only [Set.univ_pi_empty, and_true]; exact fun _ ↦ .inr (hq_empty _)⟩
      refine ⟨fun k ↦ if k = n then K k i j else Set.univ, fun k ↦ ?_, ?_⟩
      · simp only
        split_ifs with hk
        · subst hk
          exact .inr (hK k i j)
        · simp
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
  let q'' := {t : Set (Σ n, 𝓚 n) |
    ∃ s : Finset ℕ, t ∈ (s : Set ℕ).sigma '' (Set.univ.pi (fun n ↦ insert Set.univ (q n)))}
  refine ⟨q'', ?_, ?_, C, ?_, ?_⟩
  · simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const, q'']
    exact ⟨∅, fun _ ↦ Set.univ, by simp⟩
  · exact IsCompactSystem.sigma (fun n ↦ (hq_compact n).insert_univ)
  · choose A hA hB_eq using hB_prod
    have hC_eq : C = ⋂ k, Prod.swap '' ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm ''
        (Set.sigma Set.univ (fun n ↦ Prod.swap '' (A n k)))) := by
      simp only [C, ← hB_eq]
      rw [← Set.image_iInter Prod.swap_bijective, ← Set.image_iInter (Equiv.bijective _)]
      simp only [Equiv.sigmaProdDistrib_symm_apply, Set.iInf_eq_iInter]
      simp_rw [Set.image_iInter Prod.swap_bijective]
      congr
      ext
      simp
    rw [hC_eq]
    refine countableInfClosed_countableInfClosure.iInf_mem fun k ↦ subset_countableInfClosure ?_
    simp_rw [mem_countableSupClosure_image2_prod_iff] at hA
    choose B hB K hK hA_eq using hA
    simp_rw [hA_eq]
    have h_eq : Prod.swap '' ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm '' Set.univ.sigma
        fun n ↦ Prod.swap '' ⋃ n_1, B n k n_1 ×ˢ K n k n_1)
      = ⋃ n_1, Prod.swap '' ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm '' Set.univ.sigma
        fun n ↦ Prod.swap '' (B n k n_1 ×ˢ K n k n_1)) := by ext; simp; grind
    rw [h_eq]
    refine countableSupClosed_countableSupClosure.iSup_mem fun i ↦ ?_
    simp only [Set.image_swap_prod, Set.sigma_eq_biUnion, Set.mem_univ, Set.iUnion_true,
      Set.image_iUnion]
    refine countableSupClosed_countableSupClosure.iSup_mem fun j ↦ subset_countableSupClosure ?_
    refine ⟨B j k i, hB _ _ _, Sigma.mk j '' (K j k i), ?_, by ext; simp; grind⟩
    simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_const, q'']
    refine ⟨{j}, fun j ↦ K j k i, ?_⟩
    simp only [Finset.coe_singleton, Set.singleton_sigma, and_true]
    exact fun m ↦ .inr (hK _ _ _)
  · simp only [hB_eq, Equiv.sigmaProdDistrib_symm_apply, C]
    ext y
    simp only [Set.mem_iUnion, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
      Set.mem_sigma_iff, Set.mem_univ, Prod.swap_prod_mk, true_and, Sigma.exists, Prod.mk.injEq,
      ↓existsAndEq, exists_eq_right_right, Sigma.mk.injEq, and_true]
    grind

lemma IsPavingAnalytic.iUnion {s : ℕ → Set 𝓧} (hs : ∀ n, IsPavingAnalytic p (s n)) :
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
  let q'' : Set (Set (𝓚 × 𝓚')) := Set.image2 (· ×ˢ ·) (insert Set.univ q) (insert Set.univ q')
  refine ⟨q'', ?_, ?_, C ∩ C', ?_, ?_⟩
  · simp [q'']
    grind
  · exact IsCompactSystem.image2_prod hq_compact.insert_univ hq'_compact.insert_univ
  · refine infClosed_countableInfClosure ?_ ?_
    · rw [← prodSigmaDelta]
      simp_rw [mem_prodSigmaDelta_iff] at hB_prod ⊢
      choose A hA K hK hB_eq using hB_prod
      refine ⟨A, hA, fun i j ↦ {y | y.1 ∈ K i j}, fun i j ↦ ?_, ?_⟩
      · simp only [q'']
        rcases Set.eq_empty_or_nonempty (K i j) with hK_empty | hK_nonempty
        · simp only [hK_empty, Set.mem_empty_iff_false, Set.setOf_false]
          exact ⟨∅, by simp [hq_empty]⟩
        refine ⟨K i j, ?_⟩
        simp only [Set.mem_insert_iff, hK, or_true, exists_eq_or_imp, true_and]
        left
        ext
        simp
      · ext y
        simp only [hB_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq, C]
    · rw [← prodSigmaDelta]
      simp_rw [mem_prodSigmaDelta_iff] at hB'_prod ⊢
      choose A hA K hK hB_eq using hB'_prod
      refine ⟨A, hA, fun i j ↦ {y | y.2 ∈ K i j}, fun i j ↦ ?_, ?_⟩
      · simp only [q'']
        rcases Set.eq_empty_or_nonempty (K i j) with hK_empty | hK_nonempty
        · simp only [hK_empty, Set.mem_empty_iff_false, Set.setOf_false]
          exact ⟨∅, by simp [hq_empty]⟩
        simp only [Set.mem_image2, Set.mem_insert_iff, exists_eq_or_imp, Set.univ_prod_univ]
        left
        right
        refine ⟨K i j, ?_⟩
        simp only [hK, true_and]
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
lemma IsPavingAnalyticFor.union.{u} {𝓚 𝓚' : Type u} {t : Set 𝓧}
    (hs : IsPavingAnalyticFor p 𝓚 s) (ht : IsPavingAnalyticFor p 𝓚' t) :
    IsPavingAnalyticFor p (𝓚 ⊕ 𝓚') (s ∪ t) := by
  choose q hq_empty hq_compact B hB_prod hB_eq using hs
  choose q' hq'_empty hq'_compact B' hB'_prod hB'_eq using ht
  let C : Set (𝓧 × (𝓚 ⊕ 𝓚')) :=
    (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm (B, B')
  let q'' := {t | Sum.inl ⁻¹' t ∈ insert Set.univ q ∧ Sum.inr ⁻¹' t ∈ insert Set.univ q'}
  refine ⟨q'', ?_, ?_, C, ?_, ?_⟩
  · simp only [Set.mem_insert_iff, Set.preimage_eq_univ_iff, Set.mem_setOf_eq,
      Set.subset_empty_iff, Set.range_eq_empty_iff, Set.preimage_empty, q'']
    exact ⟨.inr hq_empty, .inr hq'_empty⟩
  · exact IsCompactSystem.sum hq_compact.insert_univ hq'_compact.insert_univ
  · choose A hA hB_eq using hB_prod
    choose A' hA' hB'_eq using hB'_prod
    have hC_eq : C = ⋂ k,
    (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm (A k, A' k) := by
      simp only [C, ← hB_eq, ← hB'_eq]
      rw [← Set.image_iInter (Equiv.bijective _)]
      congr
      calc Set.sumEquiv.symm (⋂ n, A n, ⋂ n, A' n)
      _ = Set.sumEquiv.symm (⨅ n, (A n, A' n)) := by
        congr 1
        ext <;> simp [iInf, Prod.fst_sInf, Prod.snd_sInf]
      _ = ⨅ n, Set.sumEquiv.symm (A n, A' n) := OrderIso.map_iInf _ _
      _ = ⋂ i, Set.sumEquiv.symm (A i, A' i) := rfl
    rw [hC_eq]
    refine countableInfClosed_countableInfClosure.iInf_mem fun k ↦ subset_countableInfClosure ?_
    simp_rw [mem_countableSupClosure_image2_prod_iff] at hA hA'
    choose B hB K hK hA_eq using hA
    choose B' hB' K' hK' hA'_eq using hA'
    simp_rw [hA_eq, hA'_eq]
    have h_eq : (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm
          (⋃ n, B k n ×ˢ K k n, ⋃ n, B' k n ×ˢ K' k n)
        = ⋃ n, (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm
          (B k n ×ˢ K k n, B' k n ×ˢ K' k n) := by
      rw [← Set.image_iUnion]
      congr 1
      calc Set.sumEquiv.symm (⋃ n, B k n ×ˢ K k n, ⋃ n, B' k n ×ˢ K' k n)
      _ = Set.sumEquiv.symm (⨆ n, (B k n ×ˢ K k n, B' k n ×ˢ K' k n)) := by
        congr 1
        ext <;> simp [iSup, Prod.fst_sSup, Prod.snd_sSup]
      _ = ⨆ n, Set.sumEquiv.symm (B k n ×ˢ K k n, B' k n ×ˢ K' k n) := OrderIso.map_iSup _ _
      _ = ⋃ i, Set.sumEquiv.symm (B k i ×ˢ K k i, B' k i ×ˢ K' k i) := rfl
    rw [h_eq]
    refine countableSupClosed_countableSupClosure.iSup_mem fun i ↦ ?_
    simp only [Set.sumEquiv, Set.le_eq_subset, OrderIso.symm_mk, RelIso.coe_fn_mk,
      Equiv.coe_fn_symm_mk]
    rw [Set.image_union]
    refine supClosed_countableSupClosure
      (subset_countableSupClosure ?_) (subset_countableSupClosure ?_)
    · refine ⟨B k i, hB _ _, Sum.inl '' (K k i), ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.preimage_eq_univ_iff, Set.mem_setOf_eq,
          Set.preimage_inr_image_inl, q'']
        refine ⟨.inr ?_, .inr hq'_empty⟩
        convert hK k i
        ext
        simp
      · ext; simp [Equiv.prodSumDistrib]; grind
    · refine ⟨B' k i, hB' _ _, Sum.inr '' (K' k i), ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.preimage_eq_univ_iff, Set.mem_setOf_eq,
          Set.preimage_inl_image_inr, q'']
        refine ⟨.inr hq_empty, .inr ?_⟩
        convert hK' k i
        ext
        simp
      · ext; simp [Equiv.prodSumDistrib]; grind
  · simp only [hB_eq, hB'_eq, C]
    ext
    simp [Equiv.prodSumDistrib, Equiv.sumProdDistrib, Set.sumEquiv]

lemma IsPavingAnalytic.union {t : Set 𝓧}
    (hs : IsPavingAnalytic p s) (ht : IsPavingAnalytic p t) :
    IsPavingAnalytic p (s ∪ t) := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  choose 𝓚' h𝓚' ht𝓚' using ht
  exact (IsPavingAnalyticFor.union hs𝓚 ht𝓚').isPavingAnalytic

lemma isPavingAnalyticFor_of_mem_countableInfClosure_of_imp {p' : Set (Set 𝓧)}
    (hs : s ∈ countableInfClosure p') (hqp : ∀ x, x ∈ p' → IsPavingAnalyticFor p 𝓚 x) :
    IsPavingAnalyticFor p (Π _ : ℕ, 𝓚) s := by
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalyticFor.iInter fun n ↦ hqp _ (hA n)

lemma isPavingAnalytic_of_mem_countableInfClosure_of_imp {p' : Set (Set 𝓧)}
    (hs : s ∈ countableInfClosure p') (hqp : ∀ x, x ∈ p' → IsPavingAnalytic p x) :
    IsPavingAnalytic p s := by
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalytic.iInter fun n ↦ hqp _ (hA n)

lemma isPavingAnalyticFor_of_mem_countableSupClosure_of_imp {p' : Set (Set 𝓧)}
    (hs : s ∈ countableSupClosure p') (hqp : ∀ x, x ∈ p' → IsPavingAnalyticFor p 𝓚 x) :
    IsPavingAnalyticFor p (Σ _ : ℕ, 𝓚) s := by
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalyticFor.iUnion fun n ↦ hqp _ (hA n)

lemma isPavingAnalytic_of_mem_countableSupClosure_of_imp {p' : Set (Set 𝓧)}
    (hs : s ∈ countableSupClosure p') (hqp : ∀ x, x ∈ p' → IsPavingAnalytic p x) :
    IsPavingAnalytic p s := by
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalytic.iUnion fun n ↦ hqp _ (hA n)

-- He 1.28
/-- The projection of an analytic set is analytic. -/
lemma IsPavingAnalyticFor.fst {𝓚' : Type*} (hq_empty : ∅ ∈ q) (hq : IsCompactSystem q)
    {s : Set (𝓧 × 𝓚)} (hs : IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p q) 𝓚' s) :
    IsPavingAnalyticFor p (𝓚 × 𝓚') (Prod.fst '' s) := by
  obtain ⟨q', hq'_empty, hq', K, hK, rfl⟩ := hs
  refine ⟨Set.image2 (· ×ˢ ·) q q', ?_, hq.image2_prod hq', Equiv.prodAssoc 𝓧 𝓚 𝓚' '' K, ?_,
    by ext; simp⟩
  · exact ⟨∅, hq_empty, ∅, hq'_empty, by simp⟩
  simp_rw [mem_prodSigmaDelta_iff] at hK ⊢
  obtain ⟨B, hB, K', hK', rfl⟩ := hK
  choose A hA K hK h_eq using hB
  refine ⟨A, hA, fun n m ↦ K n m ×ˢ K' n m, fun n m ↦ ?_, ?_⟩
  · exact ⟨K n m, hK n m, K' n m, hK' n m, rfl⟩
  · rw [Set.image_iInter (Equiv.prodAssoc 𝓧 𝓚 𝓚').bijective]
    simp_rw [Set.image_iUnion]
    congr
    ext
    simp
    grind

/-- The projection of an analytic set is analytic. -/
lemma IsPavingAnalytic.fst {𝓚 : Type} [Nonempty 𝓚] {q : Set (Set 𝓚)}
    (hq_empty : ∅ ∈ q) (hq : IsCompactSystem q)
    {s : Set (𝓧 × 𝓚)} (hs : IsPavingAnalytic (Set.image2 (· ×ˢ ·) p q) s) :
    IsPavingAnalytic p (Prod.fst '' s) := by
  obtain ⟨𝓚', h𝓚', hs𝓚'⟩ := hs
  exact (hs𝓚'.fst hq_empty hq).isPavingAnalytic

lemma IsPavingAnalyticFor.prod_left {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (ht : r t) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) 𝓚 (t ×ˢ s) := by
  obtain ⟨q, hq_empty, hq_compact, s', hs_prod, hs_eq⟩ := hs
  have h_eq' : t ×ˢ s = Prod.fst '' ((Equiv.prodAssoc _ _ _).symm '' (t ×ˢ s')) := by
    ext; simp; grind
  refine ⟨q, hq_empty, hq_compact, (Equiv.prodAssoc _ _ _).symm '' (t ×ˢ s'), ?_, h_eq'⟩
  simp_rw [mem_prodSigmaDelta_iff] at hs_prod ⊢
  obtain ⟨A, hA, K, hK, rfl⟩ := hs_prod
  refine ⟨fun n m ↦ t ×ˢ A n m, fun n m ↦ ?_, K, hK, ?_⟩
  · exact ⟨t, ht, A n m, hA n m, rfl⟩
  · rw [Set.prod_iInter, Set.image_iInter (Equiv.prodAssoc _ _ _).symm.bijective]
    congr with
    simp
    grind

lemma IsPavingAnalytic.prod_left {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (ht : r t) (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) r p) (t ×ˢ s) := by
  obtain ⟨𝓚, h𝓚, hs𝓚⟩ := hs
  exact (hs𝓚.prod_left ht).isPavingAnalytic

lemma IsPavingAnalyticFor.prod_right {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (hs : IsPavingAnalyticFor p 𝓚 s) (ht : r t) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p r) 𝓚 (s ×ˢ t) := by
  obtain ⟨q, hq_empty, hq_compact, s', hs_prod, hs_eq⟩ := hs
  have h_eq' : s ×ˢ t = Prod.fst '' ((Equiv.prodAssoc _ _ _).symm ''
      (Prod.map id Prod.swap '' ((Equiv.prodAssoc _ _ _) '' (s' ×ˢ t)))) := by
    congr with
    simp
    grind
  refine ⟨q, hq_empty, hq_compact, (Equiv.prodAssoc _ _ _).symm ''
      (Prod.map id Prod.swap '' ((Equiv.prodAssoc _ _ _) '' (s' ×ˢ t))), ?_, h_eq'⟩
  simp_rw [mem_prodSigmaDelta_iff] at hs_prod ⊢
  obtain ⟨A, hA, K, hK, rfl⟩ := hs_prod
  refine ⟨fun n m ↦ A n m ×ˢ t, fun n m ↦ ?_, K, hK, ?_⟩
  · exact ⟨A n m, hA n m, t, ht, rfl⟩
  · rw [Set.iInter_prod, Set.image_iInter (Equiv.prodAssoc _ _ _).bijective,
      Set.image_iInter, Set.image_iInter (Equiv.prodAssoc _ _ _).symm.bijective]
    swap; · exact Function.bijective_id.prodMap Prod.swap_bijective
    congr with n x
    simp
    grind

lemma IsPavingAnalytic.prod_right {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (hs : IsPavingAnalytic p s) (ht : r t) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) p r) (s ×ˢ t) := by
  obtain ⟨𝓚, h𝓚, hs𝓚⟩ := hs
  exact (hs𝓚.prod_right ht).isPavingAnalytic

lemma isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_left {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓨 × 𝓧)} (ht : t ∈ Set.image2 (· ×ˢ ·) r (IsPavingAnalyticFor p 𝓚)) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) 𝓚 t := by
  obtain ⟨A, hA, s, hs, rfl⟩ := ht
  exact hs.prod_left hA

lemma isPavingAnalytic_of_image2_prod_isPavingAnalytic_left {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓨 × 𝓧)} (ht : t ∈ Set.image2 (· ×ˢ ·) r (IsPavingAnalytic p)) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) r p) t := by
  obtain ⟨A, hA, s, hs, rfl⟩ := ht
  exact hs.prod_left hA

lemma isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_right {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓧 × 𝓨)} (ht : t ∈ Set.image2 (· ×ˢ ·) (IsPavingAnalyticFor p 𝓚) r) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p r) 𝓚 t := by
  obtain ⟨A, hA, s, hs, rfl⟩ := ht
  exact hA.prod_right hs

lemma isPavingAnalytic_of_image2_prod_isPavingAnalytic_right {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓧 × 𝓨)} (ht : t ∈ Set.image2 (· ×ˢ ·) (IsPavingAnalytic p) r) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) p r) t := by
  obtain ⟨A, hA, s, hs, rfl⟩ := ht
  exact hA.prod_right hs

lemma isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_left
    {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set (𝓨 × 𝓧)}
    (ht : t ∈ countableSupClosure (Set.image2 (· ×ˢ ·) r (IsPavingAnalyticFor p 𝓚))) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) (Σ _ : ℕ, 𝓚) t := by
  refine isPavingAnalyticFor_of_mem_countableSupClosure_of_imp
    (p' := Set.image2 (· ×ˢ ·) r (IsPavingAnalyticFor p 𝓚)) ht fun s hs ↦ ?_
  exact isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_left hs

lemma isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_right
    {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set (𝓧 × 𝓨)}
    (ht : t ∈ countableSupClosure (Set.image2 (· ×ˢ ·) (IsPavingAnalyticFor p 𝓚) r)) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p r) (Σ _ : ℕ, 𝓚) t := by
  refine isPavingAnalyticFor_of_mem_countableSupClosure_of_imp
    (p' := Set.image2 (· ×ˢ ·) (IsPavingAnalyticFor p 𝓚) r) ht fun s hs ↦ ?_
  exact isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_right hs

lemma IsPavingAnalyticFor.prod_mem_countableSupClosure_left {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set 𝓨} (ht : t ∈ countableSupClosure r) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) (Σ _ : ℕ, 𝓚) (t ×ˢ s) := by
  refine isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_left ?_
  obtain ⟨A, hA, rfl⟩ := ht
  refine ⟨fun n ↦ A n ×ˢ s, fun n ↦ ⟨A n, hA n, s, hs, rfl⟩, ?_⟩
  simp only [Set.iSup_eq_iUnion]
  rw [Set.iUnion_prod_const]

lemma IsPavingAnalyticFor.prod_mem_countableSupClosure_right {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set 𝓨} (hs : IsPavingAnalyticFor p 𝓚 s) (ht : t ∈ countableSupClosure r) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p r) (Σ _ : ℕ, 𝓚) (s ×ˢ t) := by
  refine isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_right ?_
  obtain ⟨A, hA, rfl⟩ := ht
  refine ⟨fun n ↦ s ×ˢ A n, fun n ↦ ⟨s, hs, A n, hA n, rfl⟩, ?_⟩
  simp only [Set.iSup_eq_iUnion]
  rw [Set.prod_iUnion]

-- He 1.27
lemma IsPavingAnalyticFor.prod {𝓨 𝓚' : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (ht : IsPavingAnalyticFor r 𝓚' t) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) ((Σ _ : ℕ, 𝓚') × (Σ _ : ℕ, 𝓚)) (t ×ˢ s) := by
  obtain ⟨t₁, ht₁, ht₁_subset⟩ := ht.exists_mem_countableSupClosure_superset
  obtain ⟨s₁, hs₁, hs₁_subset⟩ := hs.exists_mem_countableSupClosure_superset
  have h_eq : t ×ˢ s = (t ×ˢ s₁) ∩ (t₁ ×ˢ s) := by ext; simp; grind
  rw [h_eq]
  refine IsPavingAnalyticFor.inter ?_ ?_
  · exact ht.prod_mem_countableSupClosure_right hs₁
  · exact hs.prod_mem_countableSupClosure_left ht₁

lemma IsPavingAnalytic.prod {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (ht : IsPavingAnalytic r t) (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) r p) (t ×ˢ s) := by
  obtain ⟨𝓚', h𝓚', ht'⟩ := ht
  obtain ⟨𝓚, h𝓚, hs'⟩ := hs
  exact (IsPavingAnalyticFor.prod ht' hs').isPavingAnalytic

-- He 1.29
lemma isPavingAnalyticFor_isPavingAnalyticFor
    (hs : IsPavingAnalyticFor (IsPavingAnalyticFor p 𝓚) 𝓚 s) :
    IsPavingAnalyticFor p (𝓚 × (ℕ → (_ : ℕ) × 𝓚)) s := by
  obtain ⟨q, hq_empty, hq, t, ht, rfl⟩ := hs
  suffices IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p q) (ℕ → (_ : ℕ) × 𝓚) t by
    exact this.fst hq_empty hq
  refine isPavingAnalyticFor_of_mem_countableInfClosure_of_imp ht fun t ht ↦ ?_
  refine isPavingAnalyticFor_of_mem_countableSupClosure_of_imp ht fun t ht ↦ ?_
  exact isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_right ht

lemma isPavingAnalytic_isPavingAnalytic (hs : IsPavingAnalytic (IsPavingAnalytic p) s) :
    IsPavingAnalytic p s := by
  obtain ⟨𝓚, h𝓚, hs'⟩ := hs
  obtain ⟨q, hq_empty, hq, t, ht, rfl⟩ := hs'
  suffices IsPavingAnalytic (Set.image2 (· ×ˢ ·) p q) t from (this.fst hq_empty hq)
  refine isPavingAnalytic_of_mem_countableInfClosure_of_imp ht fun t ht ↦ ?_
  refine isPavingAnalytic_of_mem_countableSupClosure_of_imp ht fun t ht ↦ ?_
  exact isPavingAnalytic_of_image2_prod_isPavingAnalytic_right ht

@[simp]
lemma isPavingAnalytic_isPavingAnalytic_iff :
    IsPavingAnalytic (IsPavingAnalytic p) s ↔ IsPavingAnalytic p s :=
  ⟨isPavingAnalytic_isPavingAnalytic, fun hs ↦ isPavingAnalytic_of_mem hs⟩

-- He 1.30
lemma IsPavingAnalyticFor.inter_set (hs : IsPavingAnalyticFor p 𝓚 s) (t : Set 𝓧) :
    IsPavingAnalyticFor {u | ∃ v, v ∈ p ∧ u = v ∩ t} 𝓚 (s ∩ t) := by
  obtain ⟨q, hq_empty, hq, A, hA, rfl⟩ := hs
  let A' := (t ×ˢ .univ) ∩ A
  refine ⟨q, hq_empty, hq, A', ?_, by ext; simp; grind⟩
  simp_rw [mem_prodSigmaDelta_iff] at hA ⊢
  obtain ⟨B, hB, K, hK, rfl⟩ := hA
  refine ⟨fun n m ↦ B n m ∩ t, fun n m ↦ ⟨B n m, hB n m, rfl⟩, K, hK, ?_⟩
  simp only [A']
  simp_rw [Set.inter_iInter, Set.inter_iUnion]
  congr with
  simp
  grind

-- He 1.30
lemma exists_isPavingAnalyticFor_of_inter_set (t : Set 𝓧)
    (hs : IsPavingAnalyticFor {u | ∃ v, v ∈ p ∧ u = v ∩ t} 𝓚 s) :
    ∃ s', IsPavingAnalyticFor p 𝓚 s' ∧ s = s' ∩ t := by
  obtain ⟨q, hq_empty, hq, A, hA, rfl⟩ := hs
  rw [mem_prodSigmaDelta_iff] at hA
  obtain ⟨B, hB, K, hK, rfl⟩ := hA
  choose A' hA' hBA' using hB
  refine ⟨Prod.fst '' (⋂ n, ⋃ m, A' n m ×ˢ K n m), ?_, ?_⟩
  · refine ⟨q, hq_empty, hq, ?_⟩
    refine ⟨⋂ n, ⋃ m, A' n m ×ˢ K n m, ?_, rfl⟩
    rw [mem_prodSigmaDelta_iff]
    exact ⟨A', hA', K, hK, rfl⟩
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
lemma isPavingAnalytic_of_measurableSet_generateFrom (hp_empty : ∅ ∈ p)
    (hp : ∀ s, s ∈ p → IsPavingAnalytic p sᶜ)
    (hs : MeasurableSet[MeasurableSpace.generateFrom p] s) :
    IsPavingAnalytic p s := by
  let G : Set (Set 𝓧) := {t | IsPavingAnalytic p t ∧ IsPavingAnalytic p tᶜ}
  suffices s ∈ G by
    simp only [Set.mem_setOf_eq, G] at this
    exact this.1
  have hsG : MeasurableSet[MeasurableSpace.generateFrom G] s := by
    have h_subset : {t | p t} ⊆ G := by
      intro t ht
      simp only [Set.mem_setOf_eq, G]
      exact ⟨isPavingAnalytic_of_mem ht, hp t ht⟩
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
    exact ⟨isPavingAnalytic_of_mem hp_empty, hp⟩
  · exact fun _ ↦ id
  · simp only [Set.mem_setOf_eq, compl_compl, and_imp, G]
    intro t _ ht htc
    exact ⟨htc, ht⟩
  · intro f hf_disj hf_meas hfG
    simp only [Set.mem_setOf_eq, Set.compl_iUnion, G] at hfG ⊢
    exact ⟨IsPavingAnalytic.iUnion fun n ↦ (hfG n).1,
      IsPavingAnalytic.iInter fun n ↦ (hfG n).2⟩

lemma Iic_mem_countableSupClosure_Icc (u : ℝ) :
    Set.Iic u ∈ countableSupClosure {t | ∃ a b, Set.Icc a b = t} := by
  refine ⟨fun n ↦ Set.Icc (-(n : ℝ)) u, fun n ↦ ⟨-n, u, rfl⟩, ?_⟩
  ext x
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_Icc, exists_and_right, Set.mem_Iic,
    and_iff_right_iff_imp]
  simp_rw [neg_le]
  exact fun _ ↦ ⟨⌈-x⌉₊, Nat.le_ceil (-x)⟩

lemma Ici_mem_countableSupClosure_Icc (u : ℝ) :
    Set.Ici u ∈ countableSupClosure {t | ∃ a b, Set.Icc a b = t} := by
  refine ⟨fun n ↦ Set.Icc u n, fun n ↦ ⟨u, n, rfl⟩, ?_⟩
  ext x
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_Icc, exists_and_left, Set.mem_Ici,
    and_iff_left_iff_imp]
  exact fun _ ↦ ⟨⌈x⌉₊, Nat.le_ceil x⟩

lemma Iio_mem_countableSupClosure_Icc (u : ℝ) :
    Set.Iio u ∈ countableSupClosure {t | ∃ a b, Set.Icc a b = t} := by
  obtain ⟨s, hs_mono, hs_lt, hs_tendsto⟩ := exists_seq_strictMono_tendsto u
  have : Set.Iio u = ⋃ n, Set.Iic (s n) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    refine ⟨fun hxu ↦ ?_, fun ⟨i, hi⟩ ↦ hi.trans_lt (hs_lt i)⟩
    exact (hs_tendsto.eventually_const_le hxu).exists
  rw [this]
  exact countableSupClosed_countableSupClosure.iSup_mem
    fun n ↦ Iic_mem_countableSupClosure_Icc (s n)

lemma Ioi_mem_countableSupClosure_Icc (u : ℝ) :
    Set.Ioi u ∈ countableSupClosure {t | ∃ a b, Set.Icc a b = t} := by
  obtain ⟨s, hs_mono, hs_gt, hs_tendsto⟩ := exists_seq_strictAnti_tendsto u
  have : Set.Ioi u = ⋃ n, Set.Ici (s n) := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ici]
    refine ⟨fun hxu ↦ ?_, fun ⟨i, hi⟩ ↦ (hs_gt i).trans_le hi⟩
    exact (hs_tendsto.eventually_le_const hxu).exists
  rw [this]
  exact countableSupClosed_countableSupClosure.iSup_mem
    fun n ↦ Ici_mem_countableSupClosure_Icc (s n)

lemma univ_mem_countableSupClosure_Icc :
    (Set.univ : Set ℝ) ∈ countableSupClosure {t | ∃ a b, Set.Icc a b = t} := by
  have : (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ioi 0 := by ext; simp
  rw [this]
  exact supClosed_countableSupClosure (Iic_mem_countableSupClosure_Icc 0)
    (Ioi_mem_countableSupClosure_Icc 0)

lemma aux_Icc (l u : ℝ) : (Set.Icc l u)ᶜ ∈ countableSupClosure {t | ∃ a b, Set.Icc a b = t} := by
  rcases lt_or_ge u l with hlu | hlu
  · simp only [not_le, hlu, Set.Icc_eq_empty, Set.compl_empty]
    exact univ_mem_countableSupClosure_Icc
  · have : (Set.Icc l u)ᶜ = Set.Iio l ∪ Set.Ioi u := by ext; simp; grind
    rw [this]
    exact supClosed_countableSupClosure (Iio_mem_countableSupClosure_Icc l)
      (Ioi_mem_countableSupClosure_Icc u)

lemma aux'_Icc [MeasurableSpace 𝓧] (s : Set (𝓧 × ℝ))
    (hs : s ∈ Set.image2 (· ×ˢ ·) MeasurableSet {t | ∃ a b, Set.Icc a b = t}) :
     sᶜ ∈ countableSupClosure (Set.image2 (· ×ˢ ·) MeasurableSet {t | ∃ a b, Set.Icc a b = t}) := by
  obtain ⟨A, hA, K, ⟨l, u, rfl⟩, rfl⟩ := hs
  have hK' := aux_Icc l u
  rw [Set.compl_prod_eq_union]
  refine supClosed_countableSupClosure ?_ ?_
  · obtain ⟨B, hB, h_eq⟩ := univ_mem_countableSupClosure_Icc
    rw [← h_eq, Set.iSup_eq_iUnion, Set.prod_iUnion]
    refine ⟨fun i ↦ Aᶜ ×ˢ B i, fun n ↦ ?_, rfl⟩
    exact ⟨Aᶜ, hA.compl, B n, hB n, rfl⟩
  · obtain ⟨B, hB, h_eq⟩ := aux_Icc l u
    rw [← h_eq, Set.iSup_eq_iUnion, Set.prod_iUnion]
    refine ⟨fun i ↦ Set.univ ×ˢ B i, fun n ↦ ?_, rfl⟩
    exact ⟨Set.univ, .univ, B n, hB n, rfl⟩

lemma borel_eq_generateFrom_isCompact : borel ℝ = MeasurableSpace.generateFrom IsCompact := by
  refine le_antisymm ?_ ?_
  · rw [borel_eq_generateFrom_Icc]
    refine MeasurableSpace.generateFrom_mono fun s hs ↦ ?_
    obtain ⟨a, b, hab, rfl⟩ := hs
    exact isCompact_Icc
  · rw [MeasurableSpace.generateFrom_le_iff]
    exact fun _ hs ↦ hs.measurableSet

theorem borel_eq_generateFrom_Icc' (α : Type*) [TopologicalSpace α] [SecondCountableTopology α]
    [LinearOrder α] [OrderTopology α] :
    borel α = .generateFrom { S : Set α | ∃ (l u : α), Set.Icc l u = S } := by
  rw [borel_eq_generateFrom_Icc]
  refine le_antisymm ?_ ?_
  · exact MeasurableSpace.generateFrom_mono fun s ⟨l, u, hlu, hs⟩ ↦ ⟨l, u, hs⟩
  · rw [MeasurableSpace.generateFrom_le_iff]
    rintro - ⟨a, b, rfl⟩
    rcases le_or_gt a b with hab | hab
    · exact MeasurableSpace.measurableSet_generateFrom ⟨a, b, hab, rfl⟩
    · simp [hab]

-- Icc variant of He 1.32 (1)
lemma _root_.MeasurableSet.isPavingAnalytic_Icc_real {s : Set ℝ} (hs : MeasurableSet s) :
    IsPavingAnalytic {t | ∃ a b, Set.Icc a b = t} s := by
  have hs' : MeasurableSet[MeasurableSpace.generateFrom {t | ∃ a b, Set.Icc a b = t}] s := by
    rwa [Real.measurableSpace, borel_eq_generateFrom_Icc'] at hs
  refine isPavingAnalytic_of_measurableSet_generateFrom ?_ ?_ hs'
  · simp only [Set.mem_setOf_eq]
    exact ⟨1, 0, by simp⟩
  · rintro - ⟨l, u, rfl⟩
    exact isPavingAnalytic_of_mem_countableSupClosure_of_imp (p' := {t | ∃ a b, Set.Icc a b = t})
      (aux_Icc l u) (fun K hK ↦ isPavingAnalytic_of_mem hK)

lemma IsPavingAnalytic_measurableSet_iff_isPavingAnalytic_Icc (s : Set ℝ) :
    IsPavingAnalytic {t | MeasurableSet t} s ↔ IsPavingAnalytic {t | ∃ a b, Set.Icc a b = t} s := by
  refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
  · rw [← isPavingAnalytic_isPavingAnalytic_iff]
    exact hs.mono fun s hs ↦ MeasurableSet.isPavingAnalytic_Icc_real hs
  · refine hs.mono fun s hs ↦ ?_
    obtain ⟨l, u, rfl⟩ := hs
    simp

lemma isCountablySpanning_isCompact : IsCountablySpanning (IsCompact (X := ℝ)) := by
  refine ⟨fun n : ℕ ↦ Set.Icc (-n : ℝ) n, fun _ ↦ isCompact_Icc, ?_⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true, ← abs_le]
  exact ⟨⌈|x|⌉₊, Nat.le_ceil _⟩

lemma isCountablySpanning_Icc : IsCountablySpanning {t | ∃ a b : ℝ, Set.Icc a b = t} := by
  refine ⟨fun n : ℕ ↦ Set.Icc (-n : ℝ) n, fun n ↦ ⟨-n, n, rfl⟩, ?_⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true, ← abs_le]
  exact ⟨⌈|x|⌉₊, Nat.le_ceil _⟩

-- Icc version of He 1.32 (2)
lemma _root_.MeasurableSet.isPavingAnalytic_image2_prod {s : Set (𝓧 × ℝ)} {m𝓧 : MeasurableSpace 𝓧}
    (hs : MeasurableSet s) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) MeasurableSet {t | ∃ a b : ℝ, Set.Icc a b = t}) s := by
  have h_compl (t : Set (𝓧 × ℝ))
      (ht : t ∈ Set.image2 (· ×ˢ ·) MeasurableSet {t | ∃ a b : ℝ, Set.Icc a b = t}) :
      IsPavingAnalytic (Set.image2 (· ×ˢ ·) MeasurableSet {t | ∃ a b : ℝ, Set.Icc a b = t}) tᶜ :=
    isPavingAnalytic_of_mem_countableSupClosure_of_imp (aux'_Icc _ ht)
      fun s hs ↦ isPavingAnalytic_of_mem hs
  refine isPavingAnalytic_of_measurableSet_generateFrom ?_ h_compl ?_
  · have : (∅ : Set (𝓧 × ℝ)) = ∅ ×ˢ ∅ := by simp
    rw [this]
    exact ⟨∅, MeasurableSet.empty, ∅, ⟨1, 0, by simp⟩, rfl⟩
  · convert hs
    have h_prod_eq := generateFrom_eq_prod (α := 𝓧) (β := ℝ) (C := setOf MeasurableSet)
      (D := {t | ∃ a b : ℝ, Set.Icc a b = t}) MeasurableSpace.generateFrom_measurableSet ?_
      isCountablySpanning_measurableSet isCountablySpanning_Icc
    · rw [← h_prod_eq]
      rfl
    · rw [Real.measurableSpace, borel_eq_generateFrom_Icc']

-- Icc version of He 1.32 (2)
lemma isPavingAnalytic_image2_prod_measurableSet_Icc_iff {s : Set (𝓧 × ℝ)} [MeasurableSpace 𝓧] :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) MeasurableSet {t | ∃ a b : ℝ, Set.Icc a b = t}) s ↔
      IsPavingAnalytic MeasurableSet s := by
  refine ⟨fun hs ↦ hs.mono fun s hs ↦ ?_, fun hs ↦ ?_⟩
  · obtain ⟨A, hA, K, ⟨a, b, rfl⟩, rfl⟩ := hs
    exact hA.prod measurableSet_Icc
  · exact isPavingAnalytic_isPavingAnalytic
      (hs.mono fun _ ↦ MeasurableSet.isPavingAnalytic_image2_prod)

-- Icc version of He 1.32 (3)
lemma isPavingAnalytic_fst_of_image2_prod_measurableSet_Icc [MeasurableSpace 𝓧] {s : Set (𝓧 × ℝ)}
    (hs : IsPavingAnalytic (Set.image2 (· ×ˢ ·) MeasurableSet {t | ∃ a b : ℝ, Set.Icc a b = t}) s) :
    IsPavingAnalytic MeasurableSet (Prod.fst '' s) :=
  hs.fst (⟨1, 0, by simp⟩ : ∅ ∈ {t | ∃ a b : ℝ, Set.Icc a b = t}) isCompactSystem_Icc

lemma _root_.MeasurableSet.isPavingAnalytic_fst {m𝓧 : MeasurableSpace 𝓧} {s : Set (𝓧 × ℝ)}
    (hs : MeasurableSet s) :
    IsPavingAnalytic MeasurableSet (Prod.fst '' s) :=
  isPavingAnalytic_fst_of_image2_prod_measurableSet_Icc hs.isPavingAnalytic_image2_prod

/-- A set `s` of a measurable space `𝓧` is measurably analytic for a measurable space `𝓚` if it
is the projection of a measurable set of `𝓧 × 𝓚`. -/
def IsMeasurableAnalyticFor (𝓚 : Type*) [MeasurableSpace 𝓚] [MeasurableSpace 𝓧] (s : Set 𝓧) :
    Prop :=
  ∃ t : Set (𝓧 × 𝓚), MeasurableSet t ∧ s = Prod.fst '' t

/-- A set `s` of a measurable space `𝓧` is measurably analytic if it is the projection of
a measurable set of `𝓧 × ℝ`. -/
def IsMeasurableAnalytic [MeasurableSpace 𝓧] (s : Set 𝓧) : Prop := IsMeasurableAnalyticFor ℝ s

/-- If a set is measurably analytic for any standard Borel space `𝓚`,
then it is measurably analytic for `ℝ`. -/
lemma IsMeasurableAnalyticFor.isMeasurableAnalytic {m𝓧 : MeasurableSpace 𝓧}
    {m𝓚 : MeasurableSpace 𝓚} [StandardBorelSpace 𝓚]
    (hs : IsMeasurableAnalyticFor 𝓚 s) :
    IsMeasurableAnalytic s := by
  obtain ⟨t, ht, rfl⟩ := hs
  refine ⟨Prod.map id (embeddingReal 𝓚) '' t, ?_, by ext; simp⟩
  refine MeasurableEmbedding.measurableSet_image' ?_ ht
  exact MeasurableEmbedding.id.prodMap (measurableEmbedding_embeddingReal 𝓚)

lemma IsMeasurableAnalytic.isPavingAnalytic {m𝓧 : MeasurableSpace 𝓧} (hs : IsMeasurableAnalytic s) :
    IsPavingAnalytic MeasurableSet s := by
  obtain ⟨t, ht, rfl⟩ := hs
  exact MeasurableSet.isPavingAnalytic_fst ht

end MeasureTheory
