/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.HasGaussianLaw
import Mathlib.Probability.Independence.Process
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Gaussian processes

-/

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {S T Ω E F : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T → Ω → E}

section Basic

variable [MeasurableSpace E] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-- A stochastic process is a Gaussian process if all its finite dimensional distributions are
Gaussian. -/
class IsGaussianProcess (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop where
  hasGaussianLaw : ∀ I : Finset T, HasGaussianLaw (fun ω ↦ I.restrict (X · ω)) P

attribute [instance] IsGaussianProcess.hasGaussianLaw

lemma IsGaussianProcess.isProbabilityMeasure [hX : IsGaussianProcess X P] :
    IsProbabilityMeasure P :=
  hX.hasGaussianLaw Classical.ofNonempty |>.isProbabilityMeasure

lemma IsGaussianProcess.aemeasurable [hX : IsGaussianProcess X P] (t : T) :
    AEMeasurable (X t) P := by
  by_contra h
  have := (hX.hasGaussianLaw {t}).isGaussian_map
  rw [Measure.map_of_not_aemeasurable] at this
  · exact this.toIsProbabilityMeasure.ne_zero _ rfl
  · rw [aemeasurable_pi_iff]
    push_neg
    exact ⟨⟨t, by simp⟩, h⟩

lemma IsGaussianProcess.modification [IsGaussianProcess X P] (hXY : ∀ t, X t =ᵐ[P] Y t) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    constructor
    rw [map_restrict_eq_of_forall_ae_eq fun t ↦ (hXY t).symm]
    infer_instance

end Basic

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

instance {E ι : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [Subsingleton ι] :
    BorelSpace (ι → E) := by
  refine ⟨le_antisymm pi_le_borel_pi ?_⟩
  obtain h | h := isEmpty_or_nonempty ι
  · exact fun s _ ↦ Subsingleton.set_cases .empty .univ s
  have := @Unique.mk' ι ⟨Classical.choice h⟩ inferInstance
  rw [borel]
  refine MeasurableSpace.generateFrom_le fun s hs ↦ ?_
  simp only [Pi.topologicalSpace, ciInf_unique, isOpen_induced_eq, Set.mem_image,
    Set.mem_setOf_eq] at hs
  simp_rw [MeasurableSpace.measurableSet_iSup, MeasurableSpace.measurableSet_comap]
  refine MeasurableSpace.GenerateMeasurable.basic _ ⟨Classical.choice h, ?_⟩
  obtain ⟨t, ht, rfl⟩ := hs
  exact ⟨t, ht.measurableSet, by rw [Subsingleton.elim (Classical.choice h) default]⟩

instance IsGaussianProcess.hasGaussianLaw_eval [IsGaussianProcess X P] (t : T) :
    HasGaussianLaw (X t) P := by
  have : X t = (ContinuousLinearMap.proj (R := ℝ) ⟨t, by simp⟩) ∘
    (fun ω ↦ ({t} : Finset T).restrict (X · ω)) := by ext; simp
  rw [this]
  infer_instance

variable [SecondCountableTopology E]

instance IsGaussianProcess.hasGaussianLaw_sub [IsGaussianProcess X P]
    {s t : T} : HasGaussianLaw (X s - X t) P := by
  classical
  have : X s - X t =
      (ContinuousLinearMap.proj (R := ℝ) (ι := ({s, t} : Finset T))
        (φ := fun _ ↦ E) ⟨s, by simp⟩ -
      ContinuousLinearMap.proj (R := ℝ) (ι := ({s, t} : Finset T))
        (φ := fun _ ↦ E) ⟨t, by simp⟩) ∘
    (fun ω ↦ Finset.restrict {s, t} (X · ω)) := by ext; simp
  rw [this]
  infer_instance

instance IsGaussianProcess.hasGaussianLaw_fun_sub
    [IsGaussianProcess X P] {s t : T} : HasGaussianLaw (fun ω ↦ X s ω - X t ω) P :=
  IsGaussianProcess.hasGaussianLaw_sub

instance IsGaussianProcess.hasGaussianLaw_increments
    [IsGaussianProcess X P] {n : ℕ} {t : Fin (n + 1) → T} :
    HasGaussianLaw (fun ω (i : Fin n) ↦ X (t i.succ) ω - X (t i.castSucc) ω) P := by
  classical
  let L : ((Finset.univ.image t) → E) →L[ℝ] Fin n → E :=
    { toFun x i := x ⟨t i.succ, by simp⟩ - x ⟨t i.castSucc, by simp⟩
      map_add' x y := by ext; simp; abel
      map_smul' m x := by ext; simp; module
      cont := by fun_prop }
  have : (fun ω i ↦ X (t i.succ) ω - X (t i.castSucc) ω) =
      L ∘ fun ω ↦ (Finset.univ.image t).restrict (X · ω) := by ext; simp [L]
  rw [this]
  infer_instance

lemma IsGaussianProcess.indepFun [CompleteSpace E] {X : S → Ω → E} {Y : T → Ω → E}
    (h : IsGaussianProcess (Sum.elim X Y) P) (hX : ∀ s, Measurable (X s))
    (hY : ∀ t, Measurable (Y t))
    (h' : ∀ s t (L₁ L₂ : StrongDual ℝ E), cov[L₁ ∘ X s, L₂ ∘ Y t; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P := by
  have := h.isProbabilityMeasure
  have _ s : HasGaussianLaw (X s) P := h.hasGaussianLaw_eval (.inl s)
  have _ t : HasGaussianLaw (Y t) P := h.hasGaussianLaw_eval (.inr t)
  refine IndepFun.indepFun_process hX hY fun I J ↦
    HasGaussianLaw.indepFun_of_cov ?_ fun L₁ L₂ ↦ ?_
  · let L : (I.disjSum J → E) →L[ℝ] (I → E) × (J → E) :=
      { toFun x := (fun s ↦ x ⟨Sum.inl s, Finset.inl_mem_disjSum.2 s.2⟩,
          fun t ↦ x ⟨Sum.inr t, Finset.inr_mem_disjSum.2 t.2⟩)
        map_add' x y := by ext <;> simp
        map_smul' c x := by ext <;> simp }
    have : (fun ω ↦ (fun i : I ↦ X i ω, fun j : J ↦ Y j ω)) =
        L ∘ (fun ω ↦ (I.disjSum J).restrict (Sum.elim X Y · ω)) := by
      ext <;> simp [L]
    rw [this]
    infer_instance
  classical
  have h1 : L₁ ∘ (fun ω i ↦ X i ω) = ∑ i : I, (L₁ ∘L .single ℝ _ i) ∘ X i := by
    ext ω
    simp only [Function.comp_apply, ← L₁.sum_comp_single, Finset.univ_eq_attach, Finset.sum_apply]
  have h2 : L₂ ∘ (fun ω j ↦ Y j ω) = ∑ j : J, (L₂ ∘L .single ℝ _ j) ∘ Y j := by
    ext ω
    simp only [Function.comp_apply, ← L₂.sum_comp_single, Finset.univ_eq_attach, Finset.sum_apply]
  rw [h1, h2, covariance_sum_sum]
  · exact Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ h' ..
  all_goals exact fun _ ↦ HasGaussianLaw.memLp_two

lemma IsGaussianProcess.iIndepFun [CompleteSpace E] {S : T → Type*}
    {X : (t : T) → (s : S t) → Ω → E}
    (h : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (hX : ∀ t s, Measurable (X t s))
    (h' : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂) (L₁ L₂ : StrongDual ℝ E),
      cov[L₁ ∘ X t₁ s₁, L₂ ∘ X t₂ s₂; P] = 0) :
    iIndepFun (fun t ω s ↦ X t s ω) P := by
  have := h.isProbabilityMeasure
  have _ t s : HasGaussianLaw (X t s) P := h.hasGaussianLaw_eval ⟨t, s⟩
  refine iIndepFun.iIndepFun_process hX fun I J ↦
    HasGaussianLaw.iIndepFun_of_cov ?_ fun i j hij L₁ L₂ ↦ ?_
  · classical
    let L : (I.sigma (fun i ↦ if hi : i ∈ I then J ⟨i, hi⟩ else ∅) → E) →L[ℝ] (i : I) → J i → E :=
      { toFun x i j := x ⟨⟨i, j⟩, by simp⟩
        map_add' x y := by ext; simp
        map_smul' c x := by ext; simp
        cont := by fun_prop }
    have : (fun ω (i : I) (j : J i) ↦ X i j ω) =
        L ∘ (fun ω ↦ (I.sigma (fun i ↦ if hi : i ∈ I then J ⟨i, hi⟩ else ∅)).restrict
          (fun p ↦ X p.1 p.2 ω)) := by
      ext; simp [L]
    rw [this]
    infer_instance
  classical
  have h1 : L₁ ∘ (fun ω k ↦ X i k ω) = ∑ k : J i, (L₁ ∘L .single ℝ _ k) ∘ X i k := by
    ext ω
    simp only [Function.comp_apply, ← L₁.sum_comp_single, Finset.univ_eq_attach, Finset.sum_apply]
  have h2 : L₂ ∘ (fun ω k ↦ X j k ω) = ∑ k : J j, (L₂ ∘L .single ℝ _ k) ∘ X j k := by
    ext ω
    simp only [Function.comp_apply, ← L₂.sum_comp_single, Finset.univ_eq_attach, Finset.sum_apply]
  rw [h1, h2, covariance_sum_sum]
  · exact Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦ h' i j (by simpa) ..
  all_goals exact fun _ ↦ HasGaussianLaw.memLp_two

open RealInnerProductSpace in
lemma IsGaussianProcess.indepFun'
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    {X : S → Ω → E} {Y : T → Ω → E}
    (h : IsGaussianProcess (Sum.elim X Y) P) (hX : ∀ s, Measurable (X s))
    (hY : ∀ t, Measurable (Y t))
    (h' : ∀ s t x y, cov[fun ω ↦ ⟪x, X s ω⟫, fun ω ↦ ⟪y, Y t ω⟫; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P :=
  h.indepFun hX hY fun _ _ _ _ ↦ by simpa [← inner_toDual_symm_eq_self] using h' ..

open RealInnerProductSpace in
lemma IsGaussianProcess.iIndepFun'
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E] {S : T → Type*}
    {X : (t : T) → (s : S t) → Ω → E}
    (h : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (hX : ∀ t s, Measurable (X t s))
    (h' : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂) (x y : E),
      cov[fun ω ↦ ⟪x, X t₁ s₁ ω⟫, fun ω ↦ ⟪y, X t₂ s₂ ω⟫; P] = 0) :
    ProbabilityTheory.iIndepFun (fun t ω s ↦ X t s ω) P :=
  h.iIndepFun hX fun _ _ h'' _ _ _ _ ↦ by simpa [← inner_toDual_symm_eq_self] using h' _ _ h'' ..

lemma IsGaussianProcess.indepFun'' {X : S → Ω → ℝ} {Y : T → Ω → ℝ}
    (h : IsGaussianProcess (Sum.elim X Y) P) (hX : ∀ s, Measurable (X s))
    (hY : ∀ t, Measurable (Y t)) (h' : ∀ s t, cov[X s, Y t; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P :=
  h.indepFun' hX hY fun _ _ _ _ ↦ by
    simp [mul_comm, covariance_mul_left, covariance_mul_right, h']

lemma IsGaussianProcess.iIndepFun'' {S : T → Type*}
    {X : (t : T) → (s : S t) → Ω → ℝ}
    (h : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (hX : ∀ t s, Measurable (X t s))
    (h' : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂), cov[X t₁ s₁, X t₂ s₂; P] = 0) :
    ProbabilityTheory.iIndepFun (fun t ω s ↦ X t s ω) P :=
  h.iIndepFun' hX fun _ _ h'' _ _ _ _ ↦ by
    simp [mul_comm, covariance_mul_left, covariance_mul_right, h' _ _ h'']

/-- If a stochastic process `Y` is such that for `s`, `Y s` can be written as a linear
combination of finitely many values of a Gaussian process, then `Y` is a Gaussian process. -/
lemma IsGaussianProcess.of_isGaussianProcess [IsGaussianProcess X P]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] {Y : S → Ω → F}
    (h : ∀ s, ∃ I : Finset T, ∃ L : (I → E) →L[ℝ] F, ∀ ω, Y s ω = L (I.restrict (X · ω))) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    choose J L hL using h
    classical
    let K : (I.biUnion J → E) →L[ℝ] I → F :=
      { toFun x s := L s (fun t ↦ x ⟨t.1, Finset.mem_biUnion.2 ⟨s.1, s.2, t.2⟩⟩)
        map_add' x y := by ext; simp [← Pi.add_def]
        map_smul' c x := by ext; simp [← Pi.smul_def]
        cont := by fun_prop }
    have : (fun ω ↦ I.restrict (Y · ω)) = K ∘ (fun ω ↦ (I.biUnion J).restrict (X · ω)) := by
      ext; simp [K, hL]; rfl
    rw [this]
    infer_instance

lemma IsGaussianProcess.comp_right [h : IsGaussianProcess X P]
    (f : S → T) : IsGaussianProcess (X ∘ f) P :=
  h.of_isGaussianProcess fun s ↦ ⟨{f s},
    { toFun x := x ⟨f s, by simp⟩
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

lemma IsGaussianProcess.comp_left {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (L : T → E →L[ℝ] F) [h : IsGaussianProcess X P] :
    IsGaussianProcess (fun t ω ↦ L t (X t ω)) P :=
  h.of_isGaussianProcess fun t ↦ ⟨{t},
    { toFun x := L t (x ⟨t, by simp⟩),
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

instance IsGaussianProcess.smul [SecondCountableTopology E] (c : T → ℝ) [IsGaussianProcess X P] :
    IsGaussianProcess (fun t ω ↦ c t • (X t ω)) P :=
  letI L t : E →L[ℝ] E :=
    { toFun x := c t • x
      map_add' := by simp
      map_smul' := by simp [smul_smul, mul_comm]
      cont := by fun_prop }
  IsGaussianProcess.comp_left L

instance IsGaussianProcess.shift [SecondCountableTopology E]
    [Add T] [h : IsGaussianProcess X P] (t₀ : T) :
    IsGaussianProcess (fun t ω ↦ X (t₀ + t) ω - X t₀ ω) P := by
  classical
  exact h.of_isGaussianProcess fun t ↦ ⟨{t₀, t₀ + t},
    { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
      map_add' x y := by simp; abel
      map_smul' c x := by simp; module },
    by simp⟩

instance IsGaussianProcess.restrict [SecondCountableTopology E]
    [h : IsGaussianProcess X P] (s : Set T) :
    IsGaussianProcess (fun t : s ↦ X t) P :=
  h.of_isGaussianProcess fun t ↦ ⟨{t.1},
    { toFun x := x ⟨t.1, by simp⟩
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

end ProbabilityTheory
