/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.HasGaussianLaw
import BrownianMotion.Continuity.KolmogorovChentsov
import BrownianMotion.Gaussian.GaussianProcess
import BrownianMotion.Gaussian.Moment
import BrownianMotion.Gaussian.ProjectiveLimit
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Brownian motion

-/

open MeasureTheory NNReal WithLp Finset NormedSpace
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

section IsPreBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (X : ℝ≥0 → Ω → ℝ)

class IsPreBrownian (P : Measure Ω := by volume_tac) : Prop where
  hasLaw : ∀ I : Finset ℝ≥0, HasLaw (fun ω ↦ I.restrict (X · ω)) (gaussianProjectiveFamily I) P

variable {X} {P : Measure Ω}

lemma IsPreBrownian.congr {Y : ℝ≥0 → Ω → ℝ} [hX : IsPreBrownian X P] (h : ∀ t, X t =ᵐ[P] Y t) :
    IsPreBrownian Y P where
  hasLaw I := by
    refine (hX.hasLaw I).congr ?_
    have : ∀ᵐ ω ∂P, ∀ i : I, X i ω = Y i ω := ae_all_iff.2 fun _ ↦ h _
    filter_upwards [this] with ω hω using funext fun i ↦ (hω i).symm

instance IsPreBrownian.isGaussianProcess [IsPreBrownian X P] : IsGaussianProcess X P where
  hasGaussianLaw I := (IsPreBrownian.hasLaw I).hasGaussianLaw

lemma IsPreBrownian.aemeasurable [IsPreBrownian X P] (t : ℝ≥0) : AEMeasurable (X t) P :=
  HasGaussianLaw.aemeasurable

lemma IsPreBrownian.hasLaw_gaussianLimit [IsPreBrownian X P]
    (hX : AEMeasurable (fun ω ↦ (X · ω)) P) :
    HasLaw (fun ω ↦ (X · ω)) gaussianLimit P where
  aemeasurable := hX
  map_eq := by
    refine isProjectiveLimit_gaussianLimit.unique ?_ |>.symm
    intro I
    rw [AEMeasurable.map_map_of_aemeasurable _ hX]
    · exact (IsPreBrownian.hasLaw I).map_eq
    · fun_prop

lemma isPreBrownian_of_hasLaw_gaussianLimit (hX : HasLaw (fun ω ↦ (X · ω)) gaussianLimit P) :
    IsPreBrownian X P where
  hasLaw _ := hasLaw_restrict_gaussianLimit.comp hX

@[gcongr]
private lemma mono_cast (n m : ℕ) (h : n = m) (i j : Fin n) (hij : i ≤ j) :
    h ▸ i ≤ h ▸ j := by
  cases h
  exact hij

private lemma fin_cast_eq (n m : ℕ) (h : n = m) (i : Fin n) :
    h ▸ i = Fin.cast h i := by
  cases h; rfl

section secret

variable (I : Finset ℝ≥0) (hI : I.Nonempty)

include hI in
lemma test {i : Fin (#I - 1 + 2)} (hi : i ≠ 0) : (i.pred hi).val < (I.sort (· ≤ ·)).length := by
  simp only [Fin.coe_pred, length_sort]
  have := i.isLt
  have := hI.card_ne_zero
  omega

lemma lol {t : ℝ≥0} (ht : t ∈ I) : (I.sort (· ≤ ·)).idxOf t < #I - 1 + 1 := by
  have h := List.idxOf_lt_length_of_mem (Finset.mem_sort (· ≤ ·) |>.2 ht)
  have := Finset.Nonempty.card_ne_zero ⟨t, ht⟩
  rw [← I.length_sort (· ≤ ·)]
  omega

/-- Given a nonempty `I : Finset ℝ≥0` of cardinality `n`, `toFin : Fin (#I - 1 + 2) → ℝ≥0`
is the map `(0, t₁, ..., tₙ)`, where `t₁ < ... < tₙ` are the elements of `I`. -/
noncomputable def toFin (i : Fin #I) : ℝ≥0 := (I.sort (· ≤ ·)).get (I.length_sort (· ≤ ·) ▸ i)

lemma monotone_toFin : Monotone (toFin I) :=
  fun i j hij ↦ (I.sort_sorted (· ≤ ·)).rel_get_of_le (by grind)

lemma toFin_mem (i : Fin #I) : toFin I i ∈ I := I.mem_sort (· ≤ ·) |>.1 <| List.get_mem _ _

noncomputable def ofFin (i : I) : Fin #I :=
  haveI : NeZero #I := ⟨Finset.Nonempty.card_ne_zero ⟨i.1, i.2⟩⟩
  Fin.ofNat #I ((I.sort (· ≤ ·)).idxOf i.1)

lemma toFin_ofFin (i : I) : toFin I (ofFin I i) = i.1 := by
  rw [toFin, ofFin]
  nth_rw 2 [← (I.sort (· ≤ ·)).idxOf_get (a := i.1)]
  · congr
    rw [fin_cast_eq]
    ext
    simp only [Fin.ofNat_eq_cast, Fin.coe_cast, Fin.val_natCast]
    rw [Nat.mod_eq_of_lt]
    rw [← I.length_sort (· ≤ ·)]
    refine List.idxOf_lt_length_of_mem ?_
    exact I.mem_sort (· ≤ ·) |>.2 i.2
  refine List.idxOf_lt_length_of_mem ?_
  exact I.mem_sort (· ≤ ·) |>.2 i.2

lemma ofFin_toFin (i : Fin #I) : ofFin I ⟨toFin I i, toFin_mem I i⟩ = i := by
  simp_rw [toFin, ofFin]
  rw [List.get_idxOf]
  · simp [fin_cast_eq]
  · exact sort_nodup (fun x1 x2 ↦ x1 ≤ x2) I

noncomputable def toFin' (i : Fin (#I + 1)) : ℝ≥0 :=
  if h : i = 0
    then 0
    else toFin I (i.pred h)

@[simp]
lemma toFin'_zero : toFin' I 0 = 0 := rfl

lemma toFin'_of_ne_zero (i : Fin (#I + 1)) (hi : i ≠ 0) :
    toFin' I i = toFin I (i.pred hi) := by rw [toFin', dif_neg hi]

@[simp]
lemma toFin'_succ (i : Fin #I) :
    toFin' I i.succ = toFin I i := by
  rw [toFin'_of_ne_zero, Fin.pred_succ]
  simp

lemma toFin'_mem (i : Fin (#I + 1)) (hi : i ≠ 0) : toFin' I i ∈ I := by
  rw [toFin'_of_ne_zero _ _ hi]
  exact toFin_mem I _

lemma monotone_toFin' : Monotone (toFin' I) := by
  intro i j hij
  obtain rfl | hi := eq_or_ne i 0
  · simp
  rw [toFin'_of_ne_zero I i hi, toFin'_of_ne_zero I j (by aesop)]
  apply monotone_toFin
  simpa

end secret

lemma IsPreBrownian.hasLaw_eval [h : IsPreBrownian X P] (t : ℝ≥0) :
    HasLaw (X t) (gaussianReal 0 t) P :=
  (hasLaw_eval_gaussianProjectiveFamily ⟨t, by simp⟩).comp (h.hasLaw {t})

lemma IsPreBrownian.hasLaw_sub [IsPreBrownian X P] (s t : ℝ≥0) :
    HasLaw (X s - X t) (gaussianReal 0 (max (s - t) (t - s))) P := by
  have : X s - X t = ((fun x ↦ x ⟨s, by simp⟩) - (fun x ↦ x ⟨t, by simp⟩)) ∘
      (fun ω ↦ ({s, t} : Finset ℝ≥0).restrict (X · ω)) := by ext; simp
  rw [this]
  exact (hasLaw_eval_sub_eval_gaussianProjectiveFamily _ _).comp (IsPreBrownian.hasLaw _)

lemma IsPreBrownian.law_zero [IsPreBrownian X P] : X 0 =ᵐ[P] 0 := by
  change id ∘ (X 0) =ᵐ[P] (fun _ ↦ 0) ∘ (X 0)
  apply ae_eq_comp
  · exact IsPreBrownian.aemeasurable 0
  · rw [(IsPreBrownian.hasLaw_eval 0).map_eq, gaussianReal_zero_var]
    exact MeasureTheory.ae_eq_dirac _

lemma IsPreBrownian.covariance_fun_eval [h : IsPreBrownian X P] (s t : ℝ≥0) :
    cov[fun ω ↦ X s ω, fun ω ↦ X t ω; P] = min s t := by
  convert (h.hasLaw {s, t}).covariance_fun_comp (f := Function.eval ⟨s, by simp⟩)
    (g := Function.eval ⟨t, by simp⟩) _ _
  · simp [covariance_eval_gaussianProjectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)

/-- A process `X : T → Ω → E` has independent increments if for any `n ≥ 2` and `t₁ ≤ ... ≤ tₙ`,
the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are independent. -/
def HasIndepIncrements {Ω T E : Type*} {mΩ : MeasurableSpace Ω} [Sub E]
    [Preorder T] [MeasurableSpace E] (X : T → Ω → E) (P : Measure Ω) : Prop :=
  ∀ n, ∀ t : Fin (n + 1) → T, Monotone t →
    iIndepFun (fun (i : Fin n) ω ↦ X (t i.succ) ω - X (t i.castSucc) ω) P

lemma IsPreBrownian.hasIndepIncrements [h : IsPreBrownian X P] : HasIndepIncrements X P := by
  have : IsProbabilityMeasure P := HasGaussianLaw.isProbabilityMeasure (X := X 0)
  refine fun n t ht ↦ HasGaussianLaw.iIndepFun_of_covariance_eq_zero fun i j hij ↦ ?_
  rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right]
  · simp_rw [IsPreBrownian.covariance_fun_eval]
    wlog h' : i < j generalizing i j
    · simp_rw [← this j i hij.symm (by omega), min_comm]
      ring
    have h1 : i.succ ≤ j.succ := Fin.succ_le_succ_iff.mpr h'.le
    have h2 : i.castSucc ≤ j.succ := Fin.le_of_lt h1
    have h3 : i.castSucc ≤ j.castSucc := Fin.le_castSucc_iff.mpr h1
    rw [min_eq_left (ht h1), min_eq_left (ht h'), min_eq_left (ht h2), min_eq_left (ht h3)]
    simp
  all_goals exact HasGaussianLaw.memLp_two

noncomputable def lin (I : Finset ℝ≥0) : (Fin #I → ℝ) →L[ℝ] (I → ℝ) :=
  { toFun x i := ∑ j ≤ ofFin I i, x j
    map_add' x y := by ext; simp [sum_add_distrib]
    map_smul' m x := by ext; simp [mul_sum]
    cont := by fun_prop }

lemma fonda (n : ℕ) (a : Fin n) (f : Fin (n + 1) → ℝ) :
    ∑ i ∈ Iic a, (f i.succ - f i.castSucc) = f a.succ - f 0 := by
  let g : Fin n → ℝ := fun i ↦ if i ∈ Iic a then f i.succ - f i.castSucc else 0
  let h : Fin n → ℝ := fun i ↦ f i.succ - f i.castSucc
  change ∑ i ∈ Iic a, h i = _
  have h1 : ∑ i ∈ Iic a, h i = ∑ i, g i := by
    simp_rw [g]
    rw [Finset.sum_ite_mem, univ_inter]
  let k : ℕ → ℝ := fun i ↦ if hi : i < n then g ⟨i, hi⟩ else 0
  have : ∑ i, g i = ∑ i : Fin n, k i := by
    congr with i
    simp_rw [k, dif_pos i.2]
  have h2 : ∑ i ∈ range n, k i = ∑ i ∈ range a.succ, k i := by
    refine Finset.sum_congr_of_eq_on_inter ?_ (by grind) (by grind)
    simp only [mem_range, Fin.val_succ, not_lt]
    intro i hi1 hi2
    simp_rw [k, dif_pos hi1, g]
    rw [if_neg]
    simpa
  have h3 : ∑ i ∈ range a.succ, k i =
      ∑ i ∈ range a.succ, (f (Fin.ofNat (n + 1) (i + 1)) - f (Fin.ofNat (n + 1) i)) := by
    apply Finset.sum_congr rfl
    simp only [Fin.val_succ, mem_range, Fin.ofNat_eq_cast]
    intro i hi
    simp_rw [k]
    rw [dif_pos (by omega)]
    simp_rw [g]
    rw [if_pos]
    · congr
      · ext
        simp only [Fin.succ_mk, Fin.val_natCast]
        rw [Nat.mod_eq_of_lt]
        omega
      · ext
        simp only [Fin.castSucc_mk, Fin.val_natCast]
        rw [Nat.mod_eq_of_lt]
        omega
    rw [Finset.mem_Iic, Fin.le_def]
    simp
    omega
  rw [h1, this, Fin.sum_univ_eq_sum_range, h2, h3,
    Finset.sum_range_sub (fun i ↦ f (Fin.ofNat (n + 1) i))]
  congr
  ext
  simp

lemma aux (h : ∀ᵐ ω ∂P, X 0 ω = 0) {I : Finset ℝ≥0} (hI : I.Nonempty) :
    (fun ω ↦ I.restrict (X · ω)) =ᵐ[P]
        (lin I) ∘ (fun ω i ↦ X (toFin' I i.succ) ω - X (toFin' I i.castSucc) ω) := by
  have : NeZero #I := ⟨hI.card_ne_zero⟩
  filter_upwards [h] with ω hω
  ext t
  simp only [restrict, lin, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply]
  rw [fonda #I (ofFin I t) (fun j ↦ X (toFin' I j) ω), toFin'_succ, toFin_ofFin, toFin'_zero, hω,
    sub_zero]

lemma IndepFun.charFunDual_map_add_eq_mul {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [CompleteSpace E] [BorelSpace E]
    [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : IndepFun X Y P) :
    charFunDual (P.map (X + Y)) = charFunDual (P.map X) * charFunDual (P.map Y) := by
  ext L
  rw [(hXY.hasLaw_add (hasLaw_map mX) (hasLaw_map mY)).map_eq, charFunDual_conv, Pi.mul_apply]

lemma IndepFun.charFun_map_add_eq_mul {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [CompleteSpace E] [BorelSpace E]
    [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : IndepFun X Y P) :
    charFun (P.map (X + Y)) = charFun (P.map X) * charFun (P.map Y) := by
  ext t
  rw [(hXY.hasLaw_add (hasLaw_map mX) (hasLaw_map mY)).map_eq, charFun_conv, Pi.mul_apply]

lemma IndepFun.hasLaw_sub_of_gaussian {X Y : Ω → ℝ} {μX μY : ℝ} {vX vY : ℝ≥0}
    (hX : HasLaw X (gaussianReal μX vX) P) (hY : HasLaw (X + Y) (gaussianReal μY vY) P)
    (h : IndepFun X Y P) :
    HasLaw Y (gaussianReal (μY - μX) (vY - vX)) P where
  aemeasurable := by
    convert hY.aemeasurable.sub hX.aemeasurable
    simp
  map_eq := by
    have : IsProbabilityMeasure P := hX.hasGaussianLaw.isProbabilityMeasure
    refine Measure.ext_of_charFun <| funext fun t ↦ ?_
    apply mul_left_cancel₀ (a := charFun (P.map X) t)
    · rw [hX.map_eq, charFun_gaussianReal]
      exact Complex.exp_ne_zero _
    · rw [← Pi.mul_apply, ← h.charFun_map_add_eq_mul, hY.map_eq, hX.map_eq, charFun_gaussianReal,
        charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add, NNReal.coe_sub,
        Complex.ofReal_sub]
      · congr
        field_simp
        push_cast
        ring
      · rw [← @Real.toNNReal_coe vY, ← @variance_id_gaussianReal μY vY, ← hY.variance_eq,
          h.variance_add, hX.variance_eq, variance_id_gaussianReal, Real.toNNReal_add,
          Real.toNNReal_coe]
        any_goals simp
        · exact variance_nonneg _ _
        · exact hX.hasGaussianLaw.memLp_two
        · convert hY.hasGaussianLaw.memLp_two.sub hX.hasGaussianLaw.memLp_two
          simp
      · exact hX.aemeasurable
      · convert hY.aemeasurable.sub hX.aemeasurable
        simp

lemma IndepFun.hasGaussianLaw_sub' {X Y : Ω → ℝ}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw (X + Y) P)
    (h : IndepFun X Y P) :
    HasGaussianLaw Y P where
  isGaussian_map := by
    have h1 : HasLaw X (gaussianReal _ _) P := ⟨hX.aemeasurable, hX.map_eq_gaussianReal⟩
    have h2 : HasLaw (X + Y) (gaussianReal _ _) P := ⟨hY.aemeasurable, hY.map_eq_gaussianReal⟩
    have := h.hasLaw_sub_of_gaussian h1 h2
    exact this.hasGaussianLaw.isGaussian_map

lemma IndepFun.hasGaussianLaw_sub {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [CompleteSpace E] [BorelSpace E]
    [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw (X + Y) P)
    (h : IndepFun X Y P) :
    HasGaussianLaw Y P where
  isGaussian_map := by
    refine ⟨fun L ↦ ?_⟩
    conv => enter [2, 1, 2, x]; change id (L x)
    rw [← integral_map, ← variance_id_map]
    · refine @IsGaussian.eq_gaussianReal _ ?_
      rw [AEMeasurable.map_map_of_aemeasurable]
      · refine @HasGaussianLaw.isGaussian_map (self := ?_)
        apply IndepFun.hasGaussianLaw_sub' (X := L ∘ X)
        · infer_instance
        · rw [← map_comp_add]
          infer_instance
        · exact h.comp L.measurable L.measurable
      · fun_prop
      · convert hY.aemeasurable.sub hX.aemeasurable
        simp
    all_goals fun_prop

lemma HasIndepIncrements.indepFun_incr {Ω T E : Type*} {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    [Preorder T] {X : T → Ω → E} {P : Measure Ω} (h : HasIndepIncrements X P)
    {r s t : T} (hrs : r ≤ s) (hst : s ≤ t) (hX : ∀ᵐ ω ∂P, X r ω = 0) :
    IndepFun (X s) (X t - X s) P := by
  let τ : Fin (2 + 1) → T := ![r, s, t]
  have hτ : Monotone τ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    any_goals simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, le_refl, τ]
    any_goals assumption
    any_goals contradiction
    exact hrs.trans hst
  have h' : (0 : Fin (1 + 1)) ≠ (1 : Fin (1 + 1)) := by simp
  have := (h 2 τ hτ).indepFun h'
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.cons_val_zero,
    Fin.castSucc_zero, Fin.succ_one_eq_two, Matrix.cons_val, Fin.castSucc_one, τ] at this
  have h' : X s =ᵐ[P] X s - X r := by
    filter_upwards [hX] with ω hω
    simp [hω]
  exact this.congr h'.symm ae_eq_rfl

lemma HasLaw.aeeq_of_dirac' {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} [MeasurableSingletonClass 𝓧]
    {x : 𝓧} {X : Ω → 𝓧}
    (hX : HasLaw X (.dirac x) P) : X =ᵐ[P] (fun _ ↦ x) := by
  apply ae_of_ae_map (p := fun y ↦ y = x) hX.aemeasurable
  rw [hX.map_eq, ae_dirac_iff]
  simp

lemma HasLaw.aeeq_of_dirac {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} [MeasurableSingletonClass 𝓧]
    {x : 𝓧} {X : Ω → 𝓧}
    (hX : HasLaw X (.dirac x) P) : ∀ᵐ ω ∂P, X ω = x := hX.aeeq_of_dirac'

lemma HasIndepIncrements.hasGaussianLaw_restrict (law : ∀ t, HasLaw (X t) (gaussianReal 0 t) P)
    (incr : HasIndepIncrements X P) :
    IsGaussianProcess X P where
  hasGaussianLaw I := by
    have := (law 0).isProbabilityMeasure_iff.1 inferInstance
    obtain rfl | hI := I.eq_empty_or_nonempty
    · constructor
      have : IsEmpty {x // x ∈ (∅ : Finset ℝ≥0)} := inferInstance
      have : P.map (fun ω ↦ Finset.restrict ∅ fun x ↦ X x ω) = .dirac this.elim := by
        ext s -
        apply Subsingleton.set_cases (p := fun s ↦ Measure.map _ _ s = _)
        · simp
        simp only [measure_univ]
        exact @measure_univ _ _ _
          (Measure.isProbabilityMeasure_map (aemeasurable_pi_lambda _ fun _ ↦ (law _).aemeasurable))
      rw [this]
      infer_instance
    have aeeq : ∀ᵐ ω ∂P, X 0 ω = 0 := by
      apply HasLaw.aeeq_of_dirac
      rw [← gaussianReal_zero_var]
      exact law 0
    have := aux aeeq hI
    refine @HasGaussianLaw.congr _ _ _ _ _ _ _ _ _ _ ?_ this.symm
    refine @HasGaussianLaw.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
    apply iIndepFun.hasGaussianLaw
    · intro i
      convert incr.indepFun_incr (zero_le (toFin' I i.castSucc))
        (monotone_toFin' I ?_) aeeq |>.hasGaussianLaw_sub ?_ ?_
      · exact Fin.castSucc_le_succ i
      · exact law (toFin' I i.castSucc) |>.hasGaussianLaw
      · simpa using law (toFin' I i.succ) |>.hasGaussianLaw
    exact incr _ _ (monotone_toFin' I)

lemma isPreBrownian_of (h1 : IsGaussianProcess X P) (h2 : ∀ t, P[X t] = 0)
    (h3 : ∀ s t, cov[X s, X t; P] = min s t) :
    IsPreBrownian X P where
  hasLaw := by
    intro I
    refine ⟨aemeasurable_pi_lambda _ fun _ ↦ h1.aemeasurable _, ?_⟩
    apply (MeasurableEquiv.toLp 2 (_ → ℝ)).map_measurableEquiv_injective
    rw [MeasurableEquiv.coe_toLp, ← PiLp.continuousLinearEquiv_symm_apply 2 ℝ]
    apply IsGaussian.ext
    · rw [integral_map, integral_map, integral_map]
      · simp only [PiLp.continuousLinearEquiv_symm_apply, id_eq]
        simp_rw [← PiLp.continuousLinearEquiv_symm_apply 2 ℝ, ← ContinuousLinearEquiv.coe_coe]
        rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_gaussianProjectiveFamily,
          ContinuousLinearMap.integral_comp_comm]
        · simp only [ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply,
            toLp_zero]
          convert toLp_zero 2
          ext i
          rw [eval_integral]
          · simp only [restrict, Pi.zero_apply]
            exact h2 _
          · exact fun _ ↦ h1.hasGaussianLaw_eval.integrable
        · apply Integrable.of_eval
          exact fun _ ↦ h1.hasGaussianLaw_eval.integrable
        · exact IsGaussian.integrable_id
      · fun_prop
      · exact aestronglyMeasurable_id
      · exact aemeasurable_pi_lambda _ fun _ ↦ h1.aemeasurable _
      · exact Measurable.aestronglyMeasurable (by fun_prop)
      · fun_prop
      · exact aestronglyMeasurable_id
    · refine ContinuousBilinForm.ext_of_isSymm (isPosSemidef_covInnerBilin ?_).isSymm
        (isPosSemidef_covInnerBilin ?_).isSymm fun x ↦ ?_
      · exact IsGaussian.memLp_two_id
      · exact IsGaussian.memLp_two_id
      rw [PiLp.continuousLinearEquiv_symm_apply, covInnerBilin_apply_pi, covInnerBilin_apply_pi]
      · congr with i
        congr with j
        congr 1
        rw [covariance_eval_gaussianProjectiveFamily, covariance_map]
        · change cov[X i, X j; P] = _
          exact h3 _ _
        · exact Measurable.aestronglyMeasurable (by fun_prop)
        · exact Measurable.aestronglyMeasurable (by fun_prop)
        · exact aemeasurable_pi_lambda _ (fun _ ↦ h1.aemeasurable _)
      · exact fun _ ↦ HasGaussianLaw.memLp_two
      · exact fun _ ↦ HasGaussianLaw.memLp_two

lemma isPreBrownian_of_hasLaw_of_hasIndepIncrements
    (law : ∀ t, HasLaw (X t) (gaussianReal 0 t) P) (incr : HasIndepIncrements X P) :
    IsPreBrownian X P := by
  apply isPreBrownian_of
  · exact incr.hasGaussianLaw_restrict law
  · intro t
    rw [(law t).integral_eq, integral_id_gaussianReal]
  · intro s t
    wlog hst : s ≤ t generalizing s t
    · rw [min_comm, covariance_comm, this t s (by grind)]
    have aeeq : ∀ᵐ ω ∂P, X 0 ω = 0 := by
      apply HasLaw.aeeq_of_dirac
      rw [← gaussianReal_zero_var]
      exact law 0
    have h1 := incr.indepFun_incr (zero_le s) hst aeeq
    have := (law 0).isProbabilityMeasure_iff.1 inferInstance
    have h2 : X t = X t - X s + X s := by simp
    rw [h2, covariance_add_right, h1.covariance_eq_zero, covariance_self, (law s).variance_eq,
      variance_id_gaussianReal]
    · simpa
    · exact (law s).aemeasurable
    · exact (law s).hasGaussianLaw.memLp_two
    · exact (law t).hasGaussianLaw.memLp_two.sub (law s).hasGaussianLaw.memLp_two
    · exact (law s).hasGaussianLaw.memLp_two
    · exact (law t).hasGaussianLaw.memLp_two.sub (law s).hasGaussianLaw.memLp_two
    · exact (law s).hasGaussianLaw.memLp_two

end IsPreBrownian

section IsBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (X : ℝ≥0 → Ω → ℝ)

class IsBrownian (P : Measure Ω := by volume_tac) : Prop extends IsPreBrownian X P where
  cont : ∀ᵐ ω ∂P, Continuous (X · ω)

end IsBrownian

def preBrownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω ↦ ω t

@[fun_prop]
lemma measurable_preBrownian (t : ℝ≥0) : Measurable (preBrownian t) := by
  unfold preBrownian
  fun_prop

lemma hasLaw_preBrownian : HasLaw (fun ω ↦ (preBrownian · ω)) gaussianLimit gaussianLimit where
  aemeasurable := (measurable_pi_lambda _ measurable_preBrownian).aemeasurable
  map_eq := Measure.map_id

instance isPreBrownian_preBrownian : IsPreBrownian preBrownian gaussianLimit :=
  isPreBrownian_of_hasLaw_gaussianLimit hasLaw_preBrownian

lemma isKolmogorovProcess_preBrownian {n : ℕ} (hn : 0 < n) :
    IsKolmogorovProcess preBrownian gaussianLimit (2 * n) n
      (Nat.doubleFactorial (2 * n - 1)) := by
  constructor
  · intro s t
    rw [← BorelSpace.measurable_eq]
    fun_prop
  rotate_left
  · positivity
  · positivity
  refine fun s t ↦ Eq.le ?_
  norm_cast
  simp_rw [edist_dist, Real.dist_eq]
  change ∫⁻ ω, (fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    ((preBrownian s - preBrownian t) ω) ∂_ = _
  rw [(IsPreBrownian.hasLaw_sub s t).lintegral_comp (f := fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    (by fun_prop)]
  simp_rw [← fun x ↦ ENNReal.ofReal_pow (abs_nonneg x)]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [pow_two_mul_abs]
    rw [← centralMoment_of_integral_id_eq_zero _ (by simp), ← NNReal.sq_sqrt (max _ _),
    centralMoment_fun_two_mul_gaussianReal, ENNReal.ofReal_mul (by positivity), mul_comm]
    norm_cast
    rw [pow_mul, NNReal.sq_sqrt, ← ENNReal.ofReal_pow dist_nonneg, ← NNReal.nndist_eq,
      NNReal.coe_pow, coe_nndist]
  · simp_rw [← Real.norm_eq_abs]
    apply MemLp.integrable_norm_pow'
    exact IsGaussian.memLp_id _ _ (ENNReal.natCast_ne_top (2 * n))
  · exact ae_of_all _ fun _ ↦ by positivity

lemma exists_brownian :
    ∃ Y : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[gaussianLimit] preBrownian t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))),
          ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · ω) U :=
  exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ (isKolmogorovProcess_preBrownian (by positivity : 0 < n + 2)).IsAEKolmogorovProcess)
    (fun n ↦ by finiteness) zero_lt_one (fun n ↦ by simp; norm_cast; omega)

noncomputable
def brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  exists_brownian.choose

@[fun_prop]
lemma measurable_brownian (t : ℝ≥0) : Measurable (brownian t) :=
  exists_brownian.choose_spec.1 t

lemma brownian_ae_eq_preBrownian (t : ℝ≥0) :
    brownian t =ᵐ[gaussianLimit] preBrownian t :=
  exists_brownian.choose_spec.2.1 t

lemma memHolder_brownian (ω : ℝ≥0 → ℝ) (t : ℝ≥0) (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) :
    ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (brownian · ω) U := by
  convert exists_brownian.choose_spec.2.2 ω t β hβ_pos ?_
  suffices ⨆ n, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)) = 2⁻¹ by rw [this]; norm_cast
  refine iSup_eq_of_forall_le_of_tendsto (F := Filter.atTop) (fun n ↦ ?_) ?_
  · calc
    ((↑(n + 2) : ℝ) - 1) / (2 * ↑(n + 2)) = 2⁻¹ * (n + 1) / (n + 2) := by
      simp only [Nat.cast_add, Nat.cast_ofNat]; field_simp; ring
    _ ≤ 2⁻¹ * 1 := by grw [mul_div_assoc, (div_le_one₀ (by positivity)).2]; linarith
    _ = 2⁻¹ := mul_one _
  · have : (fun n : ℕ ↦ ((↑(n + 2) : ℝ) - 1) / (2 * ↑(n + 2))) =
        (fun n : ℕ ↦ 2⁻¹ * ((n : ℝ) / (n + 1))) ∘ (fun n ↦ n + 1) := by
      ext n
      simp only [Nat.cast_add, Nat.cast_ofNat, Function.comp_apply, Nat.cast_one]
      field_simp
      ring
    rw [this]
    refine Filter.Tendsto.comp ?_ (Filter.tendsto_add_atTop_nat 1)
    nth_rw 2 [← mul_one 2⁻¹]
    exact (tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul _

@[fun_prop]
lemma continuous_brownian (ω : ℝ≥0 → ℝ) : Continuous (brownian · ω) := by
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  obtain ⟨U, hu_mem, ⟨C, h⟩⟩ := memHolder_brownian ω t 4⁻¹ (by norm_num)
    (NNReal.inv_lt_inv (by norm_num) (by norm_num))
  exact (h.continuousOn (by norm_num)).continuousAt hu_mem

instance isBrownian_brownian : IsBrownian brownian gaussianLimit where
  toIsPreBrownian := isPreBrownian_preBrownian.congr (fun t ↦ (brownian_ae_eq_preBrownian t).symm)
  cont := ae_of_all _ continuous_brownian

lemma measurable_brownian_uncurry : Measurable brownian.uncurry :=
  measurable_uncurry_of_continuous_of_measurable continuous_brownian measurable_brownian

lemma isKolmogorovProcess_brownian {n : ℕ} (hn : 0 < n) :
    IsKolmogorovProcess brownian gaussianLimit (2 * n) n
      (Nat.doubleFactorial (2 * n - 1)) where
  measurablePair := measurable_pair_of_measurable measurable_brownian
  kolmogorovCondition := (isKolmogorovProcess_preBrownian hn).IsAEKolmogorovProcess.congr
    (fun t ↦ (brownian_ae_eq_preBrownian t).symm) |>.kolmogorovCondition
  p_pos := by positivity
  q_pos := by positivity

lemma mem_pair_iff {α : Type*} [DecidableEq α] {x y z : α} :
    x ∈ ({y, z} : Finset α) ↔ x = y ∨ x = z := by simp

lemma covariance_brownian (s t : ℝ≥0) : cov[brownian s, brownian t; gaussianLimit] = min s t :=
  IsPreBrownian.covariance_fun_eval s t

lemma hasIndepIncrements_brownian : HasIndepIncrements brownian gaussianLimit :=
  IsPreBrownian.hasIndepIncrements

section Measure

noncomputable
def wienerMeasureAux : Measure {f : ℝ≥0 → ℝ // Continuous f} :=
  gaussianLimit.map (fun ω ↦ (⟨fun t ↦ brownian t ω, continuous_brownian ω⟩))

section ContinuousMap.MeasurableSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

instance : MeasurableSpace C(X, Y) := borel _
instance : BorelSpace C(X, Y) where
  measurable_eq := rfl

lemma isClosed_sUnion_of_finite {X : Type*} [TopologicalSpace X] {s : Set (Set X)}
    (h1 : s.Finite) (h2 : ∀ t ∈ s, IsClosed t) : IsClosed (⋃₀ s) := by
  rw [Set.sUnion_eq_biUnion]
  exact h1.isClosed_biUnion h2

open TopologicalSpace in
lemma ContinuousMap.borel_eq_iSup_comap_eval [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y] :
    borel C(X, Y) = ⨆ a : X, (borel Y).comap fun b ↦ b a := by
  -- https://math.stackexchange.com/questions/4789531/when-does-the-borel-sigma-algebra-of-compact-convergence-coincide-with-the-pr
  apply le_antisymm
  swap
  · refine iSup_le fun x ↦ ?_
    simp_rw [← measurable_iff_comap_le, ← BorelSpace.measurable_eq]
    exact Continuous.measurable (by fun_prop)
  -- Denote by `M(K, U)` the set of functions `f` such that `Set.MapsTo f K U`. These form a
  -- basis for the compact-open topology when `K` is compact and `U` is open.
  -- Because `C(X, Y)` is second-countable, it suffices to prove that those sets are measurable.
  -- Let therefore `K` be a compact set of `X` and `U` an open set of `Y`.
  rw [borel_eq_generateFrom_of_subbasis ContinuousMap.compactOpen_eq]
  refine MeasurableSpace.generateFrom_le fun s hs ↦ ?_
  obtain ⟨K, hK, U, hU, hs⟩ := hs
  rw [← hs]
  -- Consider `V` a countable basis of the topology on Y.
  let V := countableBasis Y
  have hV : IsTopologicalBasis V := isBasis_countableBasis Y
  have cV : V.Countable := countable_countableBasis Y
  let W₁ := {v | v ∈ V ∧ closure v ⊆ U}
  -- Consider `W` the set of `closure v`, where `v ∈ V` and `closure v ⊆ U`.
  let W := {v | ∃ u ∈ V, v ⊆ U ∧ v = closure u}
  -- Because `V` is countable, so is `W`.
  have cW : W.Countable := by
    apply (cV.image closure ).mono
    rintro - ⟨u, hu, -, rfl⟩
    exact ⟨u, hu, rfl⟩
  -- Because `Y` is regular, we can write that `U = ⋃_{v ∈ W} v`.
  have U_eq_sUnion_W : U = ⋃₀ W := by
    ext x
    rw [Set.mem_sUnion]
    constructor
    · intro hx
      obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := hV.nhds_basis_closure x |>.mem_iff.1 <| hU.mem_nhds hx
      exact ⟨closure v, ⟨v, hv2, hv3, rfl⟩, subset_closure hv1⟩
    · rintro ⟨-, ⟨t, ht1, ht2, rfl⟩, hx⟩
      exact ht2 hx
  -- Similarly, we can write that `U = ⋃_{v ∈ V, closure v ⊆ U} v`.
  have U_eq_sUnion_W₁ : U = ⋃₀ W₁ := by
    ext x
    rw [Set.mem_sUnion]
    refine ⟨fun hx ↦ ?_, fun ⟨t, ⟨ht1, ht2⟩, hx⟩ ↦ ht2 <| subset_closure hx⟩
    obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := hV.nhds_basis_closure x |>.mem_iff.1 <| hU.mem_nhds hx
    exact ⟨v, ⟨hv2, hv3⟩, hv1⟩
  -- For any continuous `f` such that `f '' K ⊆ U`, because `K` is compact, `f '' K` is compact.
  -- But we just proved that `U = ⋃_{v ∈ V, closure v ⊆ U} v`, and each `v ∈ V` is open,
  -- so there exists `J` a finite set of `v ∈ V` such that `closure v ⊆ U` and
  -- `f '' K ⊆ ⋃ v ∈ J, v`. We thus have `f '' K ⊆ ⋃ v ∈ J, closure v`. This is equivalent to
  -- having `I` a finite subset of `W` such that `f '' K ⊆ ⋃ v ∈ I, v`.
  have (f : C(X, Y)) (hf : K.MapsTo f U) : ∃ I, I.Finite ∧ I ⊆ W ∧ K.MapsTo f (⋃₀ I) := by
    simp_rw [Set.mapsTo_iff_image_subset] at hf ⊢
    rw [U_eq_sUnion_W₁, Set.sUnion_eq_biUnion] at hf
    have : ∀ i ∈ {v | v ∈ V ∧ closure v ⊆ U}, IsOpen i :=
      fun x ⟨hx, _⟩ ↦ hV.isOpen hx
    obtain ⟨b, hb1, hb2, hb3⟩ := (hK.image f.continuous).elim_finite_subcover_image this hf
    refine ⟨closure '' b, hb2.image _, ?_, ?_⟩
    · rintro - ⟨v, hv, rfl⟩
      exact ⟨v, (hb1 hv).1, (hb1 hv).2, rfl⟩
    rw [← Set.sUnion_eq_biUnion] at hb3
    exact hb3.trans <| Set.sUnion_mono_subsets fun _ ↦ subset_closure
  -- Therefore, we obtain that
  -- `M(K, U) = ⋃_{I ⊆ W, I finite}, M(K, ⋃ v ∈ I, v)`.
  have : {f : C(X, Y) | K.MapsTo f U} =
      ⋃₀ {v | ∃ I, I.Finite ∧ I ⊆ W ∧ v = {f : C(X, Y) | K.MapsTo f (⋃₀ I)}} := by
    ext f
    rw [Set.mem_sUnion]
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨I, hI1, hI2, hI3⟩ := this f h
      exact ⟨{f : C(X, Y) | K.MapsTo f (⋃₀ I)}, ⟨I, hI1, hI2, rfl⟩, hI3⟩
    · rintro ⟨-, ⟨I, hI1, hI2, rfl⟩, h⟩
      simp only [Set.mapsTo_iff_image_subset] at h ⊢
      rw [U_eq_sUnion_W]
      exact h.trans <| Set.sUnion_subset_sUnion hI2
  simp only
  rw [this]
  -- In particular, because `W` is countable, si this is a countable union.
  -- To show measurability it is therefore enough to show the measurability of each term.
  apply MeasurableSet.sUnion
  · let f : Set (Set Y) → Set C(X, Y) := fun I ↦ {f : C(X, Y) | Set.MapsTo (⇑f) K (⋃₀ I)}
    refine ((Set.countable_setOf_finite_subset cW).image f).mono ?_
    rintro - ⟨I, hI1, hI2, rfl⟩
    exact ⟨I, ⟨hI1, hI2⟩, rfl⟩
  -- Consider now `I` a finite subset of `W`.
  rintro - ⟨I, hI1, hI2, rfl⟩
  -- First, `⋃ v ∈ I, v` is closed as a finite union of closed sets.
  have hI : IsClosed (⋃₀ I) := by
    refine isClosed_sUnion_of_finite hI1 fun x hx ↦ ?_
    obtain ⟨u, -, -, rfl⟩ := hI2 hx
    exact isClosed_closure
  -- Consider `Q` a countable dense subset of `K`, which exists by second-countability assumption.
  obtain ⟨Q, cQ, dQ⟩ := TopologicalSpace.exists_countable_dense K
  have Q_sub_K : Subtype.val '' Q ⊆ K := Subtype.coe_image_subset K Q
  -- Because `f` is continuous and `⋃ v ∈ I, v` is closed and `Q` is dense in `K`, having
  -- `f '' K ⊆ ⋃ v ∈ I, v` is the same as `f '' Q ⊆ ⋃ v ∈ I, v`.
  have : {f : C(X, Y) | K.MapsTo f (⋃₀ I)} =
      {f : C(X, Y) | (Subtype.val '' Q).MapsTo f (⋃₀ I)} := by
    ext f
    refine ⟨fun h x hx ↦ h (Q_sub_K hx), fun h x hx ↦ ?_⟩
    obtain ⟨u, hu1, hu2⟩ := mem_closure_iff_seq_limit.1 <| Subtype.dense_iff.1 dQ hx
    exact hI.mem_of_tendsto ((f.continuous.tendsto x).comp hu2)
      (Filter.Eventually.of_forall fun n ↦ h (hu1 n))
  -- We can write `M(Q, ⋃ v ∈ I, v) = ⋂ q ∈ Q, (fun f ↦ f q) ⁻¹' (⋃ v ∈ I, v)`.
  have : {f : C(X, Y) | K.MapsTo f (⋃₀ I)} =
      ⋂ q ∈ Subtype.val '' Q, (fun f ↦ f q) ⁻¹' (⋃₀ I) := by
    rw [this]
    ext f
    rw [Set.mem_iInter₂]
    exact ⟨fun h x hx ↦ h hx, fun h x hx ↦ h x hx⟩
  rw [this]
  -- This is a countable intersection, so it suffices to prove that each term is measurable.
  -- Because `⋃ v ∈ I, v` is closed, it is measurable, so it suffices to prove that
  -- for any `q ∈ Q`, `fun f ↦ f q` is measurable for the product σ-algebra.
  -- The latter is the coarsest σ-algebra which makes the maps `fun f ↦ f x` measurable,
  -- so we are done.
  refine MeasurableSet.biInter (cQ.image _)
    fun q hq ↦ MeasurableSet.preimage hI.measurableSet (Measurable.le (le_iSup _ q) ?_)
  rw [BorelSpace.measurable_eq (α := Y)]
  exact comap_measurable _

lemma ContinuousMap.measurableSpace_eq_iSup_comap_eval
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y] :
    (inferInstance : MeasurableSpace C(X, Y))
      = ⨆ a : X, (inferInstance : MeasurableSpace Y).comap fun b ↦ b a := by
  simp_rw [BorelSpace.measurable_eq, borel_eq_iSup_comap_eval]

lemma ContinuousMap.measurable_iff_eval {α : Type*} [MeasurableSpace α]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (g : α → C(X, Y)) :
    Measurable g ↔ ∀ (x : X), Measurable fun (a : α) ↦ g a x := by
  simp_rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, measurable_iff_comap_le,
    MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp, Function.comp_def]

end ContinuousMap.MeasurableSpace

def MeasurableEquiv.continuousMap : {f : ℝ≥0 → ℝ // Continuous f} ≃ᵐ C(ℝ≥0, ℝ) where
  toFun := fun f ↦ ContinuousMap.mk f.1 f.2
  invFun := fun f ↦ ⟨f, f.continuous⟩
  left_inv f := rfl
  right_inv f := rfl
  measurable_toFun := by
    simp only [Equiv.coe_fn_mk]
    rw [ContinuousMap.measurable_iff_eval]
    intro x
    simp only [ContinuousMap.coe_mk]
    revert x
    rw [← measurable_pi_iff]
    exact measurable_subtype_coe
  measurable_invFun := by
    simp only [Equiv.coe_fn_symm_mk]
    refine Measurable.subtype_mk ?_
    rw [measurable_pi_iff]
    exact fun _ ↦ Continuous.measurable (by fun_prop)


noncomputable
def wienerMeasure : Measure C(ℝ≥0, ℝ) := wienerMeasureAux.map MeasurableEquiv.continuousMap

end Measure

end ProbabilityTheory
