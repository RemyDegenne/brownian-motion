/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Continuity.KolmogorovChentsov
import BrownianMotion.Gaussian.GaussianProcess
import BrownianMotion.Gaussian.Moment
import BrownianMotion.Gaussian.ProjectiveLimit
import BrownianMotion.Auxiliary.HasGaussianLaw
import Mathlib.Probability.Independence.Integrable
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Brownian motion

-/

open MeasureTheory NNReal WithLp Finset NormedSpace Fin.NatCast
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

variable {I : Finset ℝ≥0} (hI : I.Nonempty)

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
noncomputable def toFin : Fin (#I - 1 + 2) → ℝ≥0 := fun i ↦ if h : i = 0 then 0 else
      (I.sort (· ≤ ·))[(i.pred h).val]'(test hI h)

@[simp]
lemma toFin_zero : toFin hI 0 = 0 := rfl

lemma toFin_of_ne_zero {i : Fin (#I - 1 + 2)} (hi : i ≠ 0) :
    toFin hI i = (I.sort (· ≤ ·))[(i.pred hi).val]'(test hI hi) := by
  rw [toFin, dif_neg hi]

include hI in
lemma omg (i : Fin (#I - 1 + 1)) : i.val < (I.sort (· ≤ ·)).length := by
  rw [Finset.length_sort]
  have := i.isLt
  have := hI.card_ne_zero
  omega

lemma toFin_succ (i : Fin (#I - 1 + 1)) : toFin hI i.succ = (I.sort (· ≤ ·))[i]'(omg hI i) := by
  simp [toFin]

lemma toFin_mem {i : Fin (#I - 1 + 2)} (hi : i ≠ 0) :
    toFin hI i ∈ I := by
  rw [toFin_of_ne_zero hI hi, ← Finset.mem_sort (· ≤ ·)]
  exact List.get_mem _ _

lemma _root_.List.getElem_idxOf' {α : Type*} [DecidableEq α] {a : α} {l : List α}
    (h : a ∈ l) : l[l.idxOf a]'(l.idxOf_lt_length_of_mem h) = a :=
  l.getElem_idxOf (l.idxOf_lt_length_of_mem h)

lemma ah {a b : ℕ} (h : a < b + 1) :
    (a : Fin (b + 1)).succ = (↑(a + 1) : Fin (b + 2)) := by
  ext
  simp only [Fin.val_succ, Fin.val_natCast]
  rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
  all_goals omega

lemma toFin_idxOf_sort {t : ℝ≥0} (ht : t ∈ I) :
    toFin ⟨t, ht⟩ ((I.sort (· ≤ ·)).idxOf t).succ = t := by
  rw [Nat.succ_eq_add_one, ← ah (lol ht), toFin_succ]
  simp only [Fin.getElem_fin, Fin.val_natCast]
  convert List.getElem_idxOf' (Finset.mem_sort (· ≤ ·) |>.2 ht)
  rw [Nat.mod_eq_of_lt (lol ht)]

lemma toFin_idxOf (i : Fin (#I - 1 + 1)) :
    (I.sort (· ≤ ·))[i.val]'(omg hI i) = toFin hI i.succ := by
  simp [toFin]

lemma monotone_toFin : Monotone (toFin hI) := by
  intro i j hij
  obtain rfl | hi := eq_or_ne i 0
  · simp
  rw [← Fin.pos_iff_ne_zero] at hi
  simp only [ne_eq, hi.ne', not_false_eq_true, toFin_of_ne_zero, Fin.coe_pred,
    (hi.trans_le hij).ne']
  apply (I.sort_sorted (· ≤ ·)).rel_get_of_le
  simp only [Fin.mk_le_mk, tsub_le_iff_right]
  omega

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
  ∀ n, ∀ t : Fin (n + 2) → T, Monotone t →
    iIndepFun (fun (i : Fin (n + 1)) ω ↦ X (t i.succ) ω - X (t i.castSucc) ω) P

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

noncomputable def lin (I : Finset ℝ≥0) : (Fin (#I - 1 + 1) → ℝ) →L[ℝ] (I → ℝ) :=
  { toFun x i := ∑ j ≤ (I.sort (· ≤ ·)).idxOf i.1, x j
    map_add' x y := by ext; simp [sum_add_distrib]
    map_smul' m x := by ext; simp [mul_sum]
    cont := by fun_prop }

lemma aux (h : ∀ᵐ ω ∂P, X 0 ω = 0) {I : Finset ℝ≥0} (hI : I.Nonempty) :
    (fun ω ↦ I.restrict (X · ω)) =ᵐ[P]
        (lin I) ∘ (fun ω i ↦ X (toFin hI i.succ) ω - X (toFin hI i.castSucc) ω) := by
  filter_upwards [h] with ω hω
  ext t
  simp only [restrict, lin, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, toFin,
    Fin.succ_ne_zero, ↓reduceDIte, Fin.pred_succ, Fin.castSucc_eq_zero_iff, Fin.coe_pred,
    Fin.coe_castSucc, Function.comp_apply, Fin.val_natCast, Fin.natCast_eq_zero]
  rw [← Finset.Iio_succ_eq_Iic, Nat.succ_eq_succ, Finset.Iio_eq_Ico]
  have : #I ≠ 0 := hI.card_ne_zero
  convert (Finset.sum_Ico_sub (fun n ↦ X (toFin hI n) ω) (bot_le)).symm with n hn
  · rw [toFin_idxOf_sort t.2]
    simp [hω]
  · have : n < #I := by
      have := Finset.mem_Ico.1 hn |>.2
      have := lol t.2
      omega
    rw [← ah (by omega), toFin_succ hI]
    rfl
  · have : n < #I := by
      have := Finset.mem_Ico.1 hn |>.2
      have := lol t.2
      omega
    split_ifs with h
    · rw [Nat.eq_zero_of_dvd_of_lt h (by omega), Nat.cast_zero, toFin_zero]
    · have : n ≠ 0 := fun h' ↦ h (h' ▸ Nat.dvd_zero _)
      rw [toFin_of_ne_zero]
      · congr 2
        simp only [Fin.val_natCast]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      · simp only [ne_eq, Fin.natCast_eq_zero]
        exact mt (Nat.eq_zero_of_dvd_of_lt · (by omega)) this

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
  let τ : Fin (1 + 2) → T := ![r, s, t]
  have hτ : Monotone τ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    any_goals simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, le_refl, τ]
    any_goals assumption
    any_goals contradiction
    exact hrs.trans hst
  have h' : (0 : Fin (1 + 1)) ≠ (1 : Fin (1 + 1)) := by simp
  have := (h 1 τ hτ).indepFun h'
  simp only [Nat.reduceAdd, Fin.isValue, Fin.succ_zero_eq_one, Matrix.cons_val_one,
    Matrix.cons_val_zero, Fin.castSucc_zero, Fin.succ_one_eq_two, Matrix.cons_val, Fin.castSucc_one,
    τ] at this
  have h' : X s =ᵐ[P] X s - X r := by
    filter_upwards [hX] with ω hω
    simp [hω]
  exact this.congr h'.symm ae_eq_rfl

lemma covariance_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    cov[X, Y; P] = P[X * Y] - P[X] * P[Y] := by
  simp_rw [covariance, sub_mul, mul_sub]
  rw [integral_sub, integral_sub, integral_sub]
  · simp_rw [integral_mul_const, integral_const_mul, integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul]
    simp
  · exact hY.const_mul _ |>.integrable (by norm_num)
  · exact integrable_const _
  · exact hX.integrable_mul hY
  · conv => enter [1, a]; rw [mul_comm]
    exact hX.const_mul _ |>.integrable (by norm_num)
  · apply Integrable.sub
    · exact hX.integrable_mul hY
    · conv => enter [1, a]; rw [mul_comm]
      exact hX.const_mul _ |>.integrable (by norm_num)
  · apply Integrable.sub
    · exact hY.const_mul _ |>.integrable (by norm_num)
    · exact integrable_const _

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
    (incr : HasIndepIncrements X P) (I : Finset ℝ≥0) :
    HasGaussianLaw (fun ω ↦ I.restrict fun x ↦ X x ω) P where
  isGaussian_map := by
    have := (law 0).isProbabilityMeasure_iff.1 inferInstance
    obtain rfl | hI := I.eq_empty_or_nonempty
    · have : IsEmpty {x // x ∈ (∅ : Finset ℝ≥0)} := inferInstance
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
    rw [Measure.map_congr this]
    have : HasGaussianLaw
        (fun ω (i : Fin (#I - 1 + 1)) ↦ X (toFin hI i.succ) ω - X (toFin hI i.castSucc) ω) P := by
      have ind := incr (#I - 1) (toFin hI) (monotone_toFin hI)
      have (i : Fin (#I - 1 + 1)) :
          HasGaussianLaw (fun ω ↦ X (toFin hI i.succ) ω - X (toFin hI i.castSucc) ω) P := by
        have : i.succ ≠ i.castSucc := Fin.castSucc_lt_succ i |>.ne'
        apply IndepFun.hasGaussianLaw_sub (X := X (toFin hI i.castSucc))
          (Y := X (toFin hI i.succ) - X (toFin hI i.castSucc))
        · exact (law _).hasGaussianLaw
        · simpa using (law _).hasGaussianLaw
        apply incr.indepFun_incr (r := 0)
        · simp
        · apply monotone_toFin hI
          exact Fin.castSucc_lt_succ i |>.le
        · exact aeeq
      exact ind.hasGaussianLaw
    infer_instance

lemma isPreBrownian_of_hasLaw_of_hasIndepIncrements
    (law : ∀ t, HasLaw (X t) (gaussianReal 0 t) P) (incr : HasIndepIncrements X P) :
    IsPreBrownian X P where
  hasLaw := by
    classical
    have : IsProbabilityMeasure P := (law 0).hasGaussianLaw.isProbabilityMeasure
    refine fun I ↦ ⟨aemeasurable_pi_lambda _ fun _ ↦ (law _).aemeasurable, ?_⟩
    have : IsProbabilityMeasure (P.map fun ω ↦ I.restrict (X · ω)) := by
      apply Measure.isProbabilityMeasure_map
      exact aemeasurable_pi_lambda _ fun _ ↦ (law _).aemeasurable
    obtain rfl | hI := I.eq_empty_or_nonempty
    · ext s -
      apply Subsingleton.set_cases (p := fun s ↦ Measure.map _ _ s = _)
      all_goals simp
    have := incr.hasGaussianLaw_restrict law
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
            rw [(law _).integral_eq, integral_id_gaussianReal]
          · exact fun _ ↦ (law _).hasGaussianLaw.integrable
        · apply Integrable.of_eval
          exact fun _ ↦ (law _).hasGaussianLaw.integrable
        · exact IsGaussian.integrable_id
      · fun_prop
      · exact aestronglyMeasurable_id
      · exact aemeasurable_pi_lambda _ fun _ ↦ (law _).aemeasurable
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
          wlog hij : i ≤ j generalizing i j
          · rw [covariance_comm, this j i (le_of_not_ge hij), min_comm]
          rw [show X j = X j - X i + X i  by simp, covariance_add_right,
            IndepFun.covariance_eq_zero, covariance_self, (law _).variance_eq,
            variance_id_gaussianReal]
          · simpa
          · exact (law _).aemeasurable
          · apply incr.indepFun_incr (r := 0)
            · simp
            · simpa
            · apply HasLaw.aeeq_of_dirac
              rw [← gaussianReal_zero_var]
              exact law 0
          · exact (law _).hasGaussianLaw.memLp_two
          · exact (law _).hasGaussianLaw.memLp_two.sub (law _).hasGaussianLaw.memLp_two
          · exact (law _).hasGaussianLaw.memLp_two
          · exact (law _).hasGaussianLaw.memLp_two.sub (law _).hasGaussianLaw.memLp_two
          · exact (law _).hasGaussianLaw.memLp_two
        · exact Measurable.aestronglyMeasurable (by fun_prop)
        · exact Measurable.aestronglyMeasurable (by fun_prop)
        · exact aemeasurable_pi_lambda _ (fun _ ↦ (law _).aemeasurable)
      · exact fun _ ↦ HasGaussianLaw.memLp_two
      · exact fun _ ↦ HasGaussianLaw.memLp_two

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
