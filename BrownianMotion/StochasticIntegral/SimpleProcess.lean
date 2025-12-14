/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Thomas Zhu
-/
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import BrownianMotion.Auxiliary.StoppedProcess
import BrownianMotion.Gaussian.BrownianMotion

/-! # Simple processes and elementary stochastic integral

## Main definitions

- `ElementaryPredictableSet`: the type of elementary predictable sets
- `SimpleProcess`: the type of simple processes, as a Module over ℝ
- `SimpleProcess.toFun`: simple process interpreted as a stochastic process, with a CoeFun instance
- `SimpleProcess.integral`: elementary stochastic integral
- `SimpleProcess.isPredictable`: simple processes are predictable

## Implementation notes

`SimpleProcess` consists of a value function as a `Finsupp`: `value : ι × ι →₀ Ω → E` and a
value at ⊥: `valueBot : Ω → E`. This allows the definition of operations like addition to be
defined naturally.

However, this makes the function `SimpleProcess.toFun` non-injective, so `SimpleProcess` is not
`FunLike`. In other words, two distinct elements `X Y : SimpleProcess E 𝓕` may produce the same
function `(⇑X : ι → Ω → E) = (⇑Y : ι → Ω → E)`.

There are subtleties that are caused by this: for example, by a nonnegative simple
process, we mean `X : SimpleProcess E 𝓕` with `0 ≤ X.valueBot` and `0 ≤ X.value`, which is not the
same as `0 ≤ (⇑X : ι → Ω → E)`.

Similarly, `ElementaryPredictableSet` is a data type that has a coercion to `Set (ι × Ω)`, but
this coercion is not injective, so it is not `SetLike`. This makes it easy to define the indicator
function of an elementary predictable set as a simple process by mapping respective datas
(which is why it also requires disjoint unions).

## TODO

- Generalize instance variables.
-/

open MeasureTheory Finset Filter ContinuousLinearMap
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω}
variable [NormedAddCommGroup E] [mE : MeasurableSpace E]
-- Note: separable space is needed for `ContinuousAdd.measurableMul₂` (which has the wrong name)
variable [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
variable {𝓕 : Filtration ι mΩ}

attribute [local measurability]
  measurableSet_predictable_singleton_bot_prod
  measurableSet_predictable_Ioi_prod
  measurableSet_predictable_Ioc_prod

/-- An **elementary predictable set** is a finite disjoint union of sets of the form `{⊥} × B` for
`B ∈ 𝓕 ⊥` and of the form `(s, t] × B` for `s < t` in `ι` and `B ∈ 𝓕 s`.

Note that we require the union to be disjoint. This is not necessary, but makes it easier to define
the indicator function of an elementary predictable set as a `SimpleProcess`. -/
structure ElementaryPredictableSet (𝓕 : Filtration ι mΩ) where
  /-- The set over `⊥`. -/
  setBot : Set Ω
  /-- The finite index for sets over `(s, t]`. -/
  I : Finset (ι × ι)
  /-- The sets over `(s, t]`. -/
  set : ι × ι → Set Ω
  le_of_mem_I : ∀ p ∈ I, p.1 ≤ p.2
  measurableSet_setBot : MeasurableSet[𝓕 ⊥] setBot
  measurableSet_set : ∀ p ∈ I, MeasurableSet[𝓕 p.1] (set p)
  pairwiseDisjoint : Set.PairwiseDisjoint ↑I (fun p : ι × ι ↦ Set.Ioc p.1 p.2 ×ˢ set p)

namespace ElementaryPredictableSet

attribute [measurability] measurableSet_setBot measurableSet_set

/-- Coercion from an `ElementaryPredictableSet 𝓕` to a `Set (ι × Ω)`. -/
@[coe] def toSet (S : ElementaryPredictableSet 𝓕) : Set (ι × Ω) :=
    {⊥} ×ˢ S.setBot ∪ ⋃ p ∈ S.I, (Set.Ioc p.1 p.2) ×ˢ S.set p

instance : CoeOut (ElementaryPredictableSet 𝓕) (Set (ι × Ω)) where
  coe := toSet

/-- The set `{⊥} × B₀` as an `ElementaryPredictableSet`. -/
def singletonBotProd {B₀ : Set Ω} (hB₀ : MeasurableSet[𝓕 ⊥] B₀) :
    ElementaryPredictableSet 𝓕 where
  setBot := B₀
  I := ∅
  set := default
  le_of_mem_I := by simp
  measurableSet_setBot := hB₀
  measurableSet_set := by simp
  pairwiseDisjoint := by simp

@[simp] lemma coe_singletonBotProd {B₀ : Set Ω} (hB₀ : MeasurableSet[𝓕 ⊥] B₀) :
    ↑(singletonBotProd hB₀) = {(⊥ : ι)} ×ˢ B₀ := by
  simp [toSet, singletonBotProd]

/-- The set `(i, j] × B` as an `ElementaryPredictableSet`. -/
def IocProd (i j : ι) {B : Set Ω} (hB : MeasurableSet[𝓕 i] B) :
    ElementaryPredictableSet 𝓕 where
  setBot := ∅
  I := if i ≤ j then {(i, j)} else ∅
  set := fun p ↦ B
  le_of_mem_I := by
    split_ifs
    · simpa
    · simp
  measurableSet_setBot := by simp
  measurableSet_set := by
    split_ifs
    · simpa
    · simp
  pairwiseDisjoint := by split_ifs <;> simp

@[simp] lemma coe_IocProd (i j : ι) {B : Set Ω} (hB : MeasurableSet[𝓕 i] B) :
    ↑(IocProd i j hB) = (Set.Ioc i j) ×ˢ B := by
  unfold IocProd
  split_ifs with h
  · simp [toSet]
  · simp [toSet, Set.Ioc_eq_empty_of_le (not_le.1 h).le]

end ElementaryPredictableSet

/-- A **simple process** is defined as a finite sum of indicator functions of intervals `(s, t]`,
each assigned to a bounded `𝓕 s`-measurable random variable `value`, plus a `valueBot` at ⊥. -/
@[ext]
structure SimpleProcess (F : Type*) [NormedAddCommGroup F] [MeasurableSpace F] [NormedSpace ℝ F]
    [BorelSpace F] [SecondCountableTopology F] (𝓕 : Filtration ι mΩ) where
  /-- The value at ⊥. -/
  valueBot : Ω → F
  /-- The value on each interval. Note that intervals are not necessarily disjoint. -/
  value : ι × ι →₀ Ω → F
  /-- The intervals in the support of `value` are ordered. -/
  le_of_mem_support_value : ∀ p ∈ value.support, p.1 ≤ p.2
  /-- The value at ⊥ is measurable with respect to the filtration at ⊥. -/
  measurable_valueBot : Measurable[𝓕 ⊥] valueBot := by
    first | measurability | eta_expand; measurability
  /-- The value on each interval is measurable with respect to the filtration at the left endpoint.

  Do not use this lemma directly. Use `SimpleProcess.measurable_value` instead. -/
  measurable_value' : ∀ p ∈ value.support, Measurable[𝓕 p.1] (value p) := by
    -- Note: Most of the time we need to eta-expand to make `fun_prop` find the right lemma,
    -- such as `Measurability.neg` that can only recognize `fun x ↦ -f x` rather than `-f`.
    -- On the other hand, some other lemmas like `Measurable.const_smul` can only recognize `c • f`
    -- rather than `fun x ↦ c • f x`, so we also need to try directly applying `measurability`.
    first | measurability | eta_expand; measurability
  /-- The value at ⊥ is bounded. -/
  bounded_valueBot : ∃ C : ℝ, ∀ ω : Ω, ‖valueBot ω‖ ≤ C
  /-- The value on each interval is bounded. -/
  bounded_value : ∃ C : ℝ, ∀ p ∈ value.support, ∀ ω : Ω, ‖value p ω‖ ≤ C

namespace SimpleProcess

attribute [fun_prop] measurable_valueBot

/-- A bound on the value at ⊥. -/
noncomputable def valueBotBound (V : SimpleProcess E 𝓕) : ℝ := max 0 V.bounded_valueBot.choose

/-- The value at ⊥ is bounded by `valueBotBound`. -/
@[simp] lemma valueBot_le_valueBotBound (V : SimpleProcess E 𝓕) (ω : Ω) :
    ‖V.valueBot ω‖ ≤ V.valueBotBound :=
  le_max_of_le_right (V.bounded_valueBot.choose_spec ω)

@[simp] lemma valueBotBound_nonneg (V : SimpleProcess E 𝓕) : 0 ≤ V.valueBotBound := le_max_left _ _

/-- The value of the simple process at the left endpoint of an interval is measurable
with respect to the filtration at the left endpoint.

Note that we do not require `p ∈ V.value.support`, because the value is 0 otherwise,
which is measurable. -/
@[fun_prop]
lemma measurable_value (V : SimpleProcess E 𝓕) (p : ι × ι) : Measurable[𝓕 p.1] (V.value p) := by
  by_cases hp : p ∈ V.value.support
  · exact V.measurable_value' p hp
  · rw [show V.value p = 0 by simpa using hp]
    exact measurable_const

/-- A nonnegative bound on the value on each interval. -/
noncomputable def valueBound (V : SimpleProcess E 𝓕) : ℝ := max 0 (V.bounded_value.choose)

/-- The value on each interval is bounded by `valueBound`. Note that we do not require
`p ∈ V.value.support`. -/
@[simp] lemma value_le_valueBound (V : SimpleProcess E 𝓕) (p : ι × ι) (ω : Ω) :
    ‖V.value p ω‖ ≤ V.valueBound := by
  by_cases hp : p ∈ V.value.support
  · exact le_max_of_le_right (V.bounded_value.choose_spec p hp ω)
  · apply le_max_of_le_left
    rw [show V.value p = 0 by simpa using hp]
    simp

@[simp] lemma valueBound_nonneg (V : SimpleProcess E 𝓕) : 0 ≤ V.valueBound := le_max_left _ _

section Module

@[simps]
instance instZero : Zero (SimpleProcess E 𝓕) where
  zero := {
    valueBot := 0,
    value := 0,
    le_of_mem_support_value := by simp,
    bounded_valueBot := ⟨0, by simp⟩,
    bounded_value := ⟨0, by simp⟩ }

@[simps]
instance instNeg : Neg (SimpleProcess E 𝓕) where
  neg V := {
    valueBot := -V.valueBot,
    value := -V.value,
    le_of_mem_support_value := by simpa using V.le_of_mem_support_value,
    bounded_valueBot := ⟨V.valueBotBound, by simp⟩,
    bounded_value := ⟨V.valueBound, by simp⟩ }

@[simps]
instance instAdd : Add (SimpleProcess E 𝓕) where
  add V W := {
    valueBot := V.valueBot + W.valueBot,
    value := V.value + W.value,
    le_of_mem_support_value := fun p hp ↦ (mem_union.1 (Finsupp.support_add hp)).elim
      (V.le_of_mem_support_value p) (W.le_of_mem_support_value p),
    bounded_valueBot := ⟨V.valueBotBound + W.valueBotBound, fun ω ↦ by
      dsimp
      grw [norm_add_le, V.valueBot_le_valueBotBound, W.valueBot_le_valueBotBound]⟩,
    bounded_value := ⟨V.valueBound + W.valueBound, fun p _ ω ↦ by
      dsimp
      grw [norm_add_le, V.value_le_valueBound, W.value_le_valueBound]⟩ }

@[simps]
instance instSub : Sub (SimpleProcess E 𝓕) where
  sub V W := {
    valueBot := V.valueBot - W.valueBot,
    value := V.value - W.value,
    le_of_mem_support_value := fun p hp ↦ (mem_union.1 (Finsupp.support_sub hp)).elim
      (V.le_of_mem_support_value p) (W.le_of_mem_support_value p),
    bounded_valueBot := ⟨V.valueBotBound + W.valueBotBound, fun ω ↦ by
      dsimp
      grw [norm_sub_le, V.valueBot_le_valueBotBound, W.valueBot_le_valueBotBound]⟩,
    bounded_value := ⟨V.valueBound + W.valueBound, fun p _ ω ↦ by
      dsimp
      grw [norm_sub_le, V.value_le_valueBound, W.value_le_valueBound]⟩ }

@[simps]
instance instSMul : SMul ℝ (SimpleProcess E 𝓕) where
  smul c V := {
    valueBot := c • V.valueBot,
    value := c • V.value,
    le_of_mem_support_value := by simpa using fun p _ ↦ V.le_of_mem_support_value p,
    bounded_valueBot := ⟨|c| * V.valueBotBound, fun ω ↦ by
      dsimp
      grw [norm_smul, V.valueBot_le_valueBotBound, Real.norm_eq_abs]⟩,
    bounded_value := ⟨|c| * V.valueBound, fun p _ ω ↦ by
      dsimp
      grw [norm_smul, V.value_le_valueBound, Real.norm_eq_abs]⟩ }

instance instAddCommGroup : AddCommGroup (SimpleProcess E 𝓕) where
  sub_eq_add_neg U V := by ext <;> apply sub_eq_add_neg
  add_assoc U V W := by ext <;> apply add_assoc
  add_comm U V := by ext <;> apply add_comm
  zero_add V := by ext <;> apply zero_add
  add_zero V := by ext <;> apply add_zero
  neg_add_cancel V := by ext <;> apply neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instModule : Module ℝ (SimpleProcess E 𝓕) where
  zero_smul V := by ext <;> simp
  smul_zero V := by ext <;> simp
  add_smul U V W := by ext <;> simp [add_smul]
  smul_add U V W := by ext <;> simp [smul_add]
  one_smul V := by ext <;> simp
  mul_smul U V W := by ext <;> simp [mul_smul]

-- TODO: Mathlib's Finset.measurable_prod is wrong because it is currently an exact duplicate of
-- Finset.measurable_fun_sum; we want the following version instead.
@[to_additive (attr := measurability, fun_prop)]
theorem Finset.measurable_prod' {M ι α : Type*} [CommMonoid M] [MeasurableSpace M]
    [MeasurableMul₂ M] {m : MeasurableSpace α} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (∏ i ∈ s, f i) := by
  change Measurable (fun a ↦ (∏ i ∈ s, f i) a)
  measurability

end Module

section ToFun

/-- Coercion from a simple process to a function. Note that this is not injective. -/
@[coe] def toFun (V : SimpleProcess E 𝓕) (i : ι) (ω : Ω) : E :=
  ({⊥} : Set ι).indicator (fun _ ↦ V.valueBot ω) i
    + V.value.sum fun p v => (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) i

instance instCoeFun : CoeFun (SimpleProcess E 𝓕) (fun _ ↦ ι → Ω → E) where
  coe := toFun

lemma apply_eq (V : SimpleProcess E 𝓕) (i : ι) (ω : Ω) :
  ⇑V i ω = ({⊥} : Set ι).indicator (fun _ ↦ V.valueBot ω) i
    + V.value.sum fun p v => (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) i := rfl

@[simp] lemma coe_zero : ⇑(0 : SimpleProcess E 𝓕) = 0 := by ext; simp [apply_eq]

@[simp] lemma coe_neg (V : SimpleProcess E 𝓕) : ⇑(-V) = -⇑V := by
  ext; simp [apply_eq, Set.indicator_neg, Finsupp.sum_neg_index]; abel

@[simp] lemma coe_add (V W : SimpleProcess E 𝓕) :
   ⇑(V + W) = ⇑V + ⇑W := by
  ext; simp [apply_eq, Set.indicator_add, Finsupp.sum_add_index]; abel

@[simp] lemma coe_sub (V W : SimpleProcess E 𝓕) :
   ⇑(V - W) = ⇑V - ⇑W := by
  ext; simp [apply_eq, Set.indicator_sub, Finsupp.sum_sub_index]; abel

@[simp] lemma coe_smul (c : ℝ) (V : SimpleProcess E 𝓕) :
   ⇑(c • V) = c • ⇑V := by
  ext; simp [apply_eq, Set.indicator_smul, Finsupp.sum_smul_index', Finsupp.smul_sum]

lemma coe_bounded (V : SimpleProcess E 𝓕) :
    ∃ C : ℝ, ∀ i : ι, ∀ ω : Ω, ‖⇑V i ω‖ ≤ C := by
  use V.valueBotBound + #V.value.support • V.valueBound
  intro i ω
  dsimp [apply_eq]
  grw [norm_add_le, Finsupp.sum, norm_sum_le, norm_indicator_le_norm_self,
    V.valueBot_le_valueBotBound, Finset.sum_le_card_nsmul]
  · intro p hp
    grw [norm_indicator_le_norm_self, V.value_le_valueBound]

end ToFun

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

section Integral

/-- The **elementary stochastic integral** with respect to a continuous bilinear map `B`. -/
def integral (B : E →L[ℝ] F →L[ℝ] G) (V : SimpleProcess E 𝓕) (X : ι → Ω → F) :
    WithTop ι → Ω → G :=
  fun i ω ↦ V.value.sum fun p v =>
    B (v ω) (stoppedProcess X (fun _ ↦ i) p.2 ω - stoppedProcess X (fun _ ↦ i) p.1 ω)

/-- The **linear elementary stochastic integral** where the simple process takes values in
`E →L[ℝ] F`, as a special case of `integral` with `B` the evaluation map. -/
abbrev integralEval [SecondCountableTopology (E →L[ℝ] F)] (V : SimpleProcess (E →L[ℝ] F) 𝓕)
    (X : ι → Ω → E) : WithTop ι → Ω → F :=
  integral (.id ℝ (E →L[ℝ] F)) V X

-- TODO: possible notation V●X, possibly for more general integrals

variable {B : E →L[ℝ] F →L[ℝ] G}

@[simp] lemma integral_const_right (c : Ω → F) (V : SimpleProcess E 𝓕) :
    integral B V (fun _ ↦ c) = fun _ ↦ 0 := by ext; simp [integral]

@[simp] lemma integral_neg_right (V : SimpleProcess E 𝓕) (X : ι → Ω → F) :
    integral B V (-X) = -integral B V X := by
  ext; simp [integral]; abel

@[simp] lemma integral_add_right (V : SimpleProcess E 𝓕) (X Y : ι → Ω → F) :
    integral B V (X + Y) = integral B V X + integral B V Y := by
  ext; simp [integral]; abel

@[simp] lemma integral_sub_right (V : SimpleProcess E 𝓕) (X Y : ι → Ω → F) :
    integral B V (X - Y) = integral B V X - integral B V Y := by
  ext; simp [integral]; abel

@[simp] lemma integral_smul_right (c : ℝ) (V : SimpleProcess E 𝓕) (X : ι → Ω → F) :
    integral B V (c • X) = c • integral B V X := by
  ext; simp [integral, Finsupp.smul_sum, smul_sub]

@[simp] lemma integral_zero_left (X : ι → Ω → F) :
    integral B (0 : SimpleProcess E 𝓕) X = fun _ ↦ 0 := by
  ext; simp [integral]

@[simp] lemma integral_neg_left (V : SimpleProcess E 𝓕) (X : ι → Ω → F) :
    integral B (-V) X = -integral B V X := by
  ext; simp [integral, Finsupp.sum_neg_index]; abel

@[simp] lemma integral_add_left (V W : SimpleProcess E 𝓕) (X : ι → Ω → F) :
    integral B (V + W) X = integral B V X + integral B W X := by
  ext; simp [integral, Finsupp.sum_add_index]; abel

@[simp] lemma integral_sub_left (V W : SimpleProcess E 𝓕) (X : ι → Ω → F) :
    integral B (V - W) X = integral B V X - integral B W X := by
  ext; simp [integral, Finsupp.sum_sub_index]; abel

@[simp] lemma integral_smul_left (c : ℝ) (V : SimpleProcess E 𝓕) (X : ι → Ω → F) :
    integral B (c • V) X = c • integral B V X := by
  ext; simp [integral, Finsupp.sum_smul_index', Finsupp.smul_sum, smul_sub]

@[simp] lemma integral_bot (V : SimpleProcess E 𝓕) (X : ι → Ω → F) :
    integral B V X ⊥ = fun _ ↦ 0 := by ext; simp [integral]

@[simp] lemma integral_top (V : SimpleProcess E 𝓕) (X : ι → Ω → F) (ω : Ω) :
    integral B V X ⊤ ω = V.value.sum fun p v ↦ B (v ω) (X p.2 ω - X p.1 ω) := by simp [integral]

theorem stoppedProcess_integral (V : SimpleProcess E 𝓕) (X : ι → Ω → F) (τ : Ω → WithTop ι) :
    stoppedProcess (integral B V X ∘ WithTop.some) τ =
      integral B V (stoppedProcess X τ) ∘ WithTop.some := by
  ext i ω
  rw [stoppedProcess]
  dsimp [integral]
  conv_rhs => rw [stoppedProcess_stoppedProcess]
  simp [stoppedProcess, WithTop.untopA_eq_untop]

end Integral

section Assoc

section Bilin

section map₂

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- Application of a bounded bilinear map pointwise to two simple processes. -/
@[simps] def map₂ (B : E →L[ℝ] F →L[ℝ] G) (V : SimpleProcess E 𝓕) (W : SimpleProcess F 𝓕) :
    SimpleProcess G 𝓕 where
  valueBot := fun ω ↦ B (V.valueBot ω) (W.valueBot ω)
  value := V.value.sum fun p v ↦ W.value.sum fun q w ↦
    Finsupp.single (p.1 ⊔ q.1, p.2 ⊓ q.2)
      (if q.1 ≤ p.2 ∧ p.1 ≤ q.2 then (fun ω ↦ B (v ω) (w ω)) else 0)
  le_of_mem_support_value := by
    intro p' hp'
    obtain ⟨p, hp, h⟩ := mem_biUnion.1 (Finsupp.support_sum hp')
    obtain ⟨q, hq, h⟩ := mem_biUnion.1 (Finsupp.support_sum h)
    split_ifs at h with h_le
    · simpa [(Finsupp.mem_support_single _ _ _).1 h] using
        ⟨⟨V.le_of_mem_support_value p hp, h_le.1⟩, ⟨h_le.2, W.le_of_mem_support_value q hq⟩⟩
    · simp at h
  bounded_valueBot := by
    refine ⟨‖B‖ * V.valueBotBound * W.valueBotBound, fun ω ↦ ?_⟩
    dsimp
    grw [B.le_opNorm₂, V.valueBot_le_valueBotBound, W.valueBot_le_valueBotBound]
    exact mul_nonneg B.opNorm_nonneg V.valueBotBound_nonneg
  bounded_value := by
    refine ⟨#V.value.support • #W.value.support • (‖B‖ * V.valueBound * W.valueBound),
      fun p _ ω ↦ ?_⟩
    simp only [Finsupp.sum, Finsupp.single_eq_indicator, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.indicator_apply, mem_singleton, dite_eq_ite]
    grw [norm_sum_le, Finset.sum_le_card_nsmul]
    intro p hp
    grw [norm_sum_le, Finset.sum_le_card_nsmul]
    intro q hq
    split_ifs
    · dsimp
      grw [B.le_opNorm₂, V.value_le_valueBound, W.value_le_valueBound]
      exact mul_nonneg B.opNorm_nonneg V.valueBound_nonneg
    all_goals
      simpa using mul_nonneg (mul_nonneg B.opNorm_nonneg V.valueBound_nonneg) W.valueBound_nonneg
  measurable_valueBot := by
    exact (show Continuous fun (v, w) ↦ B v w by fun_prop).measurable.comp
      (V.measurable_valueBot.prodMk (W.measurable_valueBot))
  measurable_value' := by
    simp only [Finsupp.sum_apply]
    refine fun p' hp' ↦ Finset.measurable_sum' _ fun p hp ↦ Finset.measurable_sum' _ fun q hq ↦ ?_
    simp_rw [Finsupp.single_apply]
    split_ifs with h h_le
    · have hV : Measurable[𝓕 p'.1] (V.value p) :=
        (V.measurable_value p).mono (𝓕.mono (by simp [← h])) le_rfl
      have hW : Measurable[𝓕 p'.1] (W.value q) :=
        (W.measurable_value q).mono (𝓕.mono (by simp [← h])) le_rfl
      exact (show Continuous fun (v, w) ↦ B v w by fun_prop).measurable.comp (hV.prodMk hW)
    · exact measurable_const
    · exact measurable_const

lemma map₂_swap (B : E →L[ℝ] F →L[ℝ] G) (V : SimpleProcess E 𝓕) (W : SimpleProcess F 𝓕) :
    map₂ B V W = map₂ B.flip W V := by
  ext
  · simp
  · simp [W.value.sum_comm, min_comm, max_comm, and_comm]

-- Analogous to LinearMap.finsupp_sum_apply and AddMonoidHom.finsuppSum_apply:
@[simp]
theorem _root_.ContinuousLinearMap.finsuppSum_apply {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂]
    {σ₁₂ : R₁ →+* R₂} {M₁ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type*}
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂] [ContinuousAdd M₂]
    {ι A : Type*} [Zero A] (g : ι →₀ A) (f : ι → A → M₁ →SL[σ₁₂] M₂) (b : M₁) :
    g.sum f b = g.sum fun i a ↦ f i a b :=
  ContinuousLinearMap.sum_apply _ _ _

/-- Interpreted as functions, `map₂` is just applying `B` pointwise. -/
@[simp] lemma coe_map₂ (B : E →L[ℝ] F →L[ℝ] G) (V : SimpleProcess E 𝓕)
    (W : SimpleProcess F 𝓕) : ⇑(map₂ B V W) = fun i ω ↦ B (⇑V i ω) (⇑W i ω) := by
  ext i ω
  calc
    _ = ({⊥} : Set ι).indicator (fun _ ↦ B (V.valueBot ω) (W.valueBot ω)) i +
      V.value.sum fun p v ↦ W.value.sum fun q w ↦
        (Finsupp.single (p.1 ⊔ q.1, p.2 ⊓ q.2)
          (if q.1 ≤ p.2 ∧ p.1 ≤ q.2 then fun ω ↦ B (v ω) (w ω) else 0)).sum
          fun p' v' ↦ (Set.Ioc p'.1 p'.2).indicator (fun _ ↦ v' ω) i := by
      simp [apply_eq, Finsupp.sum_sum_index, Set.indicator_add]
    _ = ({⊥} : Set ι).indicator (fun _ ↦ B (V.valueBot ω) (W.valueBot ω)) i +
      V.value.sum fun p v ↦ W.value.sum fun q w ↦
        (Set.Ioc (p.1 ⊔ q.1) (p.2 ⊓ q.2)).indicator (fun _ ↦ B (v ω) (w ω)) i := by
      congr! with p v q w
      split_ifs with h_le
      · simp
      · have : p.2 < q.1 ∨ q.2 < p.1 := by contrapose! h_le; exact h_le
        have : p.2 ⊓ q.2 < p.1 ⊔ q.1 := by simp; tauto
        simp [Set.Ioc_eq_empty_of_le this.le]
    _ = _ := by
      have h1 (s t : Set ι) (f : ι → E) (g : ι → F) (i : ι) :
          B (s.indicator f i) (t.indicator g i) = (s ∩ t).indicator (fun j ↦ B (f j) (g j)) i := by
        rw [← Set.indicator_indicator]
        unfold Set.indicator
        split_ifs <;> simp
      have h2 (i j : ι) : Set.Ioc i j ∩ {⊥} = ∅ := by simp
      have h3 (i j : ι) : {⊥} ∩ Set.Ioc i j = ∅ := by simp
      simp [apply_eq, map_finsuppSum, h1, h2, h3, Set.Ioc_inter_Ioc]

end map₂

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {I : Type*} [NormedAddCommGroup I] [NormedSpace ℝ I]
variable {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]
variable [MeasurableSpace J] [BorelSpace J] [SecondCountableTopology J]

/-- The most general case of associativity of the elementary stochastic integral. -/
theorem integral_assoc {B₁ : E →L[ℝ] H →L[ℝ] I} {B₂ : F →L[ℝ] G →L[ℝ] H} {B₃ : E →L[ℝ] F →L[ℝ] J}
    {B₄ : J →L[ℝ] G →L[ℝ] I} (hB : ∀ x y z, B₁ x (B₂ y z) = B₄ (B₃ x y) z)
    (V : SimpleProcess E 𝓕) (W : SimpleProcess F 𝓕) (X : ι → Ω → G) :
    integral B₁ V (integral B₂ W X ∘ WithTop.some) = integral B₄ (map₂ B₃ V W) X := by
  ext i ω
  let Xi := stoppedProcess X (fun _ ↦ i)
  calc
    _ = V.value.sum fun p v ↦ W.value.sum fun q w ↦ B₄ (B₃ (v ω) (w ω))
        ((Xi (p.2 ⊓ q.2) ω - Xi (p.2 ⊓ q.1) ω) - (Xi (p.1 ⊓ q.2) ω - Xi (p.1 ⊓ q.1) ω)) := by
      simp only [integral, stoppedProcess_integral, Function.comp_apply,
        stoppedProcess_stoppedProcess, map_sub, Finsupp.sum_sub, map_finsuppSum]
      congr! 6 with p v q w <;> simp [Xi, hB, stoppedProcess, min_left_comm, min_assoc]
    _ = V.value.sum fun p v ↦ W.value.sum fun q w ↦ if q.1 ≤ p.2 ∧ p.1 ≤ q.2 then
        B₄ (B₃ (v ω) (w ω)) (Xi (p.2 ⊓ q.2) ω - Xi (p.1 ⊔ q.1) ω) else 0 := by
      refine Finsupp.sum_congr fun p hp ↦ ?_
      refine Finsupp.sum_congr fun q hq ↦ ?_
      split_ifs with h_le
      · by_cases h_le' : p.1 ≤ q.1
        · simp [h_le, h_le']
        · simp [h_le, (not_le.1 h_le').le]
      · have : p.2 ≤ q.1 ∨ q.2 ≤ p.1 := by contrapose! h_le; exact ⟨h_le.1.le, h_le.2.le⟩
        rcases this with h_le | h_le
        · have h : p.1 ≤ p.2 ∧ p.2 ≤ q.1 ∧ q.1 ≤ q.2 := by
            simp [h_le, V.le_of_mem_support_value p hp, W.le_of_mem_support_value q hq]
          simp [h, h.2.1.trans h.2.2, h.1.trans h.2.1, (h.1.trans h.2.1).trans h.2.2]
        · have h : q.1 ≤ q.2 ∧ q.2 ≤ p.1 ∧ p.1 ≤ p.2 := by
            simp [h_le, W.le_of_mem_support_value q hq, V.le_of_mem_support_value p hp]
          simp [h, h.2.1.trans h.2.2, h.1.trans h.2.1, (h.1.trans h.2.1).trans h.2.2]
    _ = _ := by
      simp [integral, Finsupp.sum_sum_index, Xi, -map_sub, ite_apply, apply_ite (α := J),
        DFunLike.ite_apply]

end Bilin

section Comp

variable [SecondCountableTopology (F →L[ℝ] G)]
variable [SecondCountableTopology (E →L[ℝ] F)]
variable [SecondCountableTopology (E →L[ℝ] G)]
omit mE [SecondCountableTopology E]

/-- Composition of simple processes taking values in continuous linear maps. -/
@[simps!] def comp (V : SimpleProcess (F →L[ℝ] G) 𝓕) (W : SimpleProcess (E →L[ℝ] F) 𝓕) :
    SimpleProcess (E →L[ℝ] G) 𝓕 :=
  map₂ (compL ℝ E F G) V W

@[simp] lemma coe_comp (V : SimpleProcess (F →L[ℝ] G) 𝓕) (W : SimpleProcess (E →L[ℝ] F) 𝓕) :
   ⇑(V.comp W) = fun i ω ↦ ⇑V i ω ∘L ⇑W i ω := by
  simp [comp]

theorem integralEval_assoc (X : ι → Ω → E) (V : SimpleProcess (F →L[ℝ] G) 𝓕)
    (W : SimpleProcess (E →L[ℝ] F) 𝓕) :
    integralEval V (integralEval W X ∘ WithTop.some) = integralEval (comp V W) X := by
  apply integral_assoc
  simp

end Comp

section SMul

-- TODO: cor:elemStochIntegral_assoc_real_bilin and lem:elemStochIntegral_assoc

end SMul

end Assoc

end SimpleProcess

section Indicator

namespace ElementaryPredictableSet

/-- The indicator function of an elementary predictable set as a simple process.
This takes value `0` at time not in `S`, and `e` at time `S`. -/
def indicator (S : ElementaryPredictableSet 𝓕) (e : E) : SimpleProcess E 𝓕 where
  valueBot := S.setBot.indicator fun _ ↦ e
  value := Finsupp.onFinset S.I (fun p ↦ if p ∈ S.I then (S.set p).indicator fun _ ↦ e else 0)
    (by simp +contextual)
  le_of_mem_support_value := fun p hp ↦ S.le_of_mem_I p (Finsupp.support_onFinset_subset hp)
  bounded_valueBot := ⟨‖e‖, fun _ ↦ norm_indicator_le_norm_self _ _⟩
  bounded_value := ⟨‖e‖, fun _ _ _ ↦ by
    rw [Finsupp.onFinset_apply]
    split_ifs
    · exact norm_indicator_le_norm_self _ _
    · simp⟩
  measurable_value' := fun p hp ↦ by
    rw [Finsupp.onFinset_apply]
    measurability

@[simp] lemma coe_indicator (S : ElementaryPredictableSet 𝓕) (e : E) :
    ⇑(S.indicator e) = Function.curry ((S : Set (ι × Ω)).indicator fun _ ↦ e) := by
  classical
  ext i ω
  rw [ElementaryPredictableSet.toSet, Set.indicator_union_of_disjoint, Finset.indicator_biUnion]
  · simp only [ElementaryPredictableSet.indicator, SimpleProcess.apply_eq, Pi.zero_apply,
      Set.indicator_zero, implies_true, Finsupp.onFinset_sum, Function.curry_apply]
    congr 1
    · simp [Set.indicator, ite_and]
    · apply Finset.sum_congr rfl
      intro p hp
      simp [Set.indicator, ite_and, hp]
  · exact S.pairwiseDisjoint
  · rw [Set.disjoint_iff]
    intro (i, ω)
    simp +contextual

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Explicit formula for `1_S ● X` where `S` is an elementary predictable set. -/
lemma integral_indicator_apply (S : ElementaryPredictableSet 𝓕)
    (e : E) (B : E →L[ℝ] F →L[ℝ] G) (X : ι → Ω → F) (i : ι) (ω : Ω) :
    (S.indicator e).integral B X i ω = ∑ p ∈ S.I, (S.set p).indicator (fun ω ↦
      B e (stoppedProcess X (fun _ ↦ i) p.2 ω - stoppedProcess X (fun _ ↦ i) p.1 ω)) ω := by
  rw [SimpleProcess.integral, indicator, Finsupp.onFinset_sum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [if_pos hp, Set.indicator, Set.indicator]
    split_ifs <;> simp
  simp

end ElementaryPredictableSet

end Indicator

section Predictable

namespace ElementaryPredictableSet

@[measurability]
theorem measurableSet_predictable (S : ElementaryPredictableSet 𝓕) :
    MeasurableSet[𝓕.predictable] ↑S := by
  apply MeasurableSet.union
  · measurability
  · apply MeasurableSet.biUnion (Finset.countable_toSet _)
    measurability

variable (ι Ω) in
/-- The elementary predictable sets generate the predictable σ-algebra. Note that we require the
time domain to have countably generated `atTop` so that each `(t, ∞]` can be written as a countable
union of intervals `(t, s]`. -/
theorem generateFrom_eq_predictable [(Filter.atTop : Filter ι).IsCountablyGenerated] :
    MeasurableSpace.generateFrom {↑S | S : ElementaryPredictableSet 𝓕} = 𝓕.predictable := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨S, rfl⟩
    exact S.measurableSet_predictable
  · apply measurableSpace_le_predictable_of_measurableSet
    · intro B₀ hB₀
      apply MeasurableSpace.measurableSet_generateFrom
      use singletonBotProd hB₀, coe_singletonBotProd hB₀
    · intro t B hB
      obtain ⟨seq, _, tendsto⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop ι
      have : Set.Ioi t = ⋃ n : ℕ, Set.Ioc t (seq n) := by
        ext s
        suffices ∃ n, s ≤ seq n by simpa using fun _ ↦ this
        rw [Filter.tendsto_atTop_atTop] at tendsto
        obtain ⟨n, h⟩ := tendsto s
        exact ⟨n, h n le_rfl⟩
      rw [this, Set.iUnion_prod_const]
      refine MeasurableSet.iUnion fun n ↦ MeasurableSpace.measurableSet_generateFrom ?_
      use IocProd t (seq n) hB, coe_IocProd _ _ hB

end ElementaryPredictableSet

namespace SimpleProcess

theorem isPredictable (V : SimpleProcess E 𝓕) : IsPredictable 𝓕 V := by
  apply Measurable.stronglyMeasurable
  apply Measurable.add
  · apply Measurable.indicator
    · intro s hs
      suffices MeasurableSet[𝓕.predictable] (({⊥} ∪ Set.Ioi ⊥) ×ˢ (V.valueBot ⁻¹' s)) by
        convert this
        ext; simp
      rw [Set.union_prod]
      measurability
    · change MeasurableSet[𝓕.predictable] {a | a.1 = ⊥}
      suffices MeasurableSet[𝓕.predictable] ({⊥} ×ˢ Set.univ) by
        convert this
        ext; simp
      measurability
  · apply measurable_sum
    intro p hp s hs
    suffices MeasurableSet[𝓕.predictable]
        ((Set.Ioc p.1 p.2)ᶜ ×ˢ ((fun _ ↦ 0) ⁻¹' s) ∪ Set.Ioc p.1 p.2 ×ˢ (V.value p ⁻¹' s)) by
      convert this
      ext ⟨i, ω⟩
      simp only [Set.indicator, Set.mem_preimage, Set.mem_union, Set.mem_prod, Set.mem_compl_iff]
      split_ifs with h <;> simp [h]
    apply MeasurableSet.union
    · have : (Set.Ioc p.1 p.2)ᶜ = {⊥} ∪ Set.Ioc ⊥ p.1 ∪ Set.Ioi p.2 := by
        rw [Set.compl_Ioc, ← Set.Icc_bot, ← Set.Ioc_union_left bot_le, Set.union_comm {⊥}]
      rw [this, Set.union_prod, Set.union_prod]
      measurability
    · measurability

variable (E 𝓕) in
theorem iSup_comap_eq_predictable [(Filter.atTop : Filter ι).IsCountablyGenerated]
    [MeasurableSingletonClass E] [Nontrivial E] :
    (⨆ V : SimpleProcess E 𝓕, mE.comap (Function.uncurry ⇑V)) = 𝓕.predictable := by
  apply le_antisymm
  · rw [iSup_le_iff]
    intro V
    simp [(isPredictable V).measurable.comap_le]
  · rw [← ElementaryPredictableSet.generateFrom_eq_predictable]
    apply MeasurableSpace.generateFrom_le
    rintro _ ⟨S, rfl⟩
    simp_rw [MeasurableSpace.measurableSet_iSup, MeasurableSpace.measurableSet_comap]
    apply MeasurableSpace.GenerateMeasurable.basic
    let ⟨(e : E), f_ne⟩ := exists_ne 0
    use S.indicator e, {e}, measurableSet_singleton e
    simp only [ElementaryPredictableSet.coe_indicator, ElementaryPredictableSet.toSet,
      Function.uncurry_curry]
    classical
    erw [Set.indicator_const_preimage_eq_union]
    simp [f_ne.symm]

end SimpleProcess

end Predictable

end ProbabilityTheory
