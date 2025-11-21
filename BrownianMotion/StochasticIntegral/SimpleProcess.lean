/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Thomas Zhu
-/
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

`SimpleProcess` consists of a value function as a `Finsupp`: `value : ι × ι →₀ Ω → F` and a
value at ⊥: `valueBot : Ω → F`. This allows the definition of operations like addition to be
defined naturally.

However, this makes the function `SimpleProcess.toFun` non-injective, so `SimpleProcess` is not
`FunLike`. In other words, two distinct elements `X Y : SimpleProcess F 𝓕` may produce the same
function `(⇑X : ι → Ω → F) = (⇑Y : ι → Ω → F)`.

There are subtleties that are caused by this: for example, by a nonnegative simple
process, we mean `X : SimpleProcess F 𝓕` with `0 ≤ X.valueBot` and `0 ≤ X.value`, which is not the
same as `0 ≤ (⇑X : ι → Ω → F)`.

Similarly, `ElementaryPredictableSet` is a data type that has a coercion to `Set (ι × Ω)`, but
this coercion is not injective, so it is not `SetLike`. This makes it easy to define the indicator
function of an elementary predictable set as a simple process by mapping respective datas
(which is why it also requires disjoint unions).

## TODO

- Generalize instance variables.
-/

open MeasureTheory Filter Finset
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {ι Ω F : Type*} [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω}
variable [NormedAddCommGroup F] [mF : MeasurableSpace F]
-- These are needed for e.g. `ContinuousAdd.measurableMul₂` (which, by the way, has the wrong name).
variable [NormedSpace ℝ F] [BorelSpace F] [SecondCountableTopology F]
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
  I := {(i, j)}
  set := fun p ↦ B
  measurableSet_setBot := by simp
  measurableSet_set := by simpa
  pairwiseDisjoint := by simp

@[simp] lemma coe_IocProd (i j : ι) {B : Set Ω} (hB : MeasurableSet[𝓕 i] B) :
    ↑(IocProd i j hB) = (Set.Ioc i j) ×ˢ B := by
  simp [toSet, IocProd]

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
noncomputable def valueBotBound (V : SimpleProcess F 𝓕) : ℝ := V.bounded_valueBot.choose

/-- The value at ⊥ is bounded by `valueBotBound`. -/
@[simp] lemma valueBot_le_valueBotBound (V : SimpleProcess F 𝓕) (ω : Ω) :
    ‖V.valueBot ω‖ ≤ V.valueBotBound := V.bounded_valueBot.choose_spec ω

/-- The value of the simple process at the left endpoint of an interval is measurable
with respect to the filtration at the left endpoint.

Note that we do not require `p ∈ V.value.support`, because the value is 0 otherwise,
which is measurable. -/
@[fun_prop]
lemma measurable_value (V : SimpleProcess F 𝓕) (p : ι × ι) : Measurable[𝓕 p.1] (V.value p) := by
  by_cases hp : p ∈ V.value.support
  · exact V.measurable_value' p hp
  · rw [show V.value p = 0 by simpa using hp]
    exact measurable_const

/-- A nonnegative bound on the value on each interval. -/
noncomputable def valueBound (V : SimpleProcess F 𝓕) : ℝ := max 0 (V.bounded_value.choose)

/-- The value on each interval is bounded by `valueBound`. Note that we do not require
`p ∈ V.value.support`. -/
@[simp] lemma value_le_valueBound (V : SimpleProcess F 𝓕) (p : ι × ι) (ω : Ω) :
    ‖V.value p ω‖ ≤ V.valueBound := by
  by_cases hp : p ∈ V.value.support
  · apply le_max_of_le_right
    exact V.bounded_value.choose_spec p hp ω
  · apply le_max_of_le_left
    rw [show V.value p = 0 by simpa using hp]
    simp

section Module

@[simps]
instance instZero : Zero (SimpleProcess F 𝓕) where
  zero := {
    valueBot := 0,
    value := 0,
    bounded_valueBot := ⟨0, by simp⟩,
    bounded_value := ⟨0, by simp⟩ }

@[simps]
instance instNeg : Neg (SimpleProcess F 𝓕) where
  neg V := {
    valueBot := -V.valueBot,
    value := -V.value,
    bounded_valueBot := ⟨V.valueBotBound, by simp⟩,
    bounded_value := ⟨V.valueBound, by simp⟩ }

@[simps]
instance instAdd : Add (SimpleProcess F 𝓕) where
  add V W := {
    valueBot := V.valueBot + W.valueBot,
    value := V.value + W.value,
    bounded_valueBot := ⟨V.valueBotBound + W.valueBotBound, fun ω ↦ by
      dsimp
      grw [norm_add_le, V.valueBot_le_valueBotBound, W.valueBot_le_valueBotBound]⟩,
    bounded_value := ⟨V.valueBound + W.valueBound, fun p _ ω ↦ by
      dsimp
      grw [norm_add_le, V.value_le_valueBound, W.value_le_valueBound]⟩ }

@[simps]
instance instSub : Sub (SimpleProcess F 𝓕) where
  sub V W := {
    valueBot := V.valueBot - W.valueBot,
    value := V.value - W.value,
    bounded_valueBot := ⟨V.valueBotBound + W.valueBotBound, fun ω ↦ by
      dsimp
      grw [norm_sub_le, V.valueBot_le_valueBotBound, W.valueBot_le_valueBotBound]⟩,
    bounded_value := ⟨V.valueBound + W.valueBound, fun p _ ω ↦ by
      dsimp
      grw [norm_sub_le, V.value_le_valueBound, W.value_le_valueBound]⟩ }

@[simps]
instance instSMul : SMul ℝ (SimpleProcess F 𝓕) where
  smul c V := {
    valueBot := c • V.valueBot,
    value := c • V.value,
    bounded_valueBot := ⟨|c| * V.valueBotBound, fun ω ↦ by
      dsimp
      grw [norm_smul, V.valueBot_le_valueBotBound, Real.norm_eq_abs]⟩,
    bounded_value := ⟨|c| * V.valueBound, fun p _ ω ↦ by
      dsimp
      grw [norm_smul, V.value_le_valueBound, Real.norm_eq_abs]⟩ }

instance instAddCommGroup : AddCommGroup (SimpleProcess F 𝓕) where
  sub_eq_add_neg U V := by ext <;> apply sub_eq_add_neg
  add_assoc U V W := by ext <;> apply add_assoc
  add_comm U V := by ext <;> apply add_comm
  zero_add V := by ext <;> apply zero_add
  add_zero V := by ext <;> apply add_zero
  neg_add_cancel V := by ext <;> apply neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instModule : Module ℝ (SimpleProcess F 𝓕) where
  zero_smul V := by ext <;> apply zero_smul
  smul_zero V := by ext <;> apply smul_zero
  add_smul U V W := by ext <;> apply add_smul
  smul_add U V W := by ext <;> apply smul_add
  one_smul V := by ext <;> apply one_smul
  mul_smul U V W := by ext <;> apply mul_smul

end Module

section ToFun

/-- Coercion from a simple process to a function. Note that this is not injective. -/
@[coe] def toFun (V : SimpleProcess F 𝓕) (i : ι) (ω : Ω) : F :=
  ({⊥} : Set ι).indicator (fun _ ↦ V.valueBot ω) i
    + V.value.sum fun p v => (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) i

instance instCoeFun : CoeFun (SimpleProcess F 𝓕) (fun _ ↦ ι → Ω → F) where
  coe := toFun

lemma apply_eq (V : SimpleProcess F 𝓕) (i : ι) (ω : Ω) :
  ⇑V i ω = ({⊥} : Set ι).indicator (fun _ ↦ V.valueBot ω) i
    + V.value.sum fun p v => (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) i := rfl

@[simp] lemma coe_zero : ⇑(0 : SimpleProcess F 𝓕) = 0 := by ext; simp [apply_eq]

@[simp] lemma coe_neg (V : SimpleProcess F 𝓕) : ⇑(-V) = -⇑V := by
  ext; simp [apply_eq, Set.indicator_neg, Finsupp.sum_neg_index]; abel

@[simp] lemma coe_add (V W : SimpleProcess F 𝓕) :
   ⇑(V + W) = ⇑V + ⇑W := by
  ext; simp [apply_eq, Set.indicator_add, Finsupp.sum_add_index]; abel

@[simp] lemma coe_sub (V W : SimpleProcess F 𝓕) :
   ⇑(V - W) = ⇑V - ⇑W := by
  ext; simp [apply_eq, Set.indicator_sub, Finsupp.sum_sub_index]; abel

@[simp] lemma coe_smul (c : ℝ) (V : SimpleProcess F 𝓕) :
   ⇑(c • V) = c • ⇑V := by
  ext; simp [apply_eq, Set.indicator_smul, Finsupp.sum_smul_index', Finsupp.smul_sum]

lemma coe_bounded (V : SimpleProcess F 𝓕) :
    ∃ C : ℝ, ∀ i : ι, ∀ ω : Ω, ‖⇑V i ω‖ ≤ C := by
  use V.valueBotBound + #V.value.support * V.valueBound
  intro i ω
  dsimp [apply_eq]
  grw [norm_add_le, Finsupp.sum, norm_sum_le, norm_indicator_le_norm_self,
    V.valueBot_le_valueBotBound, Finset.sum_le_card_nsmul _ _ V.valueBound]
  · simp
  · intro p hp
    grw [norm_indicator_le_norm_self, V.value_le_valueBound]

end ToFun

section Integral

variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The elementary stochastic integral. -/
def integral (B : E →L[ℝ] F →L[ℝ] G) (X : ι → Ω → E) (V : SimpleProcess F 𝓕) :
    WithTop ι → Ω → G :=
  fun i ω ↦ V.value.sum fun p v =>
    B (stoppedProcess X (fun _ ↦ i) p.2 ω - stoppedProcess X (fun _ ↦ i) p.1 ω) (v ω)

-- TODO: possible notation V●X, possibly for more general integrals

@[simp] lemma integral_zero_left {B : E →L[ℝ] F →L[ℝ] G} (V : SimpleProcess F 𝓕) :
    integral B (fun _ ↦ 0) V = fun _ ↦ 0 := by
  ext; simp [integral]

@[simp] lemma integral_neg_left {B : E →L[ℝ] F →L[ℝ] G} (X : ι → Ω → E)
    (V : SimpleProcess F 𝓕) :
    integral B (-X) V = -integral B X V := by
  ext; simp [integral]; abel

@[simp] lemma integral_add_left {B : E →L[ℝ] F →L[ℝ] G} (X Y : ι → Ω → E)
    (V : SimpleProcess F 𝓕) :
    integral B (X + Y) V = integral B X V + integral B Y V := by
  ext; simp [integral]; abel

@[simp] lemma integral_sub_left {B : E →L[ℝ] F →L[ℝ] G} (X Y : ι → Ω → E)
    (V : SimpleProcess F 𝓕) :
    integral B (X - Y) V = integral B X V - integral B Y V := by
  ext; simp [integral]; abel

@[simp] lemma integral_smul_left {B : E →L[ℝ] F →L[ℝ] G} (c : ℝ) (X : ι → Ω → E)
    (V : SimpleProcess F 𝓕) :
    integral B (c • X) V = c • integral B X V := by
  ext; simp [integral, Finsupp.smul_sum, smul_sub]

@[simp] lemma integral_zero_right {B : E →L[ℝ] F →L[ℝ] G} (X : ι → Ω → E) :
    integral B X (0 : SimpleProcess F 𝓕) = fun _ ↦ 0 := by
  ext; simp [integral]

@[simp] lemma integral_neg_right {B : E →L[ℝ] F →L[ℝ] G} (X : ι → Ω → E)
    (V : SimpleProcess F 𝓕) :
    integral B X (-V) = -integral B X V := by
  ext; simp [integral, Finsupp.sum_neg_index]; abel

@[simp] lemma integral_add_right {B : E →L[ℝ] F →L[ℝ] G} (X : ι → Ω → E)
    (V W : SimpleProcess F 𝓕) :
    integral B X (V + W) = integral B X V + integral B X W := by
  ext; simp [integral, Finsupp.sum_add_index]; abel

@[simp] lemma integral_sub_right {B : E →L[ℝ] F →L[ℝ] G}
    (X : ι → Ω → E) (V W : SimpleProcess F 𝓕) :
    integral B X (V - W) = integral B X V - integral B X W := by
  ext; simp [integral, Finsupp.sum_sub_index]; abel

@[simp] lemma integral_smul_right {B : E →L[ℝ] F →L[ℝ] G} (c : ℝ) (X : ι → Ω → E)
    (V : SimpleProcess F 𝓕) :
    integral B X (c • V) = c • integral B X V := by
  ext; simp [integral, Finsupp.sum_smul_index', Finsupp.smul_sum, smul_sub]

end Integral

end SimpleProcess

section Indicator

namespace ElementaryPredictableSet

variable (F)

/-- The indicator function of an elementary predictable set as a simple process. -/
def indicator [One F] (S : ElementaryPredictableSet 𝓕) :
    SimpleProcess F 𝓕 where
  valueBot := S.setBot.indicator 1
  value := Finsupp.onFinset S.I (fun p ↦ if p ∈ S.I then (S.set p).indicator 1 else 0)
    (by simp +contextual)
  bounded_valueBot := ⟨‖(1 : F)‖, fun _ ↦ norm_indicator_le_norm_self _ _⟩
  bounded_value := ⟨‖(1 : F)‖, fun _ _ _ ↦ by
    rw [Finsupp.onFinset_apply]
    split_ifs
    · exact norm_indicator_le_norm_self _ _
    · simp⟩
  measurable_value' := fun p hp ↦ by
    rw [Finsupp.onFinset_apply]
    measurability

@[simp] lemma coe_indicator [One F] (S : ElementaryPredictableSet 𝓕) :
    ⇑(S.indicator F) = Function.curry ((S : Set (ι × Ω)).indicator 1) := by
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

variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Explicit formula for `1_S ● X` where `S` is an elementary predictable set. -/
lemma integral_indicator [One F] (S : ElementaryPredictableSet 𝓕) (B : E →L[ℝ] F →L[ℝ] G)
    (X : ι → Ω → E) :
    (S.indicator F).integral B X = fun i ω ↦ ∑ p ∈ S.I,
      B (stoppedProcess X (fun _ ↦ i) p.2 ω - stoppedProcess X (fun _ ↦ i) p.1 ω)
        ((S.set p).indicator 1 ω) := by
  ext i ω
  rw [SimpleProcess.integral, indicator, Finsupp.onFinset_sum]
  · apply Finset.sum_congr rfl
    intro p hp
    simp [hp]
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
theorem generateFrom_eq_predictable [(atTop : Filter ι).IsCountablyGenerated] :
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

theorem isPredictable (V : SimpleProcess F 𝓕) : IsPredictable 𝓕 V := by
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

variable (F 𝓕) in
theorem iSup_comap_eq_predictable [(atTop : Filter ι).IsCountablyGenerated]
    [One F] [NeZero (1 : F)] :
    (⨆ V : SimpleProcess F 𝓕, mF.comap (Function.uncurry ⇑V)) = 𝓕.predictable := by
  apply le_antisymm
  · rw [iSup_le_iff]
    intro V
    simp [(isPredictable V).measurable.comap_le]
  · rw [← ElementaryPredictableSet.generateFrom_eq_predictable]
    apply MeasurableSpace.generateFrom_le
    rintro _ ⟨S, rfl⟩
    simp_rw [MeasurableSpace.measurableSet_iSup, MeasurableSpace.measurableSet_comap]
    apply MeasurableSpace.GenerateMeasurable.basic
    use S.indicator F, {1}, measurableSet_singleton 1
    simp only [ElementaryPredictableSet.coe_indicator, ElementaryPredictableSet.toSet,
      Function.uncurry_curry]
    classical erw [Set.indicator_const_preimage_eq_union]
    simpa using fun h ↦ nomatch h

end SimpleProcess

end Predictable

end ProbabilityTheory
