/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import BrownianMotion.Auxiliary.StoppedProcess
import BrownianMotion.Gaussian.BrownianMotion

/-! # Simple processes and elementary stochastic integral

## Main definitions

- `SimpleProcess`: the type of simple processes, as a Module over ℝ
- `SimpleProcess.toFun`: simple process interpreted as a stochastic process, with a CoeFun instance
- `SimpleProcess.integral`: elementary stochastic integral
- `SimpleProcess.isPredictable`: simple processes are predictable

## Implementation notes

`SimpleProcess` consists of a value function as a `Finsupp`: `value : ι × ι →₀ Ω → F` and a
value at ⊥: `valueBot : Ω → F`. This allows the definition of operations like addition to be
defined naturally.

However, this makes the function `SimpleProcess.toFun` non-injective, so `SimpleProcess` is not
`FunLike`.

This should not be a problem for defining the dense-inducing map of simple processes into $L^2(M)$,
because `IsDenseInducing.extend` in Mathlib does not require injectivity.

## TODO

- Generalize instance variables.
-/

open MeasureTheory Filter Finset
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {ι Ω E F G : Type*} [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [MeasurableSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {𝓕 : Filtration ι mΩ}

open scoped Function

/-- A simple process. -/
@[ext]
structure SimpleProcess (ι F : Type*) [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup F] [MeasurableSpace F] (𝓕 : Filtration ι mΩ) where
  /-- The value on each interval. -/
  value : ι × ι →₀ Ω → F
  /-- The value at ⊥. -/
  valueBot : Ω → F
  /-- The value on each interval is measurable with respect to the filtration at the left endpoint.

  Do not use this lemma directly. Use `SimpleProcess.measurable_value` instead. -/
  measurable_value' : ∀ p ∈ value.support, Measurable[𝓕 p.1] (value p) := by
    -- Note: Most of the time we need to eta-expand to make `fun_prop` find the right lemma,
    -- such as `Measurability.neg` that can only recognize `fun x ↦ -f x` rather than `-f`.
    -- On the other hand, some other lemmas like `Measurable.const_smul` can only recognize `c • f`
    -- rather than `fun x ↦ c • f x`, so we also need to try directly applying `measurability`.
    first | measurability | eta_expand; measurability
  /-- The value at ⊥ is measurable with respect to the filtration at ⊥. -/
  measurable_valueBot : Measurable[𝓕 ⊥] valueBot := by
    first | measurability | eta_expand; measurability

attribute [fun_prop] SimpleProcess.measurable_valueBot

/-- The value of the simple process at the left endpoint of an interval is measurable
with respect to the filtration at the left endpoint.

Note that we do not require `p ∈ V.value.support`, because the value is 0 otherwise,
which is measurable. -/
@[fun_prop]
lemma measurable_value (V : SimpleProcess ι F 𝓕) (p : ι × ι) : Measurable[𝓕 p.1] (V.value p) := by
  by_cases hp : p ∈ V.value.support
  · exact V.measurable_value' p hp
  · rw [show V.value p = 0 by simpa using hp]
    exact measurable_const

namespace SimpleProcess

section Module

-- These are needed for e.g. `ContinuousAdd.measurableMul₂` (which, by the way, has the wrong name).
-- Alternatively, for more generalized instances, we could just use `[Module ℝ F]`, with
-- `[MeasurableNeg F]`, `[MeasurableAdd₂ F]`, `[MeasurableSub₂ F]`, and/or
-- `[MeasurableConstSMul ℝ F]` directly.
variable [NormedSpace ℝ F] [BorelSpace F] [SecondCountableTopology F]

@[simps]
instance instZero : Zero (SimpleProcess ι F 𝓕) where
  zero := { value := 0, valueBot := 0 }

@[simps]
instance instNeg : Neg (SimpleProcess ι F 𝓕) where
  neg V := { value := -V.value, valueBot := -V.valueBot }

@[simps]
instance instAdd : Add (SimpleProcess ι F 𝓕) where
  add V W := { value := V.value + W.value, valueBot := V.valueBot + W.valueBot }

@[simps]
instance instSub : Sub (SimpleProcess ι F 𝓕) where
  sub V W := { value := V.value - W.value, valueBot := V.valueBot - W.valueBot }

@[simps]
instance instSMul : SMul ℝ (SimpleProcess ι F 𝓕) where
  smul c V := { value := c • V.value, valueBot := c • V.valueBot }

instance instAddCommGroup : AddCommGroup (SimpleProcess ι F 𝓕) where
  sub_eq_add_neg U V := by ext <;> apply sub_eq_add_neg
  add_assoc U V W := by ext <;> apply add_assoc
  add_comm U V := by ext <;> apply add_comm
  zero_add V := by ext <;> apply zero_add
  add_zero V := by ext <;> apply add_zero
  neg_add_cancel V := by ext <;> apply neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instModule : Module ℝ (SimpleProcess ι F 𝓕) where
  zero_smul V := by ext <;> apply zero_smul
  smul_zero V := by ext <;> apply smul_zero
  add_smul U V W := by ext <;> apply add_smul
  smul_add U V W := by ext <;> apply smul_add
  one_smul V := by ext <;> apply one_smul
  mul_smul U V W := by ext <;> apply mul_smul

end Module

section ToFun

/-- Coercion from a simple process to a function. Note that this is not injective. -/
@[coe]
def toFun (V : SimpleProcess ι F 𝓕) (i : ι) (ω : Ω) : F :=
  ({⊥} : Set ι).indicator (fun _ ↦ V.valueBot ω) i
    + V.value.sum fun p v => (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) i

instance instCoeFun : CoeFun (SimpleProcess ι F 𝓕) (fun _ ↦ ι → Ω → F) where
  coe := toFun

@[simp] lemma coe_apply (V : SimpleProcess ι F 𝓕) (i : ι) (ω : Ω) :
  ⇑V i ω = ({⊥} : Set ι).indicator (fun _ ↦ V.valueBot ω) i
    + V.value.sum fun p v => (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) i := rfl

@[simp] lemma coe_zero : ⇑(0 : SimpleProcess ι F 𝓕) = 0 := by ext; simp

variable [BorelSpace F]

@[simp] lemma coe_neg (V : SimpleProcess ι F 𝓕) : ⇑(-V) = -⇑V := by
  ext; simp [Set.indicator_neg, Finsupp.sum_neg_index]; abel

@[simp] lemma coe_add [SecondCountableTopology F] (V W : SimpleProcess ι F 𝓕) :
   ⇑(V + W) = ⇑V + ⇑W := by
  ext; simp [Set.indicator_add, Finsupp.sum_add_index]; abel

@[simp] lemma coe_sub [SecondCountableTopology F] (V W : SimpleProcess ι F 𝓕) :
   ⇑(V - W) = ⇑V - ⇑W := by
  ext; simp [Set.indicator_sub, Finsupp.sum_sub_index]; abel

@[simp] lemma coe_smul [NormedSpace ℝ F] (c : ℝ) (V : SimpleProcess ι F 𝓕) :
   ⇑(c • V) = c • ⇑V := by
  ext; simp [Set.indicator_smul, Finsupp.sum_smul_index', Finsupp.smul_sum]

end ToFun

section Predictable

lemma isPredictable (V : SimpleProcess ι F 𝓕) : IsPredictable 𝓕 V := by
  sorry

end Predictable

section Integral

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The elementary stochastic integral. -/
def integral (B : E →L[ℝ] F →L[ℝ] G) (X : ι → Ω → E) (V : SimpleProcess ι F 𝓕) :
    ι → Ω → G :=
  fun i ω ↦ V.value.sum fun p v =>
    B (stoppedProcess X (fun _ ↦ i) p.2 ω - stoppedProcess X (fun _ ↦ i) p.1 ω) (v ω)

-- TODO: possible notation V●X, possibly for more general integrals

@[simp] lemma integral_zero_left {B : E →L[ℝ] F →L[ℝ] G} (V : SimpleProcess ι F 𝓕) :
    integral B (fun _ ↦ 0) V = fun _ ↦ 0 := by
  ext; simp [integral]

@[simp] lemma integral_zero_right {B : E →L[ℝ] F →L[ℝ] G} (X : ι → Ω → E) :
    integral B X (0 : SimpleProcess ι F 𝓕) = fun _ ↦ 0 := by
  ext; simp [integral]

@[simp] lemma integral_add_left {B : E →L[ℝ] F →L[ℝ] G} (X Y : ι → Ω → E)
    (V : SimpleProcess ι F 𝓕) :
    integral B (X + Y) V = integral B X V + integral B Y V := by
  ext; simp [integral]; abel

@[simp] lemma integral_sub_left {B : E →L[ℝ] F →L[ℝ] G} (X Y : ι → Ω → E)
    (V : SimpleProcess ι F 𝓕) :
    integral B (X - Y) V = integral B X V - integral B Y V := by
  ext; simp [integral]; abel

@[simp] lemma integral_smul_left {B : E →L[ℝ] F →L[ℝ] G} (c : ℝ) (X : ι → Ω → E)
    (V : SimpleProcess ι F 𝓕) :
    integral B (c • X) V = c • integral B X V := by
  ext; simp [integral, Finsupp.smul_sum, smul_sub]

variable [BorelSpace F]

@[simp] lemma integral_add_right [SecondCountableTopology F] {B : E →L[ℝ] F →L[ℝ] G} (X : ι → Ω → E)
    (V W : SimpleProcess ι F 𝓕) :
    integral B X (V + W) = integral B X V + integral B X W := by
  ext; simp [integral, Finsupp.sum_add_index]; abel

@[simp] lemma integral_sub_right [SecondCountableTopology F] {B : E →L[ℝ] F →L[ℝ] G}
    (X : ι → Ω → E) (V W : SimpleProcess ι F 𝓕) :
    integral B X (V - W) = integral B X V - integral B X W := by
  ext; simp [integral, Finsupp.sum_sub_index]; abel

@[simp] lemma integral_smul_right {B : E →L[ℝ] F →L[ℝ] G} (c : ℝ) (X : ι → Ω → E)
    (V : SimpleProcess ι F 𝓕) :
    integral B X (c • V) = c • integral B X V := by
  ext; simp [integral, Finsupp.sum_smul_index', Finsupp.smul_sum, smul_sub]

end Integral

end SimpleProcess

end ProbabilityTheory
