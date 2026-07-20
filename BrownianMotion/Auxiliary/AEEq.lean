/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!

# Almost everywhere equal functions

This is the same as `AEEqFun` but for `AEMeasurable` functions rather than `AEMeasurable`
ones.

-/

@[expose] public section

-- Guard against import creep
assert_not_exists InnerProductSpace

noncomputable section

open Topology Set Filter MeasurableSpace ENNReal EMetric MeasureTheory Function

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

namespace MeasureTheory

section MeasurableSpace

variable [MeasurableSpace β]
variable (β)

/-- The equivalence relation of being almost everywhere equal for almost everywhere strongly
measurable functions. -/
@[implicit_reducible]
def Measure.aeEqSetoid' (μ : Measure α) : Setoid { f : α → β // AEMeasurable f μ } :=
  ⟨fun f g => (f : α → β) =ᵐ[μ] g, fun {f} => ae_eq_refl f.val, fun {_ _} => ae_eq_symm,
    fun {_ _ _} => ae_eq_trans⟩

variable (α)

/-- The space of equivalence classes of almost everywhere measurable functions, where two
measurable functions are equivalent if they agree almost everywhere, i.e.,
they differ on a set of measure `0`. -/
def AEEq (μ : Measure α) : Type _ :=
  Quotient (μ.aeEqSetoid' β)

variable {α β}

@[inherit_doc MeasureTheory.AEEq]
notation:25 α " →ₐₑ[" μ "] " β => AEEq α β μ

end MeasurableSpace

variable [MeasurableSpace δ]

namespace AEEq

section
variable [MeasurableSpace β]

/-- Construct the equivalence class `[f]` of an almost everywhere measurable function `f`, based
on the equivalence relation of being almost everywhere equal. -/
def mk {β : Type*} [MeasurableSpace β] (f : α → β) (hf : AEMeasurable f μ) : α →ₐₑ[μ] β :=
  Quotient.mk'' ⟨f, hf⟩

open scoped Classical in
/-- Coercion from a space of equivalence classes of almost everywhere measurable
functions to functions. We ensure that if `f` has a constant representative,
then we choose that one. -/
@[coe]
def cast (f : α →ₐₑ[μ] β) : α → β :=
  if h : ∃ (b : β), f = mk (const α b) aemeasurable_const then
    const α <| Classical.choose h else
    AEMeasurable.mk _ (Quotient.out f : { f : α → β // AEMeasurable f μ }).2

/-- A measurable representative of an `AEEqFun` [f] -/
instance instCoeFun : CoeFun (α →ₐₑ[μ] β) fun _ => α → β := ⟨cast⟩

@[fun_prop]
protected theorem measurable (f : α →ₐₑ[μ] β) : Measurable f := by
  simp only [cast]
  split_ifs with h
  · exact measurable_const
  · apply AEMeasurable.measurable_mk

@[fun_prop]
protected theorem aemeasurable (f : α →ₐₑ[μ] β) : AEMeasurable f μ :=
  f.measurable.aemeasurable

@[simp]
theorem quot_mk_eq_mk (f : α → β) (hf) :
    (Quot.mk (@Setoid.r _ <| μ.aeEqSetoid' β) ⟨f, hf⟩ : α →ₐₑ[μ] β) = mk f hf :=
  rfl

@[simp]
theorem mk_eq_mk {f g : α → β} {hf hg} : (mk f hf : α →ₐₑ[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
  Quotient.eq''

@[simp]
theorem mk_coeFn (f : α →ₐₑ[μ] β) : mk f f.aemeasurable = f := by
  conv_lhs => simp only [cast]
  split_ifs with h
  · exact Classical.choose_spec h |>.symm
  conv_rhs => rw [← Quotient.out_eq' f]
  rw [← mk, mk_eq_mk]
  exact (AEMeasurable.ae_eq_mk _).symm

@[ext]
theorem ext {f g : α →ₐₑ[μ] β} (h : f =ᵐ[μ] g) : f = g := by
  rwa [← f.mk_coeFn, ← g.mk_coeFn, mk_eq_mk]

theorem coeFn_mk (f : α → β) (hf) : (mk f hf : α →ₐₑ[μ] β) =ᵐ[μ] f := by
  rw [← mk_eq_mk (hf := AEEq.aemeasurable ..) (hg := hf), mk_coeFn]

@[elab_as_elim]
theorem induction_on (f : α →ₐₑ[μ] β) {p : (α →ₐₑ[μ] β) → Prop} (H : ∀ f hf, p (mk f hf)) : p f :=
  Quotient.inductionOn' f <| Subtype.forall.2 H

@[elab_as_elim]
theorem induction_on₂ {α' β' : Type*} [MeasurableSpace α'] [MeasurableSpace β'] {μ' : Measure α'}
    (f : α →ₐₑ[μ] β) (f' : α' →ₐₑ[μ'] β') {p : (α →ₐₑ[μ] β) → (α' →ₐₑ[μ'] β') → Prop}
    (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) : p f f' :=
  induction_on f fun f hf => induction_on f' <| H f hf

@[elab_as_elim]
theorem induction_on₃ {α' β' : Type*} [MeasurableSpace α'] [MeasurableSpace β'] {μ' : Measure α'}
    {α'' β'' : Type*} [MeasurableSpace α''] [MeasurableSpace β''] {μ'' : Measure α''}
    (f : α →ₐₑ[μ] β) (f' : α' →ₐₑ[μ'] β') (f'' : α'' →ₐₑ[μ''] β'')
    {p : (α →ₐₑ[μ] β) → (α' →ₐₑ[μ'] β') → (α'' →ₐₑ[μ''] β'') → Prop}
    (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) : p f f' f'' :=
  induction_on f fun f hf => induction_on₂ f' f'' <| H f hf

end

end AEEq

end MeasureTheory
