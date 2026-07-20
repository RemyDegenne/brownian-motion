/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

public section

open MeasureTheory

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y Z : ι → Ω → E}

/-- Two processes are indistinguishable if almost surely they agree everywhere. -/
@[expose]
def Indistinguishable (P : Measure Ω) (X Y : ι → Ω → E) : Prop :=
  ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω

/-- Two processes are indistinguishable if almost surely they agree everywhere. -/
notation3:50 X " ≡ᵐ[" P:50 "] " Y:50 => Indistinguishable P X Y

namespace Indistinguishable

@[refl, simp]
protected lemma refl (P : Measure Ω) (X : ι → Ω → E) : X ≡ᵐ[P] X :=
  .of_forall fun _ _ ↦ rfl

protected lemma rfl : X ≡ᵐ[P] X := by rfl

@[symm]
protected lemma symm (h : X ≡ᵐ[P] Y) : Y ≡ᵐ[P] X := by
  filter_upwards [h] with ω h t using (h t).symm

@[trans]
protected lemma trans (h1 : X ≡ᵐ[P] Y) (h2 : Y ≡ᵐ[P] Z) : X ≡ᵐ[P] Z := by
  filter_upwards [h1, h2] with ω h t
  grind

protected lemma fun_comp {F : Type*} (h : X ≡ᵐ[P] Y) (f : E → F) :
    (fun t ω ↦ f (X t ω)) ≡ᵐ[P] (fun t ω ↦ f (Y t ω)) := by
  filter_upwards [h] with ω h t
  rw [h]

protected lemma fun_comp₂ {F G : Type*} {Z T : ι → Ω → F} (h1 : X ≡ᵐ[P] Y)
    (h2 : Z ≡ᵐ[P] T) (f : E → F → G) :
    (fun t ω ↦ f (X t ω) (Z t ω)) ≡ᵐ[P] (fun t ω ↦ f (Y t ω) (T t ω)) := by
  filter_upwards [h1, h2] with ω h1 h2 t
  rw [h1, h2]

@[to_additive (attr := to_fun)]
protected lemma inv [Inv E] (h : X ≡ᵐ[P] Y) :
    X⁻¹ ≡ᵐ[P] Y⁻¹ := h.fun_comp _

@[to_additive (attr := to_fun)]
protected lemma mul [Mul E] {Z T : ι → Ω → E} (h1 : X ≡ᵐ[P] Y) (h2 : Z ≡ᵐ[P] T) :
    X * Z ≡ᵐ[P] Y * T := h1.fun_comp₂ h2 _

@[to_additive (attr := to_fun)]
protected lemma div [Div E] {Z T : ι → Ω → E} (h1 : X ≡ᵐ[P] Y) (h2 : Z ≡ᵐ[P] T) :
    X / Z ≡ᵐ[P] Y / T := h1.fun_comp₂ h2 _

@[to_additive (attr := to_fun)]
protected lemma smul {F : Type*} {Z T : ι → Ω → F} [SMul F E] (h1 : X ≡ᵐ[P] Y)
    (h2 : Z ≡ᵐ[P] T) :
    Z • X ≡ᵐ[P] T • Y := h2.fun_comp₂ h1 _

@[to_additive (attr := to_fun)]
protected lemma const_smul {F : Type*} [SMul F E] {c : F} (h : X ≡ᵐ[P] Y) :
    c • X ≡ᵐ[P] c • Y := h.fun_comp _

end Indistinguishable

end ProbabilityTheory
