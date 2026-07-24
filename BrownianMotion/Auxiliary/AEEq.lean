/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import BrownianMotion.Auxiliary.Adapted

/-!

# Indistinguishable processes

We build a space of equivalence classes of processes, where two processes are treated as identical
if they are `Indistinguishable`. We form the set of equivalence classes under the relation of
being indistinguishable.
We consider equivalence classes of strongly adapted processes
(or, equivalently, of almost everywhere strongly adapted processes.)

## Notation

* `α →ₚ[μ, 𝓕] β`

## Main statements

* The linear structure of `L⁰` :
  Addition and scalar multiplication are defined on `L⁰` in the natural way, i.e.,
  `[f] + [g] := [f + g]`, `c • [f] := [c • f]`. So defined, `α →ₚ β` inherits the linear structure
  of `β`. For example, if `β` is a module, then `α →ₚ β` is a module over the same ring.

  See `mk_add_mk`, `neg_mk`, `mk_sub`, `smul_mk`,
  `coeFn_add`, `coeFn_neg`, `coeFn_sub`, `coeFn_smul`

* The order structure of `L⁰` :
  `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
  And `α →ₚ β` inherits the preorder and partial order of `β`.

  TODO: Define `sup` and `inf` on `L⁰` so that it forms a lattice. It seems that `β` must be a
  linear order, since otherwise `f ⊔ g` may not be a measurable function.

## Implementation notes

* `f.cast`:      To find a representative of `f : α →ₚ β`, use the coercion `(f : α → β)`, which
                 is implemented as `f.toFun`.
                 For each operation `op` in `L⁰`, there is a lemma called `coe_fn_op`,
                 characterizing, say, `(f op g : α → β)`.
* `AEEqProcess.mk`:  To construct an `L⁰` function `α →ₚ β` from an almost everywhere strongly
                 measurable function `f : α → β`, use `ae_eq_fun.mk`
* `comp`:        Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₚ γ` when `g` is
                 continuous. Use `compMeasurable` if `g` is only measurable (this requires the
                 target space to be second countable).
* `comp₂`:       Use `comp₂ g f₁ f₂` to get `[fun a ↦ g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`

-/

@[expose] public section

noncomputable section

open Topology Set Filter TopologicalSpace ENNReal EMetric MeasureTheory Function

variable {ι α β γ δ : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}
  [Preorder ι] {𝓕 : Filtration ι mα}

namespace MeasureTheory

section MeasurableSpace

variable [TopologicalSpace β]
variable (𝓕 β)

/-- The equivalence relation of being almost everywhere equal for almost everywhere strongly
measurable functions. -/
@[implicit_reducible]
def Measure.aeEqSetoid' (μ : Measure α) :
    Setoid { X : ι → α → β // AEStronglyAdapted X 𝓕 μ } :=
  ⟨fun f g => f.1 ≡ᵐ[μ] g, fun {_} => .rfl, fun {_ _} => .symm,
    fun {_ _ _} => .trans⟩

variable (α)

/-- The space of equivalence classes of almost everywhere strongly measurable functions, where two
strongly measurable functions are equivalent if they agree almost everywhere, i.e.,
they differ on a set of measure `0`. -/
def AEEqProcess (μ : Measure α) : Type _ :=
  Quotient (μ.aeEqSetoid' β 𝓕)

variable {α β}

@[inherit_doc MeasureTheory.AEEqProcess]
notation:25 α " →ₚ[" μ ", " 𝓕 "] " β => AEEqProcess α β 𝓕 μ

end MeasurableSpace

variable [TopologicalSpace δ]

namespace AEEqProcess

section
variable [TopologicalSpace β]

/-- Construct the equivalence class `[f]` of an almost everywhere measurable function `f`, based
on the equivalence relation of being almost everywhere equal. -/
def mk {β : Type*} [TopologicalSpace β] (f : ι → α → β) (hf : AEStronglyAdapted f 𝓕 μ) :
    α →ₚ[μ, 𝓕] β :=
  Quotient.mk'' ⟨f, hf⟩

open scoped Classical in
/-- Coercion from a space of equivalence classes of almost everywhere strongly measurable
functions to functions. We ensure that if `f` has a constant representative,
then we choose that one. -/
@[coe]
def cast (X : α →ₚ[μ, 𝓕] β) : ι → α → β :=
  if h : ∃ (c : β), X = mk (fun _ _ ↦ c) .const then
    fun _ _ ↦ h.choose else
    AEStronglyAdapted.mk _ (Quotient.out X : { f : ι → α → β // AEStronglyAdapted f 𝓕 μ }).2

/-- A measurable representative of an `AEEqProcess` [f] -/
instance instCoeFun : CoeFun (α →ₚ[μ, 𝓕] β) fun _ => ι → α → β := ⟨cast⟩

protected theorem stronglyAdapted (f : α →ₚ[μ, 𝓕] β) : StronglyAdapted 𝓕 f := by
  simp only [cast]
  split_ifs with h
  · exact stronglyAdapted_const 𝓕 _
  · apply AEStronglyAdapted.stronglyAdapted_mk

protected theorem aestronglyAdapted (f : α →ₚ[μ, 𝓕] β) : AEStronglyAdapted f 𝓕 μ :=
  f.stronglyAdapted.aestronglyAdapted

protected theorem adapted [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : α →ₚ[μ, 𝓕] β) : Adapted 𝓕 f :=
  f.stronglyAdapted.adapted

@[simp]
theorem quot_mk_eq_mk (f : ι → α → β) (hf) :
    (Quot.mk (@Setoid.r _ <| μ.aeEqSetoid' β 𝓕) ⟨f, hf⟩ : α →ₚ[μ, 𝓕] β) = mk f hf :=
  rfl

@[simp]
theorem mk_eq_mk {f g : ι → α → β} {hf hg} : (mk f hf : α →ₚ[μ, 𝓕] β) = mk g hg ↔ f ≡ᵐ[μ] g :=
  Quotient.eq''

@[simp]
theorem mk_coeFn (f : α →ₚ[μ, 𝓕] β) : mk f f.aestronglyAdapted = f := by
  conv_lhs => simp only [cast]
  split_ifs with h
  · exact Classical.choose_spec h |>.symm
  conv_rhs => rw [← Quotient.out_eq' f]
  rw [← mk, mk_eq_mk]
  exact (AEStronglyAdapted.indist_mk _).symm

@[ext]
theorem ext {f g : α →ₚ[μ, 𝓕] β} (h : f ≡ᵐ[μ] g) : f = g := by
  rwa [← f.mk_coeFn, ← g.mk_coeFn, mk_eq_mk]

theorem coeFn_mk (f : ι → α → β) (hf) : (mk f hf : α →ₚ[μ, 𝓕] β) ≡ᵐ[μ] f := by
  rw [← mk_eq_mk (hf := AEEqProcess.aestronglyAdapted ..) (hg := hf), mk_coeFn]

@[elab_as_elim]
theorem induction_on (f : α →ₚ[μ, 𝓕] β) {p : (α →ₚ[μ, 𝓕] β) → Prop} (H : ∀ f hf, p (mk f hf)) :
    p f :=
  Quotient.inductionOn' f <| Subtype.forall.2 H

@[elab_as_elim]
theorem induction_on₂ {α' β' ι' : Type*} {mα' : MeasurableSpace α'} [TopologicalSpace β']
    {μ' : Measure α'} [Preorder ι'] {𝓕' : Filtration ι' mα'}
    (f : α →ₚ[μ, 𝓕] β) (f' : α' →ₚ[μ', 𝓕'] β') {p : (α →ₚ[μ, 𝓕] β) → (α' →ₚ[μ', 𝓕'] β') → Prop}
    (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) : p f f' :=
  induction_on f fun f hf => induction_on f' <| H f hf

@[elab_as_elim]
theorem induction_on₃ {α' β' ι' : Type*} {mα' : MeasurableSpace α'} [TopologicalSpace β']
    {μ' : Measure α'} [Preorder ι'] {𝓕' : Filtration ι' mα'}
    {α'' β'' ι'' : Type*} {mα'' : MeasurableSpace α''} [TopologicalSpace β''] {μ'' : Measure α''}
    [Preorder ι''] {𝓕'' : Filtration ι'' mα''}
    (f : α →ₚ[μ, 𝓕] β) (f' : α' →ₚ[μ', 𝓕'] β') (f'' : α'' →ₚ[μ'', 𝓕''] β'')
    {p : (α →ₚ[μ, 𝓕] β) → (α' →ₚ[μ', 𝓕'] β') → (α'' →ₚ[μ'', 𝓕''] β'') → Prop}
    (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) : p f f' f'' :=
  induction_on f fun f hf => induction_on₂ f' f'' <| H f hf

end

variable [TopologicalSpace β] [TopologicalSpace γ]

/-- Given a continuous function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₚ β`,
return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
`[g ∘ f] : α →ₚ γ`. -/
def comp (g : β → γ) (hg : Continuous g) (f : α →ₚ[μ, 𝓕] β) : α →ₚ[μ, 𝓕] γ :=
  Quotient.liftOn' f (fun f => mk (fun t ↦ g ∘ (f.1 t)) (hg.comp_aestronglyAdapted f.2))
    fun _ _ H => mk_eq_mk.2 <| H.fun_comp g

@[simp]
theorem comp_mk (g : β → γ) (hg : Continuous g) (f : ι → α → β) (hf) :
    comp g hg (mk f hf : α →ₚ[μ, 𝓕] β) = mk (fun t ↦ g ∘ (f t)) (hg.comp_aestronglyAdapted hf) :=
  rfl

@[simp]
theorem comp_id (f : α →ₚ[μ, 𝓕] β) : comp id (continuous_id) f = f := by
  rcases f; rfl

@[simp]
theorem comp_comp (g : γ → δ) (g' : β → γ) (hg : Continuous g) (hg' : Continuous g')
    (f : α →ₚ[μ, 𝓕] β) : comp g hg (comp g' hg' f) = comp (g ∘ g') (hg.comp hg') f := by
  rcases f; rfl

theorem comp_eq_mk (g : β → γ) (hg : Continuous g) (f : α →ₚ[μ, 𝓕] β) :
    comp g hg f = mk (fun t ↦ g ∘ (f t)) (hg.comp_aestronglyAdapted f.aestronglyAdapted) := by
  rw [← comp_mk g hg f f.aestronglyAdapted, mk_coeFn]

theorem coeFn_comp (g : β → γ) (hg : Continuous g) (f : α →ₚ[μ, 𝓕] β) :
    comp g hg f ≡ᵐ[μ] (fun t ↦ g ∘ (f t)) := by
  rw [comp_eq_mk]
  apply coeFn_mk

/-- The class of `x ↦ (f x, g x)`. -/
def pair (f : α →ₚ[μ, 𝓕] β) (g : α →ₚ[μ, 𝓕] γ) : α →ₚ[μ, 𝓕] β × γ :=
  Quotient.liftOn₂' f g (fun f g => mk (fun t ω => (f.1 t ω, g.1 t ω)) (f.2.prodMk g.2))
    fun _f _g _f' _g' Hf Hg => mk_eq_mk.2 <| Hf.prodMk Hg

@[simp]
theorem pair_mk_mk (f : ι → α → β) (hf) (g : ι → α → γ) (hg) :
    (mk f hf : α →ₚ[μ, 𝓕] β).pair (mk g hg) = mk (fun t ω => (f t ω, g t ω)) (hf.prodMk hg) :=
  rfl

theorem pair_eq_mk (f : α →ₚ[μ, 𝓕] β) (g : α →ₚ[μ, 𝓕] γ) :
    f.pair g =
      mk (fun t ω => (f t ω, g t ω)) (f.aestronglyAdapted.prodMk g.aestronglyAdapted) := by
  simp only [← pair_mk_mk, mk_coeFn, f.aestronglyAdapted, g.aestronglyAdapted]

theorem coeFn_pair (f : α →ₚ[μ, 𝓕] β) (g : α →ₚ[μ, 𝓕] γ) :
    f.pair g ≡ᵐ[μ] fun t ω => (f t ω, g t ω) := by
  rw [pair_eq_mk]
  apply coeFn_mk

/-- Given a continuous function `g : β → γ → δ`, and almost everywhere equal functions
`[f₁] : α →ₚ β` and `[f₂] : α →ₚ γ`, return the equivalence class of the function
`fun a => g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
`[fun a => g (f₁ a) (f₂ a)] : α →ₚ γ` -/
def comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₚ[μ, 𝓕] β) (f₂ : α →ₚ[μ, 𝓕] γ) :
    α →ₚ[μ, 𝓕] δ :=
  comp _ hg (f₁.pair f₂)

@[simp]
theorem comp₂_mk_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : ι → α → β) (f₂ : ι → α → γ)
    (hf₁ hf₂) :
    comp₂ g hg (mk f₁ hf₁ : α →ₚ[μ, 𝓕] β) (mk f₂ hf₂) =
      mk (fun t ω => g (f₁ t ω) (f₂ t ω)) (hg.comp_aestronglyAdapted (hf₁.prodMk hf₂)) :=
  rfl

theorem comp₂_eq_pair (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₚ[μ, 𝓕] β)
    (f₂ : α →ₚ[μ, 𝓕] γ) : comp₂ g hg f₁ f₂ = comp _ hg (f₁.pair f₂) :=
  rfl

theorem comp₂_eq_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₚ[μ, 𝓕] β)
    (f₂ : α →ₚ[μ, 𝓕] γ) : comp₂ g hg f₁ f₂ = mk (fun t ω => g (f₁ t ω) (f₂ t ω))
      (hg.comp_aestronglyAdapted (f₁.aestronglyAdapted.prodMk f₂.aestronglyAdapted)) := by
  rw [comp₂_eq_pair, pair_eq_mk, comp_mk]; rfl

theorem coeFn_comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₚ[μ, 𝓕] β)
    (f₂ : α →ₚ[μ, 𝓕] γ) : comp₂ g hg f₁ f₂ ≡ᵐ[μ] fun t ω => g (f₁ t ω) (f₂ t ω) := by
  rw [comp₂_eq_mk]
  apply coeFn_mk

/-- Interpret `f : α →ₚ[μ, 𝓕] β` as a germ at `ae μ` forgetting that `f` is almost everywhere
strongly measurable. -/
def toGerm (f : α →ₚ[μ, 𝓕] β) : Germ (ae μ) (ι → β) :=
  Quotient.liftOn' f (fun f => (fun ω t ↦ f.1 t ω : Germ (ae μ) (ι → β)))
  fun _ _ H => Germ.coe_eq.2 H.ae_eq

@[simp]
theorem mk_toGerm (f : ι → α → β) (hf) : (mk f hf : α →ₚ[μ, 𝓕] β).toGerm = (fun ω t ↦ f t ω) :=
  rfl

theorem toGerm_eq (f : α →ₚ[μ, 𝓕] β) : f.toGerm = (fun ω t ↦ f t ω) := by
  rw [← mk_toGerm f f.aestronglyAdapted, mk_coeFn]

theorem toGerm_injective : Injective (toGerm : (α →ₚ[μ, 𝓕] β) → Germ (ae μ) (ι → β)) := fun f g H =>
  ext <| EventuallyEq.indist <| Germ.coe_eq.1 <| by rwa [← toGerm_eq, ← toGerm_eq]

theorem comp_toGerm (g : β → γ) (hg : Continuous g) (f : α →ₚ[μ, 𝓕] β) :
    (comp g hg f).toGerm = f.toGerm.map (fun f t ↦ g (f t)) :=
  induction_on f fun f _ => by
    simp only [comp_mk, mk_toGerm, comp_apply, Germ.map_coe, Germ.coe_eq]
    exact ae_of_all _ (by simp)

theorem comp₂_toGerm (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₚ[μ, 𝓕] β)
    (f₂ : α →ₚ[μ, 𝓕] γ) :
    (comp₂ g hg f₁ f₂).toGerm = f₁.toGerm.map₂ (fun f h t ↦ g (f t) (h t)) f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp; rfl

/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
for almost all `a` -/
def LiftPred (p : (ι → β) → Prop) (f : α →ₚ[μ, 𝓕] β) : Prop :=
  f.toGerm.LiftPred p

/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
`(f a, g a)` for almost all `a` -/
def LiftRel (r : (ι → β) → (ι → γ) → Prop) (f : α →ₚ[μ, 𝓕] β) (g : α →ₚ[μ, 𝓕] γ) : Prop :=
  f.toGerm.LiftRel r g.toGerm

theorem liftRel_mk_mk {r : (ι → β) → (ι → γ) → Prop} {f : ι → α → β} {g : ι → α → γ} {hf hg} :
    LiftRel r (mk f hf : α →ₚ[μ, 𝓕] β) (mk g hg) ↔ ∀ᵐ a ∂μ, r (f · a) (g · a) :=
  Iff.rfl

theorem liftRel_iff_coeFn {r : (ι → β) → (ι → γ) → Prop} {f : α →ₚ[μ, 𝓕] β} {g : α →ₚ[μ, 𝓕] γ} :
    LiftRel r f g ↔ ∀ᵐ a ∂μ, r (f · a) (g · a) := by
  rw [← liftRel_mk_mk (hf := f.aestronglyAdapted) (hg := g.aestronglyAdapted),
    mk_coeFn, mk_coeFn]

variable (α)

/-- The equivalence class of a constant function: `[fun _ : α => b]`, based on the equivalence
relation of being almost everywhere equal -/
def const (b : β) : α →ₚ[μ, 𝓕] β :=
  mk (fun _ _ ↦ b) .const

theorem coeFn_const (b : β) : (const α b : α →ₚ[μ, 𝓕] β) ≡ᵐ[μ] (fun _ _ ↦ b) :=
  coeFn_mk _ _

/-- If the measure is nonzero, we can strengthen `coeFn_const` to get an equality. -/
@[simp]
theorem coeFn_const_eq [NeZero μ] (b : β) (t : ι) (x : α) : (const α b : α →ₚ[μ, 𝓕] β) t x = b := by
  simp only [cast]
  split_ifs with h
  case neg => exact h.elim ⟨b, rfl⟩
  have := h.choose_spec
  set b := h.choose with hb
  simp_rw [const, mk_eq_mk, ProbabilityTheory.Indistinguishable] at this
  have ⟨_, h1⟩ := Eventually.exists this
  rw [h1 t]

theorem coeFn_const_eq' (b : β) : ∃ b', ((const α b : α →ₚ[μ, 𝓕] β) : ι → α → β) = fun _ ↦ b' := by
  simp only [cast]
  split_ifs with h
  case neg => exact h.elim ⟨b, rfl⟩
  exact ⟨fun _ ↦ h.choose, by ext; simp⟩

variable {α}

instance instInhabited [Inhabited β] : Inhabited (α →ₚ[μ, 𝓕] β) :=
  ⟨const α default⟩

@[to_additive]
instance instOne [One β] : One (α →ₚ[μ, 𝓕] β) :=
  ⟨const α 1⟩

@[to_additive]
theorem one_def [One β] : (1 : α →ₚ[μ, 𝓕] β) = mk (fun _ _ => 1) .const :=
  rfl

@[to_additive]
theorem coeFn_one [One β] : ⇑(1 : α →ₚ[μ, 𝓕] β) ≡ᵐ[μ] 1 :=
  coeFn_const ..

@[to_additive (attr := simp)]
theorem coeFn_one_eq [NeZero μ] [One β] {t : ι} {x : α} : (1 : α →ₚ[μ, 𝓕] β) t x = 1 :=
  coeFn_const_eq ..

@[to_additive (attr := simp)]
theorem one_toGerm [One β] : (1 : α →ₚ[μ, 𝓕] β).toGerm = 1 :=
  rfl

-- Note we set up the scalar actions before the `Monoid` structures in case we want to
-- try to override the `nsmul` or `zsmul` fields in future.
section SMul

variable {𝕜 𝕜' : Type*}
variable [SMul 𝕜 γ] [ContinuousConstSMul 𝕜 γ]
variable [SMul 𝕜' γ] [ContinuousConstSMul 𝕜' γ]

instance instSMul : SMul 𝕜 (α →ₚ[μ, 𝓕] γ) :=
  ⟨fun c f => comp (c • ·) (continuous_id.const_smul c) f⟩

@[simp]
theorem smul_mk (c : 𝕜) (f : ι → α → γ) (hf : AEStronglyAdapted f 𝓕 μ) :
    c • (mk f hf : α →ₚ[μ, 𝓕] γ) = mk (c • f) hf.const_smul :=
  rfl

theorem coeFn_smul (c : 𝕜) (f : α →ₚ[μ, 𝓕] γ) : ⇑(c • f) ≡ᵐ[μ] c • ⇑f :=
  coeFn_comp _ _ _

theorem smul_toGerm (c : 𝕜) (f : α →ₚ[μ, 𝓕] γ) : (c • f).toGerm = c • f.toGerm :=
  comp_toGerm _ _ _

instance instSMulCommClass [SMulCommClass 𝕜 𝕜' γ] : SMulCommClass 𝕜 𝕜' (α →ₚ[μ, 𝓕] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_comm]⟩

instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' γ] : IsScalarTower 𝕜 𝕜' (α →ₚ[μ, 𝓕] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_assoc]⟩

instance instIsCentralScalar [SMul 𝕜ᵐᵒᵖ γ] [IsCentralScalar 𝕜 γ] :
    IsCentralScalar 𝕜 (α →ₚ[μ, 𝓕] γ) :=
  ⟨fun a f => induction_on f fun f hf => by simp_rw [smul_mk, op_smul_eq_smul]⟩

end SMul

section Mul

variable [Mul γ] [ContinuousMul γ]

@[to_additive]
instance instMul : Mul (α →ₚ[μ, 𝓕] γ) :=
  ⟨comp₂ (· * ·) continuous_mul⟩

@[to_additive (attr := simp)]
theorem mk_mul_mk (f g : ι → α → γ) (hf : AEStronglyAdapted f 𝓕 μ) (hg : AEStronglyAdapted g 𝓕 μ) :
    (mk f hf : α →ₚ[μ, 𝓕] γ) * mk g hg = mk (f * g) (hf.mul hg) :=
  rfl

@[to_additive]
theorem coeFn_mul (f g : α →ₚ[μ, 𝓕] γ) : ⇑(f * g) ≡ᵐ[μ] f * g :=
  coeFn_comp₂ _ _ _ _

@[to_additive (attr := simp)]
theorem mul_toGerm (f g : α →ₚ[μ, 𝓕] γ) : (f * g).toGerm = f.toGerm * g.toGerm :=
  comp₂_toGerm _ _ _ _

end Mul

instance instAddMonoid [AddMonoid γ] [ContinuousAdd γ] : AddMonoid (α →ₚ[μ, 𝓕] γ) :=
  toGerm_injective.addMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

instance instAddCommMonoid [AddCommMonoid γ] [ContinuousAdd γ] : AddCommMonoid (α →ₚ[μ, 𝓕] γ) :=
  toGerm_injective.addCommMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

section Monoid

variable [Monoid γ] [ContinuousMul γ]

instance instPowNat : Pow (α →ₚ[μ, 𝓕] γ) ℕ :=
  ⟨fun f n => comp _ (continuous_pow n) f⟩

@[simp]
theorem mk_pow (f : ι → α → γ) (hf) (n : ℕ) :
    (mk f hf : α →ₚ[μ, 𝓕] γ) ^ n =
      mk (f ^ n) ((_root_.continuous_pow n).comp_aestronglyAdapted hf) :=
  rfl

theorem coeFn_pow (f : α →ₚ[μ, 𝓕] γ) (n : ℕ) : ⇑(f ^ n) ≡ᵐ[μ] (⇑f) ^ n :=
  coeFn_comp _ _ _

@[simp]
theorem pow_toGerm (f : α →ₚ[μ, 𝓕] γ) (n : ℕ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _

@[to_additive existing]
instance instMonoid : Monoid (α →ₚ[μ, 𝓕] γ) :=
  toGerm_injective.monoid toGerm one_toGerm mul_toGerm pow_toGerm

/-- `AEEqProcess.toGerm` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `AEEqProcess.toGerm` as an `AddMonoidHom`. -/]
def toGermMonoidHom : (α →ₚ[μ, 𝓕] γ) →* (ae μ).Germ (ι → γ) where
  toFun := toGerm
  map_one' := one_toGerm
  map_mul' := mul_toGerm

end Monoid

@[to_additive existing]
instance instCommMonoid [CommMonoid γ] [ContinuousMul γ] : CommMonoid (α →ₚ[μ, 𝓕] γ) :=
  toGerm_injective.commMonoid toGerm one_toGerm mul_toGerm pow_toGerm

@[to_additive]
theorem coeFn_finsetProd [CommMonoid γ] [ContinuousMul γ]
    {η : Type*} (s : Finset η) (f : η → α →ₚ[μ, 𝓕] γ) :
    ⇑(∏ i ∈ s, f i) ≡ᵐ[μ] ∏ i ∈ s, ⇑(f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [coeFn_one]
  | insert a s ha ih =>
    simp only [ha, not_false_eq_true, Finset.prod_insert]
    grw [coeFn_mul, ih]

@[to_additive]
theorem coeFn_fun_finsetProd [CommMonoid γ] [ContinuousMul γ]
    {ι : Type*} (s : Finset ι) (f : ι → α →ₚ[μ, 𝓕] γ) :
    ⇑(∏ i ∈ s, f i) ≡ᵐ[μ] fun x ↦ ∏ i ∈ s, f i x := by
  grw [coeFn_finsetProd]
  filter_upwards with x using by simp

section Group

variable [Group γ] [IsTopologicalGroup γ]

section Inv

@[to_additive]
instance instInv : Inv (α →ₚ[μ, 𝓕] γ) :=
  ⟨comp Inv.inv continuous_inv⟩

@[to_additive (attr := simp)]
theorem inv_mk (f : ι → α → γ) (hf) : (mk f hf : α →ₚ[μ, 𝓕] γ)⁻¹ = mk f⁻¹ hf.inv :=
  rfl

@[to_additive]
theorem coeFn_inv (f : α →ₚ[μ, 𝓕] γ) : ⇑f⁻¹ ≡ᵐ[μ] f⁻¹ :=
  coeFn_comp _ _ _

@[to_additive]
theorem inv_toGerm (f : α →ₚ[μ, 𝓕] γ) : f⁻¹.toGerm = f.toGerm⁻¹ :=
  comp_toGerm _ _ _

end Inv

section Div

@[to_additive]
instance instDiv : Div (α →ₚ[μ, 𝓕] γ) :=
  ⟨comp₂ Div.div continuous_div'⟩

@[to_additive (attr := simp)]
theorem mk_div (f g : ι → α → γ) (hf : AEStronglyAdapted f 𝓕 μ) (hg : AEStronglyAdapted g 𝓕 μ) :
    mk (f / g) (hf.div' hg) = (mk f hf : α →ₚ[μ, 𝓕] γ) / mk g hg :=
  rfl

@[to_additive]
theorem coeFn_div (f g : α →ₚ[μ, 𝓕] γ) : ⇑(f / g) ≡ᵐ[μ] f / g :=
  coeFn_comp₂ _ _ _ _

@[to_additive]
theorem div_toGerm (f g : α →ₚ[μ, 𝓕] γ) : (f / g).toGerm = f.toGerm / g.toGerm :=
  comp₂_toGerm _ _ _ _

end Div

section ZPow

instance instPowInt : Pow (α →ₚ[μ, 𝓕] γ) ℤ :=
  ⟨fun f n => comp _ (continuous_zpow n) f⟩

@[simp]
theorem mk_zpow (f : ι → α → γ) (hf) (n : ℤ) :
    (mk f hf : α →ₚ[μ, 𝓕] γ) ^ n = mk (f ^ n) ((continuous_zpow n).comp_aestronglyAdapted hf) :=
  rfl

theorem coeFn_zpow (f : α →ₚ[μ, 𝓕] γ) (n : ℤ) : ⇑(f ^ n) ≡ᵐ[μ] (⇑f) ^ n :=
  coeFn_comp _ _ _

@[simp]
theorem zpow_toGerm (f : α →ₚ[μ, 𝓕] γ) (n : ℤ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _

end ZPow

end Group

instance instAddGroup [AddGroup γ] [IsTopologicalAddGroup γ] : AddGroup (α →ₚ[μ, 𝓕] γ) :=
  toGerm_injective.addGroup toGerm zero_toGerm add_toGerm neg_toGerm sub_toGerm
    (fun _ _ => smul_toGerm _ _) fun _ _ => smul_toGerm _ _

instance instAddCommGroup [AddCommGroup γ] [IsTopologicalAddGroup γ] :
    AddCommGroup (α →ₚ[μ, 𝓕] γ) :=
  { add_comm := add_comm }

@[to_additive existing]
instance instGroup [Group γ] [IsTopologicalGroup γ] : Group (α →ₚ[μ, 𝓕] γ) :=
  toGerm_injective.group _ one_toGerm mul_toGerm inv_toGerm div_toGerm pow_toGerm zpow_toGerm

@[to_additive existing]
instance instCommGroup [CommGroup γ] [IsTopologicalGroup γ] : CommGroup (α →ₚ[μ, 𝓕] γ) :=
  { mul_comm := mul_comm }

section Module

variable {𝕜 : Type*}

instance instMulAction [Monoid 𝕜] [MulAction 𝕜 γ] [ContinuousConstSMul 𝕜 γ] :
    MulAction 𝕜 (α →ₚ[μ, 𝓕] γ) :=
  toGerm_injective.mulAction toGerm smul_toGerm

instance instDistribMulAction [Monoid 𝕜] [AddMonoid γ] [ContinuousAdd γ] [DistribMulAction 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : DistribMulAction 𝕜 (α →ₚ[μ, 𝓕] γ) :=
  toGerm_injective.distribMulAction (toGermAddMonoidHom : (α →ₚ[μ, 𝓕] γ) →+ _) fun c : 𝕜 =>
    smul_toGerm c

instance instModule [Semiring 𝕜] [AddCommMonoid γ] [ContinuousAdd γ] [Module 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : Module 𝕜 (α →ₚ[μ, 𝓕] γ) :=
  toGerm_injective.module 𝕜 (toGermAddMonoidHom : (α →ₚ[μ, 𝓕] γ) →+ _) smul_toGerm

end Module

open ENNReal

section Star

variable {R : Type*} [TopologicalSpace R]

instance [Star R] [ContinuousStar R] : Star (α →ₚ[μ, 𝓕] R) where
  star f := (AEEqProcess.comp _ continuous_star f)

lemma coeFn_star [Star R] [ContinuousStar R] (f : α →ₚ[μ, 𝓕] R) :
    ↑(star f) ≡ᵐ[μ] (star f : ι → α → R) :=
  coeFn_comp _ (continuous_star) f

instance [InvolutiveStar R] [ContinuousStar R] : InvolutiveStar (α →ₚ[μ, 𝓕] R) where
  star_involutive f := comp_comp _ _ _ _ f |>.trans <| by simp [star_involutive.comp_self]

instance [Star R] [TrivialStar R] [ContinuousStar R] : TrivialStar (α →ₚ[μ, 𝓕] R) where
  star_trivial f := show comp _ _ f = f by simp [funext star_trivial, ← Function.id_def]

end Star

end AEEqProcess

end MeasureTheory
