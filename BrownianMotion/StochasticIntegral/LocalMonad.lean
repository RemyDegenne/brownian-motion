/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import BrownianMotion.StochasticIntegral.Locally
public import Mathlib.MeasureTheory.Category.MeasCat
public import Mathlib.CategoryTheory.Category.Preorder

/-! # The Local Monad on Stable Properties

-/

@[expose] public section

open MeasureTheory Filter CategoryTheory Filtration
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Zero E]
  [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {𝓕 : Filtration ι mΩ}

/-- The category of stable properties. -/
abbrev StableCat (E : Type*) [Zero E] (𝓕 : Filtration ι mΩ) :=
    ObjectProperty.FullSubcategory <| fun (p : (ι → Ω → E) → Prop) ↦ IsStable 𝓕 p

/-- Local is a functor from Stable to Stable. -/
def Local (P : Measure Ω) (p : StableCat E 𝓕) : StableCat E 𝓕 :=
  ⟨(Locally p.1 𝓕 · P), p.2.locally⟩

/-- The local functor is monotone. -/
lemma LocalMono (P : Measure Ω) {p q : StableCat E 𝓕} (h : p ⟶ q) (u : ι → Ω → E) :
    (Local P p).1 u ≤ (Local P q).1 u :=
  Locally.mono <| fun v ↦ leOfHom <| h.hom v

/-- The local functor. -/
def LocalFunctor (P : Measure Ω) : StableCat E 𝓕 ⥤ StableCat E 𝓕 where
  obj X := Local P X
  map f := ObjectProperty.homMk fun _ ↦ homOfLE <| LocalMono P f _
  map_id _ := rfl
  map_comp _ _ := rfl

variable [IsFiniteMeasure P] [DenselyOrdered ι] [NoMaxOrder ι] [SecondCountableTopology ι]

/-- The Stable properties form a monad with the local functor. -/
def StableMonad [𝓕.IsRightContinuous] : Monad (StableCat E 𝓕) where
  toFunctor := LocalFunctor P
  η := { app _ := ObjectProperty.homMk fun _ ↦ homOfLE Locally.of_prop
         naturality _ _ _ := rfl }
  μ := { app p := ObjectProperty.homMk fun _ ↦ homOfLE p.2.locally_locally_iff.1
         naturality _ _ _ := rfl }

end ProbabilityTheory
