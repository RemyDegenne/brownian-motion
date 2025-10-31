import BrownianMotion.StochasticIntegral.Locally
import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.CategoryTheory.Category.Preorder

open MeasureTheory Filter CategoryTheory
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Zero E]
  [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [SecondCountableTopology ι] [IsFiniteMeasure P] [DenselyOrdered ι]
  [FirstCountableTopology ι] [NoMaxOrder ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}


/-- The category of stable properties. -/
abbrev StableCat (E : Type*) [Zero E] (𝓕 : Filtration ι mΩ) :=
    ObjectProperty.FullSubcategory <| fun (p : (ι → Ω → E) → Prop) ↦ IsStable 𝓕 p

-- structure StableSkel (E : Type*) [Zero E] (𝓕 : Filtration ι mΩ) where
--   toProp : (ι → Ω → E) → Prop
--   isStable : IsStable 𝓕 toProp

-- noncomputable def StableSkel.eval {E : Type*} [Zero E] {𝓕 : Filtration ι mΩ}
--     (A : StableSkel E 𝓕) : StableCat E 𝓕 :=
--   ⟨A.toProp, A.isStable⟩

/-- Local is a functor from Stable to Stable. -/
def Local (P : Measure Ω) (p : StableCat E 𝓕) : StableCat E 𝓕 :=
  ⟨(Locally p.1 𝓕 · P), p.2.isStable_locally⟩

-- def LocalMono (P : Measure Ω) {p q : StableSkel E 𝓕}

noncomputable
def LocalFunctor : StableCat E 𝓕 ⥤ StableCat E 𝓕 where
  obj X := Local P X
  map f X := sorry
  map_id X := sorry
  map_comp := sorry


end ProbabilityTheory
