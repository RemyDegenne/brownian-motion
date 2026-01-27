/-
Copyright (c) 2025 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu
-/

import Mathlib.Probability.Process.Adapted

namespace MeasureTheory

section Comp

variable {ι ι' Ω : Type*} [Preorder ι] [Preorder ι'] {mΩ : MeasurableSpace Ω}

/-- Given a filtration on `ι` and a monotone mapping `ι' → ι`, construct a filtration on `ι'`.
This is most commonly used to restrict a filtration to a subset of the index set. -/
@[simps]
def Filtration.indexComap (𝓕 : Filtration ι mΩ) {f : ι' → ι} (hf : Monotone f) :
    Filtration ι' mΩ where
  seq k := 𝓕 (f k)
  mono' := 𝓕.mono'.comp hf
  le' i := 𝓕.le (f i)

variable {𝓕 : Filtration ι mΩ} {f : ι' → ι} (hf : Monotone f)

variable {E : Type*} [TopologicalSpace E] {X : ι → Ω → E}

theorem Adapted.indexComap (hX : Adapted 𝓕 X) (hf : Monotone f) :
    Adapted (𝓕.indexComap hf) (X ∘ f) := fun i ↦ hX (f i)

end Comp

end MeasureTheory
