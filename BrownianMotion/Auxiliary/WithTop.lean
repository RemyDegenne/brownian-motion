module

public import Mathlib.Topology.Order.WithTop

@[expose] public section

open Set
open scoped Topology

namespace Filter

variable {ι : Type*}

theorem Tendsto.min_atTop_atTop {α β : Type*}
    [Nonempty β] [LinearOrder β] [LinearOrder α]
    {f g : β → α} (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    Tendsto (fun x ↦ f x ⊓ g x) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop] at *
  exact fun a ↦ let ⟨b₁, hb₁⟩ := hf a; let ⟨b₂, hb₂⟩ := hg a
    ⟨max b₁ b₂, fun B hB ↦ le_min (hb₁ _ (max_le_iff.1 hB).1) (hb₂ _ (max_le_iff.1 hB).2)⟩

end Filter
