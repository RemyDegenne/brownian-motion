import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.WithTop

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

lemma _root_.WithTop.tendsto_atTop_nhds_top_iff {α : Type*}
    [Nonempty ι] [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    [Nonempty α] [inst : Preorder α] [IsDirected α fun x1 x2 ↦ x1 ≤ x2] (x : α → WithTop ι) :
    Tendsto x atTop (𝓝 ⊤) ↔ ∀ (i : ι), ∃ N, ∀ n ≥ N, i < x n := by
  rw [WithTop.tendsto_nhds_top_iff]
  simp only [eventually_atTop, ge_iff_le]

lemma Tendsto.tendsto_withTop_atTop_nhds_top
    [Nonempty ι] [LinearOrder ι] [NoMaxOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    {a : ℕ → ι} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n ↦ (a n : WithTop ι)) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_atTop_nhds_top_iff]
  rw [tendsto_atTop_atTop] at ha
  norm_cast
  intro i
  obtain ⟨i', hi'⟩ := NoMaxOrder.exists_gt i
  obtain ⟨j, hj⟩ := ha i'
  exact ⟨j, fun n hn ↦ lt_of_lt_of_le hi' <| hj _ hn⟩

end Filter
