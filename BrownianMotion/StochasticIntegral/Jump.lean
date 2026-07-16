/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Order.LeftRightLim

@[expose] public section

open Filter

open scoped Topology

variable {T E : Type*} [ConditionallyCompleteLinearOrder T] {f : T → E} {t : T}

noncomputable def Function.jump [TopologicalSpace E] [Sub E] (f : T → E) (t : T) : E :=
  f t - Function.leftLim f (sSup (Set.Iio t))

scoped[Function] notation "Δ" => Function.jump

open Function

lemma leftLim_add_jump [AddCommGroup E] [TopologicalSpace E] :
    leftLim f (sSup (Set.Iio t)) + Δ f t = f t := by
  rw [jump, add_sub_assoc', add_sub_cancel_left]

variable [AddGroup E] [TopologicalSpace E] [TopologicalSpace T] [OrderTopology T]

@[simp]
lemma leftLim_bot {T E : Type*} [ConditionallyCompleteLinearOrderBot T] [TopologicalSpace E]
    (f : T → E) :
    leftLim f ⊥ = f ⊥ := by
  letI : TopologicalSpace T := Preorder.topology T
  have : OrderTopology T := ⟨rfl⟩
  simp [leftLim_eq_of_eq_bot]


@[simp]
lemma jump_bot_eq_zero {T : Type*} [ConditionallyCompleteLinearOrderBot T] {f : T → E} :
    Δ f ⊥ = 0 := by
  simp [jump]

omit [TopologicalSpace T] [OrderTopology T] in
lemma sSup_Iio_le_self (h_nonempty : (Set.Iio t).Nonempty) : sSup (Set.Iio t) ≤ t := by
  rw [csSup_le_iff]
  rotate_left
  · exact ⟨t, by simp [mem_upperBounds]; grind⟩
  · exact h_nonempty
  intro b hbt
  grind

lemma sSup_Iio_eq_self_of_nhdsWithin_neBot (h : 𝓝[<] t ≠ ⊥) : sSup (Set.Iio t) = t := by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ (by grind) ?_
  · by_contra! h_empty
    refine h ?_
    rw [nhdsLT_eq_bot_iff]
    left
    intro x
    by_contra! h_lt
    have hx : x ∈ Set.Iio t := by simp [h_lt]
    grind
  · intro w hw
    by_contra! h_le
    refine h ?_
    refine nhdsLT_eq_bot_iff.mpr (.inr ⟨w, hw, fun y hwy hyt ↦ ?_⟩)
    specialize h_le y hyt
    grind

lemma sSup_Iio_eq_self_iff_nhdsWithin_neBot (h_nonempty : (Set.Iio t).Nonempty) :
    sSup (Set.Iio t) = t ↔ 𝓝[<] t ≠ ⊥ := by
  refine ⟨fun h ↦ ?__, fun h ↦ sSup_Iio_eq_self_of_nhdsWithin_neBot h⟩
  by_contra! h_bot
  rw [nhdsLT_eq_bot_iff] at h_bot
  cases h_bot with
  | inl h_bot =>
    obtain ⟨x, hx⟩ := h_nonempty
    specialize h_bot x
    grind
  | inr h =>
    obtain ⟨w, hw, h⟩ := h
    suffices sSup (Set.Iio t) ≤ w by grind
    rw [csSup_le_iff]
    rotate_left
    · exact ⟨t, by simp [mem_upperBounds]; grind⟩
    · exact h_nonempty
    intro b hbt
    grind

lemma jump_eq_zero_of_tendsto [T2Space E] (h : 𝓝[<] t ≠ ⊥) (h' : Tendsto f (𝓝[<] t) (𝓝 (f t))) :
    Δ f t = 0 := by
  have h_sSup_eq : sSup (Set.Iio t) = t := sSup_Iio_eq_self_of_nhdsWithin_neBot h
  rw [jump, h_sSup_eq, leftLim_eq_of_tendsto h h', sub_self]

lemma ContinuousWithinAt.jump_eq_zero [T2Space E]
    (h' : 𝓝[<] t ≠ ⊥) (h : ContinuousWithinAt f (Set.Iic t) t) :
    Δ f t = 0 := by
  apply jump_eq_zero_of_tendsto h'
  exact h.tendsto.mono_left (nhdsWithin_mono _ Set.Iio_subset_Iic_self)

lemma ContinuousAt.jump_eq_zero [T2Space E] (h' : 𝓝[<] t ≠ ⊥) (h : ContinuousAt f t) : Δ f t = 0 :=
  h.continuousWithinAt.jump_eq_zero h'
