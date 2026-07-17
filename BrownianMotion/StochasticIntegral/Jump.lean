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

open Classical in
/-- The jump of a function at a point `t`, defined as the difference between the value of
the function at that point and its left limit at the least upper bound of the set of points
strictly smaller.
If the point is not isolated from the left, then it is `f t - leftLim f t`.
If the point is isolated from the left, and the l.u.b. or the strictly smaller points is `s < t`,
then the jump is `f t - f s`. It there is no such point `s` because `t` is a bottom element, then
the jump is `0` (since `f ⊥ - leftLim f ⊥ = 0`). -/
noncomputable def Function.jump [TopologicalSpace E] [AddGroup E]
    (f : T → E) (t : T) : E :=
  if h : ∃ s, s ⋖ t then f t - f h.choose else f t - Function.leftLim f t

@[inherit_doc Function.jump]
scoped[Function] notation "Δ" => Function.jump

open Function

lemma jump_of_covBy [AddGroup E] [TopologicalSpace E] {s : T} (h : s ⋖ t) : Δ f t = f t - f s := by
  have h_exists : ∃ s, s ⋖ t := ⟨s, h⟩
  rw [jump, dif_pos h_exists]
  congr
  exact CovBy.unique_left h_exists.choose_spec h

@[simp]
lemma leftLim_bot {T E : Type*} [ConditionallyCompleteLinearOrderBot T] [TopologicalSpace E]
    (f : T → E) :
    leftLim f ⊥ = f ⊥ := by
  let : TopologicalSpace T := Preorder.topology T
  have : OrderTopology T := ⟨rfl⟩
  simp [leftLim_eq_of_eq_bot]

lemma jump_of_not_covBy [AddGroup E] [TopologicalSpace E] (h : ∀ s, ¬ s ⋖ t) :
    Δ f t = f t - Function.leftLim f t := by
  rw [jump, dif_neg (by simp [h])]

lemma leftLim_add_jump_of_not_covBy {E : Type*} [AddCommGroup E] [TopologicalSpace E] {f : T → E}
    (h : ∀ s, ¬ s ⋖ t) :
    leftLim f t + Δ f t = f t := by
  rw [jump_of_not_covBy h, add_sub_assoc', add_sub_cancel_left]

variable [TopologicalSpace T] [OrderTopology T] [AddGroup E] [TopologicalSpace E]

@[simp]
lemma jump_of_isBot (h : IsBot t) :
    Δ f t = 0 := by
  unfold jump
  have : ¬∃ s, s ⋖ t := by
    rintro ⟨s, hs1, hs2⟩
    specialize h s
    grind
  rw [dif_neg this, leftLim_eq_of_eq_bot, sub_self]
  exact nhdsLT_eq_bot_iff.mpr (Or.inl h)

@[simp]
lemma jump_bot {T : Type*} [ConditionallyCompleteLinearOrderBot T] [TopologicalSpace T]
    [OrderTopology T] {f : T → E} :
    Δ f ⊥ = 0 := by simp

lemma jump_of_nhdsLT_ne_bot (h : 𝓝[<] t ≠ ⊥) :
    Δ f t = f t - Function.leftLim f t := by
  simp only [ne_eq, nhdsLT_eq_bot_iff, not_or, not_exists] at h
  simp [jump, h]

lemma jump_of_nhdsLT_neBot [h : (𝓝[<] t).NeBot] :
    Δ f t = f t - Function.leftLim f t := by
  rw [jump_of_nhdsLT_ne_bot h.ne]

lemma leftLim_add_jump_of_ne_bot {E : Type*} [AddCommGroup E] [TopologicalSpace E] {f : T → E}
    (h : 𝓝[<] t ≠ ⊥) :
    leftLim f t + Δ f t = f t := by
  rw [jump_of_nhdsLT_ne_bot h, add_sub_assoc', add_sub_cancel_left]

lemma jump_eq_zero_of_tendsto [T2Space E] (h : 𝓝[<] t ≠ ⊥) (h' : Tendsto f (𝓝[<] t) (𝓝 (f t))) :
    Δ f t = 0 := by
  rw [jump_of_nhdsLT_ne_bot h, leftLim_eq_of_tendsto h h', sub_self]

lemma ContinuousWithinAt.jump_eq_zero [T2Space E]
    (h' : 𝓝[<] t ≠ ⊥) (h : ContinuousWithinAt f (Set.Iic t) t) :
    Δ f t = 0 := by
  apply jump_eq_zero_of_tendsto h'
  exact h.tendsto.mono_left (nhdsWithin_mono _ Set.Iio_subset_Iic_self)

lemma ContinuousAt.jump_eq_zero [T2Space E] (h' : 𝓝[<] t ≠ ⊥) (h : ContinuousAt f t) : Δ f t = 0 :=
  h.continuousWithinAt.jump_eq_zero h'
