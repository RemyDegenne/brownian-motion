/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Instances.Discrete
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
lemma jump_zero [T2Space E] : Δ (fun _ : T ↦ (0 : E)) t = 0 := by
  unfold jump
  split_ifs with h
  · simp
  · simp only [zero_sub, neg_eq_zero]
    by_cases h_bot : IsBot t
    · rw [leftLim_eq_of_eq_bot]
      rw [nhdsLT_eq_bot_iff]
      exact Or.inl h_bot
    · have : (𝓝[<] t).NeBot := by
        constructor
        rw [ne_eq, nhdsLT_eq_bot_iff]
        simp [h_bot, h]
      rw [leftLim_eq_of_tendsto]
      exact tendsto_const_nhds

@[simp]
lemma jump_zero' [T2Space E] : Δ (0 : T → E) t = 0 := jump_zero

lemma leftLim_congr' {E : Type*} [TopologicalSpace E] [T2Space E] {f g : T → E}
    (h_ne_bot : 𝓝[<] t ≠ ⊥) (h : f =ᶠ[𝓝[<] t] g) (ht : f t = g t) :
    Function.leftLim f t = Function.leftLim g t := by
  by_cases h_tendsto : ∃ y, Tendsto f (𝓝[<] t) (𝓝 y)
  · obtain ⟨y, hy⟩ := h_tendsto
    have hy' : Tendsto g (𝓝[<] t) (𝓝 y) := by
      refine hy.congr' h
    have : (𝓝[<] t).NeBot := ⟨h_ne_bot⟩
    rw [leftLim_eq_of_tendsto hy, leftLim_eq_of_tendsto hy']
  have hg_tendsto : ¬ ∃ y, Tendsto g (𝓝[<] t) (𝓝 y) := by
    rintro ⟨y, hy⟩
    refine h_tendsto ⟨y, hy.congr' h.symm⟩
  rw [leftLim_eq_of_not_tendsto _ h_tendsto, leftLim_eq_of_not_tendsto _ hg_tendsto, ht]

lemma leftLim_congr {E : Type*} [TopologicalSpace E] [T2Space E] {f g : T → E}
    (h : ∀ s ≤ t, f s = g s) :
    Function.leftLim f t = Function.leftLim g t := by
  by_cases h_bot : 𝓝[<] t = ⊥
  · rw [leftLim_eq_of_eq_bot _ h_bot, leftLim_eq_of_eq_bot _ h_bot]
    exact h t le_rfl
  refine leftLim_congr' h_bot ?_ (h t le_rfl)
  exact eventually_nhdsWithin_of_forall fun s hs ↦ h s (by simp at hs; exact hs.le)

lemma jump_congr {E : Type*} [AddGroup E] [TopologicalSpace E] [T2Space E] {f g : T → E}
    (h : ∀ s ≤ t, f s = g s) :
    Δ f t = Δ g t := by
  unfold jump
  split_ifs with h_covBy
  · rw [h t le_rfl, h _ h_covBy.choose_spec.1.le]
  · rw [h t le_rfl, leftLim_congr h]

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

@[simp]
lemma jump_nat {f : ℕ → E} (n : ℕ) : Δ f n = f n - f (n - 1) := by
  cases n with
  | zero => rw [← Nat.bot_eq_zero, jump_bot]; simp
  | succ n => have : (n : ℕ) ⋖ n + 1 := ⟨by simp, by grind⟩; simp [jump_of_covBy this]

lemma jump_eq_zero_of_tendsto [T2Space E] (h : 𝓝[<] t ≠ ⊥) (h' : Tendsto f (𝓝[<] t) (𝓝 (f t))) :
    Δ f t = 0 := by
  have : (𝓝[<] t).NeBot := ⟨h⟩
  rw [jump_of_nhdsLT_ne_bot h, leftLim_eq_of_tendsto h', sub_self]

lemma ContinuousWithinAt.jump_eq_zero [T2Space E]
    (h' : 𝓝[<] t ≠ ⊥) (h : ContinuousWithinAt f (Set.Iic t) t) :
    Δ f t = 0 := by
  apply jump_eq_zero_of_tendsto h'
  exact h.tendsto.mono_left (nhdsWithin_mono _ Set.Iio_subset_Iic_self)

lemma ContinuousAt.jump_eq_zero [T2Space E] (h' : 𝓝[<] t ≠ ⊥) (h : ContinuousAt f t) : Δ f t = 0 :=
  h.continuousWithinAt.jump_eq_zero h'
