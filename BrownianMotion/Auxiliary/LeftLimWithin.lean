/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Separation.Regular

/-!
# Left and right limits within a set
-/

@[expose] public section


open Set Filter

open Topology

lemma nhdsWithin_inf_principal {E : Type*} [TopologicalSpace E] (s t : Set E) (x : E) :
    𝓝[s] x ⊓ 𝓟 t = 𝓝[s ∩ t] x := by
  rw [nhdsWithin, nhdsWithin, inf_assoc, inf_principal, Set.inter_comm]

section

variable {α β : Type*} [LinearOrder α] [TopologicalSpace β]

/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the left of `f` at `a`, denoted with `leftLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its left or the function has no left
limit, we use `f a` instead to guarantee a good behavior in most cases. -/
noncomputable def Function.leftLimWithin (f : α → β) (s : Set α) (a : α) : β := by
  classical
  haveI : Nonempty β := ⟨f a⟩
  letI : TopologicalSpace α := Preorder.topology α
  exact if 𝓝[Set.Iio a ∩ s] a = ⊥ ∨ ¬∃ y, Tendsto f (𝓝[Set.Iio a ∩ s] a) (𝓝 y) then f a else
    limUnder (𝓝[Set.Iio a ∩ s] a) f

/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the right of `f` at `a`, denoted with `rightLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its right or the function has no right
limit, we use `f a` instead to guarantee a good behavior in most cases. -/
noncomputable def Function.rightLimWithin (f : α → β) (s : Set α) (a : α) : β :=
  @Function.leftLimWithin αᵒᵈ β _ _ f s a

open Function

/-! ### The within-neighbourhood filter is `NeBot` under a density hypothesis -/

/-- If `s` is dense and `𝓝[<] a` is not bot, then `a` is a left-accumulation point of `s`. -/
theorem nhdsWithin_Iio_inter_neBot_of_nhdsLT_neBot [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hs : Dense s) (a : α) [(𝓝[<] a).NeBot] :
    (𝓝[Iio a ∩ s] a).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff]
  intro U hU haU
  have hne : (U ∩ Iio a).Nonempty :=
    mem_closure_iff.1 (mem_closure_iff_nhdsWithin_neBot.2 inferInstance) U hU haU
  obtain ⟨x, hxs, hx⟩ := hs.exists_mem_open (hU.inter isOpen_Iio) hne
  exact ⟨x, hx.1, hx.2, hxs⟩

/-- If `s` is dense and `a` is not a minimum, then `a` is a left-accumulation point of `s`. -/
theorem nhdsWithin_Iio_inter_neBot [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [NoMinOrder α] {s : Set α} (hs : Dense s) (a : α) : (𝓝[Iio a ∩ s] a).NeBot :=
  nhdsWithin_Iio_inter_neBot_of_nhdsLT_neBot hs a

/-- If `s` is dense and `𝓝[>] a` is not bot, then `a` is a right-accumulation point of `s`. -/
theorem nhdsWithin_Ioi_inter_neBot_of_nhdsGT_neBot [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hs : Dense s) (a : α) [(𝓝[>] a).NeBot] :
    (𝓝[Ioi a ∩ s] a).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff]
  intro U hU haU
  have hne : (U ∩ Ioi a).Nonempty :=
    mem_closure_iff.1 (mem_closure_iff_nhdsWithin_neBot.2 inferInstance) U hU haU
  obtain ⟨x, hxs, hx⟩ := hs.exists_mem_open (hU.inter isOpen_Ioi) hne
  exact ⟨x, hx.1, hx.2, hxs⟩

/-- If `s` is dense and `a` is not a maximum, then `a` is a right-accumulation point of `s`. -/
theorem nhdsWithin_Ioi_inter_neBot [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [NoMaxOrder α] {s : Set α} (hs : Dense s) (a : α) : (𝓝[Ioi a ∩ s] a).NeBot :=
  nhdsWithin_Ioi_inter_neBot_of_nhdsGT_neBot hs a

/-! ### Basic characterisations of the within left/right limit -/

theorem leftLimWithin_eq_of_tendsto [hα : TopologicalSpace α] [h'α : OrderTopology α] [T2Space β]
    {f : α → β} {s : Set α} {a : α} {y : β} [h : (𝓝[Iio a ∩ s] a).NeBot]
    (h' : Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 y)) :
    leftLimWithin f s a = y := by
  have h'' : ∃ y, Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 y) := ⟨y, h'⟩
  rw [h'α.topology_eq_generate_intervals] at h h' h''
  simp only [leftLimWithin, neBot_iff.mp h, h'', not_true, or_self_iff, if_false]
  exact lim_eq h'

theorem rightLimWithin_eq_of_tendsto [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {s : Set α} {a : α} {y : β} [h : (𝓝[Ioi a ∩ s] a).NeBot]
    (h' : Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 y)) :
    rightLimWithin f s a = y :=
  leftLimWithin_eq_of_tendsto (α := αᵒᵈ) (h := h) h'

theorem leftLimWithin_eq_of_eq_bot [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β)
    {s : Set α} {a : α} (h : 𝓝[Iio a ∩ s] a = ⊥) : leftLimWithin f s a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLimWithin, h]

theorem rightLimWithin_eq_of_eq_bot [TopologicalSpace α] [OrderTopology α] (f : α → β)
    {s : Set α} {a : α} (h : 𝓝[Ioi a ∩ s] a = ⊥) : rightLimWithin f s a = f a :=
  leftLimWithin_eq_of_eq_bot (α := αᵒᵈ) f h

theorem leftLimWithin_eq_of_not_tendsto
    [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {s : Set α} {a : α}
    (h : ¬ ∃ y, Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 y)) : leftLimWithin f s a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLimWithin, h]

theorem rightLimWithin_eq_of_not_tendsto
    [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {s : Set α} {a : α}
    (h : ¬ ∃ y, Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 y)) : rightLimWithin f s a = f a :=
  leftLimWithin_eq_of_not_tendsto (α := αᵒᵈ) f h

theorem leftLimWithin_eq_of_isBot {f : α → β} {s : Set α} {a : α} (ha : IsBot a) :
    leftLimWithin f s a = f a := by
  let A : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  apply leftLimWithin_eq_of_eq_bot
  have : Iio a = ∅ := by simp; grind [IsBot, IsMin]
  simp [this]

theorem rightLimWithin_eq_of_isTop {f : α → β} {s : Set α} {a : α} (ha : IsTop a) :
    rightLimWithin f s a = f a :=
  leftLimWithin_eq_of_isBot (α := αᵒᵈ) ha

theorem ContinuousWithinAt.leftLimWithin_eq [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {s : Set α} {a : α} (hf : ContinuousWithinAt f (Iic a ∩ s) a) :
    leftLimWithin f s a = f a := by
  rcases eq_or_neBot (𝓝[Iio a ∩ s] a) with h' | h'
  · simp [leftLimWithin_eq_of_eq_bot f h']
  apply leftLimWithin_eq_of_tendsto
  exact hf.tendsto.mono_left (nhdsWithin_mono _ (inter_subset_inter_left _ Iio_subset_Iic_self))

theorem ContinuousWithinAt.rightLimWithin_eq [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {s : Set α} {a : α} (hf : ContinuousWithinAt f (Ici a ∩ s) a) :
    rightLimWithin f s a = f a :=
  ContinuousWithinAt.leftLimWithin_eq (α := αᵒᵈ) hf

theorem tendsto_leftLimWithin_of_tendsto [TopologicalSpace α] [h'α : OrderTopology α]
    {f : α → β} {s : Set α} {a : α} (h : ∃ y, Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 y)) :
    Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 (leftLimWithin f s a)) := by
  rcases eq_or_neBot (𝓝[Iio a ∩ s] a) with h' | h'
  · simp [h']
  rw [h'α.topology_eq_generate_intervals] at h h' ⊢
  simp only [leftLimWithin, neBot_iff.1 h', h, not_true_eq_false, or_self, ↓reduceIte]
  exact tendsto_nhds_limUnder h

theorem tendsto_rightLimWithin_of_tendsto [TopologicalSpace α] [OrderTopology α]
    {f : α → β} {s : Set α} {a : α} (h : ∃ y, Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 y)) :
    Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 (rightLimWithin f s a)) :=
  tendsto_leftLimWithin_of_tendsto (α := αᵒᵈ) h

/-- The within left limit is a cluster point of `f` along the closed left within-neighbourhood,
provided `a ∈ s`. -/
theorem mapClusterPt_leftLimWithin [TopologicalSpace α] [OrderTopology α]
    (f : α → β) {s : Set α} {a : α} (ha : a ∈ s) :
    MapClusterPt (leftLimWithin f s a) (𝓝[Iic a ∩ s] a) f := by
  have A : (𝓝 (f a) ⊓ map f (𝓝[Iic a ∩ s] a)).NeBot := by
    refine inf_neBot_iff.mpr (fun t ht t' ht' ↦ ?_)
    refine ⟨f a, mem_of_mem_nhds ht, ?_⟩
    simp only [mem_map] at ht'
    apply mem_of_mem_nhdsWithin (show a ∈ Iic a ∩ s from ⟨le_refl a, ha⟩) ht'
  rcases eq_or_neBot (𝓝[Iio a ∩ s] a) with h' | h'
  · simp only [MapClusterPt, ClusterPt, h', leftLimWithin_eq_of_eq_bot, A]
  by_cases! H : ¬ ∃ y, Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 y)
  · simp [MapClusterPt, ClusterPt, H, leftLimWithin_eq_of_not_tendsto, A]
  have : MapClusterPt (leftLimWithin f s a) (𝓝[Iio a ∩ s] a) f :=
    (tendsto_leftLimWithin_of_tendsto H).mapClusterPt
  exact MapClusterPt.mono this (nhdsWithin_mono _ (inter_subset_inter_left _ Iio_subset_Iic_self))

theorem mapClusterPt_rightLimWithin [TopologicalSpace α] [OrderTopology α]
    (f : α → β) {s : Set α} {a : α} (ha : a ∈ s) :
    MapClusterPt (rightLimWithin f s a) (𝓝[Ici a ∩ s] a) f :=
  mapClusterPt_leftLimWithin (α := αᵒᵈ) f ha

/-! ### Regularisation: the within left/right limit is one-sided continuous within `s`

These mirror the original `continuousWithinAt_leftLim_Iic` etc.: they take only the single-point
hypothesis that `f` admits a within left (resp. right) limit at `a`, and split into cases according
to whether the within-neighbourhood at each nearby point is `⊥`, has no limit, or has a limit. The
conclusions are stated *within* `s` (`Iic a ∩ s` in place of `Iic a`); restricting to `s` is what
lets the degenerate cases go through, so no density hypothesis is needed. -/

theorem continuousWithinAt_leftLimWithin_Iic [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {s : Set α} {a : α}
    (h : Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 (leftLimWithin f s a))) :
    ContinuousWithinAt (leftLimWithin f s) (Iic a ∩ s) a := by
  have hsub : Iic a ∩ s ⊆ (Iio a ∩ s) ∪ {a} := by
    rintro x ⟨hx1, hx2⟩
    rcases lt_or_eq_of_le hx1 with hlt | heq
    · exact Or.inl ⟨hlt, hx2⟩
    · exact Or.inr heq
  rw [ContinuousWithinAt]
  refine Tendsto.mono_left ?_ (nhdsWithin_mono a hsub)
  rw [nhdsWithin_union, nhdsWithin_singleton, tendsto_sup]
  refine ⟨?_, tendsto_pure_nhds _ _⟩
  apply (closed_nhds_basis (leftLimWithin f s a)).tendsto_right_iff.2
  rintro V ⟨V_mem, V_closed⟩
  rcases eq_or_neBot (𝓝[Iio a ∩ s] a) with h' | h'
  · simp [h']
  obtain ⟨b, hb⟩ : (Iio a).Nonempty :=
    (Filter.nonempty_of_mem (show Iio a ∩ s ∈ 𝓝[Iio a ∩ s] a from self_mem_nhdsWithin)).mono
      inter_subset_left
  have hev : ∀ᶠ x in 𝓝[<] a ⊓ 𝓟 s, f x ∈ V := by
    rw [nhdsWithin_inf_principal]; exact h.eventually V_mem
  obtain ⟨u, hua, hu⟩ := (nhdsLT_basis_of_exists_lt ⟨b, hb⟩).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  filter_upwards [nhdsWithin_mono a inter_subset_left (Ioo_mem_nhdsLT hua), self_mem_nhdsWithin]
    with c hc hcs
  rcases eq_or_neBot (𝓝[Iio c ∩ s] c) with h'c | h'c
  · simpa [h'c, leftLimWithin_eq_of_eq_bot] using hu hc hcs.2
  by_cases! h''c : ¬ ∃ y, Tendsto f (𝓝[Iio c ∩ s] c) (𝓝 y)
  · simpa [leftLimWithin_eq_of_not_tendsto _ h''c] using hu hc hcs.2
  apply V_closed.mem_of_tendsto (tendsto_leftLimWithin_of_tendsto h''c)
  rw [← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsLT hc.1] with d hd hds
  exact hu ⟨hd.1, hd.2.trans hc.2⟩ hds

theorem continuousWithinAt_rightLimWithin_Ici [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {s : Set α} {a : α}
    (h : Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 (rightLimWithin f s a))) :
    ContinuousWithinAt (rightLimWithin f s) (Ici a ∩ s) a :=
  continuousWithinAt_leftLimWithin_Iic (α := αᵒᵈ) h

/-- Dense version of `continuousWithinAt_leftLimWithin_Iic` with the stronger conclusion that the
regularisation is continuous along the *full* left neighbourhood `Iic a`. This needs `s` dense (so
that the within-neighbourhood is `NeBot`), the single-point hypothesis `h` that `f` has a within
left limit at `a`, and that `f` has a within left limit at every point eventually to the left of
`a`. -/
theorem continuousWithinAt_leftLimWithin_Iic_of_dense [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMinOrder α] [T3Space β] {f : α → β} {s : Set α} {a : α} (hs : Dense s)
    (h : Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 (leftLimWithin f s a)))
    (hlim : ∀ᶠ c in 𝓝[<] a, Tendsto f (𝓝[Iio c ∩ s] c) (𝓝 (leftLimWithin f s c))) :
    ContinuousWithinAt (leftLimWithin f s) (Iic a) a := by
  have hsplit : 𝓝[≤] a = 𝓝[<] a ⊔ pure a := by
    rw [← Iio_union_Icc_eq_Iic le_rfl, nhdsWithin_union]
    simp
  rw [ContinuousWithinAt, hsplit, tendsto_sup]
  simp only [tendsto_pure_nhds, and_true]
  apply (closed_nhds_basis (leftLimWithin f s a)).tendsto_right_iff.2
  rintro V ⟨V_mem, V_closed⟩
  have hev : ∀ᶠ x in 𝓝[<] a ⊓ 𝓟 s, f x ∈ V := by
    rw [nhdsWithin_inf_principal]; exact h.eventually V_mem
  obtain ⟨u, hua, hu⟩ := (nhdsLT_basis_of_exists_lt (exists_lt a)).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  filter_upwards [Ioo_mem_nhdsLT hua, hlim] with c hc hlimc
  have hne := nhdsWithin_Iio_inter_neBot hs c
  refine V_closed.mem_of_tendsto hlimc ?_
  rw [← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsLT hc.1] with x hx hxs
  exact hu ⟨hx.1, hx.2.trans hc.2⟩ hxs

/-- Dense version of `continuousWithinAt_rightLimWithin_Ici` with
the stronger conclusion `Ici a`. -/
theorem continuousWithinAt_rightLimWithin_Ici_of_dense [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMaxOrder α] [T3Space β] {f : α → β} {s : Set α} {a : α} (hs : Dense s)
    (h : Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 (rightLimWithin f s a)))
    (hlim : ∀ᶠ c in 𝓝[>] a, Tendsto f (𝓝[Ioi c ∩ s] c) (𝓝 (rightLimWithin f s c))) :
    ContinuousWithinAt (rightLimWithin f s) (Ici a) a :=
  continuousWithinAt_leftLimWithin_Iic_of_dense (α := αᵒᵈ) hs h hlim

theorem leftLimWithin_leftLimWithin [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {s : Set α} {a : α}
    (h : Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 (leftLimWithin f s a))) :
    leftLimWithin (leftLimWithin f s) s a = leftLimWithin f s a :=
  (continuousWithinAt_leftLimWithin_Iic h).leftLimWithin_eq

theorem rightLimWithin_rightLimWithin [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {s : Set α} {a : α}
    (h : Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 (rightLimWithin f s a))) :
    rightLimWithin (rightLimWithin f s) s a = rightLimWithin f s a :=
  leftLimWithin_leftLimWithin (α := αᵒᵈ) h

theorem leftLimWithin_rightLimWithin [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {s : Set α} {a : α} [h' : (𝓝[Iio a ∩ s] a).NeBot]
    (h : Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 (leftLimWithin f s a))) :
    leftLimWithin (rightLimWithin f s) s a = leftLimWithin f s a := by
  apply leftLimWithin_eq_of_tendsto
  apply (closed_nhds_basis (leftLimWithin f s a)).tendsto_right_iff.2
  rintro V ⟨V_mem, V_closed⟩
  obtain ⟨b, hb⟩ : (Iio a).Nonempty :=
    (Filter.nonempty_of_mem (show Iio a ∩ s ∈ 𝓝[Iio a ∩ s] a from self_mem_nhdsWithin)).mono
      inter_subset_left
  have hev : ∀ᶠ x in 𝓝[<] a ⊓ 𝓟 s, f x ∈ V := by
    rw [nhdsWithin_inf_principal]; exact h.eventually V_mem
  obtain ⟨u, hua, hu⟩ := (nhdsLT_basis_of_exists_lt ⟨b, hb⟩).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  filter_upwards [nhdsWithin_mono a inter_subset_left (Ioo_mem_nhdsLT hua), self_mem_nhdsWithin]
    with c hc hcs
  rcases eq_or_neBot (𝓝[Ioi c ∩ s] c) with h'c | h'c
  · simpa [h'c, rightLimWithin_eq_of_eq_bot] using hu hc hcs.2
  by_cases! h''c : ¬ ∃ y, Tendsto f (𝓝[Ioi c ∩ s] c) (𝓝 y)
  · simpa [rightLimWithin_eq_of_not_tendsto _ h''c] using hu hc hcs.2
  apply V_closed.mem_of_tendsto (tendsto_rightLimWithin_of_tendsto h''c)
  rw [← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT hc.2] with d hd hds
  exact hu ⟨hc.1.trans hd.1, hd.2⟩ hds

theorem rightLimWithin_leftLimWithin [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {s : Set α} {a : α} [h' : (𝓝[Ioi a ∩ s] a).NeBot]
    (h : Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 (rightLimWithin f s a))) :
    rightLimWithin (leftLimWithin f s) s a = rightLimWithin f s a :=
  leftLimWithin_rightLimWithin (α := αᵒᵈ) (h' := h') h

/-! ### Behaviour at infinity -/

theorem tendsto_atTop_of_mapClusterPt
    [TopologicalSpace α] [OrderTopology α] [T3Space β] [NoTopOrder α] {f g : α → β} {b : β}
    (h : Tendsto f atTop (𝓝 b)) (h' : ∀ᶠ x in atTop, MapClusterPt (g x) (𝓝 x) f) :
    Tendsto g atTop (𝓝 b) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [filter_eq_bot_of_isEmpty atTop]
  apply (closed_nhds_basis b).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, hu⟩ : ∃ a, ∀ (b : α), a ≤ b → MapClusterPt (g b) (𝓝 b) f ∧ f b ∈ s := by
    simpa [eventually_atTop] using h'.and (h s_mem)
  filter_upwards [Ioi_mem_atTop u] with a (ha : u < a)
  apply s_closed.mem_of_mapClusterPt (hu a ha.le).1
  filter_upwards [Ici_mem_nhds ha] with y hy using (hu y hy).2

theorem tendsto_atBot_of_mapClusterPt
    [TopologicalSpace α] [OrderTopology α] [T3Space β] [NoBotOrder α] {f g : α → β} {b : β}
    (h : Tendsto f atBot (𝓝 b)) (h' : ∀ᶠ x in atBot, MapClusterPt (g x) (𝓝 x) f) :
    Tendsto g atBot (𝓝 b) :=
  tendsto_atTop_of_mapClusterPt (α := αᵒᵈ) h h'

theorem tendsto_leftLimWithin_atTop_of_tendsto
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [NoMinOrder α] [NoTopOrder α]
    [T3Space β] {f : α → β} {s : Set α} {b : β} (hs : Dense s)
    (hlim : ∀ c, Tendsto f (𝓝[Iio c ∩ s] c) (𝓝 (leftLimWithin f s c)))
    (h : Tendsto f atTop (𝓝 b)) :
    Tendsto (leftLimWithin f s) atTop (𝓝 b) := by
  apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x ↦ ?_))
  have := nhdsWithin_Iio_inter_neBot hs x
  exact ((hlim x).mapClusterPt).mono nhdsWithin_le_nhds

theorem tendsto_rightLimWithin_atTop_of_tendsto [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMaxOrder α] [T3Space β] {f : α → β} {s : Set α} {b : β} (hs : Dense s)
    (hlim : ∀ c, Tendsto f (𝓝[Ioi c ∩ s] c) (𝓝 (rightLimWithin f s c)))
    (h : Tendsto f atTop (𝓝 b)) :
    Tendsto (rightLimWithin f s) atTop (𝓝 b) := by
  cases topOrderOrNoTopOrder α
  · simp only [OrderTop.atTop_eq α] at h ⊢
    have : rightLimWithin f s ⊤ = f ⊤ := rightLimWithin_eq_of_isTop isTop_top
    rw [tendsto_nhds_unique h (tendsto_pure_nhds f ⊤), ← this]
    apply tendsto_pure_nhds
  · apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x ↦ ?_))
    have := nhdsWithin_Ioi_inter_neBot hs x
    exact ((hlim x).mapClusterPt).mono nhdsWithin_le_nhds

theorem tendsto_rightLimWithin_atBot_of_tendsto
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [NoMaxOrder α] [NoBotOrder α]
    [T3Space β] {f : α → β} {s : Set α} {b : β} (hs : Dense s)
    (hlim : ∀ c, Tendsto f (𝓝[Ioi c ∩ s] c) (𝓝 (rightLimWithin f s c)))
    (h : Tendsto f atBot (𝓝 b)) :
    Tendsto (rightLimWithin f s) atBot (𝓝 b) :=
  tendsto_leftLimWithin_atTop_of_tendsto (α := αᵒᵈ) hs hlim h

theorem tendsto_leftLimWithin_atBot_of_tendsto [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMinOrder α] [T3Space β] {f : α → β} {s : Set α} {b : β} (hs : Dense s)
    (hlim : ∀ c, Tendsto f (𝓝[Iio c ∩ s] c) (𝓝 (leftLimWithin f s c)))
    (h : Tendsto f atBot (𝓝 b)) :
    Tendsto (leftLimWithin f s) atBot (𝓝 b) :=
  tendsto_rightLimWithin_atTop_of_tendsto (α := αᵒᵈ) hs hlim h

end

open Function

namespace Monotone

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Monotone f) {s : Set α} {x y : α}
include hf

/-- For a monotone function, the within left limit is the supremum of the values to the left.
Note that the supremum is over the whole `Iio x`, not just `Iio x ∩ s`: any subset of `Iio x`
accumulating at `x` yields the same limit. -/
theorem leftLimWithin_eq_sSup [TopologicalSpace α] [OrderTopology α]
    [(𝓝[Iio x ∩ s] x).NeBot] : leftLimWithin f s x = sSup (f '' Iio x) :=
  leftLimWithin_eq_of_tendsto
    ((hf.tendsto_nhdsLT x).mono_left (nhdsWithin_mono x inter_subset_left))

theorem rightLimWithin_eq_sInf [TopologicalSpace α] [OrderTopology α]
    [(𝓝[Ioi x ∩ s] x).NeBot] : rightLimWithin f s x = sInf (f '' Ioi x) :=
  rightLimWithin_eq_of_tendsto
    ((hf.tendsto_nhdsGT x).mono_left (nhdsWithin_mono x inter_subset_left))

theorem leftLimWithin_le (h : x ≤ y) : leftLimWithin f s x ≤ f y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[Iio x ∩ s] x) with h' | h'
  · simpa [leftLimWithin, h'] using hf h
  rw [leftLimWithin_eq_sSup hf]
  refine csSup_le ?_ ?_
  · simp only [image_nonempty]
    exact ((forall_mem_nonempty_iff_neBot.2 h') _ self_mem_nhdsWithin).mono inter_subset_left
  · simp only [mem_image, mem_Iio, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro z hz
    exact hf (hz.le.trans h)

theorem le_leftLimWithin (h : x < y) : f x ≤ leftLimWithin f s y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[Iio y ∩ s] y) with h' | h'
  · rw [leftLimWithin_eq_of_eq_bot _ h']
    exact hf h.le
  rw [leftLimWithin_eq_sSup hf]
  refine le_csSup ⟨f y, ?_⟩ (mem_image_of_mem _ h)
  simp only [upperBounds, mem_image, mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro z hz
  exact hf hz.le

@[gcongr, mono]
protected theorem leftLimWithin : Monotone (leftLimWithin f s) := by
  intro x y h
  rcases eq_or_lt_of_le h with (rfl | hxy)
  · exact le_rfl
  · exact (hf.leftLimWithin_le le_rfl).trans (hf.le_leftLimWithin hxy)

theorem le_rightLimWithin (h : x ≤ y) : f x ≤ rightLimWithin f s y :=
  hf.dual.leftLimWithin_le h

theorem rightLimWithin_le (h : x < y) : rightLimWithin f s x ≤ f y :=
  hf.dual.le_leftLimWithin h

@[gcongr, mono]
protected theorem rightLimWithin : Monotone (rightLimWithin f s) :=
  fun _ _ h => hf.dual.leftLimWithin h

theorem leftLimWithin_le_rightLimWithin (h : x ≤ y) :
    leftLimWithin f s x ≤ rightLimWithin f s y :=
  (hf.leftLimWithin_le le_rfl).trans (hf.le_rightLimWithin h)

theorem rightLimWithin_le_leftLimWithin (h : x < y) :
    rightLimWithin f s x ≤ leftLimWithin f s y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[Iio y ∩ s] y) with (h' | h')
  · simpa [leftLimWithin, h'] using rightLimWithin_le hf h
  have h'' : (𝓝[<] y).NeBot := h'.mono (nhdsWithin_mono y inter_subset_left)
  obtain ⟨a, ⟨xa, ay⟩⟩ : (Ioo x y).Nonempty := nonempty_of_mem (Ioo_mem_nhdsLT h)
  calc
    rightLimWithin f s x ≤ f a := hf.rightLimWithin_le xa
    _ ≤ leftLimWithin f s y := hf.le_leftLimWithin ay

variable [TopologicalSpace α] [OrderTopology α]

theorem tendsto_leftLimWithin (x : α) :
    Tendsto f (𝓝[Iio x ∩ s] x) (𝓝 (leftLimWithin f s x)) :=
  tendsto_leftLimWithin_of_tendsto
    ⟨_, (hf.tendsto_nhdsLT x).mono_left (nhdsWithin_mono x inter_subset_left)⟩

theorem tendsto_leftLimWithin_within (x : α) :
    Tendsto f (𝓝[Iio x ∩ s] x) (𝓝[≤] leftLimWithin f s x) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f (hf.tendsto_leftLimWithin x)
  filter_upwards [self_mem_nhdsWithin] with y hy using hf.le_leftLimWithin hy.1

theorem tendsto_rightLimWithin (x : α) :
    Tendsto f (𝓝[Ioi x ∩ s] x) (𝓝 (rightLimWithin f s x)) :=
  hf.dual.tendsto_leftLimWithin x

theorem tendsto_rightLimWithin_within (x : α) :
    Tendsto f (𝓝[Ioi x ∩ s] x) (𝓝[≥] rightLimWithin f s x) :=
  hf.dual.tendsto_leftLimWithin_within x

/-- A monotone function is continuous to the left within `s` at `x` if and only if its within left
limit coincides with the value of the function. -/
theorem continuousWithinAt_Iio_iff_leftLimWithin_eq :
    ContinuousWithinAt f (Iio x ∩ s) x ↔ leftLimWithin f s x = f x := by
  rcases eq_or_neBot (𝓝[Iio x ∩ s] x) with h' | h'
  · simp [leftLimWithin_eq_of_eq_bot f h', ContinuousWithinAt, h']
  refine ⟨fun h => tendsto_nhds_unique (hf.tendsto_leftLimWithin x) h.tendsto, fun h => ?_⟩
  have := hf.tendsto_leftLimWithin (s := s) x
  rwa [h] at this

/-- A monotone function is continuous to the right within `s` at `x` if and only if its within
right limit coincides with the value of the function. -/
theorem continuousWithinAt_Ioi_iff_rightLimWithin_eq :
    ContinuousWithinAt f (Ioi x ∩ s) x ↔ rightLimWithin f s x = f x :=
  hf.dual.continuousWithinAt_Iio_iff_leftLimWithin_eq

/-- A monotone function is continuous within `s` at `x` if and only if its within left and right
limits coincide. This is the within-set analogue of `continuousAt_iff_leftLim_eq_rightLim`, using
`ContinuousWithinAt f s x` in place of the full `ContinuousAt f x`. -/
theorem continuousWithinAt_iff_leftLimWithin_eq_rightLimWithin :
    ContinuousWithinAt f s x ↔ leftLimWithin f s x = rightLimWithin f s x := by
  have hdecomp : ContinuousWithinAt f s x ↔
      leftLimWithin f s x = f x ∧ rightLimWithin f s x = f x := by
    rw [← hf.continuousWithinAt_Iio_iff_leftLimWithin_eq,
      ← hf.continuousWithinAt_Ioi_iff_rightLimWithin_eq]
    refine ⟨fun h => ⟨h.mono inter_subset_right, h.mono inter_subset_right⟩, fun ⟨hL, hR⟩ => ?_⟩
    refine ((hL.union hR).union continuousWithinAt_singleton).mono ?_
    intro y hy
    rcases lt_trichotomy y x with hlt | heq | hgt
    · exact Or.inl (Or.inl ⟨hlt, hy⟩)
    · exact Or.inr heq
    · exact Or.inl (Or.inr ⟨hgt, hy⟩)
  rw [hdecomp]
  refine ⟨fun ⟨hL, hR⟩ => by rw [hL, hR], fun h => ?_⟩
  have hle : leftLimWithin f s x ≤ f x := hf.leftLimWithin_le le_rfl
  have hge : f x ≤ rightLimWithin f s x := hf.le_rightLimWithin le_rfl
  have hRfx : rightLimWithin f s x = f x := le_antisymm (h ▸ hle) hge
  exact ⟨h.trans hRfx, hRfx⟩

/-- A monotone function is continuous at `x` (for the full topology) if and only if its within left
and right limits along a *dense* set `s` coincide. Density is used to recover continuity along the
full neighbourhood `𝓝 x` from the within-`s` neighbourhoods. -/
theorem continuousAt_iff_leftLimWithin_eq_rightLimWithin
    [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] (hs : Dense s) :
    ContinuousAt f x ↔ leftLimWithin f s x = rightLimWithin f s x := by
  refine ⟨fun h => (hf.continuousWithinAt_iff_leftLimWithin_eq_rightLimWithin).1
    h.continuousWithinAt, fun h => ?_⟩
  have hL : (𝓝[Iio x ∩ s] x).NeBot := nhdsWithin_Iio_inter_neBot hs x
  have hR : (𝓝[Ioi x ∩ s] x).NeBot := nhdsWithin_Ioi_inter_neBot hs x
  have hle : leftLimWithin f s x ≤ f x := hf.leftLimWithin_le le_rfl
  have hge : f x ≤ rightLimWithin f s x := hf.le_rightLimWithin le_rfl
  have hRfx : rightLimWithin f s x = f x := le_antisymm (h ▸ hle) hge
  have hLfx : leftLimWithin f s x = f x := h.trans hRfx
  have hsupL : sSup (f '' Iio x) = f x := (hf.leftLimWithin_eq_sSup (s := s)).symm.trans hLfx
  have hsupR : sInf (f '' Ioi x) = f x := (hf.rightLimWithin_eq_sInf (s := s)).symm.trans hRfx
  refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
  · have ht := hf.tendsto_nhdsLT x
    rw [hsupL] at ht
    exact ht
  · have ht := hf.tendsto_nhdsGT x
    rw [hsupR] at ht
    exact ht

end Monotone

namespace Antitone

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Antitone f) {s : Set α} {x y : α}
include hf

theorem le_leftLimWithin (h : x ≤ y) : f y ≤ leftLimWithin f s x :=
  hf.dual_right.leftLimWithin_le h

theorem leftLimWithin_le (h : x < y) : leftLimWithin f s y ≤ f x :=
  hf.dual_right.le_leftLimWithin h

@[gcongr, mono]
protected theorem leftLimWithin : Antitone (leftLimWithin f s) :=
  hf.dual_right.leftLimWithin

theorem rightLimWithin_le (h : x ≤ y) : rightLimWithin f s y ≤ f x :=
  hf.dual_right.le_rightLimWithin h

theorem le_rightLimWithin (h : x < y) : f y ≤ rightLimWithin f s x :=
  hf.dual_right.rightLimWithin_le h

@[gcongr, mono]
protected theorem rightLimWithin : Antitone (rightLimWithin f s) :=
  hf.dual_right.rightLimWithin

theorem rightLimWithin_le_leftLimWithin (h : x ≤ y) :
    rightLimWithin f s y ≤ leftLimWithin f s x :=
  hf.dual_right.leftLimWithin_le_rightLimWithin h

theorem leftLimWithin_le_rightLimWithin (h : x < y) :
    leftLimWithin f s y ≤ rightLimWithin f s x :=
  hf.dual_right.rightLimWithin_le_leftLimWithin h

variable [TopologicalSpace α] [OrderTopology α]

theorem tendsto_leftLimWithin (x : α) :
    Tendsto f (𝓝[Iio x ∩ s] x) (𝓝 (leftLimWithin f s x)) :=
  hf.dual_right.tendsto_leftLimWithin x

theorem tendsto_leftLimWithin_within (x : α) :
    Tendsto f (𝓝[Iio x ∩ s] x) (𝓝[≥] leftLimWithin f s x) :=
  hf.dual_right.tendsto_leftLimWithin_within x

theorem tendsto_rightLimWithin (x : α) :
    Tendsto f (𝓝[Ioi x ∩ s] x) (𝓝 (rightLimWithin f s x)) :=
  hf.dual_right.tendsto_rightLimWithin x

theorem tendsto_rightLimWithin_within (x : α) :
    Tendsto f (𝓝[Ioi x ∩ s] x) (𝓝[≤] rightLimWithin f s x) :=
  hf.dual_right.tendsto_rightLimWithin_within x

/-- An antitone function is continuous to the left within `s` at `x` if and only if its within left
limit coincides with the value of the function. -/
theorem continuousWithinAt_Iio_iff_leftLimWithin_eq :
    ContinuousWithinAt f (Iio x ∩ s) x ↔ leftLimWithin f s x = f x :=
  hf.dual_right.continuousWithinAt_Iio_iff_leftLimWithin_eq

/-- An antitone function is continuous to the right within `s` at `x` if and only if its within
right limit coincides with the value of the function. -/
theorem continuousWithinAt_Ioi_iff_rightLimWithin_eq :
    ContinuousWithinAt f (Ioi x ∩ s) x ↔ rightLimWithin f s x = f x :=
  hf.dual_right.continuousWithinAt_Ioi_iff_rightLimWithin_eq

/-- An antitone function is continuous within `s` at `x` if and only if its within left and right
limits coincide. -/
theorem continuousWithinAt_iff_leftLimWithin_eq_rightLimWithin :
    ContinuousWithinAt f s x ↔ leftLimWithin f s x = rightLimWithin f s x :=
  hf.dual_right.continuousWithinAt_iff_leftLimWithin_eq_rightLimWithin

/-- An antitone function is continuous at `x` (for the full topology) if and only if its within left
and right limits along a *dense* set `s` coincide. -/
theorem continuousAt_iff_leftLimWithin_eq_rightLimWithin
    [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] (hs : Dense s) :
    ContinuousAt f x ↔ leftLimWithin f s x = rightLimWithin f s x :=
  hf.dual_right.continuousAt_iff_leftLimWithin_eq_rightLimWithin hs

end Antitone
