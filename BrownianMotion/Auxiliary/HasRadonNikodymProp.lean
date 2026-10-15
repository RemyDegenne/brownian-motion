/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.DoubleDual
public import BrownianMotion.Auxiliary.LevyUpward
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# The Radon-Nikodym property

A normed space `E` has the Radon-Nikodym property if every `E`-valued vector measure of bounded
variation which is absolutely continuous with respect to a finite measure `μ` has a density with
respect to `μ`.

## Main definitions

* `HasRadonNikodymProp E`: the space `E` has the Radon-Nikodym property. In the definition we only
  quantify over measurable spaces in `Type` and finite measures, but the property then holds for
  measurable spaces in any universe and σ-finite measures: see
  `HasRadonNikodymProp.exists_withDensityᵥ_eq`.

## Main statements

* `HasRadonNikodymProp.exists_withDensityᵥ_eq`: the defining property, for a measurable space in
  any universe and a σ-finite measure.
* `HasRadonNikodymProp.exists_withDensityᵥ_eq_of_forall_enorm_le`: in a space with the
  Radon-Nikodym property, a vector measure `ν` such that `‖ν s‖ₑ ≤ μ s` for all measurable sets
  `s` has a density with respect to `μ`, with norm at most `1`.
* `HasRadonNikodymProp.completeSpace`: a space with the Radon-Nikodym property is complete.
* `HasRadonNikodymProp.of_antilipschitzWith`, `HasRadonNikodymProp.of_continuousLinearEquiv`: the
  Radon-Nikodym property is inherited by Banach spaces which embed isomorphically, and is
  invariant under continuous linear equivalences.
* `HasRadonNikodymProp.of_forall_isSeparable`: the Radon-Nikodym property is separably determined.
  A normed space has the property as soon as its closed separable subspaces have it.
* `HasRadonNikodymProp.of_isReflexive`: a reflexive space has the Radon-Nikodym property.
* Instances: `ℝ`, real and complex Hilbert spaces, finite-dimensional spaces, finite products
  (`E × F`, `Π i, G i`, and their `L^p` versions `WithLp p (E × F)`, `PiLp p G`) and complete
  subspaces of spaces with the Radon-Nikodym property.

## Implementation notes

Two results rely on the same argument: the fact that the property holds for measurable spaces in
any universe, and the fact that it is separably determined. If a vector measure `ν` dominated by
a finite measure `μ` has a density `d m` with respect to `μ` on every countably generated
sub-σ-algebra `m`, then by Lévy's upward theorem `m ↦ d m` is a Cauchy net in `L¹`. Hence it is
eventually constant, and its eventual value is a density on the whole σ-algebra.
See `MeasureTheory.exists_withDensityᵥ_eq_of_forall_exists_isDensityOn`.

* A countably generated σ-algebra is the pullback of the σ-algebra of the Cantor space `ℕ → Bool`
  by a measurable map. The Cantor space is in `Type`, hence the image measures have a density
  there, which we pull back.
* The range of the restriction of `ν` to a countably generated σ-algebra is separable, hence
  contained in a closed separable subspace.

To prove that a separable reflexive space `E` has the Radon-Nikodym property, let `φ k` be a
sequence of continuous linear forms which separates the points of `E`. For a vector measure `ν`
dominated by `μ`, the real measures `φ k ∘ ν` have densities `g k`. For almost every `ω`, we have
`|∑ k, c k * g k ω| ≤ ‖∑ k, c k • φ k‖` for all finitely supported families of coefficients `c`,
hence by Helly's theorem (`NormedSpace.exists_norm_le_one_forall_apply_eq`) there is a point
`f ω` of norm at most `1` such that `φ k (f ω) = g k ω` for all `k`. The function `f` is
measurable because the `φ k` separate the points of the Polish space `E`, and it is a density
of `ν`.

## References

* J. Diestel, J. J. Uhl, *Vector measures*

-/

@[expose] public section

open MeasureTheory Filter TopologicalSpace Function NormedSpace
open scoped ENNReal NNReal Topology symmDiff

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {E : Type*} [NormedAddCommGroup E]

/-! ### Preliminaries on integrals and vector measures -/

/-- If the integrals of a real function `h` over the measurable sets `s` of finite measure are
bounded by `C * μ.real s`, then `|h| ≤ C` almost everywhere. -/
lemma ae_abs_le_of_forall_abs_setIntegral_le {μ : Measure Ω} [SigmaFinite μ] {h : Ω → ℝ}
    (hh : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn h s μ) {C : ℝ}
    (hC : ∀ s, MeasurableSet s → μ s < ∞ → |∫ ω in s, h ω ∂μ| ≤ C * μ.real s) :
    ∀ᵐ ω ∂μ, |h ω| ≤ C := by
  have hC_int (s : Set Ω) (hμs : μ s < ∞) : IntegrableOn (fun _ ↦ C) s μ :=
    integrableOn_const hμs.ne
  have h1 : 0 ≤ᵐ[μ] fun ω ↦ C - h ω := by
    refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
      (fun s hs hμs ↦ (hC_int s hμs).sub (hh s hs hμs)) fun s hs hμs ↦ ?_
    rw [integral_sub (hC_int s hμs) (hh s hs hμs), setIntegral_const, smul_eq_mul, mul_comm,
      sub_nonneg]
    exact (le_abs_self _).trans (hC s hs hμs)
  have h2 : 0 ≤ᵐ[μ] fun ω ↦ h ω + C := by
    refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
      (fun s hs hμs ↦ (hh s hs hμs).add (hC_int s hμs)) fun s hs hμs ↦ ?_
    rw [integral_add (hh s hs hμs) (hC_int s hμs), setIntegral_const, smul_eq_mul, mul_comm]
    linarith [(abs_le.1 (hC s hs hμs)).1]
  filter_upwards [h1, h2] with ω h1 h2
  exact abs_le.2 ⟨neg_le_iff_add_nonneg.2 h2, sub_nonneg.1 h1⟩

namespace VectorMeasure

section CodRestrict

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]

/-- The restriction of the codomain of a vector measure to a submodule which contains all its
values. -/
def codRestrict (v : VectorMeasure Ω M) (p : Submodule R M) (h : ∀ s, v s ∈ p) :
    VectorMeasure Ω p where
  measureOf' s := ⟨v s, h s⟩
  empty' := Subtype.ext v.empty
  not_measurable' _ hs := Subtype.ext (v.not_measurable hs)
  m_iUnion' _ hf hd :=
    (Topology.IsInducing.subtypeVal.hasSum_iff (g := p.subtype) _ _).1 (v.m_iUnion hf hd)

@[simp]
lemma coe_codRestrict_apply (v : VectorMeasure Ω M) (p : Submodule R M) (h : ∀ s, v s ∈ p)
    (s : Set Ω) : (v.codRestrict p h s : M) = v s := rfl

end CodRestrict

variable {μ : Measure Ω} {ν : VectorMeasure Ω E}

/-- A vector measure which is dominated by a measure `μ` is absolutely continuous with respect
to `μ`. -/
lemma absolutelyContinuous_of_forall_enorm_le (hν : ∀ s, MeasurableSet s → ‖ν s‖ₑ ≤ μ s) :
    ν ≪ᵥ μ.toENNRealVectorMeasure := by
  refine AbsolutelyContinuous.mk fun s hs hμs ↦ ?_
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hμs
  simpa [hμs] using hν s hs

/-- If a vector measure `ν` is dominated by a measure `μ`, then `‖ν s - ν t‖ₑ ≤ μ (s ∆ t)`. -/
lemma enorm_sub_le_of_forall_enorm_le (hν : ∀ s, MeasurableSet s → ‖ν s‖ₑ ≤ μ s) {s t : Set Ω}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ‖ν s - ν t‖ₑ ≤ μ (s ∆ t) := by
  have h1 : ν s = ν (s ∩ t) + ν (s \ t) := by
    rw [← of_union Set.disjoint_sdiff_inter.symm (hs.inter ht) (hs.diff ht),
      Set.inter_union_sdiff]
  have h2 : ν t = ν (s ∩ t) + ν (t \ s) := by
    rw [Set.inter_comm, ← of_union Set.disjoint_sdiff_inter.symm (ht.inter hs) (ht.diff hs),
      Set.inter_union_sdiff]
  rw [h1, h2, add_sub_add_left_eq_sub,
    measure_symmDiff_eq hs.nullMeasurableSet ht.nullMeasurableSet]
  exact enorm_sub_le.trans (add_le_add (hν _ (hs.diff ht)) (hν _ (ht.diff hs)))

/-- On a countably generated measurable space, a vector measure which is dominated by a finite
measure has a separable range. -/
lemma isSeparable_range_of_forall_enorm_le [MeasurableSpace.CountablyGenerated Ω]
    [IsFiniteMeasure μ] (hν : ∀ s, MeasurableSet s → ‖ν s‖ₑ ≤ μ s) :
    TopologicalSpace.IsSeparable (Set.range ν) := by
  obtain ⟨𝒜, h𝒜_count, h𝒜⟩ :=
    (isSeparable_of_sigmaFinite (μ := μ)).exists_countable_measureDense
  refine ((h𝒜_count.image ν).isSeparable.closure.union
    (Set.countable_singleton (0 : E)).isSeparable).mono ?_
  rintro _ ⟨s, rfl⟩
  by_cases hs : MeasurableSet s
  · refine Or.inl (Metric.mem_closure_iff.2 fun ε hε ↦ ?_)
    obtain ⟨t, ht, hst⟩ := h𝒜.approx s hs (measure_ne_top _ _) ε hε
    refine ⟨ν t, ⟨t, ht, rfl⟩, ?_⟩
    rw [dist_eq_norm, ← ENNReal.ofReal_lt_ofReal_iff hε, ofReal_norm]
    exact (enorm_sub_le_of_forall_enorm_le hν hs (h𝒜.measurable t ht)).trans_lt hst
  · exact Or.inr (ν.not_measurable hs)

end VectorMeasure

variable [NormedSpace ℝ E]

/-- If the integrals of an integrable function `f` over the measurable sets belong to a closed
subspace `S`, then `f` takes its values in `S` almost everywhere. -/
lemma Integrable.ae_mem_of_forall_setIntegral_mem [CompleteSpace E] {μ : Measure Ω} {f : Ω → E}
    (hf : Integrable f μ) {S : Submodule ℝ E} (hS : IsClosed (S : Set E))
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫ ω in s, f ω ∂μ ∈ S) :
    ∀ᵐ ω ∂μ, f ω ∈ S := by
  have : IsClosed (S : Set E) := hS
  -- the image of `f` in the quotient by `S` has zero integral on all sets
  have h0 : (fun ω ↦ S.mkQL (f ω)) =ᵐ[μ] 0 := by
    refine (S.mkQL.integrable_comp hf).ae_eq_zero_of_forall_setIntegral_eq_zero
      fun s hs hμs ↦ ?_
    rw [S.mkQL.integral_comp_comm hf.integrableOn, Submodule.mkQL_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact h s hs hμs
  filter_upwards [h0] with ω hω using (Submodule.Quotient.mk_eq_zero S).1 hω

/-- If a vector measure `ν` which is dominated by a σ-finite measure `μ` has an integrable density
with respect to `μ`, then it has a strongly measurable density with norm at most `1`. -/
private lemma exists_stronglyMeasurable_withDensityᵥ_eq [CompleteSpace E] {μ : Measure Ω}
    [SigmaFinite μ] {ν : VectorMeasure Ω E} (hν : ∀ s, MeasurableSet s → ‖ν s‖ₑ ≤ μ s) {g : Ω → E}
    (hg_int : Integrable g μ) (hg : μ.withDensityᵥ g = ν) :
    ∃ f : Ω → E, StronglyMeasurable f ∧ (∀ ω, ‖f ω‖ ≤ 1) ∧ μ.withDensityᵥ f = ν := by
  -- the density is bounded by `1` almost everywhere
  have hg_le : ∀ᵐ ω ∂μ, ‖g ω‖ₑ ≤ 1 := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hg_int.1.enorm fun s hs _ ↦ ?_
    rw [← withDensity_apply _ hs, ← Measure.variation_withDensityᵥ hg_int, hg]
    simpa using VectorMeasure.variation_le_of_forall_enorm_le hν s
  -- we modify it into a strongly measurable function which is bounded by `1` everywhere
  let g₀ : Ω → E := hg_int.1.mk g
  have hg₀ : StronglyMeasurable g₀ := hg_int.1.stronglyMeasurable_mk
  let f : Ω → E := {ω | ‖g₀ ω‖ ≤ 1}.indicator g₀
  have hf_norm (ω : Ω) : ‖f ω‖ ≤ 1 := by
    by_cases hω : ‖g₀ ω‖ ≤ 1 <;> simp [f, hω]
  have hf_ae : f =ᵐ[μ] g := by
    filter_upwards [hg_int.1.ae_eq_mk, hg_le] with ω hω hω'
    have h_le : ‖g₀ ω‖ ≤ 1 := by
      rwa [hω, ← ofReal_norm, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one]
        at hω'
    simp [f, h_le, g₀, hω]
  exact ⟨f, hg₀.indicator (measurableSet_le hg₀.norm.measurable measurable_const), hf_norm,
    (WithDensityᵥEq.congr_ae hf_ae).trans hg⟩

/-- If a vector measure `ν` of bounded variation is absolutely continuous with respect to a
σ-finite measure `μ` and has a bounded density with respect to its variation, then it has a density
with respect to `μ`. -/
private lemma exists_integrable_withDensityᵥ_eq_of_variation {μ : Measure Ω} [SigmaFinite μ]
    {ν : VectorMeasure Ω E} [IsFiniteMeasure ν.variation]
    (hν : ν ≪ᵥ μ.toENNRealVectorMeasure) {f : Ω → E} (hf_sm : StronglyMeasurable f)
    (hf_norm : ∀ ω, ‖f ω‖ ≤ 1) (hf_eq : ν.variation.withDensityᵥ f = ν) :
    ∃ g : Ω → E, Integrable g μ ∧ μ.withDensityᵥ g = ν := by
  have h_ac : ν.variation ≪ μ := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hμs ↦ ?_
    rw [VectorMeasure.variation_apply_eq_zero hs]
    intro t hts ht
    refine hν ?_
    rw [Measure.toENNRealVectorMeasure_apply_measurable ht]
    exact measure_mono_null hts hμs
  have hf_int : Integrable f ν.variation :=
    Integrable.of_bound hf_sm.aestronglyMeasurable 1 (ae_of_all _ hf_norm)
  refine ⟨fun ω ↦ (ν.variation.rnDeriv μ ω).toReal • f ω,
    (integrable_rnDeriv_smul_iff h_ac).mpr hf_int, ?_⟩
  rw [withDensityᵥ_rnDeriv_smul h_ac hf_int, hf_eq]

/-! ### Densities on countably generated sub-σ-algebras -/

/-- `f` is a density of the vector measure `ν` with respect to `μ` on the sub-σ-algebra `m`,
bounded by `1`. -/
private def IsDensityOn (μ : Measure Ω) (ν : VectorMeasure Ω E) (m : MeasurableSpace Ω)
    (f : Ω → E) : Prop :=
  StronglyMeasurable[m] f ∧ (∀ ω, ‖f ω‖ ≤ 1) ∧ ∀ s, MeasurableSet[m] s → ∫ ω in s, f ω ∂μ = ν s

private lemma IsDensityOn.integrable {μ : Measure Ω} [IsFiniteMeasure μ]
    {ν : VectorMeasure Ω E} {m : MeasurableSpace Ω} {f : Ω → E} (hf : IsDensityOn μ ν m f)
    (hm : m ≤ mΩ) :
    Integrable f μ :=
  Integrable.of_bound (hf.1.mono hm).aestronglyMeasurable 1 (ae_of_all _ hf.2.1)

private lemma IsDensityOn.condExp_ae_eq [CompleteSpace E] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ν : VectorMeasure Ω E} {m m' : MeasurableSpace Ω} {f f' : Ω → E}
    (hf : IsDensityOn μ ν m f) (hf' : IsDensityOn μ ν m' f') (hmm' : m ≤ m') (hm' : m' ≤ mΩ) :
    μ[f' | m] =ᵐ[μ] f := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq (hmm'.trans hm') (hf'.integrable hm')
    (fun s _ _ ↦ (hf.integrable (hmm'.trans hm')).integrableOn) (fun s hs _ ↦ ?_)
    hf.1.aestronglyMeasurable).symm
  rw [hf.2.2 s hs, hf'.2.2 s (hmm' s hs)]

/-- A bounded density of the restriction of `ν` to a sub-σ-algebra `m` with respect to the
restriction of `μ` is a density of `ν` with respect to `μ` on `m`. -/
private lemma isDensityOn_of_withDensityᵥ_trim_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {ν : VectorMeasure Ω E} {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f : Ω → E}
    (hf_sm : StronglyMeasurable[m] f) (hf_norm : ∀ ω, ‖f ω‖ ≤ 1)
    (hf_eq : (μ.trim hm).withDensityᵥ f = ν.trim hm) :
    IsDensityOn μ ν m f := by
  refine ⟨hf_sm, hf_norm, fun s hs ↦ ?_⟩
  have hf_int : Integrable f (μ.trim hm) :=
    Integrable.of_bound hf_sm.aestronglyMeasurable 1 (ae_of_all _ hf_norm)
  rw [setIntegral_trim hm hf_sm hs, ← withDensityᵥ_apply hf_int hs, hf_eq,
    VectorMeasure.trim_measurableSet_eq hm hs]

/-- If a vector measure `ν` has a density with respect to `μ`, bounded by `1`, on every countably
generated sub-σ-algebra, then it has a density with respect to `μ`. -/
private lemma exists_withDensityᵥ_eq_of_forall_exists_isDensityOn [CompleteSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : VectorMeasure Ω E}
    (h : ∀ m : MeasurableSpace Ω, m ≤ mΩ → @MeasurableSpace.CountablyGenerated Ω m →
      ∃ f, IsDensityOn μ ν m f) :
    ∃ f : Ω → E, StronglyMeasurable f ∧ (∀ ω, ‖f ω‖ ≤ 1) ∧ μ.withDensityᵥ f = ν := by
  -- we choose a density `d m` on each countably generated sub-σ-algebra `m`
  let 𝒞 : Type _ := {m : MeasurableSpace Ω // m ≤ mΩ ∧ @MeasurableSpace.CountablyGenerated Ω m}
  choose d hd using fun m : 𝒞 ↦ h m.1 m.2.1 m.2.2
  have hd_int (m : 𝒞) : Integrable (d m) μ := (hd m).integrable m.2.1
  have h_triangle (m₁ m₂ m₃ : 𝒞) : eLpNorm (d m₁ - d m₂) 1 μ
      ≤ eLpNorm (d m₁ - d m₃) 1 μ + eLpNorm (d m₂ - d m₃) 1 μ := by
    rw [← sub_add_sub_cancel (d m₁) (d m₃) (d m₂), eLpNorm_sub_comm (d m₂) (d m₃)]
    exact eLpNorm_add_le ((hd_int m₁).sub (hd_int m₃)).aestronglyMeasurable
      ((hd_int m₃).sub (hd_int m₂)).aestronglyMeasurable le_rfl
  have h_sup (m : ℕ → 𝒞) : ∃ m' : 𝒞, m'.1 = ⨆ n, (m n).1 := by
    choose b hb_count hb_eq using fun n ↦ (m n).2.2.isCountablyGenerated
    refine ⟨⟨⨆ n, (m n).1, iSup_le fun n ↦ (m n).2.1, @MeasurableSpace.CountablyGenerated.mk Ω
      (⨆ n, (m n).1) ⟨⋃ n, b n, Set.countable_iUnion hb_count, ?_⟩⟩, rfl⟩
    rw [← MeasurableSpace.iSup_generateFrom]
    exact iSup_congr hb_eq
  -- the densities form a Cauchy net in `L¹`
  have h_cauchy (ε : ℝ≥0∞) (hε : ε ≠ 0) :
      ∃ m : 𝒞, ∀ m' : 𝒞, m.1 ≤ m'.1 → eLpNorm (d m' - d m) 1 μ ≤ ε := by
    by_contra! h
    choose next h_le h_lt using h
    let m₀ : 𝒞 := ⟨⊥, bot_le, @MeasurableSpace.CountablyGenerated.mk Ω ⊥
      ⟨∅, Set.countable_empty, MeasurableSpace.generateFrom_empty.symm⟩⟩
    let seq : ℕ → 𝒞 := fun n ↦ next^[n] m₀
    have h_succ (n : ℕ) : seq (n + 1) = next (seq n) := Function.iterate_succ_apply' _ _ _
    have h_mono : Monotone fun n ↦ (seq n).1 := monotone_nat_of_le_succ fun n ↦ by
      rw [h_succ]
      exact h_le _
    let ℱ : Filtration ℕ mΩ := ⟨fun n ↦ (seq n).1, h_mono, fun n ↦ (seq n).2.1⟩
    obtain ⟨m', hm'⟩ := h_sup seq
    have hsm : StronglyMeasurable[⨆ n, ℱ n] (d m') := hm' ▸ (hd m').1
    have h_lim : Tendsto (fun n ↦ eLpNorm (d (seq n) - d m') 1 μ) atTop (𝓝 0) := by
      refine ((hd_int m').tendsto_eLpNorm_condExp' (ℱ := ℱ) hsm.aestronglyMeasurable).congr
        fun n ↦ eLpNorm_congr_ae ?_
      have h_le' : (seq n).1 ≤ m'.1 := hm' ▸ le_iSup (fun n ↦ (seq n).1) n
      filter_upwards [(hd (seq n)).condExp_ae_eq (hd m') h_le' m'.2.1] with ω hω
      simp only [Pi.sub_apply]
      rw [← hω]
    have h_diff : Tendsto (fun n ↦ eLpNorm (d (seq (n + 1)) - d (seq n)) 1 μ) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using (h_lim.comp (tendsto_add_atTop_nat 1)).add h_lim) (fun _ ↦ zero_le)
        fun n ↦ h_triangle _ _ m'
    obtain ⟨n, hn⟩ := ((tendsto_order.1 h_diff).2 ε (pos_iff_ne_zero.2 hε)).exists
    rw [h_succ] at hn
    exact lt_irrefl _ (hn.trans (h_lt (seq n)))
  -- hence they are eventually constant
  obtain ⟨m, hm⟩ : ∃ m : 𝒞, ∀ m' : 𝒞, m.1 ≤ m'.1 → d m' =ᵐ[μ] d m := by
    have hε (k : ℕ) : ((k : ℝ≥0∞))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top k)
    choose m hm using fun k : ℕ ↦ h_cauchy _ (hε k)
    obtain ⟨m', hm'⟩ := h_sup m
    have h_le (k : ℕ) : (m k).1 ≤ m'.1 := hm' ▸ le_iSup (fun n ↦ (m n).1) k
    refine ⟨m', fun m'' hm'' ↦ ?_⟩
    have h0 : eLpNorm (d m'' - d m') 1 μ = 0 := by
      refine le_antisymm ?_ zero_le
      have h_tendsto : Tendsto (fun k : ℕ ↦ (k : ℝ≥0∞)⁻¹ + (k : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_inv_nat_nhds_zero.add ENNReal.tendsto_inv_nat_nhds_zero
      refine ge_of_tendsto' h_tendsto fun k ↦ ?_
      exact (h_triangle m'' m' (m k)).trans
        (add_le_add (hm k m'' ((h_le k).trans hm'')) (hm k m' (h_le k)))
    have h_ae := (eLpNorm_eq_zero_iff ((hd_int m'').sub (hd_int m')).aestronglyMeasurable
      one_ne_zero).1 h0
    filter_upwards [h_ae] with ω hω using sub_eq_zero.1 hω
  -- the density on that σ-algebra is a density on the whole σ-algebra
  refine ⟨d m, (hd m).1.mono m.2.1, (hd m).2.1, ?_⟩
  ext s hs
  rw [withDensityᵥ_apply (hd_int m) hs]
  let m' : 𝒞 := ⟨m.1 ⊔ MeasurableSpace.generateFrom {s},
    sup_le m.2.1 (MeasurableSpace.generateFrom_le (by simpa using hs)),
    m.2.2.sup (@MeasurableSpace.CountablyGenerated.mk Ω (MeasurableSpace.generateFrom {s})
      ⟨{s}, Set.countable_singleton _, rfl⟩)⟩
  have hs' : MeasurableSet[m'.1] s :=
    (le_sup_right : MeasurableSpace.generateFrom {s} ≤ m'.1) s
      (MeasurableSpace.measurableSet_generateFrom rfl)
  rw [← (hd m').2.2 s hs']
  refine setIntegral_congr_ae hs ?_
  filter_upwards [hm m' le_sup_left] with ω hω _ using hω.symm

end MeasureTheory

open MeasureTheory

/-- A normed space `E` has the **Radon-Nikodym property** if every `E`-valued vector measure of
bounded variation which is absolutely continuous with respect to a finite measure `μ` has a density
with respect to `μ`.

In the definition we only quantify over measurable spaces in `Type` and finite measures. This is
not a restriction: see `HasRadonNikodymProp.exists_withDensityᵥ_eq` for measurable spaces in any
universe and σ-finite measures. -/
class HasRadonNikodymProp (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop where
  /-- Use `HasRadonNikodymProp.exists_withDensityᵥ_eq` instead, which is valid for measurable
  spaces in any universe and for σ-finite measures. -/
  exists_withDensityᵥ_eq' {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : VectorMeasure Ω E) [IsFiniteMeasure ν.variation]
    (hν : ν ≪ᵥ μ.toENNRealVectorMeasure) :
    ∃ f : Ω → E, Integrable f μ ∧ μ.withDensityᵥ f = ν

namespace HasRadonNikodymProp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `ℝ` has the Radon-Nikodym property: this is the Radon-Nikodym theorem for signed measures. -/
instance real : HasRadonNikodymProp ℝ where
  exists_withDensityᵥ_eq' μ _ ν _ hν :=
    ⟨SignedMeasure.rnDeriv ν μ, SignedMeasure.integrable_rnDeriv ν μ,
      SignedMeasure.withDensityᵥ_rnDeriv_eq ν μ hν⟩

/-- A space with the Radon-Nikodym property is complete. -/
theorem completeSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasRadonNikodymProp E] : CompleteSpace E := by
  by_contra hE
  -- otherwise all Bochner integrals are zero, hence so are all vector measures with a density
  have h0 (x : E) : x = 0 := by
    have hν : VectorMeasure.dirac () x ≪ᵥ (Measure.dirac ()).toENNRealVectorMeasure := by
      intro s hs
      by_cases hmem : () ∈ s
      · rw [Measure.toENNRealVectorMeasure_apply_measurable .of_discrete,
          Measure.dirac_apply_of_mem hmem] at hs
        exact absurd hs one_ne_zero
      · exact VectorMeasure.dirac_apply_of_notMem hmem
    obtain ⟨f, hf, hfx⟩ := exists_withDensityᵥ_eq' (Measure.dirac ()) (VectorMeasure.dirac () x) hν
    have h := congr($hfx Set.univ)
    rwa [withDensityᵥ_apply hf .univ, integral_of_not_completeSpace hE,
      VectorMeasure.dirac_apply_of_mem .univ (Set.mem_univ _), eq_comm] at h
  have : Subsingleton E := ⟨fun x y ↦ by rw [h0 x, h0 y]⟩
  exact hE inferInstance

section Universe

/-! ### Measurable spaces in any universe -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} [HasRadonNikodymProp E]

/-- Auxiliary lemma for `HasRadonNikodymProp.exists_withDensityᵥ_eq_of_forall_enorm_le`: the case
of a countably generated measurable space. We transport the measures to the Cantor space
`ℕ → Bool`, which is in `Type`. -/
private lemma exists_withDensityᵥ_eq_of_countablyGenerated [MeasurableSpace.CountablyGenerated Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : VectorMeasure Ω E)
    (hν : ∀ s, MeasurableSet s → ‖ν s‖ₑ ≤ μ s) :
    ∃ f : Ω → E, StronglyMeasurable f ∧ (∀ ω, ‖f ω‖ ≤ 1) ∧ μ.withDensityᵥ f = ν := by
  have := completeSpace E
  let π : Ω → ℕ → Bool := MeasurableSpace.mapNatBool Ω
  have hπ : Measurable π := MeasurableSpace.measurable_mapNatBool Ω
  -- every measurable set is the preimage of a measurable set of the Cantor space
  have h_comap : mΩ ≤ MeasurableSpace.comap π inferInstance := by
    rw [← MeasurableSpace.generateFrom_natGeneratingSequence Ω]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨{x | x n = true}, measurableSet_eq_fun (measurable_pi_apply n) measurable_const, ?_⟩
    ext ω
    simp [π, MeasurableSpace.mapNatBool]
  -- the image measures on the Cantor space, and a density there
  have hν₀ (B : Set (ℕ → Bool)) (hB : MeasurableSet B) : ‖ν.map π B‖ₑ ≤ μ.map π B := by
    rw [VectorMeasure.map_apply _ hπ hB, Measure.map_apply hπ hB]
    exact hν _ (hπ hB)
  have : IsFiniteMeasure (ν.map π).variation :=
    isFiniteMeasure_of_le _ (VectorMeasure.variation_le_of_forall_enorm_le hν₀)
  obtain ⟨g₀, hg₀_int, hg₀⟩ := exists_withDensityᵥ_eq' (μ.map π) (ν.map π)
    (VectorMeasure.absolutelyContinuous_of_forall_enorm_le hν₀)
  obtain ⟨g, hg_sm, hg_norm, hg⟩ := exists_stronglyMeasurable_withDensityᵥ_eq hν₀ hg₀_int hg₀
  -- we pull back the density
  have hg_int : Integrable g (μ.map π) :=
    .of_bound hg_sm.aestronglyMeasurable 1 (ae_of_all _ hg_norm)
  have hgπ_int : Integrable (g ∘ π) μ := hg_int.comp_measurable hπ
  refine ⟨g ∘ π, hg_sm.comp_measurable hπ, fun ω ↦ hg_norm _, ?_⟩
  ext s hs
  obtain ⟨B, hB, rfl⟩ := h_comap s hs
  rw [withDensityᵥ_apply hgπ_int (hπ hB), ← VectorMeasure.map_apply _ hπ hB, ← hg,
    withDensityᵥ_apply hg_int hB]
  exact (setIntegral_map hB hg_sm.aestronglyMeasurable hπ.aemeasurable).symm

/-- In a space with the Radon-Nikodym property, a vector measure `ν` such that `‖ν s‖ₑ ≤ μ s` for
all measurable sets `s`, for a finite measure `μ`, has a density with respect to `μ`, with norm
at most `1`. The measurable space can be in any universe. -/
theorem exists_withDensityᵥ_eq_of_forall_enorm_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : VectorMeasure Ω E) (hν : ∀ s, MeasurableSet s → ‖ν s‖ₑ ≤ μ s) :
    ∃ f : Ω → E, StronglyMeasurable f ∧ (∀ ω, ‖f ω‖ ≤ 1) ∧ μ.withDensityᵥ f = ν := by
  have := completeSpace E
  -- it suffices to find a density on every countably generated sub-σ-algebra
  refine exists_withDensityᵥ_eq_of_forall_exists_isDensityOn fun m hm hm_cg ↦ ?_
  have hν' (s : Set Ω) (hs : MeasurableSet[m] s) : ‖ν.trim hm s‖ₑ ≤ μ.trim hm s := by
    rw [VectorMeasure.trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs]
    exact hν s (hm s hs)
  obtain ⟨f, hf_sm, hf_norm, hf_eq⟩ :=
    exists_withDensityᵥ_eq_of_countablyGenerated (mΩ := m) (μ.trim hm) (ν.trim hm) hν'
  exact ⟨f, isDensityOn_of_withDensityᵥ_trim_eq hm hf_sm hf_norm hf_eq⟩

/-- In a space with the Radon-Nikodym property, a vector measure of bounded variation which is
absolutely continuous with respect to a σ-finite measure `μ` has a density with respect to `μ`.
This is the defining property, for a measurable space in any universe and a measure which is
σ-finite instead of finite. -/
theorem exists_withDensityᵥ_eq (μ : Measure Ω) [SigmaFinite μ] (ν : VectorMeasure Ω E)
    [IsFiniteMeasure ν.variation] (hν : ν ≪ᵥ μ.toENNRealVectorMeasure) :
    ∃ f : Ω → E, Integrable f μ ∧ μ.withDensityᵥ f = ν := by
  have := completeSpace E
  obtain ⟨f, hf_sm, hf_norm, hf_eq⟩ := exists_withDensityᵥ_eq_of_forall_enorm_le ν.variation ν
    fun s _ ↦ ν.enorm_measure_le_variation s
  exact exists_integrable_withDensityᵥ_eq_of_variation hν hf_sm hf_norm hf_eq

end Universe

section Stability

/-! ### Stability properties -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `E` has the Radon-Nikodym property, then the image by a continuous linear map
`L : F →L[ℝ] E` of an `F`-valued vector measure of bounded variation has a density. -/
private lemma exists_setIntegral_eq_map [HasRadonNikodymProp E] (L : F →L[ℝ] E)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : VectorMeasure Ω F) [IsFiniteMeasure ν.variation]
    (hν : ν ≪ᵥ μ.toENNRealVectorMeasure) :
    ∃ f : Ω → E, Integrable f μ ∧ ∀ s, MeasurableSet s → ∫ ω in s, f ω ∂μ = L (ν s) := by
  let ν' : VectorMeasure Ω E := ν.mapRange (L : F →+ E) L.continuous
  have hν'_apply (s : Set Ω) : ν' s = L (ν s) := VectorMeasure.mapRange_apply ..
  have : IsFiniteMeasure ν'.variation := by
    refine isFiniteMeasure_of_le (‖L‖₊ • ν.variation)
      (VectorMeasure.variation_le_of_forall_enorm_le fun s _ ↦ ?_)
    rw [hν'_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ← enorm_eq_nnnorm]
    exact (L.le_opENorm _).trans (by gcongr; exact VectorMeasure.enorm_measure_le_variation ..)
  obtain ⟨f, hf, hfν⟩ := exists_withDensityᵥ_eq' μ ν'
    fun s hs ↦ by rw [hν'_apply, hν hs, map_zero]
  exact ⟨f, hf, fun s hs ↦ by rw [← withDensityᵥ_apply hf hs, hfν, hν'_apply]⟩

/-- The Radon-Nikodym property is inherited by Banach spaces which embed isomorphically: if `F` is
complete, `E` has the Radon-Nikodym property and there is a continuous linear map from `F` to `E`
which is bounded from below, then `F` has the Radon-Nikodym property. -/
theorem of_antilipschitzWith [CompleteSpace F] [HasRadonNikodymProp E] (L : F →L[ℝ] E) {c : ℝ≥0}
    (hL : AntilipschitzWith c L) : HasRadonNikodymProp F where
  exists_withDensityᵥ_eq' {Ω} _ μ _ ν _ hν := by
    have := completeSpace E
    obtain ⟨f, hf, hfν⟩ := exists_setIntegral_eq_map L μ ν hν
    have hL_emb : Topology.IsClosedEmbedding L := hL.isClosedEmbedding L.uniformContinuous
    -- `f` takes its values in the range of `L` a.e., since its integrals belong to that closed
    -- subspace
    have h_closed : IsClosed (LinearMap.range (L : F →ₗ[ℝ] E) : Set E) := by
      rw [LinearMap.coe_range]
      exact hL_emb.isClosed_range
    have h_mem : ∀ᵐ ω ∂μ, f ω ∈ LinearMap.range (L : F →ₗ[ℝ] E) :=
      hf.ae_mem_of_forall_setIntegral_mem h_closed fun s hs _ ↦
        LinearMap.mem_range.2 ⟨ν s, (hfν s hs).symm⟩
    -- its preimage by `L` is the density
    let g : Ω → F := fun ω ↦ Function.invFun L (f ω)
    have hg : (fun ω ↦ L (g ω)) =ᵐ[μ] f :=
      h_mem.mono fun ω hω ↦ Function.invFun_eq (LinearMap.mem_range.1 hω)
    have hg_int : Integrable g μ := by
      refine Integrable.mono' (hf.norm.const_mul c)
        (hL_emb.isEmbedding.aestronglyMeasurable_comp_iff.1 (hf.1.congr hg.symm)) ?_
      filter_upwards [hg] with ω hω
      rw [← hω]
      exact L.bound_of_antilipschitz hL _
    refine ⟨g, hg_int, VectorMeasure.ext fun s hs ↦ hL.injective ?_⟩
    rw [withDensityᵥ_apply hg_int hs, ← L.integral_comp_comm hg_int.integrableOn, ← hfν s hs]
    exact integral_congr_ae (ae_restrict_of_ae hg)

/-- The Radon-Nikodym property is invariant under continuous linear equivalences. -/
theorem of_continuousLinearEquiv [HasRadonNikodymProp E] (e : E ≃L[ℝ] F) :
    HasRadonNikodymProp F := by
  have := completeSpace E
  have : CompleteSpace F := (completeSpace_congr (e := e.toEquiv) e.isUniformEmbedding).1 ‹_›
  exact of_antilipschitzWith (e.symm : F →L[ℝ] E) e.symm.antilipschitz

/-- A complete subspace of a space with the Radon-Nikodym property has the Radon-Nikodym
property. -/
instance submodule (S : Submodule ℝ E) [HasRadonNikodymProp E] [CompleteSpace S] :
    HasRadonNikodymProp S :=
  of_antilipschitzWith S.subtypeL (AntilipschitzWith.subtype_coe _)

/-- A closed subspace of a space with the Radon-Nikodym property has the Radon-Nikodym
property. -/
theorem submodule_of_isClosed [HasRadonNikodymProp E] (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E)) : HasRadonNikodymProp S :=
  haveI := completeSpace E
  haveI := hS.completeSpace_coe
  inferInstance

/-- The product of two spaces with the Radon-Nikodym property has the Radon-Nikodym property. -/
instance prod [HasRadonNikodymProp E] [HasRadonNikodymProp F] : HasRadonNikodymProp (E × F) where
  exists_withDensityᵥ_eq' μ _ ν _ hν := by
    have := completeSpace E
    have := completeSpace F
    obtain ⟨f, hf, hfν⟩ := exists_setIntegral_eq_map (ContinuousLinearMap.fst ℝ E F) μ ν hν
    obtain ⟨g, hg, hgν⟩ := exists_setIntegral_eq_map (ContinuousLinearMap.snd ℝ E F) μ ν hν
    refine ⟨fun ω ↦ (f ω, g ω), hf.prodMk hg, VectorMeasure.ext fun s hs ↦ ?_⟩
    rw [withDensityᵥ_apply (hf.prodMk hg) hs, integral_pair hf.integrableOn hg.integrableOn,
      hfν s hs, hgν s hs]
    rfl

/-- The `L^p` product of two spaces with the Radon-Nikodym property has the Radon-Nikodym
property. -/
instance withLpProd {p : ℝ≥0∞} [Fact (1 ≤ p)] [HasRadonNikodymProp E] [HasRadonNikodymProp F] :
    HasRadonNikodymProp (WithLp p (E × F)) :=
  of_continuousLinearEquiv (WithLp.prodContinuousLinearEquiv p ℝ E F).symm

section Pi

variable {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, NormedSpace ℝ (G i)] [∀ i, HasRadonNikodymProp (G i)]

/-- A finite product of spaces with the Radon-Nikodym property has the Radon-Nikodym property. -/
instance pi : HasRadonNikodymProp (Π i, G i) where
  exists_withDensityᵥ_eq' μ _ ν _ hν := by
    have (i : ι) := completeSpace (G i)
    choose f hf hfν using fun i ↦
      exists_setIntegral_eq_map (ContinuousLinearMap.proj (R := ℝ) (φ := G) i) μ ν hν
    have hf' : Integrable (fun ω i ↦ f i ω) μ := Integrable.of_eval hf
    refine ⟨fun ω i ↦ f i ω, hf', VectorMeasure.ext fun s hs ↦ funext fun i ↦ ?_⟩
    rw [withDensityᵥ_apply hf' hs, eval_integral (fun i ↦ (hf i).integrableOn), hfν i s hs]
    rfl

/-- A finite `L^p` product of spaces with the Radon-Nikodym property has the Radon-Nikodym
property. -/
instance piLp {p : ℝ≥0∞} [Fact (1 ≤ p)] : HasRadonNikodymProp (PiLp p G) :=
  of_continuousLinearEquiv (PiLp.continuousLinearEquiv p ℝ G).symm

end Pi

/-- A finite-dimensional normed space has the Radon-Nikodym property. -/
instance (priority := 100) of_finiteDimensional [FiniteDimensional ℝ E] : HasRadonNikodymProp E :=
  of_continuousLinearEquiv toEuclidean.symm

end Stability

section Separable

/-! ### The Radon-Nikodym property is separably determined -/

/-- Auxiliary lemma for `HasRadonNikodymProp.of_forall_isSeparable`. -/
private lemma exists_isDensityOn_of_forall_isSeparable [CompleteSpace E]
    (h : ∀ F : Submodule ℝ E, IsClosed (F : Set E) → TopologicalSpace.IsSeparable (F : Set E) →
      HasRadonNikodymProp F)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ν : VectorMeasure Ω E} (hν : ∀ s, MeasurableSet s → ‖ν s‖ₑ ≤ μ s) {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (hm_cg : @MeasurableSpace.CountablyGenerated Ω m) :
    ∃ f, IsDensityOn μ ν m f := by
  have hν' (s : Set Ω) (hs : MeasurableSet[m] s) : ‖ν.trim hm s‖ₑ ≤ μ.trim hm s := by
    rw [VectorMeasure.trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs]
    exact hν s (hm s hs)
  -- the restriction of `ν` to `m` takes its values in a closed separable subspace `F`
  obtain ⟨F, hF_closed, hF_sep, hνF⟩ : ∃ F : Submodule ℝ E, IsClosed (F : Set E) ∧
      TopologicalSpace.IsSeparable (F : Set E) ∧ ∀ s, ν.trim hm s ∈ F :=
    ⟨(Submodule.span ℝ (Set.range (ν.trim hm))).topologicalClosure,
      Submodule.isClosed_topologicalClosure _,
      (VectorMeasure.isSeparable_range_of_forall_enorm_le hν').span.closure,
      fun s ↦ Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨s, rfl⟩)⟩
  have := h F hF_closed hF_sep
  have := hF_closed.completeSpace_coe
  -- hence it has a density with values in `F`, which is also a density in `E`
  obtain ⟨f, hf_sm, hf_norm, hf_eq⟩ := exists_withDensityᵥ_eq_of_forall_enorm_le (μ.trim hm)
    ((ν.trim hm).codRestrict F hνF) hν'
  have hf_int : Integrable f (μ.trim hm) :=
    .of_bound hf_sm.aestronglyMeasurable 1 (ae_of_all _ hf_norm)
  have hf_int' : Integrable (fun ω ↦ (f ω : E)) (μ.trim hm) := F.subtypeL.integrable_comp hf_int
  refine ⟨fun ω ↦ f ω, isDensityOn_of_withDensityᵥ_trim_eq hm
    (continuous_subtype_val.comp_stronglyMeasurable hf_sm) hf_norm ?_⟩
  ext s hs
  rw [withDensityᵥ_apply hf_int' hs, ← VectorMeasure.coe_codRestrict_apply (ν.trim hm) F hνF s,
    ← hf_eq, withDensityᵥ_apply hf_int hs]
  exact F.subtypeL.integral_comp_comm hf_int.integrableOn

/-- A normed space whose closed separable subspaces have the Radon-Nikodym property is complete:
a Cauchy sequence takes its values in a closed separable subspace, which is complete. -/
private lemma completeSpace_of_forall_isSeparable
    (h : ∀ F : Submodule ℝ E, IsClosed (F : Set E) → TopologicalSpace.IsSeparable (F : Set E) →
      HasRadonNikodymProp F) :
    CompleteSpace E := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  obtain ⟨F, hF_closed, hF_sep, huF⟩ : ∃ F : Submodule ℝ E, IsClosed (F : Set E) ∧
      TopologicalSpace.IsSeparable (F : Set E) ∧ ∀ n, u n ∈ F :=
    ⟨(Submodule.span ℝ (Set.range u)).topologicalClosure, Submodule.isClosed_topologicalClosure _,
      (Set.countable_range u).isSeparable.span.closure,
      fun n ↦ Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)⟩
  have := h F hF_closed hF_sep
  have hF_complete : IsComplete (F : Set E) :=
    completeSpace_coe_iff_isComplete.1 (completeSpace F)
  obtain ⟨x, -, hx⟩ := cauchySeq_tendsto_of_isComplete hF_complete huF hu
  exact ⟨x, hx⟩

/-- The Radon-Nikodym property is separably determined: a normed space has the Radon-Nikodym
property if its closed separable subspaces have it. -/
theorem of_forall_isSeparable
    (h : ∀ F : Submodule ℝ E, IsClosed (F : Set E) → TopologicalSpace.IsSeparable (F : Set E) →
      HasRadonNikodymProp F) :
    HasRadonNikodymProp E where
  exists_withDensityᵥ_eq' μ _ ν _ hν := by
    have := completeSpace_of_forall_isSeparable h
    -- `ν` has a bounded density with respect to its variation, which has a density w.r.t. `μ`
    obtain ⟨f, hf_sm, hf_norm, hf_eq⟩ : ∃ f : _ → E, StronglyMeasurable f ∧ (∀ ω, ‖f ω‖ ≤ 1) ∧
        ν.variation.withDensityᵥ f = ν :=
      exists_withDensityᵥ_eq_of_forall_exists_isDensityOn fun _ hm hm_cg ↦
        exists_isDensityOn_of_forall_isSeparable h
          (fun s _ ↦ ν.enorm_measure_le_variation s) hm hm_cg
    exact exists_integrable_withDensityᵥ_eq_of_variation hν hf_sm hf_norm hf_eq

end Separable

end HasRadonNikodymProp

section Reflexive

/-! ### Reflexive spaces -/

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} {ν : VectorMeasure Ω E}

/-- If a vector measure `ν` is dominated by a finite measure `μ` and `ψ` is a continuous linear
form, then the real measure `ψ ∘ ν` has a density with respect to `μ`. -/
private lemma exists_setIntegral_eq_strongDual_apply [IsFiniteMeasure μ]
    (hν : ∀ s, MeasurableSet s → ‖ν s‖ₑ ≤ μ s) (ψ : StrongDual ℝ E) :
    ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
      ∀ s, MeasurableSet s → ∫ ω in s, g ω ∂μ = ψ (ν s) := by
  let νψ : SignedMeasure Ω := ν.mapRange (ψ : E →+ ℝ) ψ.continuous
  have h_ac : νψ ≪ᵥ μ.toENNRealVectorMeasure := fun s hs ↦ by
    change ψ (ν s) = 0
    rw [VectorMeasure.absolutelyContinuous_of_forall_enorm_le hν hs, map_zero]
  refine ⟨νψ.rnDeriv μ, νψ.measurable_rnDeriv μ, νψ.integrable_rnDeriv μ, fun s hs ↦ ?_⟩
  rw [← withDensityᵥ_apply (νψ.integrable_rnDeriv μ) hs, νψ.withDensityᵥ_rnDeriv_eq μ h_ac]
  rfl

/-- If the norm of a linear combination of the reals `g i` is bounded by the norm of the same
linear combination of the linear forms `φ i` for all rational coefficients, then this holds for
all real coefficients. -/
private lemma norm_linearCombination_le_of_forall_rat {ι : Type*} {φ : ι → StrongDual ℝ E}
    {g : ι → ℝ}
    (h : ∀ (s : Finset ι) (q : s → ℚ), |∑ i, (q i : ℝ) * g i| ≤ ‖∑ i, (q i : ℝ) • φ i‖)
    (c : ι →₀ ℝ) :
    ‖Finsupp.linearCombination ℝ g c‖ ≤ ‖Finsupp.linearCombination ℝ φ c‖ := by
  have h_closed : IsClosed {a : c.support → ℝ | |∑ i, a i * g i| ≤ ‖∑ i, a i • φ i‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have h_dense : DenseRange (Pi.map fun (_ : c.support) (q : ℚ) ↦ (q : ℝ)) :=
    DenseRange.piMap fun _ ↦ Rat.denseRange_cast
  have h_mem : |∑ i : c.support, c i * g i| ≤ ‖∑ i : c.support, c i • φ i‖ :=
    h_closed.closure_subset_iff.2 (by rintro _ ⟨q, rfl⟩; exact h _ q) (h_dense fun i ↦ c i)
  rwa [Finset.sum_coe_sort c.support fun i ↦ c i * g i,
    Finset.sum_coe_sort c.support fun i ↦ c i • φ i] at h_mem

/-- **Radon-Nikodym theorem** for a vector measure with values in a separable reflexive space,
dominated by a finite measure. -/
private theorem exists_withDensityᵥ_eq_of_separableSpace [SeparableSpace E]
    [StrongDual.IsReflexive ℝ E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : VectorMeasure Ω E) (hν : ∀ s, MeasurableSet s → ‖ν s‖ₑ ≤ μ s) :
    ∃ f : Ω → E, StronglyMeasurable f ∧ (∀ ω, ‖f ω‖ ≤ 1) ∧ μ.withDensityᵥ f = ν := by
  have := StrongDual.IsReflexive.completeSpace ℝ E
  -- `φ` is a sequence of continuous linear forms which separates the points of `E`, and `g k` is
  -- a density of the real measure `φ k ∘ ν` with respect to `μ`
  have hE_sep : TopologicalSpace.IsSeparable (Set.univ : Set E) := .of_separableSpace _
  obtain ⟨φ, hφ⟩ := hE_sep.exists_seq_strongDual_eq_zero_of_forall_apply_eq_zero ℝ
  choose g hg_meas hg_int hg_eq using fun k ↦ exists_setIntegral_eq_strongDual_apply hν (φ k)
  -- almost everywhere, the linear combinations of the `g k` with rational coefficients are bounded
  -- by the norms of the same linear combinations of the `φ k`
  let G : Set Ω :=
    {ω | ∀ (s : Finset ℕ) (q : s → ℚ), |∑ i, (q i : ℝ) * g i ω| ≤ ‖∑ i, (q i : ℝ) • φ i‖}
  have hG_meas : MeasurableSet G := by
    simp only [G, Set.ofPred_forall]
    exact .iInter fun s ↦ .iInter fun q ↦ measurableSet_le (by fun_prop) measurable_const
  have hG_ae : ∀ᵐ ω ∂μ, ω ∈ G := by
    refine ae_all_iff.2 fun s ↦ ae_all_iff.2 fun q ↦ ?_
    have h_int : Integrable (fun ω ↦ ∑ i, (q i : ℝ) * g i ω) μ :=
      integrable_finsetSum _ fun i _ ↦ (hg_int i).const_mul _
    refine ae_abs_le_of_forall_abs_setIntegral_le (fun _ _ _ ↦ h_int.integrableOn) fun t ht _ ↦ ?_
    have h_eq : ∫ ω in t, ∑ i, (q i : ℝ) * g i ω ∂μ = (∑ i, (q i : ℝ) • φ i) (ν t) := by
      rw [integral_finsetSum (f := fun (i : s) ω ↦ (q i : ℝ) * g i ω) _
        fun i _ ↦ ((hg_int i).const_mul _).integrableOn]
      simp [integral_const_mul, hg_eq _ t ht]
    rw [h_eq, ← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    gcongr
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono (measure_ne_top μ t) (hν t ht)
  -- by Helly's theorem, there is a point `f ω` such that `φ k (f ω) = g k ω` for all `k`
  have h_exists (ω : Ω) : ∃ y : E, ‖y‖ ≤ 1 ∧ ∀ k, φ k y = G.indicator (g k) ω := by
    by_cases hω : ω ∈ G
    · simpa only [Set.indicator_of_mem hω] using exists_norm_le_one_forall_apply_eq φ (g · ω)
        (norm_linearCombination_le_of_forall_rat hω)
    · exact ⟨0, by simp, fun k ↦ by simp [hω]⟩
  choose f hf_norm hf_φ using h_exists
  -- `f` is measurable since the forms `φ k` separate the points of the Polish space `E`
  borelize E
  have hf_meas : Measurable f := by
    have hΦ : MeasurableEmbedding fun (y : E) (k : ℕ) ↦ φ k y := by
      refine Continuous.measurableEmbedding (by fun_prop) fun y z hyz ↦
        sub_eq_zero.1 (hφ _ (Set.mem_univ _) ?_)
      exact fun k ↦ by rw [map_sub, sub_eq_zero, congrFun hyz k]
    refine hΦ.measurable_comp_iff.1 (measurable_pi_iff.2 fun k ↦ ?_)
    simpa only [Function.comp_def, hf_φ] using (hg_meas k).indicator hG_meas
  have hf_int : Integrable f μ := .of_bound hf_meas.aestronglyMeasurable 1 (ae_of_all _ hf_norm)
  refine ⟨f, hf_meas.stronglyMeasurable, hf_norm, ?_⟩
  ext s hs
  rw [withDensityᵥ_apply hf_int hs]
  refine sub_eq_zero.1 (hφ _ (Set.mem_univ _) fun k ↦ ?_)
  rw [map_sub, sub_eq_zero, ← (φ k).integral_comp_comm hf_int.integrableOn, ← hg_eq k s hs]
  refine setIntegral_congr_ae hs ?_
  filter_upwards [hG_ae] with ω hω _
  rw [hf_φ, Set.indicator_of_mem hω]

end MeasureTheory

namespace HasRadonNikodymProp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A separable reflexive Banach space has the Radon-Nikodym property. -/
private theorem of_separableSpace_of_isReflexive [SeparableSpace E] [StrongDual.IsReflexive ℝ E] :
    HasRadonNikodymProp E where
  exists_withDensityᵥ_eq' μ _ ν _ hν := by
    -- `ν` has a bounded density with respect to its variation, which has a density w.r.t. `μ`
    obtain ⟨f, hf_sm, hf_norm, hf_eq⟩ := exists_withDensityᵥ_eq_of_separableSpace ν.variation ν
      fun s _ ↦ ν.enorm_measure_le_variation s
    exact exists_integrable_withDensityᵥ_eq_of_variation hν hf_sm hf_norm hf_eq

/-- A reflexive space has the Radon-Nikodym property. In particular, a real Hilbert space has the
Radon-Nikodym property, by `InnerProductSpace.isReflexive`. -/
instance (priority := 100) of_isReflexive [StrongDual.IsReflexive ℝ E] : HasRadonNikodymProp E := by
  -- the closed separable subspaces of `E` are reflexive
  refine of_forall_isSeparable fun F hF hF_sep ↦ ?_
  have := hF_sep.separableSpace
  have := StrongDual.IsReflexive.submodule_of_isClosed F hF
  exact of_separableSpace_of_isReflexive

/-- A complex Hilbert space has the Radon-Nikodym property. -/
instance of_complexInnerProductSpace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : HasRadonNikodymProp H :=
  letI : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  inferInstance

end HasRadonNikodymProp

end Reflexive
