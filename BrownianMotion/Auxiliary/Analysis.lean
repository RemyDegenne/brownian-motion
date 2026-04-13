module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section

attribute [simp] convex_empty
attribute [simp] convex_univ

@[nontriviality]
lemma convexOn_subsingleton {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [Subsingleton E] [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 E] [Module 𝕜 β] (s : Set E)
    (f : E → β) : ConvexOn 𝕜 s f := by
  constructor
  · exact Subsingleton.set_cases (by simp) (by simp) s
  · intro x hx y hy a b ha hb hab
    simp_rw [Subsingleton.eq_zero (α := E), ← add_smul, hab, one_smul]
    rfl

lemma convexOn_rpow_norm {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : E ↦ ‖x‖ ^ p) := by
  nontriviality E
  refine ConvexOn.comp (g := fun x ↦ x ^ p) ?_ convexOn_univ_norm ?_
  · refine (convexOn_rpow hp).subset ?_ ?_
    · rintro - ⟨y, -, rfl⟩
      simp
    rintro - ⟨x, -, rfl⟩ - ⟨y, -, rfl⟩ a b ha hb hab
    obtain hx | hx := eq_or_ne ‖x‖ 0
    · refine ⟨b • y, by simp, ?_⟩
      simp [hx, norm_smul, hb]
    · refine ⟨((a * ‖x‖ + b * ‖y‖) / ‖x‖) • x, by simp, ?_⟩
      simp only [norm_smul, norm_div, Real.norm_eq_abs, abs_norm, isUnit_iff_ne_zero, ne_eq, hx,
        not_false_eq_true, IsUnit.div_mul_cancel, smul_eq_mul, abs_eq_self]
      positivity
  · apply (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (by linarith)).mono
    rintro - ⟨x, -, rfl⟩
    simp
