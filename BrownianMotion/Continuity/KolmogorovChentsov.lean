/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Continuity.HasBoundedInternalCoveringNumber
import BrownianMotion.Continuity.IsKolmogorovProcess

/-!
# Kolmogorov-Chentsov theorem

-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  {X : T → Ω → E}
  {c : ℝ≥0∞} {d p q M β : ℝ≥0}
  {P : Measure Ω}

def constL (T : Type*) [PseudoEMetricSpace T] (c : ℝ≥0∞) (d p q β : ℝ≥0) : ℝ≥0∞ := sorry

lemma constL_lt_top : constL T c d p q β < ∞ := by
  sorry

theorem countable_kolmogorov_chentsov (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    (T' : Set T) (hT' : T'.Countable) :
    ∫⁻ ω, ⨆ (s) (t) (hs : s ∈ T') (ht : t ∈ T'),
        edist (X s ω) (X t ω) ^ (p : ℝ) / edist s t ^ (β * p : ℝ) ∂P
      ≤ M * constL T c d p q β := by
  sorry

end ProbabilityTheory
