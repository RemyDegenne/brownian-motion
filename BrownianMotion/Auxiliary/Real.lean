import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Real

lemma inv_rpow_logb {b : ℝ} (hb : 0 < b) (hb' : b ≠ 1) {x : ℝ} (hx : 0 < x) :
    b⁻¹ ^ Real.logb b x = x⁻¹ := by
  rw [inv_eq_one_div, Real.div_rpow (by norm_num) (le_of_lt hb)]
  simpa using Real.rpow_logb hb hb' hx

end Real
