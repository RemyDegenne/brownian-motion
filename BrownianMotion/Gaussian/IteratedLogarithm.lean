module

public import BrownianMotion.Gaussian.BrownianMotion
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.PSeries
public import Mathlib.Probability.BorelCantelli

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {X}

lemma IsBrownian.reflection (hX : IsBrownian X P) {t : ℝ≥0} {c : ℝ} (ht : 0 < t) (hc : 0 ≤ c) :
    P.real {ω | c ≤ ⨆ s ≤ t, (X s ω).toEReal} = 2 * P.real {ω | c ≤ X t ω} :=
  sorry -- needs strong Markov property

lemma IsStandardGaussian.tail (hX : HasLaw X (gaussianReal 0 1) P) :
    Asymptotics.IsEquivalent atTop (fun x ↦ P.real {ω | x ≤ X ω})
    (fun x ↦ 1 / x * (-1/2 * x ^ 2).exp) :=
  sorry -- exponential asymptotics of standard Gaussian CDF

private lemma IsBrownian.ae_limsup_div_sqrt_log_log_le_one (hX : IsBrownian X P) :
    ∀ᵐ ω ∂P, limsup (fun t ↦ ((X t ω) / (2 * t * (t : ℝ).log.log).sqrt).toEReal) atTop ≤ 1 := by
  -- Introduce notation
  haveI := (hX.hasLaw ∅).isProbabilityMeasure
  let M := fun t ω ↦ (⨆ s ≤ t, (X s ω : EReal))
  let f := fun (t : ℝ≥0) ↦ (2 * t * (t : ℝ).log.log).sqrt
  have fmono : MonotoneOn f (Set.Ici (⟨(Real.exp 1),by positivity⟩)) := by
    intro x hx y hy hxy
    have hx0 : (0 < x) := by apply lt_of_lt_of_le (Real.exp_pos _) hx
    have hx1 : (1 ≤ Real.log x) := by
      rwa [← Real.exp_le_exp, Real.exp_log (by positivity)]
    apply Real.sqrt_le_sqrt
    apply mul_le_mul (by bound) _ (Real.log_nonneg hx1) (by bound)
    apply Real.log_le_log (by positivity)
    apply Real.log_le_log hx0 hxy
  -- Rewrite limsup inequality in terms of quantifiers which do not depend on `ω`
  simp_rw [ae_le_const_iff_forall_gt_measure_zero, ← not_lt, ← ae_iff]
  suffices h : ∀ c : ℝ≥0, 1 < c → ∀ᵐ (ω : Ω) ∂P, ∀ᶠ (t : ℝ≥0) in atTop,
      X t ω < c * f t by
    intro _ hc
    rcases EReal.lt_iff_exists_real_btwn.mp hc with ⟨b,hb⟩
    lift b to ℝ≥0 using by positivity [by exact_mod_cast hb.1]
    filter_upwards [h b <| by exact_mod_cast hb.1] with _ hω
    apply lt_of_le_of_lt _ hb.2
    apply limsup_le_of_le (hf := by isBoundedDefault)
    filter_upwards [hω] with t ht
    apply EReal.coe_le_coe <| div_le_of_le_mul₀ (by positivity) (by positivity) _
    exact le_of_lt ht
  intro c hc
  -- Prepare for application of Borel-Cantellli
  suffices h : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ω ∉ {ω | (c : ℝ) * f (c ^ n) ≤ M (c ^ (n + 1)) ω} by
    filter_upwards [h] with ω hω
    -- Make a function which relates t to n
    choose n htn1 htn2 using
      fun t ↦ exists_nat_pow_near (x := max 1 t) (y := c) (by bound) (by bound)
    have h_tt1 : Tendsto (fun t ↦ n t) atTop atTop := by
      apply Tendsto.atTop_of_add_const 1
      rw [tendsto_atTop]; intro m
      filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (c ^ m)] with t ht1 ht2
      specialize htn2 t
      rw [max_eq_right ht1] at htn2
      rw [← pow_le_pow_iff_right₀ (hc)]
      apply le_of_lt <| lt_of_le_of_lt ht2 htn2
    have h_tt2 := (tendsto_pow_atTop_atTop_of_one_lt hc).comp h_tt1
    filter_upwards [h_tt1.eventually hω, eventually_ge_atTop 1,
      h_tt2.eventually_ge_atTop ⟨(Real.exp 1),by positivity⟩] with t ht ht1 htn3
    specialize htn1 t
    specialize htn2 t
    rw [max_eq_right ht1] at htn1 htn2
    exact_mod_cast calc
      X t ω ≤ M (c ^ (n t + 1)) ω := le_iSup_of_le t <| le_iSup_of_le (by bound) (by rfl)
      _ < (c * f (c ^ (n t))) := by simpa using ht
      _ ≤ (c : ℝ) * (f t) := by
        apply mul_le_mul_of_nonneg_left _ <| le_of_lt <| by positivity
        apply EReal.coe_le_coe <| fmono htn3 (le_trans htn3 htn1) htn1
  apply ae_eventually_notMem
  conv in P _ => rw [← ofReal_measureReal]
  conv in P.real _ => rw [← EReal.coe_mul, hX.reflection (by positivity) (by positivity)]
  apply Summable.tsum_ofReal_ne_top
  rw [summable_mul_left_iff (by norm_num)]
  -- introduce auxiliary function g and show limit at infinity
  let g := fun n : ℕ ↦ (2 * c * ((c : ℝ) ^ n).log.log).sqrt
  have hg_tt : Tendsto g atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    apply Tendsto.const_mul_atTop (by positivity)
    repeat apply Real.tendsto_log_atTop.comp
    exact tendsto_pow_atTop_atTop_of_one_lt hc
  -- convert to standard Gaussian
  apply Summable.congr (f := fun n ↦ P.real {ω | g n ≤ X 1 ω}); swap
  · intro n
    simp_rw [Measure.real_def]
    rw [ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    have h : IdentDistrib (fun ω ↦ ((c : ℝ) ^ (n + 1)).sqrt * X 1 ω) (X (c ^ (n + 1))) P P := by
      apply IdentDistrib.symm
      apply (hX.hasLaw_eval _).identDistrib
      convert gaussianReal_const_mul (hX.hasLaw_eval _) _
      · norm_num
      · aesop
    convert h.measure_mem_eq (s := {x | _ ≤ (x : ℝ)}) _
    · simp_rw [Set.preimage_setOf_eq]
      congr! 2
      rw [← mul_le_mul_iff_of_pos_left (by positivity : 0 < ((c : ℝ) ^ (n + 1)).sqrt)]
      congr! 1
      rw [← Real.sqrt_sq (by positivity : 0 ≤ (c : ℝ))]
      repeat rw [← Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_sq (by positivity), pow_add]
      push_cast
      field_simp
    · measurability
  apply summable_of_isBigO_nat <| Real.summable_nat_rpow_inv.2 hc
  -- apply Gaussian tail estimate
  have h := (IsStandardGaussian.tail (hX.hasLaw_eval 1)).comp_tendsto hg_tt
  apply Asymptotics.IsEquivalent.trans_isBigO h _
  -- reduce to concrete bound
  apply Asymptotics.IsBigO.of_bound <| 1 * ((Real.log c) ^ (c : ℝ))⁻¹
  filter_upwards [hg_tt.eventually_ge_atTop 1, eventually_ge_atTop 1] with n hg1 hn
  simp_rw [Function.comp_def]
  repeat rw [Real.norm_of_nonneg (by positivity)]
  conv_rhs => rw [mul_assoc]
  apply mul_le_mul _ _ (by positivity) (by norm_num)
  · rw [one_div_le _ (by norm_num)]; swap
    · bound
    · bound
  · rw [Real.sq_sqrt]; swap
    · positivity [Real.one_le_sqrt.mp hg1]
    field_simp
    conv in Real.exp _ => rw [mul_comm]
    rw [Real.exp_neg, Real.exp_mul, Real.exp_log, Real.log_pow]; swap
    · rw [Real.log_pow]
      positivity [Real.log_pos hc]
    rw [Real.mul_rpow (by positivity) _]; swap
    · exact Real.log_nonneg <| le_of_lt hc
    field_simp; rfl

private lemma IsBrownian.ae_one_le_limsup_div_sqrt_log_log (hX : IsBrownian X P)
    (h_meas : ∀ t, Measurable (X t)) :
    ∀ᵐ ω ∂P, 1 ≤ limsup (fun t ↦ (X t ω) / (2 * t * (t : ℝ).log.log).sqrt : ℝ≥0 → EReal) atTop := by
  haveI := (hX.hasLaw ∅).isProbabilityMeasure
  let f := fun (t : ℝ≥0) ↦ (2 * t * (t : ℝ).log.log).sqrt
  -- Rewrite the inequality into a nice form with the quantifier outside
  suffices h : ∀ (c : ℝ), 1 < c → 1 < Real.log c → ∀ᵐ ω ∂P, (1 - 1 / c).sqrt - (1 / c.sqrt : ℝ) ≤
      limsup (fun t ↦ (X t ω) / (f t) : ℝ≥0 → EReal) atTop by
    simp_rw [ae_const_le_iff_forall_lt_measure_zero, ← not_lt, ← ae_iff]
    have h' : Tendsto (fun (r : ℝ) ↦ (1 - 1 / r).sqrt - (1 / r.sqrt)) atTop (nhds 1) := by
      rw [(by simp : nhds (1 : ℝ) = nhds (Real.sqrt (1 - 0) - 0))]
      apply Tendsto.sub
      · apply Tendsto.sqrt
        apply Tendsto.sub (by aesop)
        apply Tendsto.const_div_atTop <| tendsto_id
      · apply Tendsto.const_div_atTop <| Real.tendsto_sqrt_atTop
    intro c hc1
    wlog! hc0 : (0 < c) generalizing c with h
    · replace h := fun (c : ℝ) ↦ h c
      specialize h (1/2) (?_) (by norm_num)
      · apply EReal.coe_lt_coe; bound
      exact h.mono fun _ hω ↦ lt_trans (lt_of_le_of_lt hc0 (by norm_num)) hω
    · lift c to ℝ using by aesop;; norm_cast at hc0 hc1
      apply (eventually_const (f := atTop (α := ℝ))).1
      filter_upwards [eventually_gt_atTop 1, Real.tendsto_log_atTop.eventually_gt_atTop 1,
      Eventually.of_forall h, h'.eventually <| lt_mem_nhds <| hc1] with r hr1 hlogr hrimp hrc
      filter_upwards [hrimp hr1 hlogr] with ω hω
      exact lt_of_lt_of_le (by exact_mod_cast hrc) hω
  intro c hc1 hlogc
  have hloglogc := Real.log_pos hlogc
  lift c to ℝ≥0 using by positivity
  have hc0 : (0 < c) := by positivity [by exact_mod_cast hc1]
  -- Rewrite in terms of limsup of difference
  suffices h1 : ∀ᵐ ω ∂P, (1 - 1 / (c : ℝ)).sqrt ≤
      limsup (fun t ↦ ((X t ω - X (t / c) ω) / f t).toEReal) atTop by
    have h2 : ∀ᵐ ω ∂P,
        limsup (fun t ↦ (-X (t / c) ω / f (t)).toEReal) atTop
          ≤ (1 / (c : ℝ).sqrt).toEReal := by
      convert IsBrownian.ae_limsup_div_sqrt_log_log_le_one
        (X := fun t ω ↦ (c : ℝ).sqrt * (-X (t / c) ω)) _ using 1
      · funext ω
        simp_rw [← mul_div, EReal.coe_mul]
        rw [EReal.limsup_const_mul_of_nonneg_of_ne_top (by positivity) (by aesop)]
        rw [mul_comm, ← EReal.le_div_iff_mul_le (by positivity) (by aesop)]
        rfl
      · convert hX.neg.smul (c := (1 / c)) (by positivity) using 3 with t
        simp; field_simp
    filter_upwards [h1, h2] with ω hω hω'
    simp_rw [neg_div, EReal.coe_neg, ← Pi.neg_def, EReal.limsup_neg, EReal.neg_le] at hω'
    grw [sub_eq_add_neg, (add_le_add hω hω'), EReal.le_limsup_add]
    apply le_of_eq
    simp_rw [← EReal.coe_div, ← div_sub_div_same,
      EReal.coe_sub, Pi.add_def]
    norm_cast; aesop
  -- auxiliary definitions
  let g := fun (n : ℕ) ↦ (2 * ((c : ℝ) ^ n).log.log).sqrt
  let A := fun n ↦ {ω | Real.sqrt (c ^ (n + 1) - c ^ n) * g (n + 1) ≤
    (X (c ^ (n + 1)) ω - X (c ^ n) ω)}
  -- prepare for application of Borel-Cantelli
  suffices h : P (limsup A atTop) = 1 by
    rw [← mem_ae_iff_prob_eq_one <| by measurability] at h
    filter_upwards [h] with ω hω
    rw [mem_limsup_iff_frequently_mem] at hω
    apply le_limsup_of_frequently_le'
    apply Tendsto.frequently_map _ (_ : Tendsto (fun n ↦ c ^ (n + 1)) atTop atTop) _ hω
    · simp_rw [pow_add]
      apply Tendsto.atTop_mul_const (by positivity)
      exact tendsto_pow_atTop_atTop_of_one_lt hc1
    intro n hn
    replace hn := hn.out
    unfold f A g at *; push_cast at *
    -- simple rewrite
    simp_rw [Real.log_pow, pow_add] at *; push_cast at *
    rw [EReal.coe_le_coe_iff, le_div_iff₀ <| Real.sqrt_pos_of_pos <| by bound]
    convert hn using 1
    · rw [← Real.sqrt_mul (by bound), ← Real.sqrt_mul' _ (by bound)]
      field_simp
    · field_simp
  apply ProbabilityTheory.measure_limsup_eq_one (by measurability)
  all_goals unfold A
  · -- show independence
    rw [iIndepSet_iff_iIndep]
    have h' := hX.hasIndepIncrements
    rw [hasIndepIncrements_iff_nat] at h'
    specialize h' (fun n ↦ c ^ n) _
    · apply pow_right_monotone <| le_of_lt <| by exact_mod_cast hc1
    rw [iIndepFun_iff_iIndep] at h'
    apply iIndep_of_iIndep_of_le h' _
    intro n
    apply MeasurableSpace.generateFrom_singleton_le <| measurableSet_le (by measurability) _
    apply Measurable.of_comap_le (by rfl)
  -- convert to sum of reals
  conv in P _ => rw [← ofReal_measureReal]
  simp_rw [← ENNReal.ofNNReal_toNNReal, ENNReal.tsum_coe_eq_top_iff_not_summable_coe,
    Real.coe_toNNReal (r := P.real _) (by positivity)]
  -- rewrite in terms of standard Gaussian
  suffices h : ¬(Summable (fun n ↦ P.real {ω | g n ≤ X 1 ω})) by
    rw [← summable_nat_add_iff 1 (G := ℝ)] at h
    convert h using 3 with n
    -- remove .real and max
    simp_rw [Measure.real_def]
    rw [ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    have h_idd : IdentDistrib
        (fun ω ↦ X (c ^ (n + 1)) ω - X (c ^ n) ω)
        (fun ω ↦ Real.sqrt (c ^ (n + 1) - c ^ n) * X 1 ω) P P := by
      apply (hX.hasLaw_sub _ _).identDistrib
      rw [max_eq_left]; swap
      · convert zero_le (α := ℝ≥0) _
        rw [NNReal.sub_def, Real.toNNReal_eq_zero, sub_nonpos]
        push_cast; bound
      convert gaussianReal_const_mul (hX.hasLaw_eval 1) _ using 2
      · norm_num
      rw [NNReal.eq_iff]; rify
      rw [Real.sq_sqrt (by bound), NNReal.coe_sub (by bound)]
      push_cast; field_simp
    -- use identical distribution to show probabilites are equal
    convert h_idd.measure_mem_eq (s := {x | _ ≤ (x : ℝ)}) _
    · simp_rw [Set.preimage_setOf_eq]
      congr! 2
      rw [← mul_le_mul_iff_of_pos_left _]
      rw [Real.sqrt_pos, sub_pos, pow_add]
      apply lt_mul_of_one_lt_right (by positivity) (by bound)
    · measurability
  -- apply limit comparison test
  rw [Asymptotics.IsEquivalent.summable_iff_nat
      (g := fun n ↦ (1 / (g n)) * ((1 / n) * (1 / Real.log c)))]; swap
  · -- show asymptotic equivalence
    apply ((IsStandardGaussian.tail <| hX.hasLaw_eval 1).comp_tendsto _).trans_eventuallyEq
    · unfold g; simp_rw [Function.comp_def]
      filter_upwards [eventually_ge_atTop 1] with n hn; congr 1
      rw [Real.log_pow, Real.sq_sqrt (by bound)]; field_simp
      rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
    · apply Real.tendsto_sqrt_atTop.comp
      apply Tendsto.const_mul_atTop (by norm_num)
      repeat apply Real.tendsto_log_atTop.comp
      apply tendsto_pow_atTop_atTop_of_one_lt hc1
  -- show non-summability of elementary series
  -- get rid of constant
  simp_rw [← mul_assoc]
  rw [summable_mul_right_iff (by positivity)]
  -- apply Cauchy condensation test
  rw [← summable_condensed_iff_of_eventually_nonneg]; rotate_left
  · exact Eventually.of_forall (fun _ ↦ by positivity)
  · -- antitone side condition
    filter_upwards [eventually_gt_atTop 1] with n hn1
    apply mul_le_mul _ (by bound) (by positivity) (by positivity)
    unfold g; simp_rw [Real.log_pow]
    repeat rw [Real.log_mul (by positivity) (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply add_le_add_left
    apply Real.log_le_log (by positivity) (by bound)
  unfold g
  push_cast; field_simp
  -- apply limit comparison test again
  rw [Asymptotics.IsEquivalent.summable_iff_nat
    (g := fun k : ℕ ↦ 1 / (2 * Real.log 2).sqrt * (1 / Real.sqrt k))]
  · -- non-summability of p-series
    rw [summable_mul_left_iff (by positivity)]
    simp_rw [Real.sqrt_eq_rpow]
    rw [Real.summable_one_div_nat_rpow]
    norm_num
  -- asymptotic equivalence
  simp_rw [one_div_mul_one_div, Real.log_pow]
  apply Asymptotics.IsEquivalent.div (by rfl)
  apply Asymptotics.isEquivalent_of_tendsto_one
  rw [Pi.div_def]
  conv in _ / _ => rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_div (by bound),
    Real.log_mul (by positivity) (by positivity)]
  push_cast; simp_rw [Real.log_pow]; ring_nf
  simp_rw [(by simp : nhds 1 = nhds (Real.sqrt (1 + 0)))]
  apply Tendsto.sqrt
  apply Tendsto.add
  · apply Tendsto.congr' (f₁ := fun x ↦ 1) _ (by aesop)
    filter_upwards [eventually_gt_atTop 0] with n hn using by field_simp
  · field_simp
    apply Tendsto.const_div_atTop
    rw [tendsto_mul_const_atTop_iff_pos (tendsto_natCast_atTop_atTop)]
    positivity

lemma IsBrownian.ae_limsup_div_sqrt_log_log_eq_one (hX : IsBrownian X P) :
    ∀ᵐ ω ∂P, limsup (fun t ↦ (X t ω) / (2 * t * (t : ℝ).log.log).sqrt : ℝ≥0 → EReal) atTop = 1 := by
  haveI := (hX.hasLaw ∅).isProbabilityMeasure
  have h_up := IsBrownian.ae_limsup_div_sqrt_log_log_le_one hX.isBrownian_mk
  have h_low := IsBrownian.ae_one_le_limsup_div_sqrt_log_log hX.isBrownian_mk hX.measurable_mk
  have h_ae := hX.mk_ae_forall_eq
  filter_upwards [h_up, h_low, h_ae] with ω hω_up hω_low hω_ae
  convert eq_of_le_of_ge hω_up hω_low
  simp_rw [hω_ae]; rfl

end ProbabilityTheory
