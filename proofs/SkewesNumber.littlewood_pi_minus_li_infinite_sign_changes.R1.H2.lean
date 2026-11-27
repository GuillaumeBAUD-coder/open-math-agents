import OMAReductions.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R1

-- Step SkewesNumber.littlewood_pi_minus_li_infinite_sign_changes.R1.H2
-- Credit: @caa1982

open Real

theorem OMA.solution : OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R1.H2 := by
  intro x hx
  let a : ℝ := (⌊x⌋₊ : ℝ)
  have ha3 : (3 : ℝ) ≤ a := by
    have : 3 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    dsimp only [a]
    exact_mod_cast this
  have hax : a ≤ x := Nat.floor_le (by linarith)
  have hxa1 : x < a + 1 := Nat.lt_floor_add_one x
  have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Icc 2 x) := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have hlog_ne : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    exact (continuousAt_const.div (Real.continuousAt_log (by linarith)) hlog_ne).continuousWithinAt
  have hint2a : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume 2 a :=
    (hcont.mono (Set.Icc_subset_Icc_right hax)).intervalIntegrable_of_Icc (by linarith)
  have hintax : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a x :=
    (hcont.mono (Set.Icc_subset_Icc_left (by linarith))).intervalIntegrable_of_Icc hax
  have hdiff : logIntegral x - logIntegral a = ∫ t in a..x, 1 / Real.log t := by
    unfold logIntegral
    have hadd := intervalIntegral.integral_add_adjacent_intervals hint2a hintax
    linarith
  rw [hdiff]
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num)))
  constructor
  · apply intervalIntegral.integral_nonneg hax
    intro t ht
    have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    positivity
  · have hle : (∫ t in a..x, 1 / Real.log t) ≤ ∫ t in a..x, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on hax hintax intervalIntegrable_const
      intro t ht
      have hlogt : 1 ≤ Real.log t := le_trans hlog3 (Real.log_le_log (by norm_num) (by linarith [ht.1]))
      rw [div_le_one (by linarith)]
      exact hlogt
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hle
    linarith
