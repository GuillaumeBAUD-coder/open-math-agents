import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1_H3_R1

-- Step H4: min(1/40000000, 10 y^3 exp(-4y/5)) * 5 y^4 is at most 1 for y at least 0.
-- Up to y = 53 the constant branch is enough. Beyond it, one term of the exponential series
-- bounds exp(4y/5) from below by (4y/5)^20 / 20!, which dominates 50 y^7.

theorem OMA.solution : OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1_H3_R1.H4 := by
  intro y hy
  rcases le_or_gt y 53 with h | h
  · calc min (1/40000000 : ℝ) (10 * y^3 * Real.exp (-(4/5) * y)) * (5 * y^4)
        ≤ (1/40000000 : ℝ) * (5 * y^4) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ (1/40000000 : ℝ) * (5 * 53^4) := by gcongr
      _ ≤ 1 := by norm_num
  · have key : 50 * y^7 ≤ Real.exp ((4/5) * y) := by
      refine le_trans ?_ (Real.pow_div_factorial_le_exp ((4/5) * y) (by positivity) 20)
      rw [le_div_iff₀ (by positivity)]
      have h13 : (53 : ℝ)^13 ≤ y^13 := pow_le_pow_left₀ (by norm_num) h.le 13
      have num : 50 * (Nat.factorial 20 : ℝ) ≤ (4/5 : ℝ)^20 * 53^13 := by
        norm_num [Nat.factorial]
      calc 50 * y^7 * (Nat.factorial 20 : ℝ)
          = (50 * (Nat.factorial 20 : ℝ)) * y^7 := by ring
        _ ≤ ((4/5 : ℝ)^20 * 53^13) * y^7 := mul_le_mul_of_nonneg_right num (by positivity)
        _ ≤ ((4/5 : ℝ)^20 * y^13) * y^7 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h13 (by positivity)) (by positivity)
        _ = ((4/5) * y)^20 := by ring
    calc min (1/40000000 : ℝ) (10 * y^3 * Real.exp (-(4/5) * y)) * (5 * y^4)
        ≤ (10 * y^3 * Real.exp (-(4/5) * y)) * (5 * y^4) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = (50 * y^7) * Real.exp (-(4/5) * y) := by ring
      _ ≤ Real.exp ((4/5) * y) * Real.exp (-(4/5) * y) :=
          mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
      _ = 1 := by
          rw [← Real.exp_add, show (4/5 : ℝ) * y + -(4/5) * y = 0 by ring, Real.exp_zero]
