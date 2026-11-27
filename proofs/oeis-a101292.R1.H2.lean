import OMAReductions.R_oeis_a101292_R1

-- Step oeis-a101292.R1.H2: hypothesis H2 of reduction oeis-a101292.R1
-- Credit: @JamesSlash. Put u = log (x / 4e8) >= 0. Then log x < 20 + u (since exp 20 > 4e8) and
-- x = 4e8 * exp u >= 4e8 * (1 + u / 3) ^ 3, and 30442 * (20 + u) ^ 3 <= 3e8 * (1 + u / 3) ^ 3 for u >= 0.

theorem OMA.solution : OMA.R_oeis_a101292_R1.H2 := by
  intro x hx
  have hx0 : 0 < x := by linarith
  set u := Real.log (x / 400000000) with hu
  have hq : 1 < x / 400000000 := by rw [lt_div_iff₀ (by norm_num)]; linarith
  have hu0 : 0 ≤ u := (Real.log_pos hq).le
  have hexpu : Real.exp u = x / 400000000 := Real.exp_log (by linarith)
  have he20 : (400000000 : ℝ) < Real.exp 20 := by
    have h1 := Real.exp_one_gt_d9
    have h2 : Real.exp 20 = Real.exp 1 ^ 20 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    calc (400000000 : ℝ) < 2.7182818283 ^ 20 := by norm_num
      _ < Real.exp 1 ^ 20 := by gcongr
  have hlog : Real.log x < 20 + u := by
    have hsplit : Real.log x = Real.log (x / 400000000) + Real.log 400000000 := by
      rw [← Real.log_mul (by positivity) (by norm_num)]; congr 1; field_simp
    have hl4 : Real.log 400000000 < 20 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]; exact he20
    rw [hsplit]; linarith
  have hmax : max 10 (Real.log x) ≤ 20 + u := max_le (by linarith) hlog.le
  have hmax0 : 0 ≤ max 10 (Real.log x) := le_max_of_le_left (by norm_num)
  have hcube : (1 + u / 3) ^ 3 ≤ Real.exp u := by
    have h1 : u / 3 + 1 ≤ Real.exp (u / 3) := Real.add_one_le_exp (u / 3)
    have h2 : Real.exp u = Real.exp (u / 3) ^ 3 := by rw [← Real.exp_nat_mul]; congr 1; ring
    rw [h2]
    have h3 : 0 ≤ 1 + u / 3 := by linarith
    calc (1 + u / 3) ^ 3 ≤ (Real.exp (u / 3)) ^ 3 := by gcongr; linarith
      _ = Real.exp (u / 3) ^ 3 := rfl
  have hxe : x = 400000000 * Real.exp u := by rw [hexpu]; field_simp
  have hpoly : 30442 * (20 + u) ^ 3 ≤ 300000000 * (1 + u / 3) ^ 3 := by
    nlinarith [hu0, sq_nonneg u, mul_nonneg hu0 (sq_nonneg u)]
  calc 30442 * (max 10 (Real.log x)) ^ 3 ≤ 30442 * (20 + u) ^ 3 := by gcongr
    _ ≤ 300000000 * (1 + u / 3) ^ 3 := hpoly
    _ ≤ 300000000 * Real.exp u := by gcongr
    _ = 3 * x / 4 := by rw [hxe]; ring
