import OMAReductions.R_Constant7a_c7a_lt_14_797075_R2

-- Step Constant7a.c7a_lt_14_797075.R2.H2
-- Credit: @arindale, reusing the square-and-divide-by-six transfer of the c7a_le_42 proof.

open Real Filter
open scoped Topology

theorem OMA.solution : OMA.R_Constant7a_c7a_lt_14_797075_R2.H2 := by
  intro p hp h
  have hsq : LiouvilleWith (p / 2) (π ^ 2) := by
    obtain ⟨C, hC0, hfreq⟩ := h.exists_pos
    refine ⟨(2 * π + C) * C, ?_⟩
    have hsq_tendsto : Tendsto (fun n : ℕ => n ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num)
    refine hsq_tendsto.frequently (hfreq.mono ?_)
    rintro n ⟨hn1, m, hne, hlt⟩
    refine ⟨m ^ 2, ?_, ?_⟩
    · intro heq
      have h1 : (π - (m : ℝ) / n) * (π + (m : ℝ) / n) = 0 := by
        push_cast at heq
        have : ((m : ℝ) / n) ^ 2 = (m : ℝ) ^ 2 / (n : ℝ) ^ 2 := div_pow _ _ 2
        linarith
      rcases mul_eq_zero.1 h1 with hsub | hadd
      · exact hne (sub_eq_zero.1 hsub)
      · exact irrational_pi ⟨((-m : ℤ) : ℚ) / (n : ℚ), by
          push_cast
          have : (-(m : ℝ)) / (n : ℝ) = -((m : ℝ) / (n : ℝ)) := neg_div _ _
          linarith⟩
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
      have hnpow1 : (1 : ℝ) ≤ (n : ℝ) ^ p :=
        Real.one_le_rpow (by exact_mod_cast hn1) hp
      have hdiffC : |π - (m : ℝ) / n| < C := by
        calc |π - (m : ℝ) / n| < C / (n : ℝ) ^ p := hlt
          _ ≤ C / 1 := div_le_div_of_nonneg_left hC0.le zero_lt_one hnpow1
          _ = C := div_one C
      have hsum_bd : |π + (m : ℝ) / n| ≤ 2 * π + C := by
        have hrew : π + (m : ℝ) / n = 2 * π - (π - (m : ℝ) / n) := by ring
        rw [hrew]
        calc |2 * π - (π - (m : ℝ) / n)|
            ≤ |2 * π| + |π - (m : ℝ) / n| := abs_sub _ _
          _ = 2 * π + |π - (m : ℝ) / n| := by rw [abs_of_pos (by positivity)]
          _ ≤ 2 * π + C := by linarith
      have hdiff_sq : π ^ 2 - ((m ^ 2 : ℤ) : ℝ) / ((n ^ 2 : ℕ) : ℝ) =
          (π + (m : ℝ) / n) * (π - (m : ℝ) / n) := by
        push_cast; field_simp [hnpos.ne']; ring
      rw [hdiff_sq, abs_mul]
      have hden_eq : (((n ^ 2 : ℕ) : ℝ)) ^ (p / 2) = (n : ℝ) ^ p := by
        push_cast
        rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul hnpos.le]
        congr 1; ring
      rw [hden_eq, mul_div_assoc]
      calc |π + (m : ℝ) / n| * |π - (m : ℝ) / n|
          ≤ (2 * π + C) * |π - (m : ℝ) / n| :=
            mul_le_mul_of_nonneg_right hsum_bd (abs_nonneg _)
        _ < (2 * π + C) * (C / (n : ℝ) ^ p) :=
            mul_lt_mul_of_pos_left hlt (by positivity)
  have hmul := hsq.mul_rat (r := (1 / 6 : ℚ)) (by norm_num)
  simpa [div_eq_mul_inv] using hmul
