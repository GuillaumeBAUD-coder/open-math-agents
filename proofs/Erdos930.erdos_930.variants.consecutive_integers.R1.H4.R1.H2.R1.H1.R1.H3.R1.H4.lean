import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1_H3_R1
import Mathlib

/-! Overlap of the two relative error terms. For y at most 50 the constant 1/40000000 times
5 y^4 is at most 0.79. For y above 50 the bound 50 y^7 is at most (4y/5)^40/40!, which is at
most exp (4y/5) by the exponential series, so 10 y^3 exp (-4y/5) times 5 y^4 is at most 1. -/

theorem OMA.solution : OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1_H3_R1.H4 := by
  intro y hy
  by_cases h : y ≤ 50
  · have h4 : y ^ 4 ≤ (50:ℝ) ^ 4 := pow_le_pow_left₀ hy h 4
    calc min (1/40000000:ℝ) (10*y^3*Real.exp (-(4/5)*y)) * (5*y^4)
        ≤ (1/40000000:ℝ) * (5*y^4) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ 1 := by nlinarith
  · push Not at h
    have hy0 : 0 < y := by linarith
    have hE : ((4/5:ℝ)*y)^40 / (Nat.factorial 40 : ℝ) ≤ Real.exp ((4/5)*y) :=
      Real.pow_div_factorial_le_exp (x := (4/5)*y) (hx := by positivity) (n := 40)
    have hfac : (Nat.factorial 40 : ℝ) = 815915283247897734345611269596115894272000000000 := by
      norm_num [Nat.factorial]
    have hy33 : (50:ℝ)^33 ≤ y^33 := pow_le_pow_left₀ (by norm_num) h.le 33
    have hy7 : 0 < y^7 := by positivity
    have hkey : 50 * y^7 ≤ ((4/5:ℝ)*y)^40 / (Nat.factorial 40 : ℝ) := by
      rw [hfac, le_div_iff₀ (by norm_num), mul_pow]
      have e : y^40 = y^7 * y^33 := by ring
      rw [e]
      have c : (50:ℝ) * 815915283247897734345611269596115894272000000000 ≤ (4/5:ℝ)^40 * 50^33 := by
        norm_num
      calc 50 * y^7 * 815915283247897734345611269596115894272000000000
          = y^7 * ((50:ℝ) * 815915283247897734345611269596115894272000000000) := by ring
        _ ≤ y^7 * ((4/5:ℝ)^40 * 50^33) := mul_le_mul_of_nonneg_left c hy7.le
        _ ≤ y^7 * ((4/5:ℝ)^40 * y^33) := by gcongr
        _ = (4/5:ℝ)^40 * (y^7 * y^33) := by ring
    have hexp : 50 * y^7 ≤ Real.exp ((4/5)*y) := hkey.trans hE
    have hpos : 0 < Real.exp ((4/5)*y) := Real.exp_pos _
    calc min (1/40000000:ℝ) (10*y^3*Real.exp (-(4/5)*y)) * (5*y^4)
        ≤ (10*y^3*Real.exp (-(4/5)*y)) * (5*y^4) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = 50 * y^7 / Real.exp ((4/5)*y) := by
          rw [neg_mul, Real.exp_neg]; field_simp; ring
      _ ≤ 1 := by rw [div_le_one hpos]; exact hexp
