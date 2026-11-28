import OMAReductions.R_mse_1426354_R1
import Mathlib

open OMA.S_mse_1426354 Real

theorem OMA.solution : OMA.R_mse_1426354_R1.H1 := by
  intro n hn hσ
  have he : exp 1 ≤ 11 / 4 := by linarith [exp_one_lt_d9]
  have hb (k : ℕ) : exp (k : ℝ) ≤ (11 / 4 : ℝ) ^ k := by
    simpa using (show exp ((k : ℝ) * 1) ≤ (11 / 4 : ℝ) ^ k by
      rw [exp_nat_mul]
      gcongr)
  have h8 : exp 8 ≤ ((n + 1 : ℕ) : ℝ) := by
    have := hb 8
    have hn' : (5040 : ℝ) ≤ n := by exact_mod_cast hn.le
    norm_num at this ⊢
    linarith
  have hh := log_add_one_le_harmonic n
  have hp : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlow := ((le_log_iff_exp_le hp).2 h8).trans hh
  have hlog : 2 ≤ log (harmonic n : ℝ) := by
    apply (le_log_iff_exp_le (by linarith : 0 < (harmonic n : ℝ))).2
    have := hb 2
    norm_num at this
    linarith
  have hex : ((n + 1 : ℕ) : ℝ) ≤ exp (harmonic n : ℝ) := (log_le_iff_le_exp hp).1 hh
  unfold tailTerm
  calc
    _ ≤ (2 : ℝ) * n := by exact_mod_cast hσ
    _ ≤ exp (harmonic n : ℝ) * log (harmonic n : ℝ) := by
      rw [mul_comm (2 : ℝ)]
      gcongr
      push_cast at hex
      linarith
