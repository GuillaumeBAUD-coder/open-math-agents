import OMAReductions.R_Erdos5_erdos_5_variants_hildebrand_maier_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

open Filter Real Asymptotics

theorem OMA.solution : OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1.H2 := by
  have small : (fun n : ℕ => log (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [small.bound (by norm_num : (0 : ℝ) < 1/16),
    eventually_ge_atTop 10] with n hn hten
  have hn10 : (10 : ℝ) ≤ n := by exact_mod_cast hten
  have hpos : 0 < log (n : ℝ) := log_pos (by linarith)
  simp only [Real.norm_eq_abs, abs_of_nonneg hpos.le, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] at hn
  have hlow := Nat.add_two_le_nth_prime n
  have hprime : n ≤ Nat.nth Nat.Prime n := by omega
  refine ⟨hpos, log_le_log (by positivity : (0 : ℝ) < n) (by exact_mod_cast hprime), ?_⟩
  let m := n ^ 2
  have hm : (m : ℝ) = (n : ℝ)^2 := by simp [m]
  have hmlog : log (m : ℝ) = 2 * log (n : ℝ) := by simp [hm, log_pow]
  have hmp : 0 < log (m : ℝ) := by rw [hmlog]; positivity
  have ha : (m : ℝ) + 1 ≤ 2 * (n : ℝ)^2 := by rw [hm]; nlinarith
  have hb := log_le_log (by positivity : 0 < (m : ℝ) + 1) ha
  rw [log_mul (by norm_num) (by positivity), log_pow] at hb
  have hcount : n < Nat.primeCounting m := by
    by_contra! h
    have hc : (Nat.primeCounting m : ℝ) ≤ n := by exact_mod_cast h
    have hcheb := (div_le_iff₀ hmp).mp (Chebyshev.pi_ge m)
    have hmul := mul_le_mul_of_nonneg_right hc hmp.le
    rw [hmlog] at hmul hcheb
    rw [hm] at hcheb hb
    have hhalf : 1/2 ≤ log 2 := by linarith [log_two_gt_d9]
    have hbig := mul_le_mul_of_nonneg_left hhalf (sq_nonneg (n : ℝ))
    have hsmall := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    norm_num1 at hb
    have hsub : (n : ℝ)^2 / 2 - (1 + n/8) ≤ (n : ℝ)^2 / 8 := by
      calc
        _ ≤ (n : ℝ)^2 * log 2 - log ((n : ℝ)^2 + 1) := by
          nlinarith only [hbig, hb, hn, log_two_lt_d9]
        _ ≤ _ := hcheb.trans (hmul.trans (by nlinarith only [hsmall]))
    nlinarith only [hsub, hn10, sq_nonneg ((n : ℝ) - 5)]
  have hnth : Nat.nth Nat.Prime n < m + 1 := Nat.nth_lt_of_lt_count hcount
  exact (log_le_log (by exact_mod_cast (by omega : 0 < Nat.nth Nat.Prime n))
    (by exact_mod_cast (by omega : Nat.nth Nat.Prime n ≤ m))).trans hmlog.le
