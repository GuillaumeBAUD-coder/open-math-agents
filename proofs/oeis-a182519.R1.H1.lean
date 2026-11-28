import OMAReductions.R_oeis_a182519_R1
import Mathlib

/-! Analytic criterion for Firoozbakht's inequality.

With `x = (q - p) / p ≥ 0`, `q = p (1 + x)` and `(1 + x)^n ≤ (e^x)^n = e^(n x)`. The hypothesis
`n (q - p) < p log p` says `n x < log p`, so `e^(n x) < p` and
`q^n = p^n (1 + x)^n < p^n p = p^(n+1)`.
-/

namespace OMA.P_oeis_a182519_R1_H1

theorem firoozbakht_of_gap (n p q : ℕ) (hp : 2 ≤ p) (hpq : p ≤ q)
    (hg : (n : ℝ) * ((q : ℝ) - p) < p * Real.log p) : q ^ n < p ^ (n + 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  set x : ℝ := ((q : ℝ) - p) / p with hx
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hx0 : 0 ≤ x := div_nonneg (sub_nonneg.mpr hpq') hp0.le
  have hq : (q : ℝ) = p * (1 + x) := by rw [hx]; field_simp; ring
  have h1 : (1 + x) ^ n ≤ Real.exp (n * x) := by
    calc (1 + x) ^ n ≤ (Real.exp x) ^ n := by
          apply pow_le_pow_left₀ (by linarith)
          linarith [Real.add_one_le_exp x]
      _ = Real.exp (n * x) := by rw [← Real.exp_nat_mul]
  have h2 : Real.exp (n * x) < p := by
    have : (n : ℝ) * x < Real.log p := by
      rw [hx, mul_div_assoc', div_lt_iff₀ hp0]; linarith
    calc Real.exp (n * x) < Real.exp (Real.log p) := Real.exp_lt_exp.mpr this
      _ = p := Real.exp_log hp0
  have key : (q : ℝ) ^ n < (p : ℝ) ^ (n + 1) := by
    rw [hq, mul_pow, pow_succ]
    have hpn : (0 : ℝ) < (p : ℝ) ^ n := pow_pos hp0 n
    exact mul_lt_mul_of_pos_left (lt_of_le_of_lt h1 h2) hpn
  exact_mod_cast key

end OMA.P_oeis_a182519_R1_H1

theorem OMA.solution : OMA.R_oeis_a182519_R1.H1 :=
  fun n p q hp hpq hg => OMA.P_oeis_a182519_R1_H1.firoozbakht_of_gap n p q hp hpq hg
