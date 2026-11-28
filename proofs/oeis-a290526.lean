import OMAStatements.S_oeis_a290526
import Mathlib

open OMA.S_oeis_a290526 PowerSeries

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a290526.main) := by
  intro h
  have hg := h.1
  have hr := h.2
  have hp : (((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) : PowerSeries ℤ) = 1 - X ^ 1 - C (110 : ℤ) * X ^ 2 + C (110 : ℤ) * X ^ 3 + C (1000 : ℤ) * X ^ 4 - C (1000 : ℤ) * X ^ 5 := by
    (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
  have hR : (1 - 10 * X ^ 2 + 1010 * X ^ 3 - 11100 * X ^ 4 + 110000 * X ^ 6 - 100000 * X ^ 7 : PowerSeries ℤ) = 1 - C (10 : ℤ) * X ^ 2 + C (1010 : ℤ) * X ^ 3 - C (11100 : ℤ) * X ^ 4 + C (110000 : ℤ) * X ^ 6 - C (100000 : ℤ) * X ^ 7 := by
    (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
  have hq : ∀ F : PowerSeries ℤ, F * (1 - X ^ 1 - C (110 : ℤ) * X ^ 2 + C (110 : ℤ) * X ^ 3 + C (1000 : ℤ) * X ^ 4 - C (1000 : ℤ) * X ^ 5) = F - (F * X ^ 1) - C (110 : ℤ) * (F * X ^ 2) + C (110 : ℤ) * (F * X ^ 3) + C (1000 : ℤ) * (F * X ^ 4) - C (1000 : ℤ) * (F * X ^ 5) := fun F => by ring
  rw [hp, hR, hq] at hg
  have e := congrArg (coeff 6) hg
  simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow,
    coeff_X_pow, coeff_one, coeff_C] at e
  norm_num at e
  have r := hr 6 (by norm_num)
  norm_num at r
  linarith
