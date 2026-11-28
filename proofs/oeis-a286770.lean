import OMAStatements.S_oeis_a286770
import Mathlib

open OMA.S_oeis_a286770 PowerSeries

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a286770.main) := by
  intro h
  have hg := h.1
  have hr := h.2.2.2
  have hp : (((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) : PowerSeries ℤ) = 1 - C (101 : ℤ) * X ^ 2 + C (100 : ℤ) * X ^ 4 := by
    (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
  have hR : (1 + 10 * X - 101 * X ^ 2 + 100 * X ^ 3 + 101 * X ^ 4 - 100 * X ^ 6 : PowerSeries ℤ) = 1 + C (10 : ℤ) * X ^ 1 - C (101 : ℤ) * X ^ 2 + C (100 : ℤ) * X ^ 3 + C (101 : ℤ) * X ^ 4 - C (100 : ℤ) * X ^ 6 := by
    (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
  have hq : ∀ F : PowerSeries ℤ, F * (1 - C (101 : ℤ) * X ^ 2 + C (100 : ℤ) * X ^ 4) = F - C (101 : ℤ) * (F * X ^ 2) + C (100 : ℤ) * (F * X ^ 4) := fun F => by ring
  rw [hp, hR, hq] at hg
  have e := congrArg (coeff 6) hg
  simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow,
    coeff_X_pow, coeff_one, coeff_C] at e
  norm_num at e
  have r := hr 6 (by norm_num)
  norm_num at r
  linarith
