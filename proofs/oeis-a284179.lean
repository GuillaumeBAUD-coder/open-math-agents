import OMAStatements.S_oeis_a284179
import Mathlib

open OMA.S_oeis_a284179 PowerSeries

set_option maxRecDepth 10000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284179.main) := by
  intro h
  have hg := h.1
  have hr := h.2
  have hp : (((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2)) : PowerSeries ℤ) = 1 - X ^ 1 - C (10000 : ℤ) * X ^ 4 + C (10000 : ℤ) * X ^ 5 := by
    (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
  have hR : (1 + 9 * X + 91 * X ^ 2 + 909 * X ^ 3 - 899 * X ^ 4 + 1000 * X ^ 5 - 1000 * X ^ 6 + 900 * X ^ 7 + 90 * X ^ 8 + 9 * X ^ 9 + X ^ 10 + 10000 * X ^ 13 - 10000 * X ^ 14 : PowerSeries ℤ) = 1 + C (9 : ℤ) * X ^ 1 + C (91 : ℤ) * X ^ 2 + C (909 : ℤ) * X ^ 3 - C (899 : ℤ) * X ^ 4 + C (1000 : ℤ) * X ^ 5 - C (1000 : ℤ) * X ^ 6 + C (900 : ℤ) * X ^ 7 + C (90 : ℤ) * X ^ 8 + C (9 : ℤ) * X ^ 9 + X ^ 10 + C (10000 : ℤ) * X ^ 13 - C (10000 : ℤ) * X ^ 14 := by
    (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
  have hq : ∀ F : PowerSeries ℤ, F * (1 - X ^ 1 - C (10000 : ℤ) * X ^ 4 + C (10000 : ℤ) * X ^ 5) = F - (F * X ^ 1) - C (10000 : ℤ) * (F * X ^ 4) + C (10000 : ℤ) * (F * X ^ 5) := fun F => by ring
  rw [hp, hR, hq] at hg
  have e := congrArg (coeff 13) hg
  simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow,
    coeff_X_pow, coeff_one, coeff_C] at e
  simp (disch := decide) only [if_pos, if_neg, Nat.reduceSub, Int.reduceMul, Int.reduceAdd, Int.reduceNeg, mul_zero, sub_zero, add_zero, zero_add, mul_one] at e
  have r := hr 13 (by norm_num)
  simp only [Nat.reduceSub] at r
  linarith
