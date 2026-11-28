import OMAStatements.S_oeis_a284181
import Mathlib

open OMA.S_oeis_a284181 PowerSeries

set_option maxRecDepth 10000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284181.main) := by
  intro h
  have hg := h.1
  have hr := h.2
  have hp : (((1 - X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2)) : PowerSeries ℤ) = 1 - X ^ 1 - C (16 : ℤ) * X ^ 4 + C (16 : ℤ) * X ^ 5 := by
    (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
  have hR : (1 + X + 3 * X ^ 2 + 5 * X ^ 3 - 3 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 4 * X ^ 7 + 2 * X ^ 8 + X ^ 9 + X ^ 10 + 16 * X ^ 13 - 16 * X ^ 14 : PowerSeries ℤ) = 1 + X ^ 1 + C (3 : ℤ) * X ^ 2 + C (5 : ℤ) * X ^ 3 - C (3 : ℤ) * X ^ 4 + C (8 : ℤ) * X ^ 5 - C (8 : ℤ) * X ^ 6 + C (4 : ℤ) * X ^ 7 + C (2 : ℤ) * X ^ 8 + X ^ 9 + X ^ 10 + C (16 : ℤ) * X ^ 13 - C (16 : ℤ) * X ^ 14 := by
    (try simp only [map_ofNat, map_one, one_mul, pow_one]) <;> ring
  have hq : ∀ F : PowerSeries ℤ, F * (1 - X ^ 1 - C (16 : ℤ) * X ^ 4 + C (16 : ℤ) * X ^ 5) = F - (F * X ^ 1) - C (16 : ℤ) * (F * X ^ 4) + C (16 : ℤ) * (F * X ^ 5) := fun F => by ring
  rw [hp, hR, hq] at hg
  have e := congrArg (coeff 13) hg
  simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow,
    coeff_X_pow, coeff_one, coeff_C] at e
  simp (disch := decide) only [if_pos, if_neg, Nat.reduceSub, Int.reduceMul, Int.reduceAdd, Int.reduceNeg, mul_zero, sub_zero, add_zero, zero_add, mul_one] at e
  have r := hr 13 (by norm_num)
  simp only [Nat.reduceSub] at r
  linarith
