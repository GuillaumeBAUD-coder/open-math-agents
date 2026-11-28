import OMAStatements.S_oeis_a005379
import Mathlib

open PowerSeries

-- Sahand Saba's counterexample (OEIS A005379, Jan 14 2013) to Plouffe's g.f.: the coefficient of X^33
-- in gf * ((1 - X^8) * (1 - X)) is a(33) - a(32) - a(25) + a(24) = 20 - 20 - 16 + 15 = -1,
-- while the right side is a polynomial of degree 10.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a005379.main) := by
  intro h
  have a33 : OMA.S_oeis_a005379.a 33 = 20 := by decide +kernel
  have a32 : OMA.S_oeis_a005379.a 32 = 20 := by decide +kernel
  have a25 : OMA.S_oeis_a005379.a 25 = 16 := by decide +kernel
  have a24 : OMA.S_oeis_a005379.a 24 = 15 := by decide +kernel
  have e1 : OMA.S_oeis_a005379.gf * ((1 - X ^ 8) * (1 - X)) =
      OMA.S_oeis_a005379.gf * X ^ 0 - OMA.S_oeis_a005379.gf * X ^ 1
        - OMA.S_oeis_a005379.gf * X ^ 8 + OMA.S_oeis_a005379.gf * X ^ 9 := by
    ring
  have e2 : (X : PowerSeries ℤ) ^ 2 * (1 + X ^ 3 + X ^ 6 + X + X ^ 4 + X ^ 7 - X ^ 8) =
      X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 8 + X ^ 9 - X ^ 10 := by
    ring
  rw [e1, e2] at h
  have hc := congrArg (coeff 33) h
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_X_pow] at hc
  norm_num [OMA.S_oeis_a005379.gf, coeff_mk, a33, a32, a25, a24] at hc
