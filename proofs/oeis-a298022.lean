import OMAStatements.S_oeis_a298022
import Mathlib

open PowerSeries

-- OEIS A298022: Colin Barker's g.f. and his recurrence contradict each other. The g.f.
-- (1+2x+4x^2+4x^3+3x^4+2x^5-2x^8)/((1-x)^2 (1+x+x^2)) gives, at the coefficient of x^8,
-- a(8) - a(7) - a(5) + a(4) = -2, while the recurrence for n > 5 says this combination is 0
-- at n = 8. (The entry's data 1, 3, 7, 12, 17, 23, 28, 33, 37 agree with the g.f.; the
-- recurrence holds only from n = 9 on.)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a298022.main) := by
  intro h
  obtain ⟨hg, hr, -⟩ := h
  have r8 : OMA.S_oeis_a298022.a 8 = OMA.S_oeis_a298022.a 7 + OMA.S_oeis_a298022.a 5
      - OMA.S_oeis_a298022.a 4 :=
    hr 8 (by norm_num)
  have e1 : PowerSeries.mk OMA.S_oeis_a298022.a * ((1 - X) ^ 2 * (1 + X + X ^ 2)) =
      PowerSeries.mk OMA.S_oeis_a298022.a * X ^ 0 - PowerSeries.mk OMA.S_oeis_a298022.a * X ^ 1
      - PowerSeries.mk OMA.S_oeis_a298022.a * X ^ 3
      + PowerSeries.mk OMA.S_oeis_a298022.a * X ^ 4 := by
    ring
  have e2 : (1 + 2 * X + 4 * X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 8 : PowerSeries ℤ) =
      1 + X + X + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 3 + X ^ 3 + X ^ 3 + X ^ 3
        + X ^ 4 + X ^ 4 + X ^ 4 + X ^ 5 + X ^ 5 - X ^ 8 - X ^ 8 := by
    ring
  have hc := congrArg (coeff 8) hg
  simp only [e1, e2] at hc
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_X, coeff_mk] at hc
  norm_num at hc
  omega
