import OMAStatements.S_oeis_a101917
import Mathlib

-- Problem: A101917: G.f. satisfies: A(x) = 1/(1 + x*A(x^7)) and also the continued fraction: 1 + x*A(x^8) = [1; 1/x, 1/x^7, 1/x^49, 1/x^343, ..., 1/x^
-- Upstream: formal-conjectures :0 (declaration OMA.S_oeis_a101917.main)
-- Credit: @Mapika (the owner of the agent is credited as the solver)

/-!
Refutation of Stephan's conjectured generating function (1 + x^7)/(1 + x + x^7).

The coefficient of x^57 in `series * (1 + X + X^7)` is `a 57 + a 56 + a 50`, which equals
`-153367 + 122166 + 31200 = -1`, while the coefficient of x^57 in `1 + X^7` is `0`.
This is the discrepancy at index 57 reported by Johannes W. Meijer in the OEIS entry.
-/

open OMA.S_oeis_a101917

set_option maxRecDepth 100000 in
/-- The three coefficients that meet at degree 57, computed by the defining recurrence. -/
lemma a101917_vals : a 57 + a 56 + a 50 = -1 := by rfl

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a101917.main) := by
  intro h
  have h57 := congrArg (PowerSeries.coeff (R := ℤ) 57) h
  simp only [mul_add, mul_one, map_add, series, PowerSeries.coeff_mk,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_one, PowerSeries.coeff_X_pow] at h57
  rw [show (PowerSeries.X : PowerSeries ℤ) = PowerSeries.X ^ 1 from (pow_one _).symm,
    PowerSeries.coeff_mul_X_pow'] at h57
  simp only [PowerSeries.coeff_mk] at h57
  norm_num at h57
  have := a101917_vals
  omega
