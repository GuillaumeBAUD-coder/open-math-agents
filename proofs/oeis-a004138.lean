import OMAStatements.S_oeis_a004138

-- Problem: A004138: From a counter moving problem.
-- Upstream: formal-conjectures statements/oeis-a004138.lean:0 (declaration OMA.S_oeis_a004138.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Subtracting two consecutive instances of the defining recurrence gives the homogeneous recurrence
a(n) = 2 a(n-1) - 2 a(n-3) + 3 a(n-4) - 2 a(n-5) for n ≥ 6. The denominator is
(z-1)(2z^4 - z^3 + z^2 + z - 1) = 1 - 2z + 2z^3 - 3z^4 + 2z^5, so the coefficient of z^k in the product is
a(k+1) - 2 a(k) + 2 a(k-2) - 3 a(k-3) + 2 a(k-4), which is 1, 0, -1, 4, -2 for k = 0, ..., 4 and 0
otherwise. -/

namespace A004138Aux

open OMA.S_oeis_a004138 PowerSeries

theorem a_step (k : ℕ) : a (k + 5) = a (k + 4) + a (k + 3) - a (k + 2) + 2 * a (k + 1) + 2 := by
  rw [a]

theorem a1 : a 1 = 1 := by rw [a]

theorem a2 : a 2 = 2 := by rw [a]

theorem a3 : a 3 = 3 := by rw [a]

theorem a4 : a 4 = 8 := by rw [a]

theorem a5 : a 5 = 13 := by
  have h := a_step 0
  simp [a1, a2, a3, a4] at h
  linarith

theorem rec5 (m : ℕ) : a (m + 6) = 2 * a (m + 5) - 2 * a (m + 3) + 3 * a (m + 2) - 2 * a (m + 1) := by
  have h1 := a_step (m + 1)
  have h0 := a_step m
  linear_combination h1 - h0

theorem gfC : PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * C 1 +
    PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * X * C (-2) +
    PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * X * X * X * C 2 +
    PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * X * X * X * X * C (-3) +
    PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * X * X * X * X * X * C 2 =
    (1 : ℚ⟦X⟧) * C 1 + (1 : ℚ⟦X⟧) * X * X * C (-1) + (1 : ℚ⟦X⟧) * X * X * X * C 4 +
      (1 : ℚ⟦X⟧) * X * X * X * X * C (-2) := by
  ext n
  cases n with
  | zero =>
    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
    simp [a1]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
        PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
      simp [a1, a2]
    | succ n =>
      cases n with
      | zero =>
        simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
          PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
        simp [a2, a3]
        norm_num
      | succ n =>
        cases n with
        | zero =>
          simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
            PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
          simp [a1, a3, a4]
          norm_num
        | succ n =>
          cases n with
          | zero =>
            simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
              PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
            simp [a1, a2, a4, a5]
            norm_num
          | succ m =>
            simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
              PowerSeries.coeff_mk]
            have h := rec5 m
            have hq : ((a (m + 6) : ℤ) : ℚ) = 2 * ((a (m + 5) : ℤ) : ℚ) - 2 * ((a (m + 3) : ℤ) : ℚ) +
                3 * ((a (m + 2) : ℤ) : ℚ) - 2 * ((a (m + 1) : ℤ) : ℚ) := by
              exact_mod_cast h
            simp [PowerSeries.coeff_one]
            linear_combination hq

end A004138Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a004138.main := by
  have h := A004138Aux.gfC
  simp only [map_ofNat, map_neg, map_one] at h
  linear_combination h
