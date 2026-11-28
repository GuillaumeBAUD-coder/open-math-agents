import OMAStatements.S_oeis_a147821

-- Problem: A147821: Number of consistent sets of 5 irreflexive binary order relationships over n objects.
-- Upstream: formal-conjectures statements/oeis-a147821.lean:0 (declaration OMA.S_oeis_a147821.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The closed form is a polynomial of degree 10 in n, so its differences of order 11 vanish; this is
(2). For (1), the coefficient of x^n in (Sum a(k) x^k) (1 - x)^11 is the difference of order 11 of a at
n (with a(k) = 0 for k < 0), which is the corresponding coefficient of the numerator for n < 11 and 0
otherwise. -/

namespace A147821Aux

open OMA.S_oeis_a147821 PowerSeries

theorem rec (m : ℕ) : a (m + 11) = 11 * a (m + 10) - 55 * a (m + 9) + 165 * a (m + 8) - 330 * a (m + 7) + 462 * a (m + 6) - 462 * a (m + 5) + 330 * a (m + 4) - 165 * a (m + 3) + 55 * a (m + 2) - 11 * a (m + 1) + a (m) := by
  simp only [a]
  push_cast
  ring

theorem a0 : a 0 = 0 := by norm_num [a]
theorem a1 : a 1 = 0 := by norm_num [a]
theorem a2 : a 2 = 0 := by norm_num [a]
theorem a3 : a 3 = 0 := by norm_num [a]
theorem a4 : a 4 = 108 := by norm_num [a]
theorem a5 : a 5 = 6180 := by norm_num [a]
theorem a6 : a 6 = 83952 := by norm_num [a]
theorem a7 : a 7 = 601944 := by norm_num [a]
theorem a8 : a 8 = 2991576 := by norm_num [a]
theorem a9 : a 9 = 11662056 := by norm_num [a]
theorem a10 : a 10 = 38167920 := by norm_num [a]

theorem gfC : PowerSeries.mk a * C 1 +
    PowerSeries.mk a * X * C (-11) +
    PowerSeries.mk a * X * X * C 55 +
    PowerSeries.mk a * X * X * X * C (-165) +
    PowerSeries.mk a * X * X * X * X * C 330 +
    PowerSeries.mk a * X * X * X * X * X * C (-462) +
    PowerSeries.mk a * X * X * X * X * X * X * C 462 +
    PowerSeries.mk a * X * X * X * X * X * X * X * C (-330) +
    PowerSeries.mk a * X * X * X * X * X * X * X * X * C 165 +
    PowerSeries.mk a * X * X * X * X * X * X * X * X * X * C (-55) +
    PowerSeries.mk a * X * X * X * X * X * X * X * X * X * X * C 11 +
    PowerSeries.mk a * X * X * X * X * X * X * X * X * X * X * X * C (-1) =
    (1 : ℚ⟦X⟧) * X * X * X * X * C 108 + (1 : ℚ⟦X⟧) * X * X * X * X * X * C 4992 + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * C 21912 + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * X * C 552 + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * X * X * C 3492 + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * X * X * X * C (-936) + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * X * X * X * X * C 120 := by
  ext n
  cases n with
  | zero =>
    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
    simp [a0]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
      simp [a0, a1]
    | succ n =>
      cases n with
      | zero =>
        simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
        simp [a0, a1, a2]
      | succ n =>
        cases n with
        | zero =>
          simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
          simp [a0, a1, a2, a3]
        | succ n =>
          cases n with
          | zero =>
            simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
            simp [a0, a1, a2, a3, a4]
          | succ n =>
            cases n with
            | zero =>
              simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
              simp [a0, a1, a2, a3, a4, a5]
              norm_num
            | succ n =>
              cases n with
              | zero =>
                simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                simp [a0, a1, a2, a3, a4, a5, a6]
                norm_num
              | succ n =>
                cases n with
                | zero =>
                  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                  simp [a0, a1, a2, a3, a4, a5, a6, a7]
                  norm_num
                | succ n =>
                  cases n with
                  | zero =>
                    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                    simp [a0, a1, a2, a3, a4, a5, a6, a7, a8]
                    norm_num
                  | succ n =>
                    cases n with
                    | zero =>
                      simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                      simp [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
                      norm_num
                    | succ n =>
                      cases n with
                      | zero =>
                        simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                        simp [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
                        norm_num
                      | succ n =>
                        simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
                        have h := rec n
                        simp [PowerSeries.coeff_one]
                        linear_combination h

end A147821Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a147821.main := by
  refine ⟨?_, ?_⟩
  · have h := A147821Aux.gfC
    simp only [map_ofNat, map_neg, map_one] at h
    linear_combination h
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
    exact A147821Aux.rec m
