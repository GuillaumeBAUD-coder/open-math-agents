import OMAStatements.S_oeis_a298267

-- Problem: A298267: a(n) is the maximum number of heptiamonds in a hexagon of order n.
-- Upstream: formal-conjectures statements/oeis-a298267.lean:0 (declaration OMA.S_oeis_a298267.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Since 6 (n+8)^2 = 6 (n+1)^2 + 7 (12 n + 54), one has a(n+7) = a(n) + 12 n + 54. The recurrence says
that the second difference of a(n) - a(n-7) vanishes, which holds because 12 n + 54 is linear. The
denominator of the g.f. is (1 - x)^2 (1 - x^7), so the coefficient of x^n in the product is the left
side minus the right side of the recurrence, which is 3, 1, 2, 2, 1, 3 for n = 1, ..., 6 and 0
otherwise. -/

namespace A298267Aux

open OMA.S_oeis_a298267 PowerSeries

theorem step (n : ℕ) : a (n + 7) = a n + 12 * (n : ℤ) + 54 := by
  unfold a
  have e : 6 * (((n + 7 : ℕ) : ℤ) + 1) ^ 2 = 6 * ((n : ℤ) + 1) ^ 2 + 7 * (12 * (n : ℤ) + 54) := by
    push_cast
    ring
  rw [e, Int.add_mul_ediv_left _ _ (by norm_num)]
  ring

theorem rec9 (m : ℕ) : a (m + 9) = 2 * a (m + 8) - a (m + 7) + a (m + 2) - 2 * a (m + 1) + a m := by
  have s2 := step (m + 2)
  have s1 := step (m + 1)
  have s0 := step m
  push_cast at s2 s1 s0
  linear_combination s2 - 2 * s1 + s0

theorem a0 : a 0 = 0 := by norm_num [a]
theorem a1 : a 1 = 3 := by norm_num [a]
theorem a2 : a 2 = 7 := by norm_num [a]
theorem a3 : a 3 = 13 := by norm_num [a]
theorem a4 : a 4 = 21 := by norm_num [a]
theorem a5 : a 5 = 30 := by norm_num [a]
theorem a6 : a 6 = 42 := by norm_num [a]
theorem a7 : a 7 = 54 := by norm_num [a]
theorem a8 : a 8 = 69 := by norm_num [a]

theorem gfC : PowerSeries.mk (fun n => (a n : ℚ)) * C 1 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * C (-2) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * C 1 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * X * C (-1) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * X * X * C 2 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * X * X * X * C (-1) =
    (1 : ℚ⟦X⟧) * X * C 3 + (1 : ℚ⟦X⟧) * X * X * C 1 + (1 : ℚ⟦X⟧) * X * X * X * C 2 + (1 : ℚ⟦X⟧) * X * X * X * X * C 2 + (1 : ℚ⟦X⟧) * X * X * X * X * X * C 1 + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * C 3 := by
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
        norm_num
      | succ n =>
        cases n with
        | zero =>
          simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
          simp [a1, a2, a3]
          norm_num
        | succ n =>
          cases n with
          | zero =>
            simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
            simp [a2, a3, a4]
            norm_num
          | succ n =>
            cases n with
            | zero =>
              simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
              simp [a3, a4, a5]
              norm_num
            | succ n =>
              cases n with
              | zero =>
                simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                simp [a4, a5, a6]
                norm_num
              | succ n =>
                cases n with
                | zero =>
                  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                  simp [a0, a5, a6, a7]
                  norm_num
                | succ n =>
                  cases n with
                  | zero =>
                    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                    simp [a0, a1, a6, a7, a8]
                    norm_num
                  | succ n =>
                    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
                    have h := rec9 n
                    have hq : ((a (n + 9) : ℤ) : ℚ) = 2 * ((a (n + 8) : ℤ) : ℚ) - ((a (n + 7) : ℤ) : ℚ) + ((a (n + 2) : ℤ) : ℚ) -
                        2 * ((a (n + 1) : ℤ) : ℚ) + ((a n : ℤ) : ℚ) := by
                      exact_mod_cast h
                    simp [PowerSeries.coeff_one]
                    linear_combination hq

end A298267Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a298267.main := by
  refine ⟨?_, ?_⟩
  · have h := A298267Aux.gfC
    simp only [map_ofNat, map_neg, map_one] at h
    linear_combination h
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    exact A298267Aux.rec9 m
