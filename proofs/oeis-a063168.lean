import OMAStatements.S_oeis_a063168

-- Problem: A063168: Dimension of the space of weight 2n cusp forms for Gamma_0( 100 ).
-- Upstream: formal-conjectures statements/oeis-a063168.lean:0 (declaration OMA.S_oeis_a063168.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! For n ≥ 2 the terms are linear in n, which gives the recurrence. The coefficient of x^n in
(Sum a(k) x^k) (1 - 2x + x^2) is a(n) - 2 a(n-1) + a(n-2), which is 7, 22, 1 for n = 1, 2, 3 and 0
otherwise. -/

namespace A063168Aux

open OMA.S_oeis_a063168 PowerSeries

theorem a0 : a 0 = 0 := by simp [a]

theorem a1 : a 1 = 7 := by simp [a]

theorem a2 : a 2 = 36 := by norm_num [a]

theorem a3 : a 3 = 66 := by norm_num [a]

theorem a_big (m : ℕ) : a (m + 2) = 30 * (m : ℤ) + 36 := by
  have h0 : ¬ (m + 2 = 0) := by omega
  have h1 : ¬ (m + 2 = 1) := by omega
  simp [a, h1]
  ring

theorem rec2 (m : ℕ) : a (m + 4) = 2 * a (m + 3) - a (m + 2) := by
  have h4 := a_big (m + 2)
  have h3 := a_big (m + 1)
  have h2 := a_big m
  rw [h4, h3, h2]
  push_cast
  ring

theorem gfC : PowerSeries.mk (fun n => (a n : ℚ)) * C 1 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * C (-2) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * C 1 =
    (1 : ℚ⟦X⟧) * X * C 7 + (1 : ℚ⟦X⟧) * X * X * C 22 + (1 : ℚ⟦X⟧) * X * X * X * C 1 := by
  ext n
  cases n with
  | zero =>
    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
    simp [a0]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
        PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
      simp [a0, a1]
    | succ n =>
      cases n with
      | zero =>
        simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
          PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
        simp [a0, a1, a2]
        norm_num
      | succ n =>
        cases n with
        | zero =>
          simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
            PowerSeries.coeff_mk]
          simp [a1, a2, a3]
          norm_num
        | succ m =>
          simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
            PowerSeries.coeff_mk]
          have h := rec2 m
          have hq : ((a (m + 4) : ℤ) : ℚ) = 2 * ((a (m + 3) : ℤ) : ℚ) - ((a (m + 2) : ℤ) : ℚ) := by
            exact_mod_cast h
          simp [PowerSeries.coeff_one]
          linear_combination hq

end A063168Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a063168.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    exact A063168Aux.rec2 m
  · have h := A063168Aux.gfC
    simp only [map_ofNat, map_neg, map_one] at h
    linear_combination h
