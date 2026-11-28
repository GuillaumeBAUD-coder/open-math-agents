import OMAStatements.S_oeis_a114698

-- Problem: A114698: Let M(n) be the n X n matrix m(i,j)=min(i,j) for 1<=i,j<=n then a(n) is the trace of M(n)^(-3).
-- Upstream: formal-conjectures statements/oeis-a114698.lean:0 (declaration OMA.S_oeis_a114698.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! For n ≥ 2 the terms are linear in n, which gives the recurrence. The coefficient of x^k in
(Sum a(j+1) x^j) (1 - 2x + x^2) is a(k+1) - 2 a(k) + a(k-1), which is 1, 16, 3 for k = 0, 1, 2 and 0
otherwise. -/

namespace A114698Aux

open OMA.S_oeis_a114698 PowerSeries

theorem a1 : a 1 = 1 := by simp [a]

theorem a2 : a 2 = 18 := by norm_num [a]

theorem a3 : a 3 = 38 := by norm_num [a]

theorem a_big (m : ℕ) : a (m + 2) = 20 * (m : ℤ) + 18 := by
  have h : ¬ (m + 2 = 1) := by omega
  simp [a, h]
  ring

theorem rec2 (m : ℕ) : a (m + 4) = 2 * a (m + 3) - a (m + 2) := by
  have h4 := a_big (m + 2)
  have h3 := a_big (m + 1)
  have h2 := a_big m
  rw [h4, h3, h2]
  push_cast
  ring

theorem gfC : PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * C 1 +
    PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * X * C (-2) +
    PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * X * X * C 1 =
    (1 : ℚ⟦X⟧) * C 1 + (1 : ℚ⟦X⟧) * X * C 16 + (1 : ℚ⟦X⟧) * X * X * C 3 := by
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

end A114698Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a114698.main := by
  refine ⟨?_, ?_⟩
  · have h := A114698Aux.gfC
    simp only [map_ofNat, map_neg, map_one] at h
    linear_combination h
  · intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    have e : m + 3 - 1 = m + 2 := rfl
    rw [e]
    exact A114698Aux.rec2 m
