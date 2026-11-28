import OMAStatements.S_oeis_a159715

-- Problem: A159715: Number of permutations of 2 indistinguishable copies of 1..n arranged in a circle with exactly 1 local maximum.
-- Upstream: formal-conjectures statements/oeis-a159715.lean:0 (declaration OMA.S_oeis_a159715.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The closed form gives (2) directly and (3) by a computation with powers of 3. For (1), the
coefficient of x^n in (Sum a(k) x^k) (1 - 6x + 9x^2) is a(n) - 6 a(n-1) + 9 a(n-2), which is 4 for
n = 2, -6 for n = 3 and 0 otherwise. -/

namespace A159715Aux

open OMA.S_oeis_a159715 PowerSeries

theorem a0 : a 0 = 0 := by simp [a]

theorem a1 : a 1 = 0 := by simp [a]

theorem a_big (m : ℕ) : a (m + 2) = 2 * ((m : ℤ) + 2) * 3 ^ m := by
  have h : ¬ (m + 2 < 2) := by omega
  simp [a, h]

theorem rec3 (m : ℕ) : a (m + 4) = 6 * a (m + 3) - 9 * a (m + 2) := by
  have h4 := a_big (m + 2)
  have h3 := a_big (m + 1)
  have h2 := a_big m
  rw [h4, h3, h2]
  push_cast
  ring

theorem gfC : PowerSeries.mk (fun n => (a n : ℚ)) * C 1 + PowerSeries.mk (fun n => (a n : ℚ)) * X * C (-6) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * C 9 =
    (1 : ℚ⟦X⟧) * X * X * C 4 + (1 : ℚ⟦X⟧) * X * X * X * C (-6) := by
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
        have h2 := a_big 0
        simp [a0, a1, h2]
      | succ n =>
        cases n with
        | zero =>
          simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
            PowerSeries.coeff_mk]
          have h2 := a_big 0
          have h3 := a_big 1
          simp [a1, h2, h3]
          norm_num
        | succ m =>
          simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
            PowerSeries.coeff_mk]
          have h := rec3 m
          have hq : ((a (m + 4) : ℤ) : ℚ) = 6 * ((a (m + 3) : ℤ) : ℚ) - 9 * ((a (m + 2) : ℤ) : ℚ) := by
            exact_mod_cast h
          simp [PowerSeries.coeff_one]
          linear_combination hq

end A159715Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a159715.main := by
  refine ⟨?_, ?_, ?_⟩
  · have h := A159715Aux.gfC
    simp only [map_ofNat, map_neg, map_one] at h
    linear_combination h
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [A159715Aux.a_big, Nat.add_sub_cancel]
    push_cast
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    exact A159715Aux.rec3 m
