import OMAStatements.S_oeis_a298024

open PowerSeries OMA.S_oeis_a298024

theorem OMA.solution : type_of% @OMA.S_oeis_a298024.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have h : G * (1 - X - X ^ 3 + X ^ 4) = 1 + 3 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 := by
    rw [G, show (1 - X - X ^ 3 + X ^ 4 : PowerSeries ℚ) = (1 - X) * (1 - X ^ 3) by ring, mul_assoc,
      PowerSeries.inv_mul_cancel _ (by simp), mul_one]
  have := congrArg (coeff (m + 5)) h
  simp [mul_add, mul_sub, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_X] at this
  show a (m + 5) = a (m + 4) + a (m + 2) - a (m + 1)
  simp only [a]
  linarith
