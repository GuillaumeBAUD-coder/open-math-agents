import OMAStatements.S_oeis_a007392

open PowerSeries OMA.S_oeis_a007392

theorem OMA.solution : type_of% @OMA.S_oeis_a007392.main := by
  have he k : e (k + 9) = e (k + 7) + e (k + 4) := by rw [e]
  have hb k (hk : 2 ≤ k) : b (k + 4) = 2 * b (k + 2) - b k := by
    unfold b
    split_ifs <;> omega
  have hr m : a (m + 13) = 3 * a (m + 11) - 3 * a (m + 9) + a (m + 8) + a (m + 7) - 2 * a (m + 6) + a (m + 4) := by
    have h1 : e (m + 13) = e (m + 11) + e (m + 8) := he _
    have h2 : e (m + 11) = e (m + 9) + e (m + 6) := he _
    have h3 : e (m + 9) = e (m + 7) + e (m + 4) := he _
    have g1 : b (m + 13) = 2 * b (m + 11) - b (m + 9) := hb _ (by omega)
    have g2 : b (m + 11) = 2 * b (m + 9) - b (m + 7) := hb _ (by omega)
    have g3 : b (m + 8) = 2 * b (m + 6) - b (m + 4) := hb _ (by omega)
    show e (m + 13) - b (m + 13) = 3 * (e (m + 11) - b (m + 11)) - 3 * (e (m + 9) - b (m + 9)) +
      (e (m + 8) - b (m + 8)) + (e (m + 7) - b (m + 7)) - 2 * (e (m + 6) - b (m + 6)) + (e (m + 4) - b (m + 4))
    linarith
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
    exact hr m
  · ext n
    rw [show ((X ^ 5 + X ^ 2 - 1) * (X - 1) ^ 2 * (1 + X) ^ 2 : PowerSeries ℤ) =
      X ^ 9 - X ^ 7 - X ^ 7 + X ^ 6 + X ^ 5 - X ^ 4 - X ^ 4 - X ^ 4 + X ^ 2 + X ^ 2 + X ^ 2 - 1 by ring,
      show (X ^ 10 * (-5 + 3 * X ^ 2) : PowerSeries ℤ) =
      X ^ 12 + X ^ 12 + X ^ 12 - X ^ 10 - X ^ 10 - X ^ 10 - X ^ 10 - X ^ 10 by ring]
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
    by_cases h : n < 13
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
      have := hr m
      simp
      linarith
