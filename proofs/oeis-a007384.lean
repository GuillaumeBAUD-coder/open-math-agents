import OMAStatements.S_oeis_a007384

open PowerSeries OMA.S_oeis_a007384

theorem OMA.solution : type_of% @OMA.S_oeis_a007384.main := by
  have hc k : c (k + 5) = c (k + 3) + c k := by rw [c]
  have hb k : b (k + 4) = 2 * b (k + 2) - b k := by
    unfold b
    split_ifs <;> omega
  have hr m : a (m + 9) = 3 * a (m + 7) - 3 * a (m + 5) + a (m + 4) + a (m + 3) - 2 * a (m + 2) + a m := by
    have h1 : c (m + 15) = c (m + 13) + c (m + 10) := hc _
    have h2 : c (m + 13) = c (m + 11) + c (m + 8) := hc _
    have h3 : c (m + 11) = c (m + 9) + c (m + 6) := hc _
    have g1 : b (m + 9) = 2 * b (m + 7) - b (m + 5) := hb _
    have g2 : b (m + 7) = 2 * b (m + 5) - b (m + 3) := hb _
    have g3 : b (m + 4) = 2 * b (m + 2) - b m := hb _
    show c (m + 15) - b (m + 9) = 3 * (c (m + 13) - b (m + 7)) - 3 * (c (m + 11) - b (m + 5)) +
      (c (m + 10) - b (m + 4)) + (c (m + 9) - b (m + 3)) - 2 * (c (m + 8) - b (m + 2)) + (c (m + 6) - b m)
    linarith
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    exact hr (m + 1)
  · ext n
    rw [show ((X ^ 5 + X ^ 2 - 1) * (X - 1) ^ 2 * (1 + X) ^ 2 : PowerSeries ℤ) =
      X ^ 9 - X ^ 7 - X ^ 7 + X ^ 6 + X ^ 5 - X ^ 4 - X ^ 4 - X ^ 4 + X ^ 2 + X ^ 2 + X ^ 2 - 1 by ring]
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, map_neg, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
    by_cases h : n < 9
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      have := hr m
      simp
      linarith
