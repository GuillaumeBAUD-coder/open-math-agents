import OMAStatements.S_oeis_a298024

open PowerSeries OMA.S_oeis_a298024

theorem OMA.solution : type_of% @OMA.S_oeis_a298024.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have hD : constantCoeff ((1 - X) * (1 - X ^ 3) : PowerSeries ℚ) ≠ 0 := by
    simp
  have h : G * ((1 - X) * (1 - X ^ 3)) = 1 + 3 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 := by
    rw [G, mul_assoc, PowerSeries.inv_mul_cancel _ hD, mul_one]
  have h' : G - G * X ^ 1 - G * X ^ 3 + G * X ^ 4 =
      1 + (X ^ 1 + X ^ 1 + X ^ 1) + (X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2) +
        (X ^ 3 + X ^ 3 + X ^ 3) + X ^ 4 := by
    rw [show G - G * X ^ 1 - G * X ^ 3 + G * X ^ 4 = G * ((1 - X) * (1 - X ^ 3)) by ring, h]
    ring
  have key := congrArg (coeff (m + 5)) h'
  have e1 : m + 5 - 1 = m + 4 := rfl
  have e3 : m + 5 - 3 = m + 2 := rfl
  have e4 : m + 5 - 4 = m + 1 := rfl
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_X_pow, coeff_one,
    if_pos (show 1 ≤ m + 5 by omega), if_pos (show 3 ≤ m + 5 by omega),
    if_pos (show 4 ≤ m + 5 by omega), if_neg (show ¬ (m + 5 = 0) by omega),
    if_neg (show ¬ (m + 5 = 1) by omega), if_neg (show ¬ (m + 5 = 2) by omega),
    if_neg (show ¬ (m + 5 = 3) by omega), if_neg (show ¬ (m + 5 = 4) by omega), e1, e3, e4] at key
  show coeff (m + 5) G = coeff (m + 4) G + coeff (m + 2) G - coeff (m + 1) G
  linarith
