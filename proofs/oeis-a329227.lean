import OMAStatements.S_oeis_a329227

namespace OMA.S_oeis_a329227

open PowerSeries



/-- Control: the listed terms a(0..13). -/
example : (List.range 14).map a = [0, 0, 0, 0, 0, 1, 1, 2, 4, 6, 12, 20, 35, 63] := by decide

lemma rec6 (n : ℕ) :
    a (n + 6) = a (n + 5) + a (n + 4) + a (n + 3) - a (n + 2) + a (n + 1) - a n := by
  have h3 : P (n + 3) = P (n + 1) + P n := rfl
  have h4 : P (n + 4) = P (n + 2) + P (n + 1) := rfl
  have h5 : P (n + 5) = P (n + 3) + P (n + 2) := rfl
  have h6 : P (n + 6) = P (n + 4) + P (n + 3) := rfl
  have h7 : P (n + 7) = P (n + 5) + P (n + 4) := rfl
  simp only [a]
  rw [h7, h6, h5, h4, h3]
  ring

/-- Barker's conjectured generating function, as an identity of formal power series. -/
theorem gf :
    PowerSeries.mk a * ((1 - 2 * X + X ^ 2 - X ^ 3) * (1 + X - X ^ 3)) = (X ^ 5 : ℤ⟦X⟧) := by
  have hD : ((1 - 2 * X + X ^ 2 - X ^ 3) * (1 + X - X ^ 3) : ℤ⟦X⟧) =
      1 - X ^ 1 - X ^ 2 - X ^ 3 + X ^ 4 - X ^ 5 + X ^ 6 := by ring
  rw [hD]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_mk,
    coeff_X_pow]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have := rec6 m
    simp only [show ¬ (m + 6 = 5) from by omega, if_false]
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega)]
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 5 = m + 1 by omega, show m + 6 - 6 = m by omega]
    linarith

end OMA.S_oeis_a329227

theorem OMA.solution : type_of% @OMA.S_oeis_a329227.main :=
  OMA.S_oeis_a329227.gf
