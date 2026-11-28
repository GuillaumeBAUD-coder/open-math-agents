import OMAStatements.S_oeis_a196279

-- Problem: A196279, Mathar's recurrence and generating function.
-- Credit: @ShoQo
-- Proof: 7(n+10) = 7n + 70 has the same last digit and leading part + 7, so a(n+10) = a(n) + 1,
-- which gives the recurrence; the denominator is (1 - x)(1 - x^10), so the g.f. identity is the
-- recurrence for n >= 11 plus a check of the first 11 coefficients.

open PowerSeries OMA.S_oeis_a196279

namespace OMA_A196279_Proof

lemma a_add_ten (n : ℕ) : a (n + 10) = a n + 1 := by
  unfold a
  rw [show 7 * (n + 10) / 10 = 7 * n / 10 + 7 by omega, show 7 * (n + 10) % 10 = 7 * n % 10 by omega]
  rw [Nat.cast_add, show ((7 : ℕ) : ℤ) = 7 by norm_num]
  rw [show ((7 * n / 10 : ℕ) : ℤ) + 7 - 2 * ((7 * n % 10 : ℕ) : ℤ)
      = (((7 * n / 10 : ℕ) : ℤ) - 2 * ((7 * n % 10 : ℕ) : ℤ)) + 1 * 7 by ring]
  rw [Int.add_mul_ediv_right _ _ (by norm_num)]

lemma rec (n : ℕ) (hn : 11 ≤ n) : a n = a (n - 1) + a (n - 10) - a (n - 11) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
  rw [show m + 11 - 1 = m + 10 by omega, show m + 11 - 10 = m + 1 by omega,
    show m + 11 - 11 = m by omega, show m + 11 = (m + 1) + 10 by omega, a_add_ten, a_add_ten]
  ring

end OMA_A196279_Proof

open OMA_A196279_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a196279.main := by
  refine ⟨rec, ?_⟩
  rw [show ((1 + X) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) *
      (X - 1) ^ 2 : PowerSeries ℤ) = 1 - X ^ 1 - X ^ 10 + X ^ 11 by ring,
    show (X * (-2 + X - 2 * X ^ 3 + X ^ 4 - 2 * X ^ 6 + X ^ 7 + X ^ 9 + X ^ 2 + X ^ 5 + X ^ 8) :
      PowerSeries ℤ) = X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 8 + X ^ 9 + X ^ 10
        - (X ^ 1 + X ^ 1) - (X ^ 4 + X ^ 4) - (X ^ 7 + X ^ 7) by ring]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  rcases lt_or_ge n 11 with h | h
  · interval_cases n <;> norm_num [a]
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), rec n h]
    simp only [show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
      show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega,
      show n ≠ 9 by omega, show n ≠ 10 by omega, if_false]
    ring

