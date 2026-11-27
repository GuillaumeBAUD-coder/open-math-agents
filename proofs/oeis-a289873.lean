import OMAStatements.S_oeis_a289873

namespace OMA.S_oeis_a289873

open PowerSeries


/-- The generating function `Sum_{n >= 2} a(n) x^n` (offset 2). -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => if n < 2 then 0 else a n

/-- Barker's numerator and denominator. -/
noncomputable def num : ℚ⟦X⟧ := X ^ 2 * (1 + X - X ^ 2) * (1 + X ^ 2 - X ^ 3 + 2 * X ^ 4 + X ^ 5)
noncomputable def den : ℚ⟦X⟧ := (1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2) * (1 + X + X ^ 2)

lemma den_eq : den = 1 - X ^ 1 - X ^ 1 + X ^ 2 - X ^ 6 + X ^ 7 + X ^ 7 - X ^ 8 := by
  unfold den; ring

lemma num_eq : num = X ^ 2 + X ^ 3 + X ^ 7 + X ^ 7 + X ^ 7 + X ^ 7 - X ^ 8 - X ^ 9 := by
  unfold num; ring

lemma shift6 (k : ℕ) : a (k + 6) - a k = 4 * ((k + 6 : ℕ) : ℚ) - 12 := by
  unfold a
  rw [show (k + 6) % 6 = k % 6 by omega]
  push_cast
  ring

lemma coeff_A (n : ℕ) : coeff n A = if n < 2 then 0 else a n := by
  simp [A]

lemma mul_den : A * den = num := by
  rw [den_eq, num_eq]
  ext n
  have e : A * (1 - X ^ 1 - X ^ 1 + X ^ 2 - X ^ 6 + X ^ 7 + X ^ 7 - X ^ 8) =
      A - A * X ^ 1 - A * X ^ 1 + A * X ^ 2 - A * X ^ 6 + A * X ^ 7 + A * X ^ 7 - A * X ^ 8 := by
    ring
  rw [e]
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_A, coeff_X_pow]
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> norm_num [a]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    have h1 := shift6 (m + 4)
    have h2 := shift6 (m + 3)
    have h3 := shift6 (m + 2)
    simp only [show ¬ (m + 10 < 2) by omega, if_false, show 1 ≤ m + 10 by omega, if_true,
      show 2 ≤ m + 10 by omega, show 6 ≤ m + 10 by omega, show 7 ≤ m + 10 by omega,
      show 8 ≤ m + 10 by omega, show ¬ (m + 10 - 1 < 2) by omega, show ¬ (m + 10 - 2 < 2) by omega,
      show ¬ (m + 10 - 6 < 2) by omega, show ¬ (m + 10 - 7 < 2) by omega,
      show ¬ (m + 10 - 8 < 2) by omega, show m + 10 - 1 = m + 3 + 6 by omega,
      show m + 10 - 2 = m + 2 + 6 by omega, show m + 10 - 6 = m + 4 by omega,
      show m + 10 - 7 = m + 3 by omega, show m + 10 - 8 = m + 2 by omega,
      show m + 10 = m + 4 + 6 by omega, show ¬ (m + 4 + 6 = 2) by omega,
      show ¬ (m + 4 + 6 = 3) by omega, show ¬ (m + 4 + 6 = 7) by omega,
      show ¬ (m + 4 + 6 = 8) by omega, show ¬ (m + 4 + 6 = 9) by omega]
    simp only [show ¬ (m + 3 + 6 < 2) by omega, show ¬ (m + 2 + 6 < 2) by omega,
      show ¬ (m + 4 < 2) by omega, show ¬ (m + 3 < 2) by omega, show ¬ (m + 2 < 2) by omega,
      if_false]
    push_cast at h1 h2 h3 ⊢
    linarith

/-- Barker's conjecture: the g.f. of A289873 is `num / den`. -/
theorem conjecture : A = num * den⁻¹ := by
  have h : constantCoeff den ≠ 0 := by rw [den_eq]; simp
  rw [← mul_den, mul_assoc, PowerSeries.mul_inv_cancel _ h, mul_one]

/-- Controls: the listed terms a(2..8) = 1, 3, 5, 7, 9, 15, 21. -/
example : a 2 = 1 ∧ a 3 = 3 ∧ a 4 = 5 ∧ a 5 = 7 ∧ a 6 = 9 ∧ a 7 = 15 ∧ a 8 = 21 := by
  norm_num [a]

end OMA.S_oeis_a289873

theorem OMA.solution : type_of% @OMA.S_oeis_a289873.main :=
  OMA.S_oeis_a289873.mul_den
