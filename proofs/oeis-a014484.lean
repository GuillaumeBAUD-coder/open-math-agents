import OMAStatements.S_oeis_a014484

open OMA.S_oeis_a014484 in
theorem OMA.solution : type_of% @OMA.S_oeis_a014484.main := by
  have ha (k : ℕ) : (a k : ℤ) * 6 = ((k + 2).factorial * (2 * k + 3) * 2 ^ k : ℕ) := by
    exact_mod_cast Nat.div_mul_cancel (by
      cases k with
      | zero => decide
      | succ k => exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
          (Nat.factorial_dvd_factorial (show 3 ≤ k + 3 by omega)) _) _)
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h0 := ha m
  have h1 := ha (m + 1)
  have h2 := ha (m + 2)
  simp only [show m + 1 + 2 = m + 2 + 1 by omega, show m + 2 + 2 = m + 2 + 1 + 1 by omega,
    Nat.factorial_succ, pow_succ] at h0 h1 h2
  push_cast at h0 h1 h2 ⊢
  apply mul_right_cancel₀ (by decide : (6 : ℤ) ≠ 0)
  linear_combination h2 + (-2 * (m : ℤ) - 13) * h1 + 6 * ((m : ℤ) + 3) * h0
