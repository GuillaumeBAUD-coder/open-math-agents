import OMAReductions.R_mo_342377_R1

/-! With X = c² + 3c + 1 we have c(c+1)(c+2)(c+3) = X² - 1, and 4(a-1)(a+2) = (2a+1)² - 9.
So equality gives (2a+1)² = (2X)² + 5. Then 2X < 2a + 1, hence (2X + 1)² ≤ (2a+1)² = (2X)² + 5,
i.e. X ≤ 1, while X ≥ 11 for c ≥ 2. -/

theorem OMA.solution : OMA.R_mo_342377_R1.H2 := by
  intro a c ha hc h
  have h4 : Nat.ascFactorial c 4 = c * (c + 1) * (c + 2) * (c + 3) := by
    simp [Nat.ascFactorial]
    ring
  rw [h4] at h
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
  rw [show a' + 2 - 1 = a' + 1 by omega, show a' + 2 + 2 = a' + 4 by omega] at h
  have e1 : (2 * a' + 5) ^ 2 = 4 * ((a' + 1) * (a' + 4)) + 9 := by ring
  have e2 : (2 * (c ^ 2 + 3 * c + 1)) ^ 2 = 4 * (c * (c + 1) * (c + 2) * (c + 3)) + 4 := by ring
  have key : (2 * a' + 5) ^ 2 = (2 * (c ^ 2 + 3 * c + 1)) ^ 2 + 5 := by omega
  have hvu : 2 * (c ^ 2 + 3 * c + 1) < 2 * a' + 5 := by
    by_contra hc'
    push Not at hc'
    have := Nat.pow_le_pow_left hc' 2
    omega
  have h5 : (2 * (c ^ 2 + 3 * c + 1) + 1) ^ 2 ≤ (2 * a' + 5) ^ 2 := Nat.pow_le_pow_left hvu 2
  have h6 : (2 * (c ^ 2 + 3 * c + 1) + 1) ^ 2 =
      (2 * (c ^ 2 + 3 * c + 1)) ^ 2 + 2 * (2 * (c ^ 2 + 3 * c + 1)) + 1 := by ring
  have hc2 : 4 ≤ c ^ 2 := by nlinarith
  omega
