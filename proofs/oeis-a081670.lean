import OMAStatements.S_oeis_a081670

open OMA.S_oeis_a081670 in
theorem OMA.solution : type_of% @OMA.S_oeis_a081670.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have e1 : k + 3 - 1 = k + 2 := by omega
  have e2 : k + 3 - 2 = k + 1 := by omega
  have e3 : k + 3 - 3 = k := by omega
  rw [e1, e2, e3]
  simp only [a, ← Nat.centralBinom_eq_two_mul_choose]
  have h1 : ((k : ℤ) + 1) * (Nat.centralBinom (k + 1) : ℤ)
      = 2 * (2 * (k : ℤ) + 1) * (Nat.centralBinom k : ℤ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have h2n : (k + 2) * Nat.centralBinom (k + 2)
      = 2 * (2 * (k + 1) + 1) * Nat.centralBinom (k + 1) := Nat.succ_mul_centralBinom_succ (k + 1)
  have h3n : (k + 3) * Nat.centralBinom (k + 3)
      = 2 * (2 * (k + 2) + 1) * Nat.centralBinom (k + 2) := Nat.succ_mul_centralBinom_succ (k + 2)
  have h2 : ((k : ℤ) + 2) * (Nat.centralBinom (k + 2) : ℤ)
      = 2 * (2 * ((k : ℤ) + 1) + 1) * (Nat.centralBinom (k + 1) : ℤ) := by
    exact_mod_cast h2n
  have h3 : ((k : ℤ) + 3) * (Nat.centralBinom (k + 3) : ℤ)
      = 2 * (2 * ((k : ℤ) + 2) + 1) * (Nat.centralBinom (k + 2) : ℤ) := by
    exact_mod_cast h3n
  push_cast
  linear_combination (3 * (k : ℤ) ^ 2 + k + 2) * h3
    - 4 * (3 * (k : ℤ) ^ 2 + 4 * k + 2) * h2
    + 3 * (3 * (k : ℤ) ^ 2 + 7 * k + 6) * h1
