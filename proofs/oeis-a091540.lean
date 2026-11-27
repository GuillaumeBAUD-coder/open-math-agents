import OMAStatements.S_oeis_a091540

open OMA.S_oeis_a091540 in
theorem OMA.solution : type_of% @OMA.S_oeis_a091540.main := by
  intro n hn
  have hq : ∀ k, q (k + 1) = (3 * (k : ℤ) + 1) * q k := by
    intro k
    simp only [q, Finset.prod_range_succ]
    ring
  have hq2 : ∀ k, (2 : ℤ) ∣ q (k + 2) := by
    intro k
    induction k with
    | zero => exact ⟨2, by simp [q, Finset.prod_range_succ]⟩
    | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 from rfl, hq]
      exact Dvd.dvd.mul_left ih _
  have hdiv : ∀ k, (6 : ℤ) ∣ numerator (k + 2) := by
    intro k
    unfold numerator
    apply dvd_sub
    · have h3 : (3 : ℤ) ∣ 3 ^ (k + 2) := dvd_pow_self 3 (by omega)
      have h2 : (2 : ℤ) ∣ ((k + 2).factorial : ℤ) := by
        exact_mod_cast Nat.dvd_factorial (by norm_num) (by omega)
      have := mul_dvd_mul h3 h2
      simpa using this
    · have := mul_dvd_mul_left (3 : ℤ) (hq2 k)
      simpa using this
  have ha : ∀ k, numerator (k + 2) = 6 * a (k + 2) := fun k =>
    (Int.mul_ediv_cancel' (hdiv k)).symm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 + 1 + 1 := ⟨n - 4, by omega⟩
  rw [show m + 2 + 1 + 1 - 1 = m + 1 + 2 by omega, show m + 2 + 1 + 1 - 2 = m + 2 by omega]
  have h4 := ha (m + 2)
  have h3 := ha (m + 1)
  have h2 := ha m
  rw [show m + 2 + 2 = m + 2 + 1 + 1 by omega] at h4
  have e : numerator (m + 2 + 1 + 1) + (-6 * ((m + 2 + 1 + 1 : ℕ) : ℤ) + 5) * numerator (m + 1 + 2) +
      3 * (((m + 2 + 1 + 1 : ℕ) : ℤ) - 1) * (3 * ((m + 2 + 1 + 1 : ℕ) : ℤ) - 5) * numerator (m + 2) = 0 := by
    rw [show m + 1 + 2 = m + 2 + 1 by omega]
    simp only [numerator, hq, Nat.factorial_succ, pow_succ]
    push_cast
    ring
  have h6 : (6 : ℤ) * (a (m + 2 + 1 + 1) + (-6 * ((m + 2 + 1 + 1 : ℕ) : ℤ) + 5) * a (m + 1 + 2) +
      3 * (((m + 2 + 1 + 1 : ℕ) : ℤ) - 1) * (3 * ((m + 2 + 1 + 1 : ℕ) : ℤ) - 5) * a (m + 2)) = 0 := by
    linear_combination e - h4 - (-6 * ((m + 2 + 1 + 1 : ℕ) : ℤ) + 5) * h3 -
      3 * (((m + 2 + 1 + 1 : ℕ) : ℤ) - 1) * (3 * ((m + 2 + 1 + 1 : ℕ) : ℤ) - 5) * h2
  exact (mul_eq_zero.mp h6).resolve_left (by norm_num)
