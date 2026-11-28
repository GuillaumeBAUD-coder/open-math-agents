import OMAReductions.R_CarmichaelTotient_charmichaelTotient_R1

open Nat in
theorem OMA.solution : OMA.R_CarmichaelTotient_charmichaelTotient_R1.H1 := by
  have t2 {k} (h : ¬ 2 ∣ k) : φ (2 * k) = φ k := by
    simp [totient_mul ((Nat.Prime.coprime_iff_not_dvd prime_two).2 h)]
  have t3 {k} (h : ¬ 3 ∣ k) : φ (3 * k) = 2 * φ k := by
    simp [totient_mul ((Nat.Prime.coprime_iff_not_dvd prime_three).2 h), totient_prime prime_three]
  have d2 {k} (h : 2 ∣ k) : φ (2 * k) = 2 * φ k := totient_mul_of_prime_of_dvd prime_two h
  intro n hn h36
  by_cases h2 : 2 ∣ n
  · by_cases h4 : 4 ∣ n
    · by_cases h3 : 3 ∣ n
      · obtain ⟨j, rfl⟩ := h3
        exact ⟨2 * j, by omega, by rw [d2 (by omega), t3 (by omega)]⟩
      · obtain ⟨k, rfl⟩ := h2
        exact ⟨3 * k, by omega, by rw [d2 (by omega), t3 (by omega)]⟩
    · obtain ⟨k, rfl⟩ := h2
      exact ⟨k, by omega, (t2 (by omega)).symm⟩
  · exact ⟨2 * n, by omega, t2 h2⟩
