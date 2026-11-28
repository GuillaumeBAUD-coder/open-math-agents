import OMAReductions.R_CarmichaelTotient_charmichaelTotient_R1

open Nat in
theorem OMA.solution : OMA.R_CarmichaelTotient_charmichaelTotient_R1.H2 := by
  have key (k : ℕ) (h6 : 6 ∣ k) (h7 : ¬ 7 ∣ k) : φ (6 * k) = φ (7 * k) := by
    rw [show 6 * k = 2 * (3 * k) by ring, totient_mul_of_prime_of_dvd prime_two (by omega),
      totient_mul_of_prime_of_dvd prime_three (by omega),
      totient_mul ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h7), totient_prime (p := 7) (by norm_num)]
    omega
  intro n h36 h49
  by_cases h7 : 7 ∣ n
  · obtain ⟨j, rfl⟩ := h7
    exact ⟨6 * j, by omega, key j (by omega) (by omega)⟩
  · obtain ⟨k, rfl⟩ : 6 ∣ n := by omega
    exact ⟨7 * k, by omega, (key k (by omega) (by omega)).symm⟩
