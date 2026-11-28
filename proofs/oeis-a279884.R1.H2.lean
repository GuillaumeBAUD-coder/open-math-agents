import OMAReductions.R_oeis_a279884_R1

/-! Factor the power using the odd part of its exponent, as in @Raimo33's proof. -/

theorem OMA.solution : OMA.R_oeis_a279884_R1.H2 := by
  intro n hn odd notPow
  obtain ⟨k, m, hm, eq⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n + 1 ≠ 0)
  have mLarge : 1 < m := by
    have ne : m ≠ 1 := by
      rintro rfl
      exact notPow k (by simpa using eq)
    obtain ⟨j, rfl⟩ := hm
    omega
  have base : 1 < n - 1 := by
    have ne : n ≠ 1 := fun h => notPow 1 (by norm_num [h])
    obtain ⟨j, rfl⟩ := odd
    omega
  let a := (n - 1) ^ (2 ^ k)
  have large : 1 < a := Nat.one_lt_pow (by positivity) base
  rw [OMA.S_oeis_a279884.f, eq, pow_mul]
  change ¬ (a ^ m + 1).Prime
  have divisor : a + 1 ∣ a ^ m + 1 := by
    simpa using hm.nat_add_dvd_pow_add_pow a 1
  exact Nat.not_prime_of_dvd_of_lt divisor (by omega)
    (Nat.add_lt_add_right (by simpa using Nat.pow_lt_pow_right large mLarge) 1)
