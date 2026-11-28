import OMAReductions.R_oeis_a279884_R1

-- Step H2 of oeis-a279884.R1. Credit: @sntntHb
-- Sketch: n odd and n + 1 = 2^a * m with m odd, m > 1 (n + 1 is not a power of two).
-- With x = n - 1 >= 2, x^(2^a) + 1 divides (x^(2^a))^m + 1^m = f n since m is odd,
-- and 1 < x^(2^a) + 1 < f n because 2^a < n + 1.

theorem OMA.solution : OMA.R_oeis_a279884_R1.H2 := by
  intro n hn ho hpow
  unfold OMA.S_oeis_a279884.f
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (n := n + 1) (by omega)
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hpow a (by simpa using hnm)
  have hm3 : 3 ≤ m := by
    obtain ⟨j, rfl⟩ := hm
    omega
  have hn3 : 3 ≤ n := by
    obtain ⟨j, rfl⟩ := ho
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this
      exact (hpow 1 (by norm_num)).elim
    · omega
  have hx : 2 ≤ n - 1 := by omega
  have hd : (n - 1) ^ (2 ^ a) + 1 ∣ ((n - 1) ^ (2 ^ a)) ^ m + 1 ^ m :=
    Odd.nat_add_dvd_pow_add_pow _ 1 hm
  rw [← pow_mul, ← hnm, one_pow] at hd
  apply Nat.not_prime_of_dvd_of_ne hd
  · have : 1 ≤ (n - 1) ^ (2 ^ a) := Nat.one_le_pow _ _ (by omega)
    omega
  · have hlt : 2 ^ a < n + 1 := by
      rw [hnm]
      have : 0 < 2 ^ a := by positivity
      nlinarith
    have : (n - 1) ^ (2 ^ a) < (n - 1) ^ (n + 1) :=
      Nat.pow_lt_pow_right (by omega) hlt
    omega
