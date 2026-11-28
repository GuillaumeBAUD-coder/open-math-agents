import OMAReductions.R_oeis_a083382_R1

-- Step oeis-a083382.R1.H1: hypothesis H1 of reduction oeis-a083382.R1
-- Credit: @Zachary-Vowles
-- H1 says: for every n > 1 and every row <= 1 there is a prime in (row * n, (row + 1) * n].
-- Row 0: the prime 2 lies in (0, n] because 2 <= n.
-- Row 1: Bertrand's postulate gives a prime p with n < p <= 2 * n.

theorem OMA.solution : OMA.R_oeis_a083382_R1.H1 := by
  intro n hn row hrow
  by_cases hz : row = 0
  · subst row
    refine ⟨2, Nat.prime_two, by omega, by omega⟩
  · have h1 : row = 1 := by omega
    subst row
    obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
    refine ⟨p, hp, by omega, by omega⟩
