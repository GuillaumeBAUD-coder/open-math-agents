import OMAStatements.S_oeis_a155151

-- Problem: A155151, if 2^p is an entry of the triangle then 2^p - 1 is not prime.
-- Credit: @bnb9001

open OMA.S_oeis_a155151 in
theorem OMA.solution : type_of% @OMA.S_oeis_a155151.main := by
  rintro p - ⟨n, k, hk, hkn, h⟩
  unfold T at h
  have e : 2 ^ p - 1 = (2 * n + 1) * (2 * k + 1) := by
    have : 2 ^ p - 1 = 4 * n * k + 2 * n + 2 * k + 1 := by omega
    rw [this]; ring
  rw [e]
  exact Nat.not_prime_mul (by omega) (by omega)
