import OMAReductions.R_PerfectNumbers_infinitely_many_even_perfect_R1

-- Euclid's theorem (Elements IX.36): if 2^(k+1) - 1 is prime then 2^k * (2^(k+1) - 1) is a perfect number.
-- Original Lean proof of the classical theorem (Mathlib has it only in its Archive, which cannot be imported):
-- the divisor sum is multiplicative, sigma(2^k) = 2^(k+1) - 1 and sigma(M) = M + 1 for a prime M.
-- A classical theorem, not progress on the open question whether there are infinitely many Mersenne primes.

namespace OMA.Euclid

open ArithmeticFunction Finset

lemma geom2 : ∀ k : ℕ, ∑ i ∈ range (k + 1), 2 ^ i = 2 ^ (k + 1) - 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := pow_succ' 2 (k + 1)
    omega

theorem euclid (k : ℕ) (hp : (mersenne (k + 1)).Prime) : Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  have hM : mersenne (k + 1) = 2 ^ (k + 1) - 1 := rfl
  have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hpos : 0 < 2 ^ k * mersenne (k + 1) := Nat.mul_pos (by positivity) hp.pos
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply]
  have hodd : ¬ 2 ∣ mersenne (k + 1) := by
    rw [hM]
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
    omega
  have hcop : Nat.Coprime (2 ^ k) (mersenne (k + 1)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow Nat.prime_two, geom2]
  have hs : sigma 1 (mersenne (k + 1)) = mersenne (k + 1) + 1 := by
    have h := sigma_one_apply_prime_pow (i := 1) hp
    rw [pow_one, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one] at h
    rw [h, add_comm]
  rw [hs, ← hM]
  have h3 : mersenne (k + 1) + 1 = 2 * 2 ^ k := by
    rw [hM]
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
    omega
  rw [h3]
  ring

end OMA.Euclid

theorem OMA.solution : OMA.R_PerfectNumbers_infinitely_many_even_perfect_R1.H2 := by
  intro k hp
  exact OMA.Euclid.euclid k hp
