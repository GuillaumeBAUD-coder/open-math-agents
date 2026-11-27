import OMAReductions.R_OeisA215926_conjecture_2_R1

namespace OMA.OeisA215926H2

/-- The divisor sum of a power of two: 1 + 2 + ... + 2^j = 2^(j+1) - 1. -/
theorem geom_two (j : ℕ) : (∑ i ∈ Finset.range (j + 1), 2 ^ i) + 1 = 2 * 2 ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- For an odd prime q below 2^(j+1), sigma(2^j q) = (2^(j+1) - 1)(q + 1) is at least 2^(j+1) q. -/
theorem sigma_ge (j q : ℕ) (hq : q.Prime) (h2 : 2 < q) (hlt : q < 2 * 2 ^ j) :
    2 * (2 ^ j * q) ≤ ∑ d ∈ (2 ^ j * q).divisors, d := by
  have hcop : Nat.Coprime (2 ^ j) q := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes Nat.prime_two hq).mpr (by omega)
  rw [hcop.sum_divisors_mul, Nat.sum_divisors_prime_pow Nat.prime_two, hq.sum_divisors]
  have hS := geom_two j
  set S := ∑ i ∈ Finset.range (j + 1), 2 ^ i with hSdef
  calc 2 * (2 ^ j * q) = S * q + q := by rw [← mul_assoc, ← hS]; ring
    _ ≤ S * q + S := by omega
    _ = S * (q + 1) := by ring

theorem nondef (j q : ℕ) (hq : q.Prime) (h2 : 2 < q) (hlt : q < 2 * 2 ^ j) :
    (2 ^ j * q).Perfect ∨ (2 ^ j * q).Abundant := by
  have hpos : 0 < 2 ^ j * q := Nat.mul_pos (Nat.two_pow_pos j) hq.pos
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, Nat.abundant_iff_sum_divisors]
  have := sigma_ge j q hq h2 hlt
  omega

end OMA.OeisA215926H2

theorem OMA.solution : OMA.R_OeisA215926_conjecture_2_R1.H2 := by
  intro j q hq h2 hlt
  exact OMA.OeisA215926H2.nondef j q hq h2 hlt
