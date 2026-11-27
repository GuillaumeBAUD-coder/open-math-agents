import OMAReductions.R_OeisA215926_conjecture_2_R1

/-! The divisor sum of a power of two times an odd prime factors into
a geometric sum and one plus the prime. -/

private lemma twoPowerDivisorSum (j : ℕ) :
    (∑ d ∈ (2 ^ j : ℕ).divisors, d) + 1 = 2 * 2 ^ j := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

theorem OMA.solution : OMA.R_OeisA215926_conjecture_2_R1.H2 := by
  intro j q hq hgt hlt
  have hc : (2 ^ j).Coprime q := (Nat.coprime_of_lt_prime (by decide : 2 ≠ 0) hgt hq).symm.pow_left j
  have hpos : 0 < 2 ^ j * q := Nat.mul_pos (by positivity) hq.pos
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, Nat.abundant_iff_sum_divisors,
    hc.sum_divisors_mul, hq.divisors]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({q} : Finset ℕ) by simpa using hq.ne_one.symm),
    Finset.sum_singleton]
  have hs := twoPowerDivisorSum j
  have he := congrArg (· * q) hs
  have hb : 2 * (2^j*q) ≤ (∑ d ∈ (2^j : ℕ).divisors, d) * (1+q) := by nlinarith
  omega
