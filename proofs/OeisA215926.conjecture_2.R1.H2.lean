import OMAReductions.R_OeisA215926_conjecture_2_R1

/-! # Powers of two times a small odd prime are never deficient

For `n = 2 ^ j * q` with `q` an odd prime below `2 ^ (j + 1)`, the divisor sum is
`(2 ^ (j + 1) - 1) * (q + 1)`, which is at least `2 * n` because `q + 1 ≤ 2 ^ (j + 1)`.
Equality is the perfect case and strict inequality the abundant case. -/
-- Credit: @amarkowski999

theorem OMA.solution : OMA.R_OeisA215926_conjecture_2_R1.H2 := by
  intro j q hq hq2 hlt
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hcop : Nat.Coprime (2 ^ j) q := (Nat.coprime_two_left.mpr hqodd).pow_left j
  -- The divisor sum of a power of two.
  have hgeom : ∀ m : ℕ, ∑ x ∈ Finset.range (m + 1), 2 ^ x = 2 ^ (m + 1) - 1 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hp : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by
        rw [pow_succ, Nat.mul_comm]
      have hpos : 0 < 2 ^ (k + 1) := by positivity
      omega
  have hpow : ∑ d ∈ (2 ^ j).divisors, d = 2 ^ (j + 1) - 1 := by
    rw [Nat.sum_divisors_prime_pow Nat.prime_two]
    exact hgeom j
  -- The divisor sum of the odd prime.
  have hqsum : ∑ d ∈ q.divisors, d = q + 1 := by
    rw [hq.divisors, Finset.sum_insert (by simp [show (1 : ℕ) ≠ q by omega]),
      Finset.sum_singleton]
    omega
  -- Divisor sum of `2 ^ j * q`.
  have hsum : ∑ d ∈ (2 ^ j * q).divisors, d = (2 ^ (j + 1) - 1) * (q + 1) := by
    rw [hcop.sum_divisors_mul, hpow, hqsum]
  -- The divisor sum dominates twice the number.
  have hle : 2 * (2 ^ j * q) ≤ ∑ d ∈ (2 ^ j * q).divisors, d := by
    rw [hsum]
    have hP : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ, Nat.mul_comm]
    have hqle : q + 1 ≤ 2 * 2 ^ j := by omega
    rw [hP]
    have h1 : (2 * 2 ^ j - 1) * (q + 1) = (2 * 2 ^ j) * (q + 1) - (q + 1) := by
      rw [Nat.sub_mul, one_mul]
    rw [h1]
    have h : (2 * 2 ^ j) * q + (q + 1) ≤ (2 * 2 ^ j) * (q + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hq' : (2 * 2 ^ j) * q ≤ (2 * 2 ^ j) * (q + 1) - (q + 1) :=
      Nat.le_sub_of_add_le h
    calc 2 * (2 ^ j * q) = (2 * 2 ^ j) * q := by ring
      _ ≤ _ := hq'
  have hnpos : 0 < 2 ^ j * q := by positivity
  rcases lt_or_eq_of_le hle with hlt' | heq
  · exact Or.inr (Nat.abundant_iff_sum_divisors.mpr hlt')
  · exact Or.inl (Nat.perfect_iff_sum_divisors_eq_two_mul hnpos |>.mpr heq.symm)
