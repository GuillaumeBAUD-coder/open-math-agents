import OMAReductions.R_PerfectNumbers_infinitely_many_even_perfect_R1

-- Step PerfectNumbers.infinitely_many_even_perfect.R1.H2: hypothesis H2 of reduction PerfectNumbers.infinitely_many_even_perfect.R1
-- Credit: @SeanDishman
-- Euclid, Elements IX.36. sigma is multiplicative and 2 ^ k is coprime to the odd number
-- mersenne (k + 1), so sigma (2 ^ k * M) = sigma (2 ^ k) * sigma M = M * (M + 1) = M * 2 ^ (k + 1).


/-- The geometric sum `1 + 2 + ... + 2 ^ (n - 1)` is `2 ^ n - 1`. -/
theorem OMA.euclid_perfect_geom (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

theorem OMA.solution : OMA.R_PerfectNumbers_infinitely_many_even_perfect_R1.H2 := by
  intro k hp
  have hM : mersenne (k + 1) + 1 = 2 ^ (k + 1) := by
    have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    unfold mersenne
    omega
  have hcop : Nat.Coprime (2 ^ k) (mersenne (k + 1)) := by
    refine Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr ?_)
    have hdvd : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
    rw [Nat.odd_iff]
    omega
  have hgeom : ∑ i ∈ Finset.range (k + 1), 2 ^ i = mersenne (k + 1) := by
    have h := OMA.euclid_perfect_geom (k + 1)
    omega
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul (Nat.mul_pos (Nat.two_pow_pos k) hp.pos),
    ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two, hgeom,
    ArithmeticFunction.sigma_one_apply, Nat.Prime.sum_divisors hp, hM, pow_succ]
  ring

