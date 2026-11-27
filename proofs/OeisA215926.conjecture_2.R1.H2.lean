import OMAReductions.R_OeisA215926_conjecture_2_R1

-- Step OeisA215926.conjecture_2.R1.H2: hypothesis H2 of reduction OeisA215926.conjecture_2.R1
-- Credit: @marcusbuffett

theorem OMA.solution : OMA.R_OeisA215926_conjecture_2_R1.H2 := by
  intro j q hq h2q hlt
  have hcop : Nat.Coprime (2 ^ j) q :=
    ((Nat.coprime_primes Nat.prime_two hq).2 (by omega)).pow_left j
  have hs : ∑ d ∈ (2 ^ j).divisors, d = 2 ^ (j + 1) - 1 := by
    rw [Nat.sum_divisors_prime_pow Nat.prime_two]
    simpa using Nat.geomSum_eq (m := 2) (n := j + 1) (by decide)
  have hpos := hq.pos
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul (by positivity), Nat.abundant_iff_sum_divisors,
    hcop.sum_divisors_mul, hs, hq.divisors]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({q} : Finset ℕ) by simp; omega),
    Finset.sum_singleton, pow_succ]
  have hp := Nat.two_pow_pos j
  have ht : 2 ^ j * 2 - 1 + 1 = 2 ^ j * 2 := by omega
  apply Or.imp Eq.symm id
  apply eq_or_lt_of_le
  nlinarith [congrArg (· * q) ht]

