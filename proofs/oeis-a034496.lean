import OMAStatements.S_oeis_a034496

-- Problem: A034496: Sum of n-th powers of divisors of 8.
-- Upstream: formal-conjectures statements/oeis-a034496.lean:0 (declaration OMA.S_oeis_a034496.main)
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- The divisors of 8 are 1, 2, 4, 8, and 1 + 2^n + 4^n + 8^n = (1 + 2^n) * (1 + 4^n) with both factors at least 2.

theorem OMA.solution : type_of% @OMA.S_oeis_a034496.main := by
  intro n
  have h : OMA.S_oeis_a034496.a n = (1 + 2 ^ n) * (1 + 4 ^ n) := by
    unfold OMA.S_oeis_a034496.a
    rw [show (8 : ℕ).divisors = {1, 2, 4, 8} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [show (8 : ℕ) = 2 * 4 by norm_num, mul_pow]
    ring
  rw [h]
  apply Nat.not_prime_mul
  · have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  · have h1 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega
