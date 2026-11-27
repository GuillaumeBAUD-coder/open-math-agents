import OMAStatements.S_oeis_a090526

-- Problem: A090526: Primes arising in A090525, or 0 if A090525(n) = 0.
-- Upstream: formal-conjectures statements/oeis-a090526.lean:0 (declaration OMA.S_oeis_a090526.main)
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- For N = n^n >= 4 the quotient N / (N / 2) equals 2, a prime, so the set of admissible k is nonempty. Its infimum is then an element of the set: it is at least 1 and the quotient is prime, hence nonzero.

theorem OMA.solution : type_of% @OMA.S_oeis_a090526.main := by
  intro n hn
  have hN : 4 ≤ n ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
      _ ≤ n ^ n := Nat.pow_le_pow_right (by omega) hn
  have hdiv : n ^ n / (n ^ n / 2) = 2 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  have hne : {k : ℕ | 1 ≤ k ∧ (n ^ n / k).Prime}.Nonempty := by
    refine ⟨n ^ n / 2, ?_, ?_⟩
    · omega
    · rw [hdiv]
      exact Nat.prime_two
  have hmem := Nat.sInf_mem hne
  have h1 : 1 ≤ sInf {k : ℕ | 1 ≤ k ∧ (n ^ n / k).Prime} := hmem.1
  unfold OMA.S_oeis_a090526.a OMA.S_oeis_a090526.a090525
  rw [if_neg (by omega)]
  exact hmem.2.ne_zero
