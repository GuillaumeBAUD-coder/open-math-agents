import OMAStatements.S_oeis_a147803

-- Problem oeis-a147803: for m coprime to 5 with m < 5^n, rad(m (5^n - m) 5^n) = 5 rad(m (5^n - m)).
-- Upstream: statements/oeis-a147803.lean (declaration OMA.S_oeis_a147803.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: n >= 1 because m = 0 is not coprime to 5. Both m and 5^n - m are coprime to 5^n, so the radical is
-- multiplicative on the product (m (5^n - m)) * 5^n, and rad(5^n) = 5.

open UniqueFactorizationMonoid

theorem OMA.solution : type_of% @OMA.S_oeis_a147803.main := by
  intro n m hm hlt
  have hn : n ≠ 0 := by
    rintro rfl
    have h0 : m = 0 := by simpa using hlt
    subst h0
    simp at hm
  have h5 : Nat.Coprime m (5 ^ n) := Nat.Coprime.pow_right n hm
  have h5' : Nat.Coprime (5 ^ n - m) (5 ^ n) := (Nat.coprime_self_sub_left hlt.le).mpr h5
  have hc : Nat.Coprime (m * (5 ^ n - m)) (5 ^ n) := Nat.Coprime.mul_left h5 h5'
  rw [radical_mul (Nat.coprime_iff_isRelPrime.mp hc), radical_pow _ hn,
    radical_of_prime (Nat.prime_iff.mp Nat.prime_five), normalize_eq, mul_comm]
