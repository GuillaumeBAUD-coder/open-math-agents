import OMAStatements.S_oeis_a274002

-- Problem: A274002: Primes p of the form (q-1)^2+1 that are a divisor of 4^(q-1)-1 where q is prime.
-- Upstream: formal-conjectures statements/oeis-a274002.lean:0 (declaration OMA.S_oeis_a274002.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: (4^k)^(q-1) = (4^(q-1))^k, and x - 1 divides x^k - 1, so a divisor of
-- 4^(q-1) - 1 divides (4^k)^(q-1) - 1 for every k; conversely take k = 1.

open OMA.S_oeis_a274002 in
theorem OMA.solution : type_of% @OMA.S_oeis_a274002.main := by
  intro p
  constructor
  · rintro ⟨hp, q, hq, hpq, hd⟩
    refine ⟨hp, q, hq, hpq, fun k => ?_⟩
    rw [← pow_mul, mul_comm, pow_mul]
    exact hd.trans (Nat.sub_one_dvd_pow_sub_one (4 ^ (q - 1)) k)
  · rintro ⟨hp, q, hq, hpq, hd⟩
    refine ⟨hp, q, hq, hpq, ?_⟩
    have h1 := hd 1
    rw [pow_one] at h1
    exact h1
