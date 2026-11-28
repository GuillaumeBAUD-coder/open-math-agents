import OMAStatements.S_oeis_a309353

-- Problem: A309353: Let d(1), d(2), ..., d(q) be the q divisors of a number m. The sequence lists the numbers m such that {phi(d(1)), phi(d(2)), ..., phi(d(q))} is the set of the divisors of a number k, where phi is the Euler totient function.
-- Upstream: formal-conjectures statements/oeis-a309353.lean:0 (declaration OMA.S_oeis_a309353.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: k is not 0, since phi(1) = 1 is a value and 0 has no divisors. Write k = 2^i * r
-- with r odd. If r > 1, an odd prime q divides r, hence q divides k, so q = phi(d) for some
-- divisor d of m; but phi(d) is even for d > 2 and phi(1) = phi(2) = 1, a contradiction.

open OMA.S_oeis_a309353 in
theorem OMA.solution : type_of% @OMA.S_oeis_a309353.main := by
  intro m k hm hS
  have hk : k ≠ 0 := by
    rintro rfl
    have h1 : Nat.totient 1 ∈ (Nat.divisors m).image Nat.totient :=
      Finset.mem_image_of_mem _ (Nat.one_mem_divisors.mpr (by omega))
    rw [hS, Nat.divisors_zero] at h1
    exact Finset.notMem_empty _ h1
  obtain ⟨i, r, hr, hkr⟩ := Nat.exists_eq_two_pow_mul_odd hk
  refine ⟨i, ?_⟩
  have hr1 : r = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqr⟩ := Nat.exists_prime_and_dvd hne
    have hr2 : r % 2 = 1 := Nat.odd_iff.mp hr
    have hq2 : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · rw [h] at hqr
        obtain ⟨c, hc⟩ := hqr
        omega
      · exact h
    have hqk : q ∈ Nat.divisors k := by
      rw [Nat.mem_divisors]
      refine ⟨?_, hk⟩
      rw [hkr]
      exact Dvd.dvd.mul_left hqr _
    rw [← hS, Finset.mem_image] at hqk
    obtain ⟨d, hd, hdq⟩ := hqk
    have hd1 : 0 < d := Nat.pos_of_mem_divisors hd
    rcases Nat.lt_or_ge 2 d with h | h
    · obtain ⟨c, hc⟩ := Nat.totient_even h
      rw [hdq] at hc
      omega
    · have hq1 : q = 1 := by
        rw [← hdq]
        interval_cases d
        · exact Nat.totient_one
        · exact Nat.totient_two
      exact hq.one_lt.ne' hq1
  rw [hkr, hr1, mul_one]
