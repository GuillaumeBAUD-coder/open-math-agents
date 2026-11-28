import OMAStatements.S_oeis_a059324

-- Problem: A059324: Numbers n such that 6n + 5 is composite.
-- Upstream: formal-conjectures statements/oeis-a059324.lean:0 (declaration OMA.S_oeis_a059324.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: q = p^2 + 6n - 4. For p = 2, q = 6n is even and not 2. For p = 3, q = 6n + 5, which
-- is composite for a term n. For any other prime p, p^2 leaves remainder 1 on division by 3, so
-- 3 divides q, and q > p^2 >= 4 gives q > 3, so q is not prime.

open OMA.S_oeis_a059324 in
theorem OMA.solution : type_of% @OMA.S_oeis_a059324.main := by
  rintro n ⟨-, hn⟩ ⟨p, q, hp, hq, hpq, heq⟩
  have hz : ((q + 4 : ℕ) : ℤ) = ((p ^ 2 + 6 * n : ℕ) : ℤ) := by
    push_cast
    linarith
  have hnat : q + 4 = p ^ 2 + 6 * n := by exact_mod_cast hz
  have hp2 : 2 * 2 ≤ p ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul hp.two_le hp.two_le
  by_cases h2 : p = 2
  · have h4 : p ^ 2 = 4 := by
      subst h2
      norm_num
    have hq2 : 2 ∣ q := ⟨3 * n, by omega⟩
    rcases hq.eq_one_or_self_of_dvd 2 hq2 with h | h
    · omega
    · omega
  · by_cases h3 : p = 3
    · have h9 : p ^ 2 = 9 := by
        subst h3
        norm_num
      have hq' : q = 6 * n + 5 := by omega
      apply hn
      rw [← hq']
      exact hq
    · have h0 : p % 3 ≠ 0 := by
        intro h0
        rcases hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h0) with h | h
        · omega
        · exact h3 h.symm
      have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by omega
      have hsq : p ^ 2 % 3 = 1 := by
        rw [Nat.pow_mod]
        rcases hp3 with h | h <;> simp [h]
      have hq3 : 3 ∣ q := by omega
      rcases hq.eq_one_or_self_of_dvd 3 hq3 with h | h
      · omega
      · omega
