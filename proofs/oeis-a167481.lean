import OMAStatements.S_oeis_a167481

-- Problem: A167481: Convolution of the central binomial coefficients A000984(n) and (-2)^n.
-- Upstream: formal-conjectures statements/oeis-a167481.lean:0 (declaration OMA.S_oeis_a167481.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a(k+1) = -2 a(k) + C(2k+2,k+1) and (k+1) C(2k+2,k+1) = 2(2k+1) C(2k,k); the recurrence is a linear combination of these.

open OMA.S_oeis_a167481 in
theorem OMA.solution : type_of% @OMA.S_oeis_a167481.main := by
  have hc : ∀ k : ℕ, ((k : ℤ) + 1) * ((Nat.centralBinom (k + 1) : ℕ) : ℤ)
      = 2 * (2 * (k : ℤ) + 1) * ((Nat.centralBinom k : ℕ) : ℤ) := by
    intro k
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hs : ∀ k : ℕ, a (k + 1) = -2 * a k + ((Nat.centralBinom (k + 1) : ℕ) : ℤ) := by
    intro k
    unfold a
    rw [Nat.centralBinom_eq_two_mul_choose, Finset.sum_range_succ _ (k + 1), Nat.sub_self,
      pow_zero, one_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show k + 1 - j = k - j + 1 by omega, pow_succ]
    ring
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 := hs (m + 1)
  have e0 := hs m
  have c := hc (m + 1)
  rw [show m + 1 + 1 = m + 2 by omega] at e1 c
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  push_cast at c ⊢
  linear_combination ((m : ℤ) + 2) * e1 + (2 - 4 * ((m : ℤ) + 2)) * e0 + c
