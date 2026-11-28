import OMAStatements.S_oeis_a112703

-- Problem: A112703: Partial sum of Catalan numbers A000108 multiplied by powers of 9.
-- Upstream: formal-conjectures statements/oeis-a112703.lean:0 (declaration OMA.S_oeis_a112703.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a(k+1) = a(k) + C(k+1) 9^(k+1) and (k+2) C(k+1) = 2(2k+1) C(k); the recurrence is a linear combination of these.

open OMA.S_oeis_a112703 in
theorem OMA.solution : type_of% @OMA.S_oeis_a112703.main := by
  have hc : ∀ k : ℕ,
      ((k : ℤ) + 2) * (catalan (k + 1) : ℤ) = 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ) := by
    intro k
    have e1 : ((k : ℤ) + 1 + 1) * (catalan (k + 1) : ℤ) = ((k + 1).centralBinom : ℤ) := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom (k + 1)
    have e2 : ((k : ℤ) + 1) * (catalan k : ℤ) = (k.centralBinom : ℤ) := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom k
    have e3 : ((k : ℤ) + 1) * ((k + 1).centralBinom : ℤ)
        = 2 * (2 * (k : ℤ) + 1) * (k.centralBinom : ℤ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    apply mul_left_cancel₀ (show ((k : ℤ) + 1) ≠ 0 by positivity)
    linear_combination ((k : ℤ) + 1) * e1 + e3 - 2 * (2 * (k : ℤ) + 1) * e2
  have hs : ∀ k : ℕ, a (k + 1) = a k + (catalan (k + 1) : ℤ) * 9 ^ (k + 1) := by
    intro k
    unfold a
    rw [Finset.sum_range_succ _ (k + 1)]
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have s1 := hs (m + 1)
  have s0 := hs m
  have c1 := hc (m + 1)
  rw [show m + 1 + 1 = m + 2 by omega] at s1 c1
  push_cast at c1 ⊢
  linear_combination ((m : ℤ) + 3) * s1 + (18 - 36 * ((m : ℤ) + 2)) * s0 + 9 ^ (m + 2) * c1
