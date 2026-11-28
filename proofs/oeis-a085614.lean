import OMAStatements.S_oeis_a085614

-- Problem: A085614: Number of elementary arches of size n.
-- Upstream: formal-conjectures statements/oeis-a085614.lean:0 (declaration OMA.S_oeis_a085614.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: (k+3)(k+2) a(k+3) = 12(3k+4)(3k+2) a(k+1) from (m+2)!! = (m+2) m!!; the recurrence is the sum of this relation at k = n-3 and at k = n-4.

open OMA.S_oeis_a085614 in
theorem OMA.solution : type_of% @OMA.S_oeis_a085614.main := by
  have two : ∀ k : ℕ, ((k : ℚ) + 3) * ((k : ℚ) + 2) * a (k + 3)
      = 12 * (3 * (k : ℚ) + 4) * (3 * (k : ℚ) + 2) * a (k + 1) := by
    intro k
    have p : (2 : ℚ) ^ (k + 2) = 4 * 2 ^ k := by ring
    unfold a
    rw [show k + 3 - 1 = k + 2 by omega, show k + 1 - 1 = k by omega,
      show 3 * (k + 2) = 3 * k + 2 + 2 + 2 by ring,
      Nat.doubleFactorial_add_two (3 * k + 2 + 2), Nat.doubleFactorial_add_two (3 * k + 2),
      Nat.doubleFactorial_add_two (3 * k), Nat.doubleFactorial_add_two k,
      show k + 3 = k + 1 + 1 + 1 by ring, Nat.factorial_succ (k + 1 + 1),
      Nat.factorial_succ (k + 1), p]
    push_cast
    field
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega]
  have t1 := two (m + 1)
  have t0 := two m
  rw [show m + 1 + 3 = m + 4 by ring, show m + 1 + 1 = m + 2 by ring] at t1
  push_cast at t1 ⊢
  linear_combination t1 + t0
