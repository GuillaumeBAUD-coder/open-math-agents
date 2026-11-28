import OMAStatements.S_oeis_a259457

-- Problem: A259457: From higher-order arithmetic progressions.
-- Upstream: formal-conjectures statements/oeis-a259457.lean:0 (declaration OMA.S_oeis_a259457.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Writing (n+3)! = (n+3) (n+2) (n+1)!, (n+2)! = (n+2) (n+1)! for the three terms, the left side is
(n+1)! times a polynomial in n that vanishes identically. -/

theorem OMA.solution : type_of% @OMA.S_oeis_a259457.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := rfl
  have e2 : m + 2 - 2 = m := rfl
  rw [e1, e2]
  unfold OMA.S_oeis_a259457.a
  have f5 : ((m + 2 + 3).factorial : ℚ) = ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m + 3).factorial : ℚ) := by
    have e : m + 2 + 3 = m + 3 + 1 + 1 := by ring
    rw [e, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f4 : ((m + 1 + 3).factorial : ℚ) = ((m : ℚ) + 4) * ((m + 3).factorial : ℚ) := by
    have e : m + 1 + 3 = m + 3 + 1 := by ring
    rw [e, Nat.factorial_succ]
    push_cast
    ring
  rw [f5, f4]
  push_cast
  ring
