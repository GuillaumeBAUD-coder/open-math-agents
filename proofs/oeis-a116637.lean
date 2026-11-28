import OMAStatements.S_oeis_a116637

-- Problem: A116637: G.f. satisfies: A(x) = x/series_reversion(x/G(x)) where A(x) + A(-x) = 2*G(x^2) and G(x) is the g.f. of A046646.
-- Upstream: formal-conjectures statements/oeis-a116637.lean:0 (declaration OMA.S_oeis_a116637.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: (k+2) a(2k+3) = (3k+4) a(2k+2) and 2(2k+3) a(2k+2) = 3(3k+2) a(2k+1) from the factorial formula; for odd and for even n the recurrence is a linear combination of these after multiplying by a nonzero factor.

open OMA.S_oeis_a116637 in
theorem OMA.solution : type_of% @OMA.S_oeis_a116637.main := by
  have hodd : ∀ k : ℕ, a (2 * k + 1) = 2 * ((3 * k + 1).factorial : ℚ)
      / (((k + 1).factorial : ℚ) * ((2 * k + 1).factorial : ℚ)) := by
    intro k
    unfold a
    rw [if_neg (show ¬ (2 * k + 1 = 0) by omega), if_pos (show (2 * k + 1) % 2 = 1 by omega),
      show (2 * k + 1) / 2 = k by omega]
  have heven : ∀ k : ℕ, a (2 * k + 2) = 2 * ((3 * k + 3).factorial : ℚ)
      / (((k + 1).factorial : ℚ) * ((2 * k + 3).factorial : ℚ)) := by
    intro k
    unfold a
    rw [if_neg (show ¬ (2 * k + 2 = 0) by omega), if_neg (show ¬ ((2 * k + 2) % 2 = 1) by omega),
      show (2 * k + 2) / 2 = k + 1 by omega, show 3 * (k + 1) = 3 * k + 3 by ring,
      show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
  have hodd3 : ∀ k : ℕ, a (2 * k + 3) = 2 * ((3 * k + 4).factorial : ℚ)
      / (((k + 2).factorial : ℚ) * ((2 * k + 3).factorial : ℚ)) := by
    intro k
    have h := hodd (k + 1)
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, show 3 * (k + 1) + 1 = 3 * k + 4 by ring,
      show k + 1 + 1 = k + 2 by ring] at h
    exact h
  have F1 : ∀ k : ℕ, ((3 * k + 4).factorial : ℚ) = (3 * (k : ℚ) + 4) * ((3 * k + 3).factorial : ℚ) := by
    intro k
    rw [show 3 * k + 4 = 3 * k + 3 + 1 by ring, Nat.factorial_succ (3 * k + 3)]
    push_cast
    ring
  have F2 : ∀ k : ℕ, ((k + 2).factorial : ℚ) = ((k : ℚ) + 2) * ((k + 1).factorial : ℚ) := by
    intro k
    rw [show k + 2 = k + 1 + 1 by ring, Nat.factorial_succ (k + 1)]
    push_cast
    ring
  have F3 : ∀ k : ℕ, ((3 * k + 3).factorial : ℚ)
      = (3 * (k : ℚ) + 3) * (3 * (k : ℚ) + 2) * ((3 * k + 1).factorial : ℚ) := by
    intro k
    rw [show 3 * k + 3 = 3 * k + 1 + 1 + 1 by ring, Nat.factorial_succ (3 * k + 1 + 1),
      Nat.factorial_succ (3 * k + 1)]
    push_cast
    ring
  have F4 : ∀ k : ℕ, ((2 * k + 3).factorial : ℚ)
      = (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 2) * ((2 * k + 1).factorial : ℚ) := by
    intro k
    rw [show 2 * k + 3 = 2 * k + 1 + 1 + 1 by ring, Nat.factorial_succ (2 * k + 1 + 1),
      Nat.factorial_succ (2 * k + 1)]
    push_cast
    ring
  have r1 : ∀ k : ℕ, ((k : ℚ) + 2) * a (2 * k + 3) = (3 * (k : ℚ) + 4) * a (2 * k + 2) := by
    intro k
    rw [hodd3 k, heven k, F1 k, F2 k]
    field
  have r2 : ∀ k : ℕ,
      2 * (2 * (k : ℚ) + 3) * a (2 * k + 2) = 3 * (3 * (k : ℚ) + 2) * a (2 * k + 1) := by
    intro k
    rw [heven k, hodd k, F3 k, F4 k]
    field
  intro n hn
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 3 ∨ n = 2 * m + 4 := ⟨(n - 3) / 2, by omega⟩
  · rw [show 2 * m + 3 - 1 = 2 * m + 2 by omega, show 2 * m + 3 - 2 = 2 * m + 1 by omega]
    have e1 := r1 m
    have e2 := r2 m
    push_cast
    apply mul_left_cancel₀ (show ((m : ℚ) + 2) * (2 * (m : ℚ) + 3) ≠ 0 by positivity)
    linear_combination
      (2 * (m : ℚ) + 3) * (4 * (2 * (m : ℚ) + 3) * (2 * (m : ℚ) + 4) * (6 * (m : ℚ) + 8)) * e1
      + ((4 * (2 * (m : ℚ) + 3) * (2 * (m : ℚ) + 4) * (6 * (m : ℚ) + 8)) * (3 * (m : ℚ) + 4)
          + ((m : ℚ) + 2) * (-36 * (2 * (m : ℚ) + 3))) / 2 * e2
  · rw [show 2 * m + 4 - 1 = 2 * m + 3 by omega, show 2 * m + 4 - 2 = 2 * m + 2 by omega]
    have e1 := r1 m
    have e2 := r2 (m + 1)
    rw [show 2 * (m + 1) + 2 = 2 * m + 4 by ring, show 2 * (m + 1) + 1 = 2 * m + 3 by ring] at e2
    push_cast at e2 ⊢
    apply mul_left_cancel₀ (show 2 * (2 * (m : ℚ) + 5) * ((m : ℚ) + 2) ≠ 0 by positivity)
    linear_combination
      ((m : ℚ) + 2) * (4 * (2 * (m : ℚ) + 4) * (2 * (m : ℚ) + 5) * (6 * (m : ℚ) + 11)) * e2
      + (3 * (3 * (m : ℚ) + 5) * (4 * (2 * (m : ℚ) + 4) * (2 * (m : ℚ) + 5) * (6 * (m : ℚ) + 11))
          + 2 * (2 * (m : ℚ) + 5) * (-36 * (2 * (m : ℚ) + 4))) * e1
