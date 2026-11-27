import OMAStatements.S_oeis_a240558

-- Problem: A240558: a(n) = 2^n*n!/((floor(n/2)+1)*floor(n/2)!^2).
-- Upstream: formal-conjectures statements/oeis-a240558.lean:0 (declaration OMA.S_oeis_a240558.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a240558

open OMA.S_oeis_a240558

lemma solve : ∀ n : ℕ, 2 ≤ n →
    -((n : ℚ) + 2) * ((n : ℚ) ^ 2 - 5) * a n + 8 * (-2 * (n : ℚ) - 1) * a (n - 1) +
      16 * ((n : ℚ) - 1) * ((n : ℚ) ^ 2 + 2 * n - 4) * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 2 ∨ n = 2 * m + 3 := ⟨(n - 2) / 2, by omega⟩
  · unfold a
    rw [show 2 * m + 2 - 1 = 2 * m + 1 by omega, show 2 * m + 2 - 2 = 2 * m by omega,
      show (2 * m + 2) / 2 = m + 1 by omega, show (2 * m + 1) / 2 = m by omega,
      show 2 * m / 2 = m by omega]
    rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring]
    simp only [Nat.factorial_succ, pow_succ]
    have h1 : ((m.factorial : ℕ) : ℚ) ≠ 0 := by positivity
    have h2 : (((2 * m).factorial : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · unfold a
    rw [show 2 * m + 3 - 1 = 2 * m + 2 by omega, show 2 * m + 3 - 2 = 2 * m + 1 by omega,
      show (2 * m + 3) / 2 = m + 1 by omega, show (2 * m + 2) / 2 = m + 1 by omega,
      show (2 * m + 1) / 2 = m by omega]
    rw [show 2 * m + 3 = 2 * m + 1 + 1 + 1 by ring, show 2 * m + 2 = 2 * m + 1 + 1 by ring]
    simp only [Nat.factorial_succ, pow_succ]
    have h1 : ((m.factorial : ℕ) : ℚ) ≠ 0 := by positivity
    have h2 : (((2 * m + 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

end OMA.P_oeis_a240558

theorem OMA.solution : type_of% @OMA.S_oeis_a240558.main := OMA.P_oeis_a240558.solve
