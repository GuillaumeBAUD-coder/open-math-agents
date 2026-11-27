import OMAStatements.S_oeis_a157713

-- Problem: A157713: a(n) = (2*n+1)!*(2*n-2)!/((n-1)!*(n!)^2*6).
-- Upstream: formal-conjectures statements/oeis-a157713.lean:0 (declaration OMA.S_oeis_a157713.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a157713

open OMA.S_oeis_a157713

lemma solve : ∀ n : ℕ, 2 ≤ n → (n : ℚ) * a n - 4 * (2 * n + 1) * (2 * n - 3) * a (n - 1) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold a
  rw [show m + 2 - 1 = m + 1 by omega, show 2 * (m + 2) - 2 = 2 * m + 2 by omega,
    show 2 * (m + 1) - 2 = 2 * m by omega, show m + 1 - 1 = m by omega,
    show 2 * (m + 2) + 1 = (2 * m + 3) + 1 + 1 by ring, show 2 * (m + 1) + 1 = 2 * m + 3 by ring,
    show 2 * m + 2 = 2 * m + 1 + 1 by ring, show m + 2 = m + 1 + 1 by ring]
  simp only [Nat.factorial_succ]
  have h1 : ((m.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have h2 : (((2 * m).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have h3 : (((2 * m + 3).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end OMA.P_oeis_a157713

theorem OMA.solution : type_of% @OMA.S_oeis_a157713.main := OMA.P_oeis_a157713.solve
