import OMAStatements.S_oeis_a121580
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: unfold the defining first-order recurrence four times down to a(n-4); the a(n-4) coefficients cancel and the factorial terms vanish by ring. No computer search.

namespace OMA.A121580Proof

open OMA.S_oeis_a121580
theorem step (k : ℕ) : a (k + 2) = a (k + 1) + ((k + 1).factorial : ℚ) * (1 + ((k : ℚ) + 2) * ((k : ℚ) + 1) / 2) := by
  rw [a]

theorem mainP : ∀ n : ℕ, 5 ≤ n → a n + (-(n : ℚ) - 4) * a (n - 1) + 3 * ((n : ℚ) + 1) * a (n - 2) + 2 * (-2 * (n : ℚ) + 3) * a (n - 3) + 2 * ((n : ℚ) - 3) * a (n - 4) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega,
    show m + 5 - 4 = m + 1 by omega]
  rw [show m + 5 = (m + 3) + 2 by omega, step (m + 3), show m + 3 + 1 = (m + 2) + 2 by omega, step (m + 2),
    show m + 2 + 1 = (m + 1) + 2 by omega, step (m + 1), show m + 1 + 1 = m + 2 by omega, step m]
  simp only [Nat.factorial_succ]
  push_cast
  ring

end OMA.A121580Proof

open OMA.A121580Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a121580.main := mainP
