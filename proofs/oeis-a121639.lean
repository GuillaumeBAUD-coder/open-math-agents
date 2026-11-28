import OMAStatements.S_oeis_a121639
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: unfold the defining first-order recurrence four times down to a(n-4); the a(n-4)
-- coefficients cancel and the factorial terms vanish by ring. No computer search.

namespace OMA.A121639Proof

open OMA.S_oeis_a121639

theorem step (k : ℕ) :
    a (k + 4) = ((k : ℤ) + 4) * a (k + 3) + ((k + 3).factorial : ℤ) - ((k + 1).factorial : ℤ) := by
  rw [a]

theorem mainP : ∀ n : ℕ, 7 ≤ n →
    a n + (-2 * (n : ℤ) + 1) * a (n - 1) + (n : ℤ) * ((n : ℤ) - 2) * a (n - 2) +
      (2 * (n : ℤ) - 7) * a (n - 3) - ((n : ℤ) - 3) * ((n : ℤ) - 5) * a (n - 4) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega]
  rw [show m + 7 = (m + 3) + 4 by omega, step (m + 3), show m + 3 + 3 = (m + 2) + 4 by omega,
    step (m + 2), show m + 2 + 3 = (m + 1) + 4 by omega, step (m + 1),
    show m + 1 + 3 = m + 4 by omega, step m]
  simp only [Nat.factorial_succ]
  push_cast
  ring

end OMA.A121639Proof

open OMA.A121639Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a121639.main := mainP
