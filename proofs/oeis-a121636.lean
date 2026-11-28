import OMAStatements.S_oeis_a121636
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: unfold the defining first-order recurrence three times down to a(n-3); the a(n-3)
-- coefficients cancel and the factorial terms vanish by ring. No computer search.

namespace OMA.A121636Proof

open OMA.S_oeis_a121636

theorem step (k : ℕ) :
    a (k + 3) = ((k : ℤ) + 3) * ((k + 1).factorial : ℤ) + ((k : ℤ) + 2) * a (k + 2) := by
  rw [a]

theorem mainP : ∀ n : ℕ, 5 ≤ n →
    a n + (-2 * (n : ℤ) + 3) * a (n - 1) + ((n : ℤ) ^ 2 - 5 * (n : ℤ) + 7) * a (n - 2) +
      ((n : ℤ) - 3) ^ 2 * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega]
  rw [show m + 5 = (m + 2) + 3 by omega, step (m + 2), show m + 2 + 2 = (m + 1) + 3 by omega,
    step (m + 1), show m + 1 + 2 = m + 3 by omega, step m]
  simp only [Nat.factorial_succ]
  push_cast
  ring

end OMA.A121636Proof

open OMA.A121636Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a121636.main := mainP
