import OMAStatements.S_oeis_a157713
import Mathlib

-- Problem: oeis-a157713
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P157713
open OMA.S_oeis_a157713

theorem sol : type_of% @OMA.S_oeis_a157713.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold a
  rw [show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega,
    show 2 * (m + 2) + 1 = (2 * m + 4) + 1 by ring, show 2 * (m + 2) - 2 = (2 * m + 1) + 1 by omega,
    show 2 * (m + 1) + 1 = 2 * m + 3 by ring, show 2 * (m + 1) - 2 = 2 * m by omega,
    Nat.factorial_succ (2 * m + 4), show 2 * m + 4 = (2 * m + 3) + 1 by ring,
    Nat.factorial_succ (2 * m + 3), Nat.factorial_succ (2 * m + 1),
    show 2 * m + 1 = 2 * m + 1 by rfl, Nat.factorial_succ (2 * m),
    show m + 2 = (m + 1) + 1 by ring, Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  have h1 : (m.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * m).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((2 * m + 3).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end OMA.P157713

theorem OMA.solution : type_of% @OMA.S_oeis_a157713.main := OMA.P157713.sol
