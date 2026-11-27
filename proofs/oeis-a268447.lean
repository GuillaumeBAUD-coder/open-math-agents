import OMAStatements.S_oeis_a268447
import Mathlib

-- Problem: oeis-a268447
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P268447
open OMA.S_oeis_a268447

theorem sol : type_of% @OMA.S_oeis_a268447.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  unfold a
  rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 8 = m + 1 by omega,
    show m + 8 - 8 = m by omega, show 2 * (m + 9) + 1 = (2 * m + 18) + 1 by ring,
    show 2 * (m + 8) + 1 = 2 * m + 17 by ring, show m + 9 + 10 = (m + 18) + 1 by ring,
    show m + 8 + 10 = m + 18 by ring, Nat.factorial_succ (2 * m + 18),
    show 2 * m + 18 = (2 * m + 17) + 1 by ring, Nat.factorial_succ (2 * m + 17),
    Nat.factorial_succ m, Nat.factorial_succ (m + 18)]
  have h1 : (m.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((m + 18).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end OMA.P268447

theorem OMA.solution : type_of% @OMA.S_oeis_a268447.main := OMA.P268447.sol
