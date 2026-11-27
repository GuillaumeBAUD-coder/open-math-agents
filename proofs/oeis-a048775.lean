import OMAStatements.S_oeis_a048775
import Mathlib

-- Problem: oeis-a048775
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P048775
open OMA.S_oeis_a048775

lemma r (k : ℕ) : ((2 * (k + 1) + 1).choose (k + 1 + 1) : ℚ)
    = ((2 * k + 1).choose (k + 1) : ℚ) * ((2 * (k : ℚ) + 3) * (2 * k + 2)) / ((k + 2) * (k + 1)) := by
  rw [Nat.cast_choose ℚ (by omega), Nat.cast_choose ℚ (by omega),
    show 2 * (k + 1) + 1 - (k + 1 + 1) = k + 1 by omega, show 2 * k + 1 - (k + 1) = k by omega,
    show 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 by ring, Nat.factorial_succ (2 * k + 1 + 1),
    Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (k + 1), Nat.factorial_succ k]
  have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((k + 1).factorial : ℚ) ≠ 0 := by positivity
  push_cast; field_simp; ring

theorem sol : type_of% @OMA.S_oeis_a048775.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [← Int.cast_inj (α := ℚ)]
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega,
    show m + 5 - 4 = m + 1 by omega]
  unfold a
  push_cast
  rw [show 2 * (m + 5) + 1 = 2 * (m + 4 + 1) + 1 by ring, show m + 5 + 1 = m + 4 + 1 + 1 by ring, r (m + 4),
    show 2 * (m + 4) + 1 = 2 * (m + 3 + 1) + 1 by ring, show m + 4 + 1 = m + 3 + 1 + 1 by ring, r (m + 3),
    show 2 * (m + 3) + 1 = 2 * (m + 2 + 1) + 1 by ring, show m + 3 + 1 = m + 2 + 1 + 1 by ring, r (m + 2),
    show 2 * (m + 2) + 1 = 2 * (m + 1 + 1) + 1 by ring, show m + 2 + 1 = m + 1 + 1 + 1 by ring, r (m + 1)]
  push_cast
  field_simp
  ring

end OMA.P048775

theorem OMA.solution : type_of% @OMA.S_oeis_a048775.main := OMA.P048775.sol
