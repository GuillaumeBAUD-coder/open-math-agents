import OMAStatements.S_oeis_a024719
import Mathlib

-- Problem: oeis-a024719
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P024719
open OMA.S_oeis_a024719

lemma ratio (m : ℕ) : ((3 * (m + 1)).choose (m + 1) : ℚ) * (((m : ℚ) + 1) * (2 * m + 2) * (2 * m + 1))
    = ((3 * m).choose m : ℚ) * ((3 * m + 3) * (3 * m + 2) * (3 * m + 1)) := by
  rw [Nat.cast_choose ℚ (by omega), Nat.cast_choose ℚ (by omega),
    show 3 * (m + 1) - (m + 1) = (2 * m + 1) + 1 by omega, show 3 * m - m = 2 * m by omega,
    show 3 * (m + 1) = ((3 * m + 1) + 1) + 1 by ring,
    Nat.factorial_succ (3 * m + 1 + 1), Nat.factorial_succ (3 * m + 1), Nat.factorial_succ (3 * m),
    Nat.factorial_succ (2 * m + 1), Nat.factorial_succ (2 * m), Nat.factorial_succ m]
  have h1 : (m.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * m).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem sol : type_of% @OMA.S_oeis_a024719.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold a
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
    show m + 2 + 1 = (m + 1 + 1) + 1 by ring, Finset.sum_range_succ,
    show m + 1 + 1 = (m + 1) + 1 by ring, Finset.sum_range_succ (n := m + 1)]
  have r1 := ratio (m + 1)
  rw [show m + 1 + 1 = m + 2 by ring] at r1
  push_cast at r1 ⊢
  rw [show m + 1 + 1 = m + 2 by ring]
  have r1' : ((3 * (m + 2)).choose (m + 2) : ℚ) * ((2 * (m : ℚ) + 4) * (2 * m + 3)) =
      ((3 * (m + 1)).choose (m + 1) : ℚ) * (3 * (3 * (m : ℚ) + 5) * (3 * m + 4)) := by
    have h : ((m : ℚ) + 2) ≠ 0 := by positivity
    apply mul_left_cancel₀ h
    linear_combination r1
  linear_combination (1 / 3 : ℚ) * r1'

theorem OMA.solution : type_of% @OMA.S_oeis_a024719.main := OMA.P024719.sol
