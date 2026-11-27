import OMAStatements.S_oeis_a193282
import Mathlib

-- Problem: oeis-a193282
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P193282
open OMA.S_oeis_a193282

theorem sol : type_of% @OMA.S_oeis_a193282.main := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    subst hj
    unfold a
    rw [show k + 2 + (k + 2) - 1 = 2 * k + 3 by omega, show k + 2 + (k + 2) - 2 = 2 * k + 2 by omega,
      show k + 2 + (k + 2) - 3 = 2 * k + 1 by omega, show k + 2 + (k + 2) - 4 = 2 * k by omega,
      show (k + 2 + (k + 2)) / 2 = k + 2 by omega, show (2 * k + 3) / 2 = k + 1 by omega,
      show (2 * k + 2) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega,
      show 2 * k / 2 = k by omega, show k + 2 + (k + 2) = 2 * k + 3 + 1 by omega,
      Nat.factorial_succ (2 * k + 3), show 2 * k + 3 = 2 * k + 2 + 1 by omega,
      Nat.factorial_succ (2 * k + 2), show 2 * k + 2 = 2 * k + 1 + 1 by omega,
      Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k),
      show k + 2 = k + 1 + 1 by omega, Nat.factorial_succ (k + 1), Nat.factorial_succ k]
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    subst hj
    unfold a
    rw [show 2 * (k + 2) + 1 - 1 = 2 * k + 4 by omega, show 2 * (k + 2) + 1 - 2 = 2 * k + 3 by omega,
      show 2 * (k + 2) + 1 - 3 = 2 * k + 2 by omega, show 2 * (k + 2) + 1 - 4 = 2 * k + 1 by omega,
      show (2 * (k + 2) + 1) / 2 = k + 2 by omega, show (2 * k + 4) / 2 = k + 2 by omega,
      show (2 * k + 3) / 2 = k + 1 by omega, show (2 * k + 2) / 2 = k + 1 by omega,
      show (2 * k + 1) / 2 = k by omega, show 2 * (k + 2) + 1 = 2 * k + 4 + 1 by omega,
      Nat.factorial_succ (2 * k + 4), show 2 * k + 4 = 2 * k + 3 + 1 by omega,
      Nat.factorial_succ (2 * k + 3), show 2 * k + 3 = 2 * k + 2 + 1 by omega,
      Nat.factorial_succ (2 * k + 2), show 2 * k + 2 = 2 * k + 1 + 1 by omega,
      Nat.factorial_succ (2 * k + 1),
      show k + 2 = k + 1 + 1 by omega, Nat.factorial_succ (k + 1), Nat.factorial_succ k]
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * k + 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

end OMA.P193282

theorem OMA.solution : type_of% @OMA.S_oeis_a193282.main := OMA.P193282.sol
