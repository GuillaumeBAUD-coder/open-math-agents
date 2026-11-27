import OMAStatements.S_oeis_a240558
import Mathlib

-- Problem: oeis-a240558
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P240558
open OMA.S_oeis_a240558

theorem sol : type_of% @OMA.S_oeis_a240558.main := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    subst hj
    unfold a
    rw [show k + 1 + (k + 1) - 1 = 2 * k + 1 by omega, show k + 1 + (k + 1) - 2 = 2 * k by omega,
      show (k + 1 + (k + 1)) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega,
      show 2 * k / 2 = k by omega, show k + 1 + (k + 1) = (2 * k + 1) + 1 by omega,
      Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k), Nat.factorial_succ k]
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    rw [pow_succ, pow_succ]
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    subst hj
    unfold a
    rw [show 2 * (k + 1) + 1 - 1 = (2 * k + 1) + 1 by omega, show 2 * (k + 1) + 1 - 2 = 2 * k + 1 by omega,
      show (2 * (k + 1) + 1) / 2 = k + 1 by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega,
      show (2 * k + 1) / 2 = k by omega, show 2 * (k + 1) + 1 = ((2 * k + 1) + 1) + 1 by omega,
      Nat.factorial_succ (2 * k + 1 + 1), Nat.factorial_succ (2 * k + 1), Nat.factorial_succ k]
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * k + 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    rw [pow_succ, pow_succ]
    field_simp
    ring

end OMA.P240558

theorem OMA.solution : type_of% @OMA.S_oeis_a240558.main := OMA.P240558.sol
