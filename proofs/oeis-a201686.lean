import OMAStatements.S_oeis_a201686
import Mathlib

-- Problem: oeis-a201686
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P201686
open OMA.S_oeis_a201686

lemma L1 (k : ℕ) : ((2 * k + 1).choose k : ℚ) = ((2 * k).choose k : ℚ) * (2 * k + 1) / (k + 1) := by
  rw [Nat.cast_choose ℚ (by omega), Nat.cast_choose ℚ (by omega),
    show 2 * k + 1 - k = k + 1 by omega, show 2 * k - k = k by omega,
    Nat.factorial_succ (2 * k), Nat.factorial_succ k]
  have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma L2 (k : ℕ) : ((2 * (k + 1)).choose (k + 1) : ℚ) = ((2 * k).choose k : ℚ) * ((2 * k + 2) * (2 * k + 1)) / ((k + 1) * (k + 1)) := by
  rw [Nat.cast_choose ℚ (by omega), Nat.cast_choose ℚ (by omega),
    show 2 * (k + 1) - (k + 1) = k + 1 by omega, show 2 * k - k = k by omega,
    show 2 * (k + 1) = (2 * k + 1) + 1 by ring,
    Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k), Nat.factorial_succ k]
  have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem sol : type_of% @OMA.S_oeis_a201686.main := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    subst hj
    unfold a
    rw [show k + 2 + (k + 2) - 1 = 2 * (k + 1) + 1 by omega, show k + 2 + (k + 2) - 2 = 2 * (k + 1) by omega,
      show k + 2 + (k + 2) - 3 = 2 * k + 1 by omega, show k + 2 + (k + 2) - 4 = 2 * k by omega,
      show (k + 2 + (k + 2)) / 2 = k + 2 by omega, show (2 * (k + 1) + 1) / 2 = k + 1 by omega,
      show 2 * (k + 1) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega,
      show 2 * k / 2 = k by omega, show k + 2 + (k + 2) = 2 * (k + 1 + 1) by ring]
    suffices H : ((2 * (k + 1 + 1) : ℕ) + 1 : ℚ) * (((2 * (k + 1 + 1)).choose (k + 2) : ℚ) - 2) + 2 * (-((2 * (k + 1 + 1) : ℕ) : ℚ) - 1) * (((2 * (k + 1) + 1).choose (k + 1) : ℚ) - 2) +
        (-3 * ((2 * (k + 1 + 1) : ℕ) : ℚ) + 7) * (((2 * (k + 1)).choose (k + 1) : ℚ) - 2) +
        2 * (4 * ((2 * (k + 1 + 1) : ℕ) : ℚ) - 9) * (((2 * k + 1).choose k : ℚ) - 2) +
        4 * (-((2 * (k + 1 + 1) : ℕ) : ℚ) + 3) * (((2 * k).choose k : ℚ) - 2) = 0 by
      exact_mod_cast H
    rw [L2 (k + 1), L1 (k + 1), L2 k, L1 k]
    push_cast
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    subst hj
    unfold a
    rw [show 2 * (k + 2) + 1 - 1 = 2 * (k + 1 + 1) by omega, show 2 * (k + 2) + 1 - 2 = 2 * (k + 1) + 1 by omega,
      show 2 * (k + 2) + 1 - 3 = 2 * (k + 1) by omega, show 2 * (k + 2) + 1 - 4 = 2 * k + 1 by omega,
      show (2 * (k + 2) + 1) / 2 = k + 2 by omega, show 2 * (k + 1 + 1) / 2 = k + 1 + 1 by omega,
      show (2 * (k + 1) + 1) / 2 = k + 1 by omega, show 2 * (k + 1) / 2 = k + 1 by omega,
      show (2 * k + 1) / 2 = k by omega, show 2 * (k + 2) + 1 = 2 * (k + 1 + 1) + 1 by ring]
    suffices H : ((2 * (k + 1 + 1) + 1 : ℕ) + 1 : ℚ) * (((2 * (k + 1 + 1) + 1).choose (k + 1 + 1) : ℚ) - 2) + 2 * (-((2 * (k + 1 + 1) + 1 : ℕ) : ℚ) - 1) * (((2 * (k + 1 + 1)).choose (k + 1 + 1) : ℚ) - 2) +
        (-3 * ((2 * (k + 1 + 1) + 1 : ℕ) : ℚ) + 7) * (((2 * (k + 1) + 1).choose (k + 1) : ℚ) - 2) +
        2 * (4 * ((2 * (k + 1 + 1) + 1 : ℕ) : ℚ) - 9) * (((2 * (k + 1)).choose (k + 1) : ℚ) - 2) +
        4 * (-((2 * (k + 1 + 1) + 1 : ℕ) : ℚ) + 3) * (((2 * k + 1).choose k : ℚ) - 2) = 0 by
      exact_mod_cast H
    rw [L1 (k + 1 + 1), L2 (k + 1), L1 (k + 1), L2 k, L1 k]
    push_cast
    field_simp
    ring

end OMA.P201686

theorem OMA.solution : type_of% @OMA.S_oeis_a201686.main := OMA.P201686.sol
